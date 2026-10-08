-- Prove2me | solution 1 for HilbertSixteenth.no_limit_cycles_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:39:15.179163+00:00
-- url     : https://prove2.me/submissions/ca61bbb5-0d37-40e4-a6bd-70f687048cc6

import Mathlib
import Definitions.Def_HilbertSixteenth_PolyFields

set_option autoImplicit false

open HilbertSixteenth in
theorem H16lin_eval_affine (f : Poly2) (hf : f.totalDegree ≤ 1) :
    ∃ a b c : ℝ, ∀ p : ℝ × ℝ, evalAt f p = a * p.1 + b * p.2 + c := by
  refine ⟨∑ d ∈ f.support, f.coeff d * (if d 0 = 1 then 1 else 0),
          ∑ d ∈ f.support, f.coeff d * (if d 1 = 1 then 1 else 0),
          ∑ d ∈ f.support, f.coeff d * (if d 0 = 0 ∧ d 1 = 0 then 1 else 0), ?_⟩
  intro p
  rw [evalAt, MvPolynomial.eval_eq', Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have h1 := MvPolynomial.le_totalDegree hd
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h1
  have h2 : d 0 + d 1 ≤ 1 := le_trans h1 hf
  rw [Fin.prod_univ_two]
  rcases (by omega : d 0 = 0 ∧ d 1 = 0 ∨ d 0 = 1 ∧ d 1 = 0 ∨ d 0 = 0 ∧ d 1 = 1) with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [ha, hb]

open HilbertSixteenth in
theorem solution (V : PolyField) (hV : V.degree ≤ 1) (O : Set (ℝ × ℝ)) :
    ¬ IsLimitCycle V.toField O := by
  obtain ⟨a, b, c, hP⟩ := H16lin_eval_affine V.P (le_trans (le_max_left _ _) hV)
  obtain ⟨d, e, g, hQ⟩ := H16lin_eval_affine V.Q (le_trans (le_max_right _ _) hV)
  have hF : ∀ z : ℝ × ℝ, V.toField z = (a * z.1 + b * z.2 + c, d * z.1 + e * z.2 + g) := by
    intro z; simp [PolyField.toField, hP, hQ]
  rintro ⟨⟨γ, T, ⟨hsol, hT, hper, t0, ht0⟩, rfl⟩, U, hU, hOU, hiso⟩
  have hcont : Continuous γ := continuous_iff_continuousAt.2 fun t => (hsol t).continuousAt
  have hx : ∀ t, HasDerivAt (fun s => (γ s).1) (a * (γ t).1 + b * (γ t).2 + c) t := by
    intro t
    have := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := γ t)).comp_hasDerivAt t (hsol t)
    rw [hF] at this
    exact this
  have hy : ∀ t, HasDerivAt (fun s => (γ s).2) (d * (γ t).1 + e * (γ t).2 + g) t := by
    intro t
    have := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := γ t)).comp_hasDerivAt t (hsol t)
    rw [hF] at this
    exact this
  have hc1 : Continuous fun t => (γ t).1 := continuous_fst.comp hcont
  have hc2 : Continuous fun t => (γ t).2 := continuous_snd.comp hcont
  have hper0 : γ T = γ 0 := by simpa using hper 0
  set X := ∫ t in (0:ℝ)..T, (γ t).1 with hX
  set Y := ∫ t in (0:ℝ)..T, (γ t).2 with hY
  have eq1 : a * X + b * Y + c * T = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hx t)
      ((((hc1.const_mul a).add (hc2.const_mul b)).add continuous_const).intervalIntegrable 0 T)
    rw [hper0, sub_self, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at h
    · simp only [smul_eq_mul, sub_zero] at h
      linarith
    all_goals first
      | exact ((hc1.const_mul a).add (hc2.const_mul b)).intervalIntegrable _ _
      | exact (hc1.const_mul a).intervalIntegrable _ _
      | exact (hc2.const_mul b).intervalIntegrable _ _
      | exact continuous_const.intervalIntegrable _ _
  have eq2 : d * X + e * Y + g * T = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hy t)
      ((((hc1.const_mul d).add (hc2.const_mul e)).add continuous_const).intervalIntegrable 0 T)
    rw [hper0, sub_self, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at h
    · simp only [smul_eq_mul, sub_zero] at h
      linarith
    all_goals first
      | exact ((hc1.const_mul d).add (hc2.const_mul e)).intervalIntegrable _ _
      | exact (hc1.const_mul d).intervalIntegrable _ _
      | exact (hc2.const_mul e).intervalIntegrable _ _
      | exact continuous_const.intervalIntegrable _ _
  set p : ℝ × ℝ := (X / T, Y / T) with hp
  have hp1 : a * p.1 + b * p.2 + c = 0 := by
    have : a * p.1 + b * p.2 + c = (a * X + b * Y + c * T) / T := by
      simp only [hp]; field_simp
    rw [this, eq1, zero_div]
  have hp2 : d * p.1 + e * p.2 + g = 0 := by
    have : d * p.1 + e * p.2 + g = (d * X + e * Y + g * T) / T := by
      simp only [hp]; field_simp
    rw [this, eq2, zero_div]
  -- scaled solutions
  have hsolΓ : ∀ l : ℝ, IsSolution V.toField (fun t => p + l • (γ t - p)) := by
    intro l t
    have := (((hsol t).sub_const p).const_smul l).const_add p
    refine HasDerivAt.congr_deriv this ?_
    rw [hF, hF]
    ext
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      linear_combination (l - 1) * hp1
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      linear_combination (l - 1) * hp2
  have hcomp : IsCompact (Set.range γ) :=
    Function.Periodic.compact_of_continuous (fun t => hper t) hT.ne' hcont
  obtain ⟨z0, hz0O, hmax⟩ := hcomp.exists_isMaxOn (Set.range_nonempty γ)
    (continuous_id.dist continuous_const).continuousOn (f := fun z => dist z p)
  have hmax' : ∀ z ∈ Set.range γ, dist z p ≤ dist z0 p := fun z hz => hmax hz
  set R := dist z0 p with hR
  have hRpos : 0 < R := by
    by_contra hneg
    have h1 := hmax' (γ t0) ⟨t0, rfl⟩
    have h2 := hmax' (γ 0) ⟨0, rfl⟩
    have h1' : γ t0 = p := dist_le_zero.1 (by linarith)
    have h2' : γ 0 = p := dist_le_zero.1 (by linarith)
    exact ht0 (h1'.trans h2'.symm)
  obtain ⟨δ, hδ, hthick⟩ := hcomp.exists_thickening_subset_open hU hOU
  set ε := δ / (2 * R) with hε
  have hεpos : 0 < ε := by positivity
  set l := 1 + ε with hl
  have hl0 : l ≠ 0 := by positivity
  have hdistΓ : ∀ z : ℝ × ℝ, dist (p + l • (z - p)) p = l * dist z p := by
    intro z
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hsub : Set.range (fun t => p + l • (γ t - p)) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨γ t, ⟨t, rfl⟩, ?_⟩
    have hkey : p + l • (γ t - p) - γ t = ε • (γ t - p) := by
      rw [hl]; module
    rw [dist_eq_norm, hkey, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
    have := hmax' (γ t) ⟨t, rfl⟩
    calc ε * dist (γ t) p ≤ ε * R := by gcongr
      _ = δ / 2 := by rw [hε]; field_simp
      _ < δ := by linarith
  have hPO : IsPeriodicOrbit V.toField (Set.range (fun t => p + l • (γ t - p))) := by
    refine ⟨fun t => p + l • (γ t - p), T, ⟨hsolΓ l, hT, fun t => by simp only [hper], t0, ?_⟩, rfl⟩
    intro h
    apply ht0
    have h' := add_left_cancel h
    have h'' := smul_right_injective (ℝ × ℝ) hl0 h'
    simpa using h''
  have heq := hiso _ hPO hsub
  obtain ⟨t1, rfl⟩ := hz0O
  have hw : p + l • (γ t1 - p) ∈ Set.range γ := heq ▸ ⟨t1, rfl⟩
  have := hmax' _ hw
  rw [hdistΓ] at this
  have : l * R ≤ R := this
  have : ε * R ≤ 0 := by rw [hl] at this; linarith
  have : 0 < ε * R := mul_pos hεpos hRpos
  linarith

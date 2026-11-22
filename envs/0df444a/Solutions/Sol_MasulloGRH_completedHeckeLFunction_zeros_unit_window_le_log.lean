-- Prove2me | solution 1 for MasulloGRH.completedHeckeLFunction_zeros_unit_window_le_log
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:04:49.135187+00:00
-- url     : https://prove2.me/submissions/5cb29b65-1657-4cb7-a883-57a332976994

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_heckeLFunction_reflected_order_left_half
import Theorems.Thm_MasulloGRH_heckeLFunction_no_zero_re_ge_one
import Theorems.Thm_MasulloGRH_heckeLFunction_polynomial_growth_on_vertical_strips
import Theorems.Thm_MasulloGRH_heckeLFunction_inv_polynomial_growth_on_one_line

set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_completedHeckeLFunction_zeros_unit_window_le_log

open Filter Topology Metric

variable {F : Type*} [Field F] [NumberField F]

lemma heckeL_nf (χ : HeckeCharacter F) : MeromorphicNFOn (heckeLFunction χ) Set.univ := by
  have hex := heckeLFunction_exists_meromorphic_continuation F χ
  unfold heckeLFunction
  rw [dif_pos hex]
  exact hex.choose_spec.1

lemma gamma_analyticAt_of_re_pos {u : ℂ} (hu : 0 < u.re) : AnalyticAt ℂ Complex.Gamma u := by
  have hopen : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticAt (s := {v : ℂ | 0 < v.re})
  · intro v hv
    apply (Complex.differentiableAt_Gamma v _).differentiableWithinAt
    intro m hm
    have : v.re = -(m : ℝ) := by rw [hm]; simp
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [Set.mem_ofPred_eq] at hv
    linarith
  · exact hopen.mem_nhds hu

lemma cpow_analyticAt {b : ℂ} (hb : b ∈ Complex.slitPlane) {g : ℂ → ℂ} {x : ℂ}
    (hg : AnalyticAt ℂ g x) : AnalyticAt ℂ (fun s => b ^ g s) x :=
  (analyticAt_const).cpow hg hb

lemma pi_mem_slitPlane : (Real.pi : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.mpr Real.pi_pos

lemma two_pi_mem_slitPlane : (2 * Real.pi : ℂ) ∈ Complex.slitPlane := by
  have : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [this]
  exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

lemma archLFactor_meromorphicAt (χ : HeckeCharacter F) (w : NumberField.InfinitePlace F) (s : ℂ) :
    MeromorphicAt (χ.archLFactor w) s := by
  unfold HeckeCharacter.archLFactor
  split_ifs with h
  · apply MeromorphicAt.mul
    · exact (cpow_analyticAt pi_mem_slitPlane (by fun_prop)).meromorphicAt
    · exact (Meromorphic.Gamma _).comp_analyticAt (by fun_prop)
  · apply MeromorphicAt.mul
    · exact (cpow_analyticAt two_pi_mem_slitPlane (by fun_prop)).meromorphicAt
    · exact (Meromorphic.Gamma _).comp_analyticAt (by fun_prop)

lemma cpow_ne_zero_of_ne_zero {b : ℂ} (hb : b ≠ 0) (x : ℂ) : b ^ x ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hb]
  exact Complex.exp_ne_zero _

lemma realFactor_analytic_ne_zero (b a : ℂ) {s : ℂ} (hre : 0 < ((s + b + a) / 2).re) :
    AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-((z + b + a) / 2)) *
      Complex.Gamma ((z + b + a) / 2)) s ∧
    (Real.pi : ℂ) ^ (-((s + b + a) / 2)) * Complex.Gamma ((s + b + a) / 2) ≠ 0 := by
  have hf : AnalyticAt ℂ (fun z : ℂ => (z + b + a) / 2) s := by fun_prop (disch := norm_num)
  refine ⟨?_, ?_⟩
  · apply AnalyticAt.mul
    · exact cpow_analyticAt pi_mem_slitPlane hf.neg
    · exact AnalyticAt.comp (x := s) (f := fun z : ℂ => (z + b + a) / 2)
        (gamma_analyticAt_of_re_pos hre) hf
  · apply mul_ne_zero
    · exact cpow_ne_zero_of_ne_zero (by exact_mod_cast Real.pi_ne_zero) _
    · exact Complex.Gamma_ne_zero_of_re_pos hre

lemma complexFactor_analytic_ne_zero (b a : ℂ) {s : ℂ} (hre : 0 < (s + b + a).re) :
    AnalyticAt ℂ (fun z : ℂ => (2 * Real.pi : ℂ) ^ (-(z + b + a)) *
      Complex.Gamma (z + b + a)) s ∧
    (2 * Real.pi : ℂ) ^ (-(s + b + a)) * Complex.Gamma (s + b + a) ≠ 0 := by
  have hf : AnalyticAt ℂ (fun z : ℂ => z + b + a) s := by fun_prop
  refine ⟨?_, ?_⟩
  · apply AnalyticAt.mul
    · exact cpow_analyticAt two_pi_mem_slitPlane hf.neg
    · exact AnalyticAt.comp (x := s) (f := fun z : ℂ => z + b + a)
        (gamma_analyticAt_of_re_pos hre) hf
  · apply mul_ne_zero
    · exact cpow_ne_zero_of_ne_zero (by norm_num [Real.pi_ne_zero]) _
    · exact Complex.Gamma_ne_zero_of_re_pos hre

lemma archLFactor_analytic_ne_zero (χ : HeckeCharacter F) (w : NumberField.InfinitePlace F)
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (χ.archLFactor w) s ∧ χ.archLFactor w s ≠ 0 := by
  by_cases h : w.IsReal
  · have hre : 0 < ((s + χ.archExponent w * Complex.I + χ.archParity w) / 2).re := by
      simp
      positivity
    have := realFactor_analytic_ne_zero (χ.archExponent w * Complex.I) (χ.archParity w) hre
    have he : χ.archLFactor w = fun z : ℂ =>
        (Real.pi : ℂ) ^ (-((z + χ.archExponent w * Complex.I + χ.archParity w) / 2)) *
        Complex.Gamma ((z + χ.archExponent w * Complex.I + χ.archParity w) / 2) := by
      funext z
      simp only [HeckeCharacter.archLFactor, if_pos h]
    rw [he]
    exact this
  · have hre : 0 < (s + χ.archExponent w * Complex.I + (χ.archWeight w : ℂ) / 2).re := by
      simp
      positivity
    have := complexFactor_analytic_ne_zero (χ.archExponent w * Complex.I)
      ((χ.archWeight w : ℂ) / 2) hre
    have he : χ.archLFactor w = fun z : ℂ =>
        (2 * Real.pi : ℂ) ^ (-(z + χ.archExponent w * Complex.I + (χ.archWeight w : ℂ) / 2)) *
        Complex.Gamma (z + χ.archExponent w * Complex.I + (χ.archWeight w : ℂ) / 2) := by
      funext z
      simp only [HeckeCharacter.archLFactor, if_neg h]
    rw [he]
    exact this

lemma gammaFactor_meromorphicAt (χ : HeckeCharacter F) (s : ℂ) :
    MeromorphicAt χ.gammaFactor s := by
  have : χ.gammaFactor = ∏ w : NumberField.InfinitePlace F, χ.archLFactor w := by
    funext z
    simp [HeckeCharacter.gammaFactor]
  rw [this]
  exact MeromorphicAt.prod (fun w _ => archLFactor_meromorphicAt χ w s)

lemma gammaFactor_analytic_ne_zero (χ : HeckeCharacter F) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ χ.gammaFactor s ∧ χ.gammaFactor s ≠ 0 := by
  have : χ.gammaFactor = ∏ w : NumberField.InfinitePlace F, χ.archLFactor w := by
    funext z
    simp [HeckeCharacter.gammaFactor]
  refine ⟨?_, ?_⟩
  · rw [this]
    exact Finset.analyticAt_prod _ (fun w _ => (archLFactor_analytic_ne_zero χ w hs).1)
  · rw [HeckeCharacter.gammaFactor, Finset.prod_ne_zero_iff]
    exact fun w _ => (archLFactor_analytic_ne_zero χ w hs).2


lemma prod_meromorphicOn (χ : HeckeCharacter F) :
    MeromorphicOn (fun s => χ.gammaFactor s * heckeLFunction χ s) Set.univ :=
  fun s _ => (gammaFactor_meromorphicAt χ s).mul ((heckeL_nf χ).meromorphicOn s trivial)

lemma ord_completed (χ : HeckeCharacter F) (ρ : ℂ) :
    meromorphicOrderAt (completedHeckeLFunction χ) ρ =
      meromorphicOrderAt χ.gammaFactor ρ + meromorphicOrderAt (heckeLFunction χ) ρ := by
  unfold completedHeckeLFunction
  rw [meromorphicOrderAt_toMeromorphicNFOn (prod_meromorphicOn χ) (Set.mem_univ ρ)]
  exact meromorphicOrderAt_mul (gammaFactor_meromorphicAt χ ρ)
    ((heckeL_nf χ).meromorphicOn ρ trivial)

lemma ord_completed_of_re_pos (χ : HeckeCharacter F) {ρ : ℂ} (hρ : 0 < ρ.re) :
    meromorphicOrderAt (completedHeckeLFunction χ) ρ =
      meromorphicOrderAt (heckeLFunction χ) ρ := by
  rw [ord_completed]
  obtain ⟨ha, hne⟩ := gammaFactor_analytic_ne_zero χ hρ
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hne]
  simp

lemma zero_re_bounds (χ : HeckeCharacter F) {ρ : ℂ}
    (hρ : 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ) : 0 < ρ.re ∧ ρ.re < 1 := by
  by_cases h0 : ρ.re ≤ 0
  · exfalso
    rw [ord_completed, heckeLFunction_reflected_order_left_half F χ ρ (by linarith)] at hρ
    have := heckeLFunction_no_zero_re_ge_one F χ⁻¹ (1 - ρ) (by simp; linarith)
    exact absurd hρ (not_lt.mpr this)
  · push Not at h0
    refine ⟨h0, ?_⟩
    by_contra h1
    push Not at h1
    rw [ord_completed_of_re_pos χ h0] at hρ
    exact absurd hρ (not_lt.mpr (heckeLFunction_no_zero_re_ge_one F χ ρ h1))

lemma heckeL_ord_ne_top (χ : HeckeCharacter F) (ρ : ℂ) :
    meromorphicOrderAt (heckeLFunction χ) ρ ≠ ⊤ := by
  obtain ⟨N, -, C, T, h⟩ := heckeLFunction_inv_polynomial_growth_on_one_line F χ
  have hne := (h (|T| + 1) (by rw [abs_of_nonneg (by positivity)]; linarith [le_abs_self T])).1
  have h0 : meromorphicOrderAt (heckeLFunction χ) (1 + ((|T| + 1 : ℝ) : ℂ) * Complex.I) = 0 :=
    ((heckeL_nf χ) (Set.mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr hne
  exact (heckeL_nf χ).meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ _) (Set.mem_univ ρ) (by rw [h0]; simp)

lemma untop_pos {x : WithTop ℤ} (h0 : 0 < x) (ht : x ≠ ⊤) : 0 < x.untop₀ := by
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp ht
  simp only [WithTop.untop₀_coe]
  exact_mod_cast h0

lemma finsum_mem_le_of_subset {s t : Set ℂ} (f : ℂ → ℝ) (ht : t.Finite) (hst : s ⊆ t)
    (hf : ∀ x ∈ t, 0 ≤ f x) : ∑ᶠ x ∈ s, f x ≤ ∑ᶠ x ∈ t, f x := by
  have hs := ht.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum f hs, finsum_mem_eq_finite_toFinset_sum f ht]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact hst hx
  · intro x hx _
    exact hf x ((Set.Finite.mem_toFinset ht).mp hx)

/-- A function in normal form at `z` which is bounded near `z` is analytic at `z`. -/
lemma analyticAt_of_nf_bdd {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicNFAt f z) (B : ℝ)
    (hB : ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ B) : AnalyticAt ℂ f z := by
  rw [← hf.meromorphicOrderAt_nonneg_iff_analyticAt]
  by_contra h
  push Not at h
  have ht := tendsto_cobounded_of_meromorphicOrderAt_neg h
  rw [← tendsto_norm_atTop_iff_cobounded] at ht
  have h1 : ∀ᶠ w in 𝓝[≠] z, B < ‖f w‖ := ht.eventually_gt_atTop B
  have h2 : ∀ᶠ w in 𝓝[≠] z, ‖f w‖ ≤ B := nhdsWithin_le_nhds hB
  have := (h1.and h2).exists
  obtain ⟨w, hw1, hw2⟩ := this
  linarith


/-- The set of zeros of `L(s, χ)` whose ordinate lies in `[T - 1, T + 1]`. -/
abbrev window (χ : HeckeCharacter F) (T : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧ |ρ.im - T| ≤ 1}

lemma zero_untop_pos (χ : HeckeCharacter F) {ρ : ℂ}
    (hρ : 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ) :
    0 < (meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ := by
  have he := ord_completed_of_re_pos χ (zero_re_bounds χ hρ).1
  rw [he] at hρ ⊢
  exact untop_pos hρ (heckeL_ord_ne_top χ ρ)

/-- On a set `K` containing the zero `ρ`, the multiplicity of `ρ` as a zero of the completed
L-function is the value at `ρ` of the divisor of `L_f` on `K`. -/
lemma divisor_eq (χ : HeckeCharacter F) {K : Set ℂ} {ρ : ℂ} (hρK : ρ ∈ K)
    (hρ : 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ) :
    MeromorphicOn.divisor (heckeLFunction χ) K ρ =
      (meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ := by
  rw [MeromorphicOn.divisor_apply ((heckeL_nf χ).meromorphicOn.mono_set (Set.subset_univ K)) hρK,
    ord_completed_of_re_pos χ (zero_re_bounds χ hρ).1]

lemma zeros_in_compact_finite (χ : HeckeCharacter F) {K : Set ℂ} (hK : IsCompact K) :
    {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧ ρ ∈ K}.Finite := by
  apply ((MeromorphicOn.divisor (heckeLFunction χ) K).finiteSupport hK).subset
  intro ρ hρ
  rw [Function.mem_support, divisor_eq χ hρ.2 hρ.1]
  exact (zero_untop_pos χ hρ.1).ne'

lemma window_subset_ball (χ : HeckeCharacter F) (T : ℝ) :
    window χ T ⊆ closedBall (1 + (T : ℂ) * Complex.I) 2 := by
  intro ρ hρ
  obtain ⟨hr0, hr1⟩ := zero_re_bounds χ hρ.1
  have h1 := hρ.2
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (ρ - (1 + (T : ℂ) * Complex.I)).re = ρ.re - 1 := by simp
  have him : (ρ - (1 + (T : ℂ) * Complex.I)).im = ρ.im - T := by simp
  rw [hre, him]
  have : |ρ.re - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  linarith

lemma window_finite (χ : HeckeCharacter F) (T : ℝ) : (window χ T).Finite := by
  apply (zeros_in_compact_finite χ (isCompact_closedBall (1 + (T : ℂ) * Complex.I) 2)).subset
  intro ρ hρ
  exact ⟨hρ.1, window_subset_ball χ T hρ⟩

lemma small_bound (χ : HeckeCharacter F) (T1 : ℝ) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ T : ℝ, |T| ≤ T1 →
      ∑ᶠ ρ ∈ window χ T,
        (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ) ≤ K0 := by
  set S := {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧
    ρ ∈ closedBall (0 : ℂ) (T1 + 2)} with hS
  have hSfin : S.Finite := zeros_in_compact_finite χ (isCompact_closedBall _ _)
  have hnn : ∀ ρ ∈ S,
      (0 : ℝ) ≤ (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ) := by
    intro ρ hρ
    exact_mod_cast (zero_untop_pos χ hρ.1).le
  refine ⟨∑ᶠ ρ ∈ S, (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ),
    ?_, ?_⟩
  · have := finsum_mem_le_of_subset
      (fun ρ => (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ))
      hSfin (Set.empty_subset S) hnn
    simpa using this
  · intro T hT
    apply finsum_mem_le_of_subset _ hSfin _ hnn
    intro ρ hρ
    refine ⟨hρ.1, ?_⟩
    obtain ⟨hr0, hr1⟩ := zero_re_bounds χ hρ.1
    have h1 := hρ.2
    rw [mem_closedBall, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h2 : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h3 : |ρ.im| ≤ |ρ.im - T| + |T| := by
      have := abs_add_le (ρ.im - T) T
      simpa using this
    linarith


/-- `L_f` is analytic on the closed disc of radius `3` around `1 + iT` once `|T|` is large. -/
lemma analytic_on_disc (χ : HeckeCharacter F) {M0 C0 T0 : ℝ} (hM0 : 0 < M0)
    (hg : ∀ s : ℂ, -3 ≤ s.re → s.re ≤ 5 → T0 ≤ |s.im| →
      ‖heckeLFunction χ s‖ ≤ C0 * |s.im| ^ M0)
    {T : ℝ} (hT : T0 + 4 ≤ |T|) :
    AnalyticOnNhd ℂ (heckeLFunction χ) (closedBall (1 + (T : ℂ) * Complex.I) 3) := by
  intro z hz
  apply analyticAt_of_nf_bdd ((heckeL_nf χ) (Set.mem_univ z)) (max C0 0 * (|z.im| + 1) ^ M0)
  filter_upwards [ball_mem_nhds z one_pos] with w hw
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [mem_ball, dist_eq_norm] at hw
  have hre1 := Complex.abs_re_le_norm (z - (1 + (T : ℂ) * Complex.I))
  have him1 := Complex.abs_im_le_norm (z - (1 + (T : ℂ) * Complex.I))
  have hre2 := Complex.abs_re_le_norm (w - z)
  have him2 := Complex.abs_im_le_norm (w - z)
  have e1 : (z - (1 + (T : ℂ) * Complex.I)).re = z.re - 1 := by simp
  have e2 : (z - (1 + (T : ℂ) * Complex.I)).im = z.im - T := by simp
  have e3 : (w - z).re = w.re - z.re := by simp
  have e4 : (w - z).im = w.im - z.im := by simp
  rw [e1] at hre1
  rw [e2] at him1
  rw [e3] at hre2
  rw [e4] at him2
  have a1 := abs_le.mp (hre1.trans hz)
  have a2 := abs_le.mp (hre2.trans hw.le)
  have a3 : |T| - |w.im| ≤ |T - w.im| := abs_sub_abs_le_abs_sub T w.im
  have a4 : |T - w.im| ≤ |T - z.im| + |z.im - w.im| := abs_sub_le T z.im w.im
  have a5 : |T - z.im| = |z.im - T| := abs_sub_comm _ _
  have a6 : |z.im - w.im| = |w.im - z.im| := abs_sub_comm _ _
  have a7 : |w.im| - |z.im| ≤ |w.im - z.im| := abs_sub_abs_le_abs_sub w.im z.im
  have hwim : T0 ≤ |w.im| := by linarith
  have hwim2 : |w.im| ≤ |z.im| + 1 := by linarith
  calc ‖heckeLFunction χ w‖ ≤ C0 * |w.im| ^ M0 := hg w (by linarith) (by linarith) hwim
    _ ≤ max C0 0 * |w.im| ^ M0 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C0 0 * (|z.im| + 1) ^ M0 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hwim2 hM0.le)
          (le_max_right _ _)

/-- The bound `|L_f(z)| ≤ A₁ (|T| + 4)^{M₀}` on the circle of radius `3` around `1 + iT`. -/
lemma bound_on_sphere (χ : HeckeCharacter F) {M0 C0 T0 : ℝ} (hM0 : 0 < M0)
    (hg : ∀ s : ℂ, -3 ≤ s.re → s.re ≤ 5 → T0 ≤ |s.im| →
      ‖heckeLFunction χ s‖ ≤ C0 * |s.im| ^ M0)
    {T : ℝ} (hT : T0 + 4 ≤ |T|) :
    ∀ z ∈ sphere (1 + (T : ℂ) * Complex.I) |3|,
      ‖heckeLFunction χ z‖ ≤ max C0 1 * (|T| + 4) ^ M0 := by
  intro z hz
  rw [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at hz
  have hre1 := Complex.abs_re_le_norm (z - (1 + (T : ℂ) * Complex.I))
  have him1 := Complex.abs_im_le_norm (z - (1 + (T : ℂ) * Complex.I))
  have e1 : (z - (1 + (T : ℂ) * Complex.I)).re = z.re - 1 := by simp
  have e2 : (z - (1 + (T : ℂ) * Complex.I)).im = z.im - T := by simp
  rw [e1, hz] at hre1
  rw [e2, hz] at him1
  have a1 := abs_le.mp hre1
  have a3 : |T| - |z.im| ≤ |T - z.im| := abs_sub_abs_le_abs_sub T z.im
  have a5 : |T - z.im| = |z.im - T| := abs_sub_comm _ _
  have a7 : |z.im| - |T| ≤ |z.im - T| := abs_sub_abs_le_abs_sub z.im T
  have hzim : T0 ≤ |z.im| := by linarith
  have hzim2 : |z.im| ≤ |T| + 4 := by linarith
  calc ‖heckeLFunction χ z‖ ≤ C0 * |z.im| ^ M0 := hg z (by linarith) (by linarith) hzim
    _ ≤ max C0 1 * |z.im| ^ M0 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C0 1 * (|T| + 4) ^ M0 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hzim2 hM0.le)
          (by positivity)


/-- Jensen's inequality for `L_f` on the discs of radii `2 < 3` around `1 + iT`, combined with the
lower bound for `|L_f(1 + iT)|`. -/
lemma jensen_step (χ : HeckeCharacter F) {M0 C0 T0 : ℝ} (hM0 : 0 < M0)
    (hg : ∀ s : ℂ, -3 ≤ s.re → s.re ≤ 5 → T0 ≤ |s.im| →
      ‖heckeLFunction χ s‖ ≤ C0 * |s.im| ^ M0)
    {T : ℝ} (hT : T0 + 4 ≤ |T|) (hne : heckeLFunction χ (1 + (T : ℂ) * Complex.I) ≠ 0) :
    ∑ᶠ ρ ∈ window χ T,
        (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ) ≤
      Real.log (max C0 1 * (|T| + 4) ^ M0 / ‖heckeLFunction χ (1 + (T : ℂ) * Complex.I)‖) /
        Real.log (3 / 2) := by
  set c : ℂ := 1 + (T : ℂ) * Complex.I with hc
  set D := MeromorphicOn.divisor (heckeLFunction χ) (closedBall c 2) with hD
  have hA := analytic_on_disc χ hM0 hg hT
  have hM1 : 1 ≤ max C0 1 * (|T| + 4) ^ M0 :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (Real.one_le_rpow (by linarith [abs_nonneg T]) hM0.le)
  have J := AnalyticOnNhd.sum_divisor_le (c := c) (r := 2) (R := 3) (f := heckeLFunction χ)
    (by norm_num) (by norm_num) hM1
    (by rwa [abs_of_pos (by norm_num : (0 : ℝ) < 3)]) hne (bound_on_sphere χ hM0 hg hT)
  rw [abs_two] at J
  have hDnn : ∀ u, 0 ≤ D u := by
    intro u
    have := MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hA.mono (closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 3)))
    exact this u
  have hfin : (Function.support fun u => (D u : ℝ)).Finite := by
    apply (D.finiteSupport (isCompact_closedBall c 2)).subset
    intro u hu
    simpa using hu
  have hcast : ((∑ᶠ u, D u : ℤ) : ℝ) = ∑ᶠ u, (D u : ℝ) := by
    have := map_finsum (Int.castRingHom ℝ) (f := fun u => D u)
      (D.finiteSupport (isCompact_closedBall c 2))
    simpa using this
  calc ∑ᶠ ρ ∈ window χ T,
        (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ)
      = ∑ᶠ ρ ∈ window χ T, (D ρ : ℝ) := by
        apply finsum_mem_congr rfl
        intro ρ hρ
        rw [hD, divisor_eq χ (window_subset_ball χ T hρ) hρ.1]
    _ ≤ ∑ᶠ ρ ∈ Function.support (fun u => (D u : ℝ)), (D ρ : ℝ) := by
        apply finsum_mem_le_of_subset _ hfin _ (fun u _ => by exact_mod_cast hDnn u)
        intro ρ hρ
        rw [Function.mem_support, hD, divisor_eq χ (window_subset_ball χ T hρ) hρ.1]
        exact_mod_cast (zero_untop_pos χ hρ.1).ne'
    _ = ∑ᶠ u, (D u : ℝ) := finsum_mem_support _
    _ = ((∑ᶠ u, D u : ℤ) : ℝ) := hcast.symm
    _ ≤ _ := J


lemma log_arith {A1 C1 M0 x t : ℝ} {N : ℕ} (hA1 : 1 ≤ A1) (hM0 : 0 < M0) (hx : 0 < x)
    (ht : 0 ≤ t) (hinv : x⁻¹ ≤ C1 * t ^ N) :
    Real.log (A1 * (t + 4) ^ M0 / x) ≤
      (Real.log A1 / Real.log 2 + Real.log (max C1 1) / Real.log 2 + 2 * M0 + 2 * N) *
        Real.log (t + 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ : Real.log 2 ≤ Real.log (t + 2) := Real.log_le_log (by norm_num) (by linarith)
  have h4 : Real.log (t + 4) ≤ 2 * Real.log (t + 2) := by
    have e : Real.log ((t + 2) ^ 2) = 2 * Real.log (t + 2) := by
      rw [Real.log_pow]; norm_num
    rw [← e]
    apply Real.log_le_log (by linarith)
    nlinarith
  have h4' : 0 ≤ Real.log (t + 4) := Real.log_nonneg (by linarith)
  have hM : Real.log (A1 * (t + 4) ^ M0) = Real.log A1 + M0 * Real.log (t + 4) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by linarith)]
  have hX : Real.log (A1 * (t + 4) ^ M0 / x) = Real.log (A1 * (t + 4) ^ M0) + Real.log x⁻¹ := by
    rw [div_eq_mul_inv, Real.log_mul (by positivity) (by positivity)]
  have hA2 : x⁻¹ ≤ max C1 1 * (t + 4) ^ N := by
    refine hinv.trans ?_
    calc C1 * t ^ N ≤ max C1 1 * t ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C1 1 * (t + 4) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (by linarith) N)
            (by positivity)
  have hlx : Real.log x⁻¹ ≤ Real.log (max C1 1) + N * Real.log (t + 4) := by
    calc Real.log x⁻¹ ≤ Real.log (max C1 1 * (t + 4) ^ N) :=
          Real.log_le_log (by positivity) hA2
      _ = Real.log (max C1 1) + N * Real.log (t + 4) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlA1 : 0 ≤ Real.log A1 := Real.log_nonneg hA1
  have hlA2 : 0 ≤ Real.log (max C1 1) := Real.log_nonneg (le_max_right _ _)
  have e1 : Real.log A1 ≤ Real.log A1 / Real.log 2 * Real.log (t + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hℓ hlA1
  have e2 : Real.log (max C1 1) ≤ Real.log (max C1 1) / Real.log 2 * Real.log (t + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hℓ hlA2
  have e3 : M0 * Real.log (t + 4) ≤ 2 * M0 * Real.log (t + 2) := by nlinarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e4 : (N : ℝ) * Real.log (t + 4) ≤ 2 * N * Real.log (t + 2) := by nlinarith
  have hR : (Real.log A1 / Real.log 2 + Real.log (max C1 1) / Real.log 2 + 2 * M0 + 2 * N) *
        Real.log (t + 2) =
      Real.log A1 / Real.log 2 * Real.log (t + 2) +
        Real.log (max C1 1) / Real.log 2 * Real.log (t + 2) +
        2 * M0 * Real.log (t + 2) + 2 * N * Real.log (t + 2) := by ring
  rw [hX, hM, hR]
  linarith

lemma large_bound (χ : HeckeCharacter F) :
    ∃ K1 T1 : ℝ, ∀ T : ℝ, T1 ≤ |T| →
      ∑ᶠ ρ ∈ window χ T,
        (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ) ≤
          K1 * Real.log (|T| + 2) := by
  obtain ⟨M0, hM0, C0, T0, hg⟩ :=
    heckeLFunction_polynomial_growth_on_vertical_strips F χ (-3) 5 (by norm_num)
  obtain ⟨N, -, C1, T2, hinv⟩ := heckeLFunction_inv_polynomial_growth_on_one_line F χ
  refine ⟨(Real.log (max C0 1) / Real.log 2 + Real.log (max C1 1) / Real.log 2 + 2 * M0 +
    2 * N) / Real.log (3 / 2), max (T0 + 4) T2, ?_⟩
  intro T hT
  obtain ⟨hne, hb⟩ := hinv T (le_trans (le_max_right _ _) hT)
  have J := jensen_step χ hM0 hg (le_trans (le_max_left _ _) hT) hne
  have hx : 0 < ‖heckeLFunction χ (1 + (T : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hne
  have hinv' : ‖heckeLFunction χ (1 + (T : ℂ) * Complex.I)‖⁻¹ ≤ C1 * |T| ^ N := by
    rw [← norm_inv]; exact hb
  have hlog := log_arith (le_max_right C0 1) hM0 hx (abs_nonneg T) hinv'
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  calc _ ≤ _ := J
    _ ≤ (Real.log (max C0 1) / Real.log 2 + Real.log (max C1 1) / Real.log 2 + 2 * M0 +
          2 * N) * Real.log (|T| + 2) / Real.log (3 / 2) :=
        div_le_div_of_nonneg_right hlog hl32.le
    _ = _ := by ring

end Sol_MasulloGRH_completedHeckeLFunction_zeros_unit_window_le_log

open Sol_MasulloGRH_completedHeckeLFunction_zeros_unit_window_le_log in
theorem solution (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ C : ℝ, ∀ T : ℝ,
      {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧ |ρ.im - T| ≤ 1}.Finite ∧
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧ |ρ.im - T| ≤ 1},
          (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ)
        ≤ C * Real.log (|T| + 2) := by
  obtain ⟨K1, T1, hlarge⟩ := large_bound χ
  obtain ⟨K0, hK0, hsmall⟩ := small_bound χ T1
  refine ⟨max (K0 / Real.log 2) K1, fun T => ⟨window_finite χ T, ?_⟩⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ : Real.log 2 ≤ Real.log (|T| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  by_cases hT : T1 ≤ |T|
  · exact (hlarge T hT).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
  · have hT' : |T| ≤ T1 := le_of_lt (not_le.mp hT)
    calc _ ≤ K0 := hsmall T hT'
      _ = K0 / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ K0 / Real.log 2 * Real.log (|T| + 2) :=
          mul_le_mul_of_nonneg_left hℓ (div_nonneg hK0 hl2.le)
      _ ≤ max (K0 / Real.log 2) K1 * Real.log (|T| + 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)

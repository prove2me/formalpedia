-- Prove2me | solution 1 for HunterPDE.Parabolic.galerkin_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T09:37:55.051626+00:00
-- url     : https://prove2.me/submissions/443607db-c6dc-43e9-b162-c17cdd26c09c

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace P6525923f

open HunterPDE.Parabolic


-- ==== part A1 ====


/-! ## Linear Volterra equation with bounded measurable operator coefficient -/

section picard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Extension of a function on `[0, T]` to `ℝ` by clamping. -/
noncomputable def clampExt {T : ℝ} (hT : 0 ≤ T) (v : C(Icc (0:ℝ) T, E)) : ℝ → E :=
  fun s => v (projIcc 0 T hT s)

lemma clampExt_cont {T : ℝ} (hT : 0 ≤ T) (v : C(Icc (0:ℝ) T, E)) : Continuous (clampExt hT v) :=
  v.continuous.comp continuous_projIcc

lemma clampExt_mem {T : ℝ} (hT : 0 ≤ T) (v : C(Icc (0:ℝ) T, E)) {s : ℝ} (hs : s ∈ Icc 0 T) :
    clampExt hT v s = v ⟨s, hs⟩ := by
  simp [clampExt, projIcc_of_mem hT hs]

variable {T K : ℝ} (A : ℝ → E →L[ℝ] E) (F : ℝ → E)

lemma volterra_integrand_int
    (hAm : ∀ v : ℝ → E, Continuous v → AEStronglyMeasurable (fun s => A s (v s)) (volume.restrict (Ioc 0 T)))
    (hAb : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)), ‖A s‖ ≤ K)
    (hF : IntegrableOn F (Ioc 0 T)) (v : ℝ → E) (hv : Continuous v) :
    IntegrableOn (fun s => A s (v s) + F s) (Ioc 0 T) := by
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) T)) := isFiniteMeasure_restrict.2 (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hv.continuousOn
  have h1 : Integrable (fun s => A s (v s)) (volume.restrict (Ioc 0 T)) := by
    refine Integrable.mono' (integrable_const (K * B)) (hAm v hv) ?_
    filter_upwards [hAb, ae_restrict_mem measurableSet_Ioc] with s hs hsI
    calc ‖A s (v s)‖ ≤ ‖A s‖ * ‖v s‖ := (A s).le_opNorm _
      _ ≤ K * B := mul_le_mul hs (hB s ⟨hsI.1.le, hsI.2⟩) (norm_nonneg _)
          ((norm_nonneg _).trans hs)
  exact h1.add hF

lemma intervalInt_of_Ioc {g : ℝ → E} (hT : 0 < T) (hg : IntegrableOn g (Ioc 0 T)) {t : ℝ}
    (ht : t ∈ Icc 0 T) : IntervalIntegrable g volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hg.mono_set (Ioc_subset_Ioc_right ht.2))

lemma volterra_step_bound (hT : 0 < T)
    (hAm : ∀ v : ℝ → E, Continuous v → AEStronglyMeasurable (fun s => A s (v s)) (volume.restrict (Ioc 0 T)))
    (hAb : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)), ‖A s‖ ≤ K)
    (hF : IntegrableOn F (Ioc 0 T)) (u₁ u₂ : ℝ → E) (hu₁ : Continuous u₁) (hu₂ : Continuous u₂)
    (b : ℝ → ℝ) (hb : Continuous b)
    (hub : ∀ s ∈ Icc 0 T, ‖u₁ s - u₂ s‖ ≤ b s) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(∫ s in (0:ℝ)..t, (A s (u₁ s) + F s)) - ∫ s in (0:ℝ)..t, (A s (u₂ s) + F s)‖ ≤
      K * ∫ s in (0:ℝ)..t, b s := by
  have i1 := intervalInt_of_Ioc hT (volterra_integrand_int A F hAm hAb hF u₁ hu₁) ht
  have i2 := intervalInt_of_Ioc hT (volterra_integrand_int A F hAm hAb hF u₂ hu₂) ht
  rw [← intervalIntegral.integral_sub i1 i2]
  have hae := (ae_restrict_iff' measurableSet_Ioc).1 hAb
  have hbI : IntervalIntegrable b volume 0 t := hb.intervalIntegrable _ _
  have hKb : K * ∫ s in (0:ℝ)..t, b s = ∫ s in (0:ℝ)..t, K * b s :=
    (intervalIntegral.integral_const_mul K b).symm
  rw [hKb]
  refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_ (hbI.const_mul K)
  filter_upwards [hae] with s hs hsI
  have hsT : s ∈ Icc 0 T := ⟨hsI.1.le, hsI.2.trans ht.2⟩
  have hK0 : s ∈ Ioc 0 T := ⟨hsI.1, hsI.2.trans ht.2⟩
  have : A s (u₁ s) + F s - (A s (u₂ s) + F s) = A s (u₁ s - u₂ s) := by
    rw [map_sub]; abel
  rw [this]
  calc ‖A s (u₁ s - u₂ s)‖ ≤ ‖A s‖ * ‖u₁ s - u₂ s‖ := (A s).le_opNorm _
    _ ≤ K * b s := mul_le_mul (hs hK0) (hub s hsT) (norm_nonneg _)
        ((norm_nonneg _).trans (hs hK0))

open scoped Nat in
lemma int_bound_poly (K D t : ℝ) (m : ℕ) :
    K * ∫ s in (0:ℝ)..t, (K * s) ^ m / (m ! : ℝ) * D = (K * t) ^ (m + 1) / ((m + 1)! : ℝ) * D := by
  have : ∀ s : ℝ, (K * s) ^ m / (m ! : ℝ) * D = (K ^ m / (m ! : ℝ) * D) * s ^ m := by
    intro s; rw [mul_pow]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
  push_cast
  have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (m ! : ℝ) ≠ 0 := by positivity
  simp only [zero_pow (Nat.succ_ne_zero m), sub_zero]
  rw [mul_pow, pow_succ K m, pow_succ]
  field_simp

open scoped Nat in
theorem volterra_exists (hT : 0 < T) (hK : 0 ≤ K)
    (hAm : ∀ v : ℝ → E, Continuous v → AEStronglyMeasurable (fun s => A s (v s)) (volume.restrict (Ioc 0 T)))
    (hAb : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)), ‖A s‖ ≤ K)
    (hF : IntegrableOn F (Ioc 0 T)) (c0 : E) :
    ∃ c : ℝ → E, Continuous c ∧ ∀ t ∈ Icc 0 T, c t = c0 + ∫ s in (0:ℝ)..t, (A s (c s) + F s) := by
  have hex : ∀ v : C(Icc (0:ℝ) T, E), ∃ w : C(Icc (0:ℝ) T, E), ∀ t : Icc (0:ℝ) T,
      w t = c0 + ∫ s in (0:ℝ)..t, (A s (clampExt hT.le v s) + F s) := by
    intro v
    have hint := volterra_integrand_int A F hAm hAb hF _ (clampExt_cont hT.le v)
    have hI : IntegrableOn (fun s => A s (clampExt hT.le v s) + F s) (uIcc 0 T) := by
      rw [uIcc_of_le hT.le]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hint
    have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) hI
    rw [uIcc_of_le hT.le] at hc
    refine ⟨⟨fun t => c0 + ∫ s in (0:ℝ)..t, (A s (clampExt hT.le v s) + F s), ?_⟩, fun t => rfl⟩
    exact continuous_const.add (hc.comp_continuous continuous_subtype_val (fun t => t.2))
  choose Φ hΦ using hex
  -- iterate bound
  have hiter : ∀ (m : ℕ) (v w : C(Icc (0:ℝ) T, E)) (t : Icc (0:ℝ) T),
      ‖(Φ^[m] v) t - (Φ^[m] w) t‖ ≤ (K * t) ^ m / (m ! : ℝ) * dist v w := by
    intro m
    induction m with
    | zero =>
      intro v w t
      simp only [Function.iterate_zero, id_eq, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        one_mul]
      rw [← dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist t
    | succ m ih =>
      intro v w t
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hΦ, hΦ, add_sub_add_left_eq_sub]
      have hb := volterra_step_bound A F hT hAm hAb hF
        (clampExt hT.le (Φ^[m] v)) (clampExt hT.le (Φ^[m] w)) (clampExt_cont hT.le _)
        (clampExt_cont hT.le _) (fun s => (K * s) ^ m / (m ! : ℝ) * dist v w)
        (by fun_prop) (t := (t : ℝ)) (fun s hs => by
          rw [clampExt_mem hT.le _ hs, clampExt_mem hT.le _ hs]
          exact ih v w ⟨s, hs⟩) t.2
      rw [int_bound_poly K (dist v w) t m] at hb
      exact hb
  have hlip : ∀ m : ℕ, LipschitzWith (((K * T) ^ m / (m ! : ℝ)).toNNReal) (Φ^[m]) := by
    intro m
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    have hc0 : (0:ℝ) ≤ (K * T) ^ m / (m ! : ℝ) := by positivity
    rw [Real.coe_toNNReal _ hc0, mul_comm]
    rw [ContinuousMap.dist_le (by have : 0 ≤ dist v w := dist_nonneg; positivity)]
    intro t
    rw [dist_eq_norm]
    refine (hiter m v w t).trans ?_
    have : (K * (t : ℝ)) ^ m ≤ (K * T) ^ m :=
      pow_le_pow_left₀ (mul_nonneg hK t.2.1) (mul_le_mul_of_nonneg_left t.2.2 hK) m
    have h2 : (K * (t : ℝ)) ^ m / (m ! : ℝ) ≤ (K * T) ^ m / (m ! : ℝ) :=
      div_le_div_of_nonneg_right this (by positivity)
    exact (mul_le_mul_of_nonneg_right h2 (dist_nonneg : (0:ℝ) ≤ dist v w)).trans_eq (mul_comm _ _)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (K * T) ^ m / (m ! : ℝ) < 1 := by
    have := FloorSemiring.tendsto_pow_div_factorial_atTop (K * T)
    exact (this.eventually (gt_mem_nhds one_pos)).exists
  have hcontr : ContractingWith (((K * T) ^ m / (m ! : ℝ)).toNNReal) (Φ^[m]) := by
    refine ⟨?_, hlip m⟩
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity)]
    simpa using hm
  have hfix := hcontr.isFixedPt_fixedPoint_iterate
  set v := hcontr.fixedPoint (Φ^[m]) with hv
  refine ⟨clampExt hT.le v, clampExt_cont hT.le v, fun t ht => ?_⟩
  rw [clampExt_mem hT.le v ht]
  have h : (Φ v) ⟨t, ht⟩ = v ⟨t, ht⟩ := by rw [hfix]
  rw [hΦ] at h
  exact h.symm

end picard

/-! ## Gronwall: uniqueness for the Volterra equation -/

lemma gronwall_zero {E : Type*} [NormedAddCommGroup E] {T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    {Δ : ℝ → E} (hΔ : ContinuousOn Δ (Icc 0 T))
    (h : ∀ t ∈ Icc 0 T, ‖Δ t‖ ≤ K * ∫ s in (0:ℝ)..t, ‖Δ s‖) : ∀ t ∈ Icc 0 T, Δ t = 0 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ψ = fun s => ‖Δ (projIcc 0 T hT.le s)‖ := ⟨_, rfl⟩
  have hψc : Continuous ψ := by
    rw [hψ]
    exact (hΔ.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun x => (projIcc 0 T hT.le x).2)).norm
  have hψeq : ∀ s ∈ Icc 0 T, ψ s = ‖Δ s‖ := fun s hs => by
    rw [hψ]; simp only [projIcc_of_mem hT.le hs]
  have hψ0 : ∀ s, 0 ≤ ψ s := fun s => by rw [hψ]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = fun x => ∫ t in (0 : ℝ)..x, ψ t := ⟨_, rfl⟩
  have hRd : ∀ x, HasDerivAt R (ψ x) x := fun x => by
    rw [hR]
    exact (hψc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hReq : ∀ x ∈ Icc 0 T, R x = ∫ t in (0:ℝ)..x, ‖Δ t‖ := by
    intro x hx
    rw [hR]
    simp only
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx.1] at ht
    exact hψeq t ⟨ht.1, ht.2.trans hx.2⟩
  have hkey : ∀ x ∈ Icc 0 T, ψ x ≤ K * R x := by
    intro x hx
    rw [hψeq x hx, hReq x hx]
    exact h x hx
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := R) (f' := ψ) (δ := 0)
    (K := K) (ε := 0) (a := 0) (b := T)
    (fun x _ => (hRd x).continuousAt.continuousWithinAt)
    (fun x _ => (hRd x).hasDerivWithinAt)
    (by rw [hR]; simp)
    (fun x hx => by
      have h1 := hkey x (Ico_subset_Icc_self hx)
      rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 x), Real.norm_eq_abs, add_zero]
      exact h1.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hK))
  intro x hx
  have h1 := hgr x hx
  rw [gronwallBound_ε0_δ0] at h1
  have hRx : R x = 0 := norm_le_zero_iff.mp h1
  have h2 := hkey x hx
  rw [hRx, mul_zero, hψeq x hx] at h2
  exact norm_eq_zero.mp (le_antisymm h2 (norm_nonneg _))


-- ==== part A2 ====


/-! ## Weak derivative of a primitive, and the du Bois-Reymond lemma -/

/-- Weak derivative of an absolutely continuous function, against a test function on `(0,T)`. -/
lemma weak_deriv_of_ac {T : ℝ} (hT : 0 ≤ T) {y y' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval y 0 T)
    (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt y (y' t) t) (φ : ℝ → ℝ)
    (hφ : IsTestFunctionOn T φ) :
    ∫ t in Ioo 0 T, deriv φ t * y t = -∫ t in Ioo 0 T, φ t * y' t := by
  obtain ⟨hφs, -, hφt⟩ := hφ
  have hφac : AbsolutelyContinuousOnInterval φ 0 T :=
    (hφs.contDiffOn.of_le (by simp)).absolutelyContinuousOnInterval
  have key := hac.integral_mul_deriv_eq_deriv_mul hφac
  have h0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have := hφt h; simp at this)
  have hTT : φ T = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have := hφt h; simp at this)
  rw [h0, hTT] at key
  simp only [mul_zero, sub_zero] at key
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at key
  have hcongr : ∫ t in Ioo 0 T, deriv y t * φ t = ∫ t in Ioo 0 T, φ t * y' t := by
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hd] with t ht htI
    rw [(ht htI).deriv, mul_comm]
  rw [← hcongr]
  simp_rw [mul_comm (deriv φ _) (y _)]
  rw [key]
  ring

/-- The weak derivative of the primitive `y0 + ∫₀ᵗ g` is `g`. -/
lemma primitive_weak_deriv {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo 0 T))
    (y0 : ℝ) (φ : ℝ → ℝ) (hφ : IsTestFunctionOn T φ) :
    ∫ t in Ioo 0 T, deriv φ t * (y0 + ∫ s in (0:ℝ)..t, g s) = -∫ t in Ioo 0 T, φ t * g t := by
  have hu : uIcc (0:ℝ) T = Icc 0 T := uIcc_of_le hT.le
  have hgI : IntervalIntegrable g volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hg
  have hZac : AbsolutelyContinuousOnInterval (fun t => ∫ s in (0:ℝ)..t, g s) 0 T :=
    hgI.absolutelyContinuousOnInterval_intervalIntegral (by simp [hu, hT.le])
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => y0) 0 T :=
    ((LipschitzWith.const (α := ℝ) y0).lipschitzOnWith (s := uIcc (0:ℝ) T)).absolutelyContinuousOnInterval
  have hac : AbsolutelyContinuousOnInterval (fun t => y0 + ∫ s in (0:ℝ)..t, g s) 0 T :=
    hconst.add hZac
  refine weak_deriv_of_ac hT.le hac ?_ φ hφ
  have h1 := hgI.ae_hasDerivAt_integral
  filter_upwards [h1] with t ht htT
  have htI : t ∈ uIcc 0 T := by rw [hu]; exact Ioo_subset_Icc_self htT
  have h0 : (0:ℝ) ∈ uIcc 0 T := by simp [hu, hT.le]
  exact (ht htI 0 h0).const_add y0

lemma test_zero_off {T : ℝ} {φ : ℝ → ℝ} (hφ : IsTestFunctionOn T φ) {t : ℝ} (ht : t ∉ Ioo 0 T) :
    φ t = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => ht (hφ.2.2 h))

lemma exists_Icc_of_compact {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hS : IsCompact S) (hST : S ⊆ Ioo 0 T) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ b < T ∧ S ⊆ Icc a b := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨T / 3, 2 * T / 3, by positivity, by linarith, by linarith, empty_subset _⟩
  · have ha : sInf S ∈ S := hS.sInf_mem hne
    have hb : sSup S ∈ S := hS.sSup_mem hne
    exact ⟨sInf S, sSup S, (hST ha).1, csInf_le hS.bddBelow hb, (hST hb).2,
      fun x hx => ⟨csInf_le hS.bddBelow hx, le_csSup hS.bddAbove hx⟩⟩

lemma primitive_test {T : ℝ} (hT : 0 < T) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) (hsupp : ∀ t, t ∉ Icc a b → χ t = 0)
    (hint : ∫ t, χ t = 0) :
    IsTestFunctionOn T (fun t => ∫ s in (0:ℝ)..t, χ s) ∧
      deriv (fun t => ∫ s in (0:ℝ)..t, χ s) = χ := by
  have hderiv : ∀ x, HasDerivAt (fun t => ∫ s in (0:ℝ)..t, χ s) (χ x) x := fun x =>
    (hχ.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hd : deriv (fun t => ∫ s in (0:ℝ)..t, χ s) = χ := funext fun x => (hderiv x).deriv
  have hz : ∀ t, t ∉ Icc a b → ∫ s in (0:ℝ)..t, χ s = 0 := by
    intro t ht
    rcases lt_or_ge t a with hta | hta
    · have : ∀ s ∈ uIcc (0:ℝ) t, χ s = 0 := by
        intro s hs
        apply hsupp
        intro hsI
        have : s ≤ max 0 t := hs.2
        have := max_lt ha hta
        linarith [hsI.1]
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) this]
      simp
    · have htb : b < t := by
        by_contra hh
        exact ht ⟨hta, not_lt.mp hh⟩
      have h0t : 0 ≤ t := by linarith
      have hcompl : ∀ x, x ∉ Ioc 0 t → χ x = 0 := by
        intro x hx
        apply hsupp
        intro hxI
        exact hx ⟨ha.trans_le hxI.1, hxI.2.trans htb.le⟩
      rw [intervalIntegral.integral_of_le h0t, setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
      exact hint
  refine ⟨⟨?_, ?_, ?_⟩, hd⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hderiv x).differentiableAt, by rw [hd]; exact hχ⟩
  · exact HasCompactSupport.intro isCompact_Icc hz
  · have : tsupport (fun t => ∫ s in (0:ℝ)..t, χ s) ⊆ Icc a b :=
      closure_minimal (fun t ht => by_contra fun h => ht (hz t h)) isClosed_Icc
    exact this.trans fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩

lemma exists_unit_test {T : ℝ} (hT : 0 < T) :
    ∃ φ0 : ℝ → ℝ, IsTestFunctionOn T φ0 ∧ ∫ t, φ0 t = 1 := by
  let b : ContDiffBump (T / 2 : ℝ) := ⟨T / 8, T / 4, by positivity, by linarith⟩
  have hI : 0 < ∫ t, b t := b.integral_pos
  refine ⟨fun t => (∫ s, b s)⁻¹ * b t, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact contDiff_const.mul b.contDiff
  · exact b.hasCompactSupport.mul_left
  · have h1 : tsupport (fun t => (∫ s, b s)⁻¹ * b t) ⊆ tsupport b :=
      closure_mono (Function.support_mul_subset_right (fun _ => (∫ s, b s)⁻¹) b)
    refine h1.trans ?_
    rw [b.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    have : b.rOut = T / 4 := rfl
    rw [this] at hx
    constructor <;> linarith [hx.1, hx.2]
  · simp only
    rw [integral_const_mul, inv_mul_cancel₀ hI.ne']

lemma test_mul_int {T : ℝ} {φ : ℝ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo 0 T)) : IntegrableOn (fun t => φ t * f t) (Ioo 0 T) := by
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hφs
  exact Integrable.bdd_mul hf hφc.aestronglyMeasurable (Filter.Eventually.of_forall hC)

lemma dbr_core {T : ℝ} (hT : 0 < T) {k : ℝ → ℝ} (hk : IntegrableOn k (Ioo 0 T))
    (h : ∀ φ, IsTestFunctionOn T φ → ∫ t in Ioo 0 T, deriv φ t * k t = 0) :
    ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), k t = C := by
  obtain ⟨φ0, hφ0, hφ0I⟩ := exists_unit_test hT
  obtain ⟨C, hC⟩ : ∃ C, C = ∫ t in Ioo 0 T, φ0 t * k t := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), t ∈ Ioo 0 T := ae_restrict_mem measurableSet_Ioo
  have hloc : LocallyIntegrableOn (fun t => k t - C) (Ioo 0 T) (volume.restrict (Ioo 0 T)) := by
    have : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) T)) := isFiniteMeasure_restrict.2 (by simp)
    exact (hk.sub (integrable_const C)).locallyIntegrable.locallyIntegrableOn _
  have hz := (isOpen_Ioo).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [hz, hmem] with t ht1 ht2
    have := ht1 ht2
    linarith
  · intro g hgs hgc hgt
    have hgT : IsTestFunctionOn T g := ⟨hgs, hgc, hgt⟩
    -- the primitive of `g - (∫ g) φ0`
    obtain ⟨a, b, ha, hab, hb, hsub⟩ := exists_Icc_of_compact hT (hgc.isCompact.union hφ0.2.1.isCompact)
      (union_subset hgt hφ0.2.2)
    have hgi : Integrable g := hgs.continuous.integrable_of_hasCompactSupport hgc
    have hφi : Integrable φ0 := hφ0.1.continuous.integrable_of_hasCompactSupport hφ0.2.1
    obtain ⟨I, hI⟩ : ∃ I, I = ∫ t, g t := ⟨_, rfl⟩
    have hχs : ∀ t, t ∉ Icc a b → g t - I * φ0 t = 0 := by
      intro t ht
      have h1 : t ∉ tsupport g := fun h' => ht (hsub (Or.inl h'))
      have h2 : t ∉ tsupport φ0 := fun h' => ht (hsub (Or.inr h'))
      rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
      ring
    have hχint : ∫ t, (g t - I * φ0 t) = 0 := by
      rw [integral_sub hgi (hφi.const_mul I), integral_const_mul, hφ0I, ← hI]
      ring
    obtain ⟨hX, hXd⟩ := primitive_test hT (χ := fun t => g t - I * φ0 t)
      (hgs.sub (contDiff_const.mul hφ0.1)) ha hab hb hχs hχint
    have hkey := h _ hX
    rw [hXd] at hkey
    have e1 : IntegrableOn (fun t => g t * k t) (Ioo 0 T) := test_mul_int hgs.continuous hgc hk
    have e2 : IntegrableOn (fun t => φ0 t * k t) (Ioo 0 T) :=
      test_mul_int hφ0.1.continuous hφ0.2.1 hk
    have e3 : ∫ t in Ioo 0 T, (g t - I * φ0 t) * k t =
        (∫ t in Ioo 0 T, g t * k t) - I * ∫ t in Ioo 0 T, φ0 t * k t := by
      rw [← integral_const_mul, ← integral_sub e1 (e2.const_mul I)]
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      ring
    rw [e3] at hkey
    have e4 : ∫ t in Ioo 0 T, g t = I := by
      rw [hI]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
        test_zero_off hgT ht
    have e5 : ∫ x, g x • (k x - C) ∂(volume.restrict (Ioo 0 T)) =
        (∫ t in Ioo 0 T, g t * k t) - C * ∫ t in Ioo 0 T, g t := by
      have hg1 : IntegrableOn g (Ioo 0 T) := hgi.integrableOn
      rw [← integral_const_mul, ← integral_sub e1 (hg1.const_mul C)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [smul_eq_mul]
      ring
    rw [e5, e4]
    rw [← hC] at hkey
    linarith

theorem dbr_scalar {T : ℝ} (hT : 0 < T) {h w : ℝ → ℝ} (hh : IntegrableOn h (Ioo 0 T))
    (hw : IntegrableOn w (Ioo 0 T))
    (hweak : ∀ φ, IsTestFunctionOn T φ →
      ∫ t in Ioo 0 T, deriv φ t * h t = -∫ t in Ioo 0 T, φ t * w t) :
    ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), h t = C + ∫ s in (0:ℝ)..t, w s := by
  have hwI : IntervalIntegrable w volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hw
  have hYc : ContinuousOn (fun t => ∫ s in (0:ℝ)..t, w s) (Icc 0 T) := by
    have hI : IntegrableOn w (uIcc 0 T) := by
      rw [uIcc_of_le hT.le]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 ((integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hw)
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) hI
    rwa [uIcc_of_le hT.le] at this
  have hYi : IntegrableOn (fun t => ∫ s in (0:ℝ)..t, w s) (Ioo 0 T) :=
    (hYc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  obtain ⟨C, hC⟩ := dbr_core hT (k := fun t => h t - ∫ s in (0:ℝ)..t, w s) (hh.sub hYi) (by
    intro φ hφ
    have hd : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
    have hdc : HasCompactSupport (deriv φ) := hφ.2.1.deriv
    have e1 := test_mul_int hd hdc hh
    have e2 := test_mul_int hd hdc hYi
    have e3 := primitive_weak_deriv hT hw 0 φ hφ
    simp only [zero_add] at e3
    have e4 : ∫ t in Ioo 0 T, deriv φ t * (h t - ∫ s in (0:ℝ)..t, w s) =
        (∫ t in Ioo 0 T, deriv φ t * h t) - ∫ t in Ioo 0 T, deriv φ t * ∫ s in (0:ℝ)..t, w s := by
      rw [← integral_sub e1 e2]
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      ring
    rw [e4, e3, hweak φ hφ]
    ring)
  refine ⟨C, ?_⟩
  filter_upwards [hC] with t ht
  linarith


-- ==== part B1 ====


variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-! ## Components of `H¹₀` elements as `L²` functions -/

noncomputable def pdCLM (n : ℕ) (j : Fin n) : Jet n →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))

noncomputable def pdL (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (j : Fin n) :
    H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ((pdCLM n j).compLpL 2 (volume.restrict Ω)).comp (H10 n Ω).subtypeL

lemma pdL_ae (j : Fin n) (u : H10 n Ω) :
    (pdL n Ω j u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict Ω] pd u j := by
  have := (pdCLM n j).coeFn_compLp (μ := volume.restrict Ω) (p := 2) (u : JetL2 n Ω)
  filter_upwards [this] with x hx
  exact hx

lemma val_ae (u : H10 n Ω) :
    (toL2L n Ω u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict Ω] val u := by
  have := (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLp
    (μ := volume.restrict Ω) (p := 2) (u : JetL2 n Ω)
  filter_upwards [this] with x hx
  exact hx

lemma val_memLp (u : H10 n Ω) : MemLp (val u) 2 (volume.restrict Ω) :=
  (Lp.memLp (toL2L n Ω u)).ae_eq (val_ae u)

lemma pd_memLp (u : H10 n Ω) (j : Fin n) : MemLp (pd u j) 2 (volume.restrict Ω) :=
  (Lp.memLp (pdL n Ω j u)).ae_eq (pdL_ae j u)

lemma val_sub (u₁ u₂ : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), val (u₁ - u₂) x = val u₁ x - val u₂ x := by
  have h := Lp.coeFn_sub (toL2L n Ω u₁) (toL2L n Ω u₂)
  filter_upwards [val_ae (u₁ - u₂), val_ae u₁, val_ae u₂, h] with x h0 h1 h2 h3
  rw [← h0, ← h1, ← h2, map_sub, h3, Pi.sub_apply]

lemma pd_sub (u₁ u₂ : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ∀ j, pd (u₁ - u₂) j x = pd u₁ j x - pd u₂ j x := by
  rw [ae_all_iff]
  intro j
  have h := Lp.coeFn_sub (pdL n Ω j u₁) (pdL n Ω j u₂)
  filter_upwards [pdL_ae j (u₁ - u₂), pdL_ae j u₁, pdL_ae j u₂, h] with x h0 h1 h2 h3
  rw [← h0, ← h1, ← h2, map_sub, h3, Pi.sub_apply]

lemma val_add (u₁ u₂ : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), val (u₁ + u₂) x = val u₁ x + val u₂ x := by
  have h := Lp.coeFn_add (toL2L n Ω u₁) (toL2L n Ω u₂)
  filter_upwards [val_ae (u₁ + u₂), val_ae u₁, val_ae u₂, h] with x h0 h1 h2 h3
  rw [← h0, ← h1, ← h2, map_add, h3, Pi.add_apply]

lemma pd_add (u₁ u₂ : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ∀ j, pd (u₁ + u₂) j x = pd u₁ j x + pd u₂ j x := by
  rw [ae_all_iff]
  intro j
  have h := Lp.coeFn_add (pdL n Ω j u₁) (pdL n Ω j u₂)
  filter_upwards [pdL_ae j (u₁ + u₂), pdL_ae j u₁, pdL_ae j u₂, h] with x h0 h1 h2 h3
  rw [← h0, ← h1, ← h2, map_add, h3, Pi.add_apply]

lemma val_smul (c : ℝ) (u : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), val (c • u) x = c * val u x := by
  have h := Lp.coeFn_smul c (toL2L n Ω u)
  filter_upwards [val_ae (c • u), val_ae u, h] with x h0 h1 h3
  rw [← h0, ← h1, map_smul, h3, Pi.smul_apply, smul_eq_mul]

lemma pd_smul (c : ℝ) (u : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ∀ j, pd (c • u) j x = c * pd u j x := by
  rw [ae_all_iff]
  intro j
  have h := Lp.coeFn_smul c (pdL n Ω j u)
  filter_upwards [pdL_ae j (c • u), pdL_ae j u, h] with x h0 h1 h3
  rw [← h0, ← h1, map_smul, h3, Pi.smul_apply, smul_eq_mul]

lemma norm_toL2L_sq (u : H10 n Ω) :
    ‖toL2L n Ω u‖ ^ 2 = ∫ x in Ω, val u x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [val_ae u] with x hx
  rw [hx]
  simp [sq]

/-! ## Time sections of coefficients on the cylinder -/

lemma ae_time_of_cyl {T : ℝ} {p : EuclideanSpace ℝ (Fin n) × ℝ → Prop}
    (h : ∀ᵐ q ∂(cylMeasure Ω T), p q) :
    ∀ᵐ t ∂(timeMeasure T), ∀ᵐ x ∂(volume.restrict Ω), p (x, t) := by
  have h2 : ∀ᵐ z ∂((timeMeasure T).prod (volume.restrict Ω)), p z.swap :=
    (Measure.measurePreserving_swap (μ := timeMeasure T)
      (ν := volume.restrict Ω)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h2

lemma aesm_time_of_cyl {T : ℝ} {f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (h : AEStronglyMeasurable f (cylMeasure Ω T)) :
    ∀ᵐ t ∂(timeMeasure T), AEStronglyMeasurable (fun x => f (x, t)) (volume.restrict Ω) :=
  (h.comp_measurePreserving (Measure.measurePreserving_swap (μ := timeMeasure T)
      (ν := volume.restrict Ω))).prodMk_left

lemma ae_bound_of_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (h : MemLp f ⊤ μ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ q ∂μ, |f q| ≤ M := by
  refine ⟨(eLpNorm f ⊤ μ).toReal, ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with q hq
  have hlt := h.eLpNorm_lt_top
  rw [eLpNorm_exponent_top] at hlt ⊢
  have := ENNReal.toReal_mono hlt.ne hq
  rwa [toReal_enorm, Real.norm_eq_abs] at this

/-- A time `t` at which the coefficients are measurable and bounded by `M` on `Ω` and elliptic
with constant `θ`. -/
def GoodT (P : Coeffs n) (Ω : Set (EuclideanSpace ℝ (Fin n))) (θ M t : ℝ) : Prop :=
  (∀ i j, AEStronglyMeasurable (fun x => P.a i j x t) (volume.restrict Ω)) ∧
  (∀ j, AEStronglyMeasurable (fun x => P.b j x t) (volume.restrict Ω)) ∧
  AEStronglyMeasurable (fun x => P.c x t) (volume.restrict Ω) ∧
  (∀ᵐ x ∂(volume.restrict Ω), (∀ i j, |P.a i j x t| ≤ M) ∧ (∀ j, |P.b j x t| ≤ M) ∧
    |P.c x t| ≤ M ∧ ∀ ξ : Fin n → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j x t * ξ i * ξ j)

lemma good_ae {T : ℝ} {P : Coeffs n} (hP : P.Assumption61 Ω T) :
    ∃ θ M : ℝ, 0 < θ ∧ 0 ≤ M ∧ ∀ᵐ t ∂(timeMeasure T), GoodT P Ω θ M t := by
  obtain ⟨ha, hb, hc, -, θ, hθ, hell⟩ := hP
  choose Ma hMa0 hMa using fun i j => ae_bound_of_top (ha i j)
  choose Mb hMb0 hMb using fun j => ae_bound_of_top (hb j)
  obtain ⟨Mc, hMc0, hMc⟩ := ae_bound_of_top hc
  obtain ⟨M, hM⟩ : ∃ M, M = (∑ i, ∑ j, Ma i j) + (∑ j, Mb j) + Mc := ⟨_, rfl⟩
  have hSa : 0 ≤ ∑ i, ∑ j, Ma i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hMa0 i j
  have hSb : 0 ≤ ∑ j, Mb j := Finset.sum_nonneg fun j _ => hMb0 j
  have hMa_le : ∀ i j, Ma i j ≤ M := by
    intro i j
    have h1 : Ma i j ≤ ∑ j', Ma i j' :=
      Finset.single_le_sum (f := fun j' => Ma i j') (fun j' _ => hMa0 i j') (Finset.mem_univ j)
    have h2 : ∑ j', Ma i j' ≤ ∑ i', ∑ j', Ma i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', Ma i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => hMa0 i' j') (Finset.mem_univ i)
    linarith
  have hMb_le : ∀ j, Mb j ≤ M := by
    intro j
    have h1 : Mb j ≤ ∑ j', Mb j' :=
      Finset.single_le_sum (f := fun j' => Mb j') (fun j' _ => hMb0 j') (Finset.mem_univ j)
    linarith
  have hMc_le : Mc ≤ M := by linarith
  refine ⟨θ, M, hθ, by linarith, ?_⟩
  have h1 : ∀ᵐ q ∂(cylMeasure Ω T), ∀ i j, |P.a i j q.1 q.2| ≤ Ma i j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact hMa i
  have h2 : ∀ᵐ q ∂(cylMeasure Ω T), ∀ j, |P.b j q.1 q.2| ≤ Mb j := by
    rw [ae_all_iff]; exact hMb
  have hall : ∀ᵐ q ∂(cylMeasure Ω T), (∀ i j, |P.a i j q.1 q.2| ≤ M) ∧
      (∀ j, |P.b j q.1 q.2| ≤ M) ∧ |P.c q.1 q.2| ≤ M ∧
      ∀ ξ : Fin n → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j q.1 q.2 * ξ i * ξ j := by
    filter_upwards [h1, h2, hMc, hell] with q q1 q2 q3 q4
    exact ⟨fun i j => (q1 i j).trans (hMa_le i j), fun j => (q2 j).trans (hMb_le j),
      q3.trans hMc_le, q4⟩
  have hA : ∀ᵐ t ∂(timeMeasure T), ∀ i j,
      AEStronglyMeasurable (fun x => P.a i j x t) (volume.restrict Ω) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    exact aesm_time_of_cyl (f := fun p => P.a i j p.1 p.2) (ha i j).aestronglyMeasurable
  have hB : ∀ᵐ t ∂(timeMeasure T), ∀ j,
      AEStronglyMeasurable (fun x => P.b j x t) (volume.restrict Ω) := by
    rw [ae_all_iff]; intro j
    exact aesm_time_of_cyl (f := fun p => P.b j p.1 p.2) (hb j).aestronglyMeasurable
  have hC : ∀ᵐ t ∂(timeMeasure T),
      AEStronglyMeasurable (fun x => P.c x t) (volume.restrict Ω) :=
    aesm_time_of_cyl (f := fun p => P.c p.1 p.2) hc.aestronglyMeasurable
  filter_upwards [hA, hB, hC, ae_time_of_cyl hall] with t t1 t2 t3 t4
  exact ⟨t1, t2, t3, t4⟩

/-! ## The form at a good time -/

lemma int3 {X : Type*} [MeasurableSpace X] {μ : Measure X} {g p q : X → ℝ} {M : ℝ}
    (hg : AEStronglyMeasurable g μ) (hgb : ∀ᵐ x ∂μ, |g x| ≤ M) (hp : MemLp p 2 μ)
    (hq : MemLp q 2 μ) : Integrable (fun x => g x * p x * q x) μ := by
  have hgp : MemLp (fun x => g x * p x) 2 μ := by
    refine hp.of_le_mul (c := M) (hg.mul hp.1) ?_
    filter_upwards [hgb] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  exact hgp.integrable_mul hq

lemma memLp_mul_bdd {X : Type*} [MeasurableSpace X] {μ : Measure X} {g p : X → ℝ} {M : ℝ}
    (hg : AEStronglyMeasurable g μ) (hgb : ∀ᵐ x ∂μ, |g x| ≤ M) (hp : MemLp p 2 μ) :
    MemLp (fun x => g x * p x) 2 μ := by
  refine hp.of_le_mul (c := M) (hg.mul hp.1) ?_
  filter_upwards [hgb] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

section good
variable {P : Coeffs n} {θ M t : ℝ}

lemma form_terms_int (hg : GoodT P Ω θ M t) (u v : H10 n Ω) :
    (∀ i j, Integrable (fun x => P.a i j x t * pd u i x * pd v j x) (volume.restrict Ω)) ∧
    (∀ j, Integrable (fun x => P.b j x t * pd u j x * val v x) (volume.restrict Ω)) ∧
    Integrable (fun x => P.c x t * val u x * val v x) (volume.restrict Ω) := by
  obtain ⟨ha, hb, hc, hbd⟩ := hg
  refine ⟨fun i j => int3 (M := M) (ha i j) ?_ (pd_memLp u i) (pd_memLp v j),
    fun j => int3 (M := M) (hb j) ?_ (pd_memLp u j) (val_memLp v), int3 (M := M) hc ?_ (val_memLp u) (val_memLp v)⟩
  · filter_upwards [hbd] with x hx using hx.1 i j
  · filter_upwards [hbd] with x hx using hx.2.1 j
  · filter_upwards [hbd] with x hx using hx.2.2.1

lemma form_integrand_int (hg : GoodT P Ω θ M t) (u v : H10 n Ω) :
    Integrable (fun x => (∑ i, ∑ j, P.a i j x t * pd u i x * pd v j x) +
      (∑ j, P.b j x t * pd u j x * val v x) + P.c x t * val u x * val v x)
      (volume.restrict Ω) := by
  obtain ⟨hA, hB, hC⟩ := form_terms_int hg u v
  exact ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hA i j).add
    (integrable_finsetSum _ fun j _ => hB j)).add hC

lemma form_eq_sum (hg : GoodT P Ω θ M t) (u v : H10 n Ω) :
    form P t u v = (∑ i, ∑ j, ∫ x in Ω, P.a i j x t * pd u i x * pd v j x) +
      (∑ j, ∫ x in Ω, P.b j x t * pd u j x * val v x) +
      ∫ x in Ω, P.c x t * val u x * val v x := by
  obtain ⟨hA, hB, hC⟩ := form_terms_int hg u v
  have h1 : Integrable (fun x => ∑ i, ∑ j, P.a i j x t * pd u i x * pd v j x)
      (volume.restrict Ω) := integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hA i j
  have h2 : Integrable (fun x => ∑ j, P.b j x t * pd u j x * val v x) (volume.restrict Ω) :=
    integrable_finsetSum _ fun j _ => hB j
  have h12 : Integrable (fun x => (∑ i, ∑ j, P.a i j x t * pd u i x * pd v j x) +
      ∑ j, P.b j x t * pd u j x * val v x) (volume.restrict Ω) := h1.add h2
  rw [form, integral_add h12 hC, integral_add h1 h2,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hA i j,
    integral_finsetSum _ fun j _ => hB j]
  congr 2
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hA i j


/-- The integrand of the bilinear form, as a function of the jets of `u` and `v` at the point. -/
def qf (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (U : Fin n → ℝ) (u0 : ℝ)
    (V : Fin n → ℝ) (v0 : ℝ) : ℝ :=
  (∑ i, ∑ j, P.a i j x t * U i * V j) + (∑ j, P.b j x t * U j * v0) + P.c x t * u0 * v0

lemma qf_add_left (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (U U' : Fin n → ℝ)
    (u0 u0' : ℝ) (V : Fin n → ℝ) (v0 : ℝ) :
    qf P t x (fun i => U i + U' i) (u0 + u0') V v0 = qf P t x U u0 V v0 + qf P t x U' u0' V v0 := by
  simp only [qf, mul_add, add_mul, Finset.sum_add_distrib]
  ring

lemma qf_add_right (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (U : Fin n → ℝ) (u0 : ℝ)
    (V V' : Fin n → ℝ) (v0 v0' : ℝ) :
    qf P t x U u0 (fun i => V i + V' i) (v0 + v0') = qf P t x U u0 V v0 + qf P t x U u0 V' v0' := by
  simp only [qf, mul_add, add_mul, Finset.sum_add_distrib]
  ring

lemma qf_smul_left (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (U : Fin n → ℝ)
    (u0 : ℝ) (V : Fin n → ℝ) (v0 : ℝ) :
    qf P t x (fun i => c * U i) (c * u0) V v0 = c * qf P t x U u0 V v0 := by
  have hA : (∑ i, ∑ j, P.a i j x t * (c * U i) * V j) = c * ∑ i, ∑ j, P.a i j x t * U i * V j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hB : (∑ j, P.b j x t * (c * U j) * v0) = c * ∑ j, P.b j x t * U j * v0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold qf
  rw [hA, hB]
  ring

lemma qf_smul_right (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (U : Fin n → ℝ)
    (u0 : ℝ) (V : Fin n → ℝ) (v0 : ℝ) :
    qf P t x U u0 (fun i => c * V i) (c * v0) = c * qf P t x U u0 V v0 := by
  have hA : (∑ i, ∑ j, P.a i j x t * U i * (c * V j)) = c * ∑ i, ∑ j, P.a i j x t * U i * V j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hB : (∑ j, P.b j x t * U j * (c * v0)) = c * ∑ j, P.b j x t * U j * v0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold qf
  rw [hA, hB]
  ring

lemma form_eq_qf (P : Coeffs n) (t : ℝ) (u v : H10 n Ω) :
    form P t u v = ∫ x in Ω, qf P t x (fun i => pd u i x) (val u x) (fun j => pd v j x) (val v x) :=
  rfl

lemma qf_int (hg : GoodT P Ω θ M t) (u v : H10 n Ω) :
    Integrable (fun x => qf P t x (fun i => pd u i x) (val u x) (fun j => pd v j x) (val v x))
      (volume.restrict Ω) :=
  form_integrand_int hg u v

lemma form_add_left (hg : GoodT P Ω θ M t) (u₁ u₂ v : H10 n Ω) :
    form P t (u₁ + u₂) v = form P t u₁ v + form P t u₂ v := by
  rw [form_eq_qf, form_eq_qf, form_eq_qf, ← integral_add (qf_int hg u₁ v) (qf_int hg u₂ v)]
  refine integral_congr_ae ?_
  filter_upwards [pd_add u₁ u₂, val_add u₁ u₂] with x hpd hval
  have : (fun i => pd (u₁ + u₂) i x) = fun i => pd u₁ i x + pd u₂ i x := funext hpd
  rw [this, hval, qf_add_left]

lemma form_smul_left (hg : GoodT P Ω θ M t) (c : ℝ) (u v : H10 n Ω) :
    form P t (c • u) v = c * form P t u v := by
  rw [form_eq_qf, form_eq_qf, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [pd_smul c u, val_smul c u] with x hpd hval
  have : (fun i => pd (c • u) i x) = fun i => c * pd u i x := funext hpd
  rw [this, hval, qf_smul_left]

lemma form_add_right (hg : GoodT P Ω θ M t) (u v₁ v₂ : H10 n Ω) :
    form P t u (v₁ + v₂) = form P t u v₁ + form P t u v₂ := by
  rw [form_eq_qf, form_eq_qf, form_eq_qf, ← integral_add (qf_int hg u v₁) (qf_int hg u v₂)]
  refine integral_congr_ae ?_
  filter_upwards [pd_add v₁ v₂, val_add v₁ v₂] with x hpd hval
  have : (fun i => pd (v₁ + v₂) i x) = fun i => pd v₁ i x + pd v₂ i x := funext hpd
  rw [this, hval, qf_add_right]

lemma form_smul_right (hg : GoodT P Ω θ M t) (c : ℝ) (u v : H10 n Ω) :
    form P t u (c • v) = c * form P t u v := by
  rw [form_eq_qf, form_eq_qf, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [pd_smul c v, val_smul c v] with x hpd hval
  have : (fun i => pd (c • v) i x) = fun i => c * pd v i x := funext hpd
  rw [this, hval, qf_smul_right]

/-- Pointwise bound on the integrand of the form at a good time. -/
noncomputable def qBnd (M : ℝ) (u v : H10 n Ω) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  M * ((∑ i, ∑ j, |pd u i x * pd v j x|) + (∑ j, |pd u j x * val v x|) + |val u x * val v x|)

lemma qBnd_int (M : ℝ) (u v : H10 n Ω) : Integrable (qBnd M u v) (volume.restrict Ω) := by
  have h1 : ∀ i j, Integrable (fun x => |pd u i x * pd v j x|) (volume.restrict Ω) :=
    fun i j => ((pd_memLp u i).integrable_mul (pd_memLp v j)).abs
  have h2 : ∀ j, Integrable (fun x => |pd u j x * val v x|) (volume.restrict Ω) :=
    fun j => ((pd_memLp u j).integrable_mul (val_memLp v)).abs
  have h3 : Integrable (fun x => |val u x * val v x|) (volume.restrict Ω) :=
    ((val_memLp u).integrable_mul (val_memLp v)).abs
  exact (((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h1 i j).add
    (integrable_finsetSum _ fun j _ => h2 j)).add h3).const_mul M

noncomputable def formBnd (M : ℝ) (u v : H10 n Ω) : ℝ := ∫ x in Ω, qBnd M u v x

lemma qf_abs_le {t M : ℝ} {x : EuclideanSpace ℝ (Fin n)} (P : Coeffs n) (U V : Fin n → ℝ) (u0 v0 : ℝ)
    (ha : ∀ i j, |P.a i j x t| ≤ M) (hb : ∀ j, |P.b j x t| ≤ M) (hc : |P.c x t| ≤ M) :
    |qf P t x U u0 V v0| ≤
      M * ((∑ i, ∑ j, |U i * V j|) + (∑ j, |U j * v0|) + |u0 * v0|) := by
  have h1 : |∑ i, ∑ j, P.a i j x t * U i * V j| ≤ M * ∑ i, ∑ j, |U i * V j| := by
    calc |∑ i, ∑ j, P.a i j x t * U i * V j| ≤ ∑ i, |∑ j, P.a i j x t * U i * V j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |P.a i j x t * U i * V j| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, M * |U i * V j| :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [mul_assoc, abs_mul]
            exact mul_le_mul_of_nonneg_right (ha i j) (abs_nonneg _)
      _ = M * ∑ i, ∑ j, |U i * V j| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have h2 : |∑ j, P.b j x t * U j * v0| ≤ M * ∑ j, |U j * v0| := by
    calc |∑ j, P.b j x t * U j * v0| ≤ ∑ j, |P.b j x t * U j * v0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, M * |U j * v0| :=
          Finset.sum_le_sum fun j _ => by
            rw [mul_assoc, abs_mul]
            exact mul_le_mul_of_nonneg_right (hb j) (abs_nonneg _)
      _ = M * ∑ j, |U j * v0| := by rw [Finset.mul_sum]
  have h3 : |P.c x t * u0 * v0| ≤ M * |u0 * v0| := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  unfold qf
  calc _ ≤ |(∑ i, ∑ j, P.a i j x t * U i * V j) + (∑ j, P.b j x t * U j * v0)| +
        |P.c x t * u0 * v0| := abs_add_le _ _
    _ ≤ |∑ i, ∑ j, P.a i j x t * U i * V j| + |∑ j, P.b j x t * U j * v0| +
        |P.c x t * u0 * v0| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

lemma form_abs_le (hg : GoodT P Ω θ M t) (u v : H10 n Ω) : |form P t u v| ≤ formBnd M u v := by
  rw [form_eq_qf, formBnd]
  have := norm_integral_le_of_norm_le (qBnd_int M u v) (μ := volume.restrict Ω)
    (f := fun x => qf P t x (fun i => pd u i x) (val u x) (fun j => pd v j x) (val v x)) (by
      obtain ⟨-, -, -, hbd⟩ := hg
      filter_upwards [hbd] with x hx
      rw [Real.norm_eq_abs]
      exact qf_abs_le P _ _ _ _ hx.1 hx.2.1 hx.2.2.1)
  rwa [Real.norm_eq_abs] at this

end good

/-! ## Measurability of the form in time -/

lemma form_aesm {T : ℝ} {P : Coeffs n} (hP : P.Assumption61 Ω T) (u v : H10 n Ω) :
    AEStronglyMeasurable (fun t => form P t u v) (timeMeasure T) := by
  obtain ⟨ha, hb, hc, -, -⟩ := hP
  have hfst : ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, AEStronglyMeasurable f (volume.restrict Ω) →
      AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ => f q.1) (cylMeasure Ω T) :=
    fun hf => hf.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict Ω) (ν := timeMeasure T))
  have hG : AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
      qf P q.2 q.1 (fun i => pd u i q.1) (val u q.1) (fun j => pd v j q.1) (val v q.1))
      (cylMeasure Ω T) := by
    have e1 : AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
        ∑ i, ∑ j, P.a i j q.1 q.2 * pd u i q.1 * pd v j q.1) (cylMeasure Ω T) :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        (((ha i j).aestronglyMeasurable).mul (hfst (pd_memLp u i).aestronglyMeasurable)).mul
          (hfst (pd_memLp v j).aestronglyMeasurable)
    have e2 : AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
        ∑ j, P.b j q.1 q.2 * pd u j q.1 * val v q.1) (cylMeasure Ω T) :=
      Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        (((hb j).aestronglyMeasurable).mul (hfst (pd_memLp u j).aestronglyMeasurable)).mul
          (hfst (val_memLp v).aestronglyMeasurable)
    have e3 : AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
        P.c q.1 q.2 * val u q.1 * val v q.1) (cylMeasure Ω T) :=
      ((hc.aestronglyMeasurable).mul (hfst (val_memLp u).aestronglyMeasurable)).mul
        (hfst (val_memLp v).aestronglyMeasurable)
    exact (e1.add e2).add e3
  have hsw := hG.comp_measurePreserving
    (Measure.measurePreserving_swap (μ := timeMeasure T) (ν := volume.restrict Ω))
  exact hsw.integral_prod_right'


-- ==== part B2 ====


/-! ## `L²` inner product, coordinates and the Galerkin space -/

lemma l2inner_eq (u v : H10 n Ω) : l2inner u v = inner ℝ (toL2L n Ω u) (toL2L n Ω v) := by
  rw [l2inner, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [val_ae u, val_ae v] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

lemma l2inner_comm (u v : H10 n Ω) : l2inner u v = l2inner v u := by
  rw [l2inner_eq, l2inner_eq, real_inner_comm]

lemma l2inner_add_left (u u' v : H10 n Ω) : l2inner (u + u') v = l2inner u v + l2inner u' v := by
  simp only [l2inner_eq, map_add, inner_add_left]

lemma l2inner_smul_left (c : ℝ) (u v : H10 n Ω) : l2inner (c • u) v = c * l2inner u v := by
  simp only [l2inner_eq, map_smul, real_inner_smul_left]

lemma l2inner_add_right (u v v' : H10 n Ω) : l2inner u (v + v') = l2inner u v + l2inner u v' := by
  simp only [l2inner_eq, map_add, inner_add_right]

lemma l2inner_smul_right (c : ℝ) (u v : H10 n Ω) : l2inner u (c • v) = c * l2inner u v := by
  simp only [l2inner_eq, map_smul, real_inner_smul_right]

/-- The `j`-th coordinate functional `u ↦ (w_j, u)_{L²}`. -/
noncomputable def coordCLM (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (w : ℕ → H10 n Ω)
    (j : ℕ) : H10 n Ω →L[ℝ] ℝ :=
  (innerSL ℝ (toL2L n Ω (w j))).comp (toL2L n Ω)

lemma coordCLM_apply (w : ℕ → H10 n Ω) (j : ℕ) (u : H10 n Ω) :
    coordCLM n Ω w j u = l2inner (w j) u := by
  simp [coordCLM, l2inner_eq]

section orth
variable {w : ℕ → H10 n Ω}

/-- The combination `∑_{k<N} c_k w_k`. -/
noncomputable def fsum (w : ℕ → H10 n Ω) (N : ℕ) (c : Fin N → ℝ) : H10 n Ω :=
  ∑ k : Fin N, c k • w k

lemma fsum_mem (w : ℕ → H10 n Ω) (N : ℕ) (c : Fin N → ℝ) : fsum w N c ∈ galerkinSpace w N :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, k.2, rfl⟩)

lemma fsum_zero (w : ℕ → H10 n Ω) (N : ℕ) : fsum w N (fun _ => 0) = 0 := by
  simp [fsum]

lemma fsum_add (w : ℕ → H10 n Ω) (N : ℕ) (c c' : Fin N → ℝ) :
    fsum w N (fun k => c k + c' k) = fsum w N c + fsum w N c' := by
  simp [fsum, add_smul, Finset.sum_add_distrib]

lemma fsum_smul (w : ℕ → H10 n Ω) (N : ℕ) (a : ℝ) (c : Fin N → ℝ) :
    fsum w N (fun k => a * c k) = a • fsum w N c := by
  simp [fsum, Finset.smul_sum, mul_smul]

lemma coord_fsum (horth : ∀ j k, l2inner (w j) (w k) = if j = k then 1 else 0) {N : ℕ}
    (c : Fin N → ℝ) (j : Fin N) : coordCLM n Ω w j (fsum w N c) = c j := by
  simp only [fsum, map_sum, map_smul, coordCLM_apply, horth, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk (Fin.ext h.symm)
  · simp

lemma expand_galerkin (horth : ∀ j k, l2inner (w j) (w k) = if j = k then 1 else 0) {N : ℕ}
    {x : H10 n Ω} (hx : x ∈ galerkinSpace w N) :
    x = fsum w N (fun k => coordCLM n Ω w k x) := by
  unfold galerkinSpace at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hjN : (j : ℕ) < N := hj
    have : (fun k : Fin N => coordCLM n Ω w (k : ℕ) (w j)) = fun k : Fin N => if (k : ℕ) = j then (1:ℝ) else 0 := by
      funext k
      rw [coordCLM_apply, horth]
    rw [this]
    simp only [fsum, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single (⟨j, hjN⟩ : Fin N)]
    · simp
    · intro k _ hk
      rw [if_neg]
      intro h
      exact hk (Fin.ext h)
    · simp
  | zero => simp [fsum]
  | add y z _ _ hy hz =>
    have : (fun k : Fin N => coordCLM n Ω w (k : ℕ) (y + z)) =
        fun k : Fin N => coordCLM n Ω w (k : ℕ) y + coordCLM n Ω w (k : ℕ) z :=
      funext fun k => map_add _ _ _
    rw [this, fsum_add, ← hy, ← hz]
  | smul a y _ hy =>
    have : (fun k : Fin N => coordCLM n Ω w (k : ℕ) (a • y)) =
        fun k : Fin N => a * coordCLM n Ω w (k : ℕ) y :=
      funext fun k => by rw [map_smul, smul_eq_mul]
    rw [this, fsum_smul, ← hy]

lemma form_fsum_left {P : Coeffs n} {θ M t : ℝ} (hg : GoodT P Ω θ M t) {N : ℕ} (c : Fin N → ℝ)
    (v : H10 n Ω) : form P t (fsum w N c) v = ∑ k : Fin N, c k * form P t (w k) v := by
  let L : H10 n Ω →ₗ[ℝ] ℝ :=
    { toFun := fun u => form P t u v
      map_add' := fun u u' => form_add_left hg u u' v
      map_smul' := fun a u => form_smul_left hg a u v }
  have : form P t (fsum w N c) v = L (fsum w N c) := rfl
  rw [this, fsum, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul]; rfl

end orth


-- ==== part B3 ====


/-! ## The coefficient matrix of the Galerkin system -/

lemma qBnd_nonneg {M : ℝ} (hM : 0 ≤ M) (u v : H10 n Ω) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ qBnd M u v x := by
  unfold qBnd
  refine mul_nonneg hM ?_
  have h1 : 0 ≤ ∑ i, ∑ j, |pd u i x * pd v j x| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have h2 : 0 ≤ ∑ j, |pd u j x * val v x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : 0 ≤ |val u x * val v x| := abs_nonneg _
  linarith

lemma formBnd_nonneg {M : ℝ} (hM : 0 ≤ M) (u v : H10 n Ω) : 0 ≤ formBnd M u v :=
  integral_nonneg fun x => qBnd_nonneg hM u v x

lemma matrix_good {T : ℝ} {P : Coeffs n} (hP : P.Assumption61 Ω T) (w : ℕ → H10 n Ω) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ θ M : ℝ, 0 < θ ∧ 0 ≤ M ∧ ∀ᵐ t ∂(timeMeasure T),
      GoodT P Ω θ M t ∧ ∀ j k : Fin N, |form P t (w k) (w j)| ≤ K := by
  obtain ⟨θ, M, hθ, hM, hgood⟩ := good_ae hP
  refine ⟨∑ k : Fin N, ∑ j : Fin N, formBnd M (w k) (w j),
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => formBnd_nonneg hM _ _, θ, M, hθ, hM, ?_⟩
  filter_upwards [hgood] with t hg
  refine ⟨hg, fun j k => ?_⟩
  refine (form_abs_le hg (w k) (w j)).trans ?_
  have h1 : formBnd M (w k) (w j) ≤ ∑ j' : Fin N, formBnd M (w k) (w j') :=
    Finset.single_le_sum (f := fun j' : Fin N => formBnd M (w k) (w j'))
      (fun j' _ => formBnd_nonneg hM _ _) (Finset.mem_univ j)
  have h2 : ∑ j' : Fin N, formBnd M (w k) (w j') ≤
      ∑ k' : Fin N, ∑ j' : Fin N, formBnd M (w k') (w j') :=
    Finset.single_le_sum (f := fun k' : Fin N => ∑ j' : Fin N, formBnd M (w k') (w j'))
      (fun k' _ => Finset.sum_nonneg fun j' _ => formBnd_nonneg hM _ _) (Finset.mem_univ k)
  linarith

lemma ode_coords {T : ℝ} (hT : 0 < T) {P : Coeffs n} (hP : P.Assumption61 Ω T) (w : ℕ → H10 n Ω)
    (N : ℕ) (F : ℝ → Fin N → ℝ) (hF : ∀ j, MemLp (fun t => F t j) 2 (timeMeasure T))
    (c0 : Fin N → ℝ) :
    ∃ c : ℝ → Fin N → ℝ, Continuous c ∧ c 0 = c0 ∧ (∀ t ∈ Icc (0:ℝ) T, ∀ j,
      c t j = c0 j + ∫ s in (0:ℝ)..t, (F s j - ∑ k : Fin N, form P s (w k) (w j) * c s k)) ∧
      ∀ j : Fin N, MemLp (fun s => ∑ k : Fin N, form P s (w k) (w j) * c s k) 2 (timeMeasure T) := by
  obtain ⟨K, hK0, θ, M, hθ, hM, hgood⟩ := matrix_good hP w N
  have htm : timeMeasure T = volume.restrict (Ioc 0 T) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [htm] at hgood hF
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) T)) := isFiniteMeasure_restrict.2 (by simp)
  let Mm : ℝ → Matrix (Fin N) (Fin N) ℝ := fun s j k => - form P s (w k) (w j)
  let A : ℝ → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := fun s =>
    LinearMap.toContinuousLinearMap (Matrix.toLin' (Mm s))
  have hA : ∀ s v j, A s v j = ∑ k, Mm s j k * v k := by
    intro s v j
    simp [A, Matrix.mulVec, dotProduct]
  have hAm : ∀ v : ℝ → Fin N → ℝ, Continuous v →
      AEStronglyMeasurable (fun s => A s (v s)) (volume.restrict (Ioc 0 T)) := by
    intro v hv
    refine (aemeasurable_pi_iff.2 fun j => ?_).aestronglyMeasurable
    suffices h : AEStronglyMeasurable (fun s => A s (v s) j) (volume.restrict (Ioc 0 T)) from
      h.aemeasurable
    have : (fun s => A s (v s) j) = fun s => ∑ k : Fin N, (-form P s (w (k : ℕ)) (w (j : ℕ))) * v s k := by
      funext s; rw [hA]
    rw [this]
    refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    have h1 := (form_aesm hP (w k) (w j)).neg
    rw [htm] at h1
    exact h1.mul ((continuous_apply k).comp hv).aestronglyMeasurable
  have hAb : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)), ‖A s‖ ≤ N * K := by
    filter_upwards [hgood] with s hs
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [hA, Real.norm_eq_abs]
    calc |∑ k, Mm s j k * v k| ≤ ∑ k, |Mm s j k * v k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin N, K * ‖v‖ := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          refine mul_le_mul ?_ ?_ (abs_nonneg _) hK0
          · simp only [Mm, abs_neg]; exact hs.2 j k
          · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v k
      _ = N * K * ‖v‖ := by simp [Finset.sum_const]; ring
  have hFint : IntegrableOn F (Ioc 0 T) := by
    have : F = fun s => ∑ j, F s j • (Pi.single j (1:ℝ) : Fin N → ℝ) := by
      funext s; ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact integrable_finsetSum _ fun j _ =>
      ((hF j).integrable one_le_two).smul_const _
  obtain ⟨c, hc, hceq⟩ := volterra_exists A F hT (by positivity) hAm hAb hFint c0
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · have := hceq 0 ⟨le_rfl, hT.le⟩
    simpa using this
  · intro t ht j
    have hint := intervalInt_of_Ioc hT (volterra_integrand_int A F hAm hAb hFint c hc) ht
    have h1 := congrFun (hceq t ht) j
    rw [Pi.add_apply] at h1
    rw [h1]
    congr 1
    have h2 := ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin N => ℝ) j) hint
    simp only [ContinuousLinearMap.proj_apply] at h2
    rw [← h2]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Pi.add_apply, hA, Mm]
    have : ∑ k : Fin N, -form P s (w k) (w j) * c s k = -∑ k : Fin N, form P s (w k) (w j) * c s k := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    ring
  · intro j
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hc.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT.le⟩)
    rw [htm]
    refine MemLp.of_bound ?_ (N * K * B) ?_
    · refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
      have h1 := form_aesm hP (w k) (w j)
      rw [htm] at h1
      exact h1.mul ((continuous_apply k).comp hc).aestronglyMeasurable
    · filter_upwards [hgood, ae_restrict_mem measurableSet_Ioc] with s hs hsI
      rw [Real.norm_eq_abs]
      calc |∑ k : Fin N, form P s (w k) (w j) * c s k|
          ≤ ∑ k : Fin N, |form P s (w k) (w j) * c s k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin N, K * B := Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            refine mul_le_mul (hs.2 j k) ?_ (abs_nonneg _) hK0
            rw [← Real.norm_eq_abs]
            exact (norm_le_pi_norm (c s) k).trans (hB s ⟨hsI.1.le, hsI.2⟩)
        _ = N * K * B := by simp [Finset.sum_const]; ring


-- ==== part B4 ====


/-! ## Seminormed helpers (the `StrongDual` instance path of `Hm1`) -/

lemma el_norm {E : Type*} [SeminormedAddCommGroup E] (f : ℝ → E) (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm f p μ = eLpNorm (fun t => ‖f t‖) p μ :=
  eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall fun x => by simp [enorm_eq_nnnorm])

lemma el_le {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {g : ℝ → ℝ} {p : ℝ≥0∞}
    {μ : Measure ℝ} (h : ∀ᵐ t ∂μ, ‖f t‖ ≤ g t) : eLpNorm f p μ ≤ eLpNorm g p μ := by
  rw [el_norm]; exact eLpNorm_mono_ae_real (by filter_upwards [h] with t ht; simpa using ht)

lemma el_cmul_norm {E : Type*} [SeminormedAddCommGroup E] (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a)
    (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun t => a * ‖f t‖) p μ = ENNReal.ofReal a * eLpNorm f p μ := by
  have : (fun t => a * ‖f t‖) = a • (fun t => ‖f t‖) := by funext t; simp
  rw [this, eLpNorm_const_smul, ← el_norm, Real.enorm_eq_ofReal ha]

lemma comp_memLp_semi {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ℝ → E} {p : ℝ≥0∞}
    {μ : Measure ℝ} (hf : MemLp f p μ) : MemLp (fun t => L (f t)) p μ := by
  refine ⟨L.continuous.comp_aestronglyMeasurable hf.1, ?_⟩
  refine (el_le (g := fun t => ‖L‖ * ‖f t‖)
    (Filter.Eventually.of_forall fun t => L.le_opNorm _)).trans_lt ?_
  rw [el_cmul_norm f (norm_nonneg L)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2

lemma memLp_of_continuous_time {T : ℝ} {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p (timeMeasure T) := by
  haveI : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable B ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hB t (Ioo_subset_Icc_self ht)

lemma memLp_smul_const' {μ : Measure ℝ} {a : ℝ → ℝ} {p : ℝ≥0∞} (ha : MemLp a p μ)
    (x : H10 n Ω) : MemLp (fun t => a t • x) p μ := by
  refine ha.of_le_mul (c := ‖x‖) (ha.1.smul_const x) ?_
  exact Filter.Eventually.of_forall fun t => by
    rw [norm_smul, mul_comm]

/-! ## Weak time derivative of a coordinate expansion -/

lemma weak_deriv_fsum {T : ℝ} (hT : 0 < T) (w : ℕ → H10 n Ω) (N : ℕ) (c d : ℝ → Fin N → ℝ)
    (c0 : Fin N → ℝ) (hc : Continuous c)
    (hcd : ∀ t ∈ Icc (0:ℝ) T, ∀ j, c t j = c0 j + ∫ s in (0:ℝ)..t, d s j)
    (hd : ∀ j, IntegrableOn (fun s => d s j) (Ioo 0 T)) :
    HasWeakTimeDeriv (ContinuousLinearMap.id ℝ (H10 n Ω)) T (fun t => fsum w N (c t))
      (fun t => fsum w N (d t)) := by
  intro φ hφ
  have hdc : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  have hdcc : HasCompactSupport (deriv φ) := hφ.2.1.deriv
  have hcI : ∀ k, IntegrableOn (fun s => c s k) (Ioo 0 T) := fun k =>
    (((continuous_apply k).comp hc).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hscal : ∀ k : Fin N, ∫ t in Ioo 0 T, deriv φ t * c t k = -∫ t in Ioo 0 T, φ t * d t k := by
    intro k
    have := primitive_weak_deriv hT (hd k) (c0 k) φ hφ
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [hcd t (Ioo_subset_Icc_self ht) k]
  simp only [ContinuousLinearMap.id_apply, fsum, Finset.smul_sum, smul_smul]
  have e1 : ∀ k : Fin N, Integrable (fun t => (deriv φ t * c t k) • w k) (volume.restrict (Ioo 0 T)) :=
    fun k => (test_mul_int hdc hdcc (hcI k)).smul_const _
  have e2 : ∀ k : Fin N, Integrable (fun t => (φ t * d t k) • w k) (volume.restrict (Ioo 0 T)) :=
    fun k => (test_mul_int hφ.1.continuous hφ.2.1 (hd k)).smul_const _
  rw [integral_finsetSum _ (fun k _ => e1 k), integral_finsetSum _ (fun k _ => e2 k),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_const, integral_smul_const, hscal k, neg_smul]

/-! ## The Galerkin equations tested against the whole Galerkin space -/

lemma approx_eq {P : Coeffs n} {w : ℕ → H10 n Ω}
    (horth : ∀ j k, l2inner (w j) (w k) = if j = k then 1 else 0) {N : ℕ} {θ M t : ℝ}
    (hg : GoodT P Ω θ M t) (c d F : Fin N → ℝ)
    (hd : ∀ j : Fin N, d j = F j - ∑ k : Fin N, form P t (w (k : ℕ)) (w (j : ℕ)) * c k) (Fv : H10 n Ω →L[ℝ] ℝ)
    (hF : ∀ j : Fin N, Fv (w j) = F j) :
    ∀ v ∈ galerkinSpace w N, l2inner (fsum w N d) v + form P t (fsum w N c) v = Fv v := by
  let Λ : H10 n Ω →ₗ[ℝ] ℝ :=
    { toFun := fun v => l2inner (fsum w N d) v + form P t (fsum w N c) v - Fv v
      map_add' := fun v v' => by
        simp only [l2inner_add_right, form_add_right hg, map_add]; ring
      map_smul' := fun a v => by
        simp only [l2inner_smul_right, form_smul_right hg, map_smul, smul_eq_mul,
          RingHom.id_apply]; ring }
  have key : ∀ j : Fin N, Λ (w j) = 0 := by
    intro j
    have h1 : l2inner (fsum w N d) (w j) = d j := by
      rw [l2inner_comm, ← coordCLM_apply, coord_fsum horth]
    have h2 : form P t (fsum w N c) (w j) = ∑ k : Fin N, form P t (w k) (w j) * c k := by
      rw [form_fsum_left hg]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    show l2inner (fsum w N d) (w j) + form P t (fsum w N c) (w j) - Fv (w j) = 0
    rw [h1, h2, hF, hd j]
    ring
  intro v hv
  have hv' := expand_galerkin horth hv
  have : Λ v = 0 := by
    rw [hv']
    simp only [fsum, map_sum, map_smul, key, smul_zero, Finset.sum_const_zero]
  have h3 : l2inner (fsum w N d) v + form P t (fsum w N c) v - Fv v = 0 := this
  linarith


-- ==== part B5 ====


/-! ## Existence of the Galerkin approximate solution -/

theorem galerkin_exists {T : ℝ} (hT : 0 < T) {P : Coeffs n} (hP : P.Assumption61 Ω T)
    {w : ℕ → H10 n Ω} (horth : ∀ j k, l2inner (w j) (w k) = if j = k then 1 else 0)
    {f : ℝ → Hm1 n Ω} (hf : MemLp f 2 (timeMeasure T)) (g : Lp ℝ 2 (volume.restrict Ω))
    (N : ℕ) : ∃ uN uNt : ℝ → H10 n Ω, IsApproxSolution Ω T P w N f g uN uNt := by
  have hFj : ∀ j : Fin N, MemLp (fun t => f t (w j)) 2 (timeMeasure T) := fun j =>
    comp_memLp_semi (ContinuousLinearMap.apply ℝ ℝ (w j)) hf
  obtain ⟨c0, hc0def⟩ : ∃ c0 : Fin N → ℝ, c0 = fun k : Fin N => inner ℝ (toL2 (w (k : ℕ))) g := ⟨_, rfl⟩
  obtain ⟨c, hc, hc0, hceq, hmem⟩ := ode_coords hT hP w N (fun t j => f t (w j)) hFj c0
  obtain ⟨d, hd⟩ : ∃ d : ℝ → Fin N → ℝ,
      d = fun s (j : Fin N) => f s (w (j : ℕ)) - ∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * c s k := ⟨_, rfl⟩
  have hdj : ∀ j, MemLp (fun s => d s j) 2 (timeMeasure T) := fun j => by
    have : (fun s => d s j) = fun s => f s (w j) - ∑ k : Fin N, form P s (w k) (w j) * c s k := by
      rw [hd]
    rw [this]
    exact (hFj j).sub (hmem j)
  have hfin : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hdI : ∀ j, IntegrableOn (fun s => d s j) (Ioo 0 T) := fun j =>
    (hdj j).integrable one_le_two
  have hcd : ∀ t ∈ Icc (0:ℝ) T, ∀ j, c t j = c0 j + ∫ s in (0:ℝ)..t, d s j := by
    intro t ht j
    rw [hceq t ht j, hd]
  have hcont : Continuous (fun t => fsum w N (c t)) := by
    unfold fsum
    exact continuous_finsetSum _ fun k _ =>
      (((continuous_apply k).comp hc).smul continuous_const)
  obtain ⟨θ, M, hθ, hM, hgood⟩ := good_ae hP
  unfold IsApproxSolution
  refine ⟨fun t => fsum w N (c t), fun t => fsum w N (d t), fun t _ => fsum_mem w N _,
    fun t _ => fsum_mem w N _, memLp_of_continuous_time hcont 2, ?_,
    weak_deriv_fsum hT w N c d c0 hc hcd hdI, ?_, fun t => fsum w N (c t), hcont.continuousOn,
    Filter.Eventually.of_forall fun _ => rfl, ?_⟩
  · unfold fsum
    refine memLp_finsetSum _ fun k _ => ?_
    exact memLp_smul_const' (hdj k) _
  · intro v hv
    filter_upwards [hgood] with t hg
    exact approx_eq horth hg (c t) (d t) (fun j => f t (w j)) (fun j => by rw [hd]) (f t)
      (fun j => rfl) v hv
  · show fsum w N (c 0) = galerkinProj w N g
    rw [hc0, hc0def, galerkinProj, fsum, Finset.sum_range]


-- ==== part B6 ====


/-! ## Uniqueness: coordinates of an arbitrary approximate solution -/

lemma form_sum_memLp {T : ℝ} (hT : 0 < T) {P : Coeffs n} (hP : P.Assumption61 Ω T) (w : ℕ → H10 n Ω) (N : ℕ)
    {e : ℝ → Fin N → ℝ} (he : ContinuousOn e (Icc 0 T)) (j : Fin N) :
    MemLp (fun s => ∑ k : Fin N, form P s (w k) (w j) * e s k) 2 (timeMeasure T) := by
  obtain ⟨K, hK0, θ, M, hθ, hM, hgood⟩ := matrix_good hP w N
  haveI : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn he
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT.le⟩)
  refine MemLp.of_bound ?_ (N * K * B) ?_
  · refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    exact (form_aesm hP (w k) (w j)).mul
      (((continuous_apply k).comp_continuousOn he).mono Ioo_subset_Icc_self
        |>.aestronglyMeasurable measurableSet_Ioo)
  · filter_upwards [hgood, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    rw [Real.norm_eq_abs]
    calc |∑ k : Fin N, form P s (w k) (w j) * e s k|
        ≤ ∑ k : Fin N, |form P s (w k) (w j) * e s k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin N, K * B := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          refine mul_le_mul (hs.2 j k) ?_ (abs_nonneg _) hK0
          rw [← Real.norm_eq_abs]
          exact (norm_le_pi_norm (e s) k).trans (hB s (Ioo_subset_Icc_self hsI))
      _ = N * K * B := by simp [Finset.sum_const]; ring

lemma weak_coord {T : ℝ} {u ut : ℝ → H10 n Ω} (hu : MemLp u 2 (timeMeasure T))
    (hweak : HasWeakTimeDeriv (ContinuousLinearMap.id ℝ (H10 n Ω)) T u ut)
    (hut : MemLp ut 2 (timeMeasure T)) (ℓ : H10 n Ω →L[ℝ] ℝ) (φ : ℝ → ℝ)
    (hφ : IsTestFunctionOn T φ) :
    ∫ t in Ioo 0 T, deriv φ t * ℓ (u t) = -∫ t in Ioo 0 T, φ t * ℓ (ut t) := by
  haveI : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hdc : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  have hd : MemLp (deriv φ) ⊤ (timeMeasure T) :=
    hdc.memLp_top_of_hasCompactSupport hφ.2.1.deriv _
  have hp : MemLp φ ⊤ (timeMeasure T) :=
    hφ.1.continuous.memLp_top_of_hasCompactSupport hφ.2.1 _
  have i1 : Integrable (fun t => deriv φ t • u t) (timeMeasure T) :=
    (hu.integrable one_le_two).smul_of_top_right hd
  have i2 : Integrable (fun t => φ t • ut t) (timeMeasure T) :=
    (hut.integrable one_le_two).smul_of_top_right hp
  have h := hweak φ hφ
  simp only [ContinuousLinearMap.id_apply] at h
  have h2 := congrArg ℓ h
  rw [map_neg, ← ContinuousLinearMap.integral_comp_comm ℓ i1,
    ← ContinuousLinearMap.integral_comp_comm ℓ i2] at h2
  simpa [map_smul, smul_eq_mul] using h2


-- ==== part B7 ====


lemma prim_continuousOn {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo 0 T)) :
    ContinuousOn (fun t => ∫ s in (0:ℝ)..t, g s) (Icc 0 T) := by
  have hI : IntegrableOn g (uIcc 0 T) := by
    rw [uIcc_of_le hT.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2
      ((integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hg)
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) hI
  rwa [uIcc_of_le hT.le] at this

theorem approx_coords {T : ℝ} (hT : 0 < T) {P : Coeffs n} (hP : P.Assumption61 Ω T)
    {w : ℕ → H10 n Ω} (horth : ∀ j k, l2inner (w j) (w k) = if j = k then 1 else 0)
    {f : ℝ → Hm1 n Ω} (hf : MemLp f 2 (timeMeasure T)) (g : Lp ℝ 2 (volume.restrict Ω)) (N : ℕ)
    {u ut : ℝ → H10 n Ω} (h : IsApproxSolution Ω T P w N f g u ut) :
    ∃ e : ℝ → Fin N → ℝ, ContinuousOn e (Icc 0 T) ∧
      (∀ j : Fin N, e 0 j = inner ℝ (toL2 (w (j : ℕ))) g) ∧
      (∀ᵐ t ∂(timeMeasure T), u t = fsum w N (e t)) ∧
      ∃ C : Fin N → ℝ, ∀ t ∈ Icc (0:ℝ) T, ∀ j : Fin N,
        e t j = C j + ∫ s in (0:ℝ)..t,
          (f s (w (j : ℕ)) - ∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * e s k) := by
  obtain ⟨hm1, hm2, hu2, hut2, hweak, heq, ũ, hũc, hũae, hũ0⟩ := h
  have hfin : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  obtain ⟨e, he⟩ : ∃ e : ℝ → Fin N → ℝ, e = fun t (j : Fin N) => coordCLM n Ω w (j : ℕ) (ũ t) := ⟨_, rfl⟩
  have hec : ContinuousOn e (Icc 0 T) := by
    rw [he]
    exact continuousOn_pi.2 fun j => (coordCLM n Ω w (j : ℕ)).continuous.comp_continuousOn hũc
  have hproj : galerkinProj w N g = fsum w N (fun k : Fin N => inner ℝ (toL2 (w (k : ℕ))) g) := by
    rw [galerkinProj, fsum, Finset.sum_range]
  have he0 : ∀ j : Fin N, e 0 j = inner ℝ (toL2 (w (j : ℕ))) g := by
    intro j
    rw [he]
    simp only
    rw [hũ0, hproj, coord_fsum horth]
  have hFj : ∀ j : Fin N, MemLp (fun t => f t (w j)) 2 (timeMeasure T) := fun j =>
    comp_memLp_semi (ContinuousLinearMap.apply ℝ ℝ (w j)) hf
  have hcoord : ∀ᵐ t ∂(timeMeasure T), ∀ k : Fin N, coordCLM n Ω w (k : ℕ) (u t) = e t k := by
    filter_upwards [hũae] with t ht k
    rw [he]
    simp only
    rw [ht]
  have hrep : ∀ᵐ t ∂(timeMeasure T), u t = fsum w N (e t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hcoord] with t htI hc
    have hex := expand_galerkin horth (hm1 t (Ioo_subset_Icc_self htI))
    rw [hex]
    congr 1
    funext k
    exact hc k
  obtain ⟨θ, M, hθ, hM, hgood⟩ := good_ae hP
  have hode : ∀ᵐ t ∂(timeMeasure T), ∀ j : Fin N, coordCLM n Ω w (j : ℕ) (ut t) =
      f t (w j) - ∑ k : Fin N, form P t (w k) (w j) * e t k := by
    have h1 : ∀ᵐ t ∂(timeMeasure T), ∀ j : Fin N,
        l2inner (ut t) (w j) + form P t (u t) (w j) = f t (w j) :=
      ae_all_iff.2 fun j => heq (w j) (Submodule.subset_span ⟨j, j.2, rfl⟩)
    filter_upwards [h1, hgood, ae_restrict_mem measurableSet_Ioo, hcoord] with t h1 hg htI hc j
    have hform : form P t (u t) (w j) = ∑ k : Fin N, e t k * form P t (w k) (w j) := by
      have hex := expand_galerkin horth (hm1 t (Ioo_subset_Icc_self htI))
      rw [hex, form_fsum_left hg]
      exact Finset.sum_congr rfl fun k _ => by rw [hc k]
    have h2 := h1 j
    rw [l2inner_comm, ← coordCLM_apply, hform] at h2
    have h3 : ∑ k : Fin N, e t k * form P t (w k) (w j) =
        ∑ k : Fin N, form P t (w k) (w j) * e t k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    linarith
  obtain ⟨G, hGdef⟩ : ∃ G : Fin N → ℝ → ℝ, G = fun (j : Fin N) s =>
      f s (w (j : ℕ)) - ∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * e s k := ⟨_, rfl⟩
  have hG : ∀ j, MemLp (G j) 2 (timeMeasure T) := fun j => by
    rw [hGdef]
    exact (hFj j).sub (form_sum_memLp hT hP w N hec j)
  have hGI : ∀ j, IntegrableOn (G j) (Ioo 0 T) := fun j => (hG j).integrable one_le_two
  have hcw : ∀ j : Fin N, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 T →
      coordCLM n Ω w (j : ℕ) (ut s) = G j s := by
    intro j
    rw [← ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hode] with s hs
    rw [hGdef]
    exact hs j
  have hdbr : ∀ j : Fin N, ∃ C : ℝ, ∀ᵐ t ∂(timeMeasure T),
      coordCLM n Ω w (j : ℕ) (u t) = C + ∫ s in (0:ℝ)..t, coordCLM n Ω w (j : ℕ) (ut s) := by
    intro j
    exact dbr_scalar hT
      ((comp_memLp_semi (coordCLM n Ω w (j : ℕ)) hu2).integrable one_le_two)
      ((comp_memLp_semi (coordCLM n Ω w (j : ℕ)) hut2).integrable one_le_two)
      (fun φ hφ => weak_coord hu2 hweak hut2 (coordCLM n Ω w (j : ℕ)) φ hφ)
  choose C hC using hdbr
  refine ⟨e, hec, he0, hrep, C, ?_⟩
  intro t ht j
  have hEq : EqOn (fun t => e t j) (fun t => C j + ∫ s in (0:ℝ)..t, G j s) (Icc 0 T) := by
    refine Measure.eqOn_of_ae_eq (μ := volume) ?_ ((continuous_apply j).comp_continuousOn hec)
      (continuousOn_const.add (prim_continuousOn hT (hGI j)))
      (by rw [interior_Icc, closure_Ioo hT.ne])
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    filter_upwards [hC j, hcoord, ae_restrict_mem measurableSet_Ioo] with s h1 h2 hsI
    have h3 : ∫ r in (0:ℝ)..s, coordCLM n Ω w (j : ℕ) (ut r) = ∫ r in (0:ℝ)..s, G j r := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hcw j] with r hr hrI
      rw [uIoc_of_le hsI.1.le] at hrI
      exact hr ⟨hrI.1, hrI.2.trans_lt hsI.2⟩
    show e s j = C j + ∫ r in (0:ℝ)..s, G j r
    rw [← h2 j, h1, h3]
  have := hEq ht
  subst hGdef
  exact this


-- ==== part B8 ====


/-! ## Uniqueness of the Galerkin approximate solution -/

theorem galerkin_unique {T : ℝ} (hT : 0 < T) {P : Coeffs n} (hP : P.Assumption61 Ω T)
    {w : ℕ → H10 n Ω} (horth : ∀ j k, l2inner (w j) (w k) = if j = k then 1 else 0)
    {f : ℝ → Hm1 n Ω} (hf : MemLp f 2 (timeMeasure T)) (g : Lp ℝ 2 (volume.restrict Ω)) (N : ℕ)
    {u ut v vt : ℝ → H10 n Ω} (hu : IsApproxSolution Ω T P w N f g u ut)
    (hv : IsApproxSolution Ω T P w N f g v vt) : v =ᵐ[timeMeasure T] u := by
  obtain ⟨eu, heuc, heu0, heuae, Cu, hCu⟩ := approx_coords hT hP horth hf g N hu
  obtain ⟨ev, hevc, hev0, hevae, Cv, hCv⟩ := approx_coords hT hP horth hf g N hv
  obtain ⟨K, hK0, θ, M, hθ, hM, hgood⟩ := matrix_good hP w N
  have hFj : ∀ j : Fin N, MemLp (fun t => f t (w j)) 2 (timeMeasure T) := fun j =>
    comp_memLp_semi (ContinuousLinearMap.apply ℝ ℝ (w j)) hf
  haveI : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hC : ∀ j, Cu j = Cv j := by
    intro j
    have h1 : eu 0 j = Cu j := by simpa using hCu 0 ⟨le_rfl, hT.le⟩ j
    have h2 : ev 0 j = Cv j := by simpa using hCv 0 ⟨le_rfl, hT.le⟩ j
    rw [← h1, ← h2, heu0 j, hev0 j]
  obtain ⟨Gu, hGu⟩ : ∃ Gu : Fin N → ℝ → ℝ, Gu = fun (j : Fin N) s =>
      f s (w (j : ℕ)) - ∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * eu s k := ⟨_, rfl⟩
  obtain ⟨Gv, hGv⟩ : ∃ Gv : Fin N → ℝ → ℝ, Gv = fun (j : Fin N) s =>
      f s (w (j : ℕ)) - ∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * ev s k := ⟨_, rfl⟩
  have hGuI : ∀ j, IntegrableOn (Gu j) (Ioo 0 T) := fun j => by
    rw [hGu]
    exact ((hFj j).sub (form_sum_memLp hT hP w N heuc j)).integrable one_le_two
  have hGvI : ∀ j, IntegrableOn (Gv j) (Ioo 0 T) := fun j => by
    rw [hGv]
    exact ((hFj j).sub (form_sum_memLp hT hP w N hevc j)).integrable one_le_two
  have hIu : ∀ j, ∀ t ∈ Icc (0:ℝ) T, IntervalIntegrable (Gu j) volume 0 t := fun j t ht =>
    intervalInt_of_Ioc hT ((integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 (hGuI j)) ht
  have hIv : ∀ j, ∀ t ∈ Icc (0:ℝ) T, IntervalIntegrable (Gv j) volume 0 t := fun j t ht =>
    intervalInt_of_Ioc hT ((integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 (hGvI j)) ht
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ → Fin N → ℝ, Δ = fun t => eu t - ev t := ⟨_, rfl⟩
  have hΔc : ContinuousOn Δ (Icc 0 T) := by rw [hΔ]; exact heuc.sub hevc
  have hΔj : ∀ t ∈ Icc (0:ℝ) T, ∀ j : Fin N, Δ t j = ∫ s in (0:ℝ)..t, (Gu j s - Gv j s) := by
    intro t ht j
    rw [intervalIntegral.integral_sub (hIu j t ht) (hIv j t ht), hΔ]
    have h1 := hCu t ht j
    have h2 := hCv t ht j
    simp only [Pi.sub_apply]
    rw [h1, h2, hC j, hGu, hGv]
    ring
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({T} : Set ℝ) :=
    (Set.countable_singleton T).ae_notMem _
  have hbound : ∀ t ∈ Icc (0:ℝ) T, ‖Δ t‖ ≤ (N * K) * ∫ s in (0:ℝ)..t, ‖Δ s‖ := by
    intro t ht
    have hint : 0 ≤ ∫ s in (0:ℝ)..t, ‖Δ s‖ :=
      intervalIntegral.integral_nonneg ht.1 fun s _ => norm_nonneg _
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hint)).2 fun j => ?_
    rw [hΔj t ht j, Real.norm_eq_abs]
    have hcont : ContinuousOn (fun s => (N * K) * ‖Δ s‖) (uIcc 0 t) := by
      rw [uIcc_of_le ht.1]
      exact continuousOn_const.mul ((hΔc.mono (Icc_subset_Icc_right ht.2)).norm)
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc 0 t →
        ‖Gu j s - Gv j s‖ ≤ (N * K) * ‖Δ s‖ := by
      have h0 := (ae_restrict_iff' measurableSet_Ioo).1 hgood
      filter_upwards [h0, hnull] with s hs hsT hsI
      have hsI' : s ∈ Ioo 0 T := ⟨hsI.1, lt_of_le_of_ne (hsI.2.trans ht.2) hsT⟩
      have hs' := hs hsI'
      rw [Real.norm_eq_abs, hGu, hGv]
      have e1 : (f s (w (j : ℕ)) - ∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * eu s k) -
          (f s (w (j : ℕ)) - ∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * ev s k) =
          -∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * (Δ s k) := by
        rw [hΔ]
        simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring
      rw [e1, abs_neg]
      calc |∑ k : Fin N, form P s (w (k : ℕ)) (w (j : ℕ)) * Δ s k|
          ≤ ∑ k : Fin N, |form P s (w (k : ℕ)) (w (j : ℕ)) * Δ s k| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin N, K * ‖Δ s‖ := Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            refine mul_le_mul (hs'.2 j k) ?_ (abs_nonneg _) hK0
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm (Δ s) k
        _ = N * K * ‖Δ s‖ := by simp [Finset.sum_const]; ring
    calc ‖∫ s in (0:ℝ)..t, (Gu j s - Gv j s)‖ ≤ ∫ s in (0:ℝ)..t, (N * K) * ‖Δ s‖ :=
          intervalIntegral.norm_integral_le_of_norm_le ht.1 hae (hcont.intervalIntegrable)
      _ = (N * K) * ∫ s in (0:ℝ)..t, ‖Δ s‖ := intervalIntegral.integral_const_mul _ _
  have hzero := gronwall_zero hT (mul_nonneg (by positivity) hK0) hΔc hbound
  filter_upwards [heuae, hevae, ae_restrict_mem measurableSet_Ioo] with t h1 h2 htI
  rw [h1, h2]
  have := hzero t (Ioo_subset_Icc_self htI)
  rw [hΔ] at this
  have h3 : eu t = ev t := sub_eq_zero.1 this
  rw [h3]


end P6525923f

open HunterPDE.Parabolic MeasureTheory in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (P : Coeffs n)
    (hP : P.Assumption61 Ω T) (w : ℕ → H10 n Ω) (eig : ℕ → ℝ)
    (hw : IsDirichletEigenbasis Ω w eig) (f : ℝ → Hm1 n Ω) (hf : MemLp f 2 (timeMeasure T))
    (g : Lp ℝ 2 (volume.restrict Ω)) (N : ℕ) :
    ∃ uN uNt : ℝ → H10 n Ω, IsApproxSolution Ω T P w N f g uN uNt ∧
      ∀ vN vNt : ℝ → H10 n Ω, IsApproxSolution Ω T P w N f g vN vNt →
        vN =ᵐ[timeMeasure T] uN := by
  obtain ⟨uN, uNt, h⟩ := P6525923f.galerkin_exists hT hP hw.2.1 hf g N
  exact ⟨uN, uNt, h, fun vN vNt hv => P6525923f.galerkin_unique hT hP hw.2.1 hf g N h hv⟩

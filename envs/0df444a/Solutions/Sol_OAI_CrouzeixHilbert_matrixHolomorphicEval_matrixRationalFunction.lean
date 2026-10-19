-- Prove2me | solution 1 for OAI.CrouzeixHilbert.matrixHolomorphicEval_matrixRationalFunction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:43:44.39133+00:00
-- url     : https://prove2.me/submissions/b4758c2c-fa47-4be7-af90-252efa909699

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000

section
-- module Solutions.OAIQW_CrouzeixHilbert.NumericalRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact numerical closure, supremum norms, and spectral containment. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem numericalRange_nonempty [Nontrivial H] (A : Operator H) :
    (numericalRange A).Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨⟪x, A x⟫_ℂ, x, hx, rfl⟩

theorem numericalClosure_nonempty [Nontrivial H] (A : Operator H) :
    (numericalClosure A).Nonempty :=
  (numericalRange_nonempty A).mono subset_closure

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Convexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of the numerical range and its closure. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem phase_real (u v : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (c * u + star c * v).im = 0 := by
  let d : ℂ := u - star v
  have him (c : ℂ) : (c * u + star c * v).im = (c * d).im := by
    simp only [d, mul_sub, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  by_cases hd : d = 0
  · refine ⟨1, norm_one, ?_⟩
    rw [him, hd, mul_zero, Complex.zero_im]
  · refine ⟨(‖d‖ : ℂ)⁻¹ * star d, ?_, ?_⟩
    · simp [hd]
    · rw [him, mul_assoc]
      simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_inv,
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem unit_interval_of_quadratic_endpoints (B : Operator H)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hBx : ⟪x, B x⟫_ℂ = 0) (hBy : ⟪y, B y⟫_ℂ = 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ w : H, ‖w‖ = 1 ∧ ⟪w, B w⟫_ℂ = (t : ℂ) := by
  obtain ⟨c, hc, hcross⟩ := phase_real ⟪x, B y⟫_ℂ ⟪y, B x⟫_ℂ
  let y' : H := c • y
  have hy' : ‖y'‖ = 1 := by simp [y', norm_smul, hc, hy]
  have hy'B : ⟪y', B y'⟫_ℂ = 1 := by
    simp only [y', map_smul, inner_smul_left, inner_smul_right, hBy, mul_one,
      Complex.mul_conj', hc, Complex.ofReal_one, one_pow]
  have hc' : (⟪x, B y'⟫_ℂ + ⟪y', B x⟫_ℂ).im = 0 := by
    simpa only [y', map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply] using hcross
  let q : ℝ → H := fun s => ((1 - s : ℝ) : ℂ) • x + (s : ℂ) • y'
  have hq0 (s : ℝ) : q s ≠ 0 := by
    intro hz
    have heq : (((1 - s : ℝ) : ℂ) • x) = -(s : ℂ) • y' := by
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hz
    have hq := congrArg (fun z : H => ⟪z, B z⟫_ℂ) heq
    simp only [map_smul, inner_smul_left, inner_smul_right, hBx, hy'B, mul_zero,
      mul_one, map_neg, Complex.conj_ofReal, neg_mul_neg] at hq
    have hs : s = 0 := by
      have hh := congrArg Complex.re hq
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.zero_re] at hh
      nlinarith
    simp [q, hs] at hz
    rw [hz] at hx
    norm_num at hx
  have hq : Continuous q := by
    dsimp [q]
    fun_prop
  have hqi (s : ℝ) : (⟪q s, B (q s)⟫_ℂ).im = 0 := by
    have heq : ⟪q s, B (q s)⟫_ℂ = (s : ℂ) ^ 2 +
        (s : ℂ) * (1 - (s : ℂ)) * (⟪x, B y'⟫_ℂ + ⟪y', B x⟫_ℂ) := by
      simp only [q, map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal, hBx, hy'B, map_sub, map_one,
        mul_zero, mul_one, zero_add, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    rw [heq]
    simp [Complex.add_im, Complex.mul_im, hc', pow_two]
  let g : ℝ → H := fun s => (‖q s‖ : ℂ)⁻¹ • q s
  have hg (s : ℝ) : ‖g s‖ = 1 := by
    simp [g, norm_smul, hq0 s]
  have hgc : Continuous g := by
    apply Continuous.smul _ hq
    apply Continuous.inv₀ (Complex.continuous_ofReal.comp hq.norm)
    intro s
    change (‖q s‖ : ℂ) ≠ 0
    exact_mod_cast norm_ne_zero_iff.mpr (hq0 s)
  have hgi (s : ℝ) : (⟪g s, B (g s)⟫_ℂ).im = 0 := by
    simp only [g, map_smul, inner_smul_left, inner_smul_right, ← Complex.ofReal_inv,
      Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hqi s]
    ring
  let f : ℝ → ℝ := fun s => (⟪g s, B (g s)⟫_ℂ).re
  have hfc : Continuous f := Complex.continuous_re.comp (hgc.inner (𝕜 := ℂ) (B.continuous.comp hgc))
  have hf0 : f 0 = 0 := by simp [f, g, q, hx, hBx]
  have hf1 : f 1 = 1 := by simp [f, g, q, hy', hy'B]
  have hmem : t ∈ Icc (f 0) (f 1) := by simpa only [hf0, hf1] using ht
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hfc.continuousOn hmem
  refine ⟨g s, hg s, ?_⟩
  apply Complex.ext
  · exact hs
  · exact hgi s

theorem convex_numericalRange (A : Operator H) : Convex ℝ (numericalRange A) := by
  intro a ha b hb α β hα hβ hsum
  by_cases hab : a = b
  · subst b
    rw [← add_smul, hsum, one_smul]
    exact ha
  obtain ⟨x, hx, hAx⟩ := ha
  obtain ⟨y, hy, hAy⟩ := hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let B : Operator H := (b - a)⁻¹ • (A - a • 1)
  have hform (v : H) (hv : ‖v‖ = 1) :
      ⟪v, B v⟫_ℂ = (b - a)⁻¹ * (⟪v, A v⟫_ℂ - a) := by
    simp [B, inner_self_eq_norm_sq_to_K, hv]
  have hBx : ⟪x, B x⟫_ℂ = 0 := by rw [hform x hx, hAx, sub_self, mul_zero]
  have hBy : ⟪y, B y⟫_ℂ = 1 := by rw [hform y hy, hAy, inv_mul_cancel₀ hba]
  obtain ⟨w, hw, hwB⟩ := unit_interval_of_quadratic_endpoints B x y hx hy hBx hBy
    β ⟨hβ, by linarith⟩
  refine ⟨w, hw, ?_⟩
  rw [hform w hw] at hwB
  have hid := congrArg (fun z : ℂ => (b - a) * z) hwB
  simp only [← mul_assoc, mul_inv_cancel₀ hba, one_mul] at hid
  have hsumC : (α : ℂ) + (β : ℂ) = 1 := by exact_mod_cast hsum
  calc
    ⟪w, A w⟫_ℂ = (⟪w, A w⟫_ℂ - a) + a := by ring
    _ = (b - a) * (β : ℂ) + a := by rw [hid]
    _ = α • a + β • b := by
      simp only [Complex.real_smul]
      linear_combination -a * hsumC

theorem convex_numericalClosure (A : Operator H) : Convex ℝ (numericalClosure A) :=
  (convex_numericalRange A).closure

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Homotopy. -/

noncomputable section

open scoped InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem numericalClosure_operatorHomotopy_subset (A : Operator H) {a : ℂ}
    (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    numericalClosure (operatorHomotopy A a s) ⊆ numericalClosure A := by
  apply closure_minimal _ isClosed_closure
  rintro z ⟨x, hx, rfl⟩
  have h := (convex_numericalClosure A).add_smul_sub_mem ha
    (subset_closure (show ⟪x, A x⟫_ℂ ∈ numericalRange A from ⟨x, hx, rfl⟩)) hs
  simpa [operatorHomotopy, ContinuousLinearMap.algebraMap_apply,
    inner_self_eq_norm_sq_to_K, hx] using! h

theorem homotopy_resolvent_isUnit [CompleteSpace H] (A : Operator H) {a z : ℂ}
    (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : z ∉ numericalClosure A) :
    IsUnit (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) := by
  change z ∈ resolventSet ℂ (operatorHomotopy A a s)
  by_contra he
  exact hz (numericalClosure_operatorHomotopy_subset A ha hs
    (spectrum_subset_numericalClosure _ he))

theorem continuousOn_homotopyResolvent [CompleteSpace H] (A : Operator H)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (fun p : ℝ × ℂ => homotopyResolvent A a p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (numericalClosure A)ᶜ) := by
  have hc : Continuous (fun p : ℝ × ℂ =>
      algebraMap ℂ (Operator H) p.2 - operatorHomotopy A a p.1) :=
    by simp only [operatorHomotopy, Algebra.algebraMap_eq_smul_one]; fun_prop
  intro p hp
  exact ((differentiableAt_inverse (𝕜 := ℝ)
    (homotopy_resolvent_isUnit A ha hp.1 hp.2)).continuousAt.comp
      (f := fun q : ℝ × ℂ => algebraMap ℂ (Operator H) q.2 - operatorHomotopy A a q.1)
      (x := p) hc.continuousAt).continuousWithinAt

theorem commute_homotopyResolvent (A : Operator H) (a : ℂ) (s : ℝ) (z : ℂ) :
    Commute (A - algebraMap ℂ (Operator H) a) (homotopyResolvent A a s z) := by
  let D := A - algebraMap ℂ (Operator H) a
  have hc : Commute D (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) := by
    apply Commute.sub_right (Algebra.commutes z D).symm
    exact (show Commute D (algebraMap ℂ (Operator H) a) from (Algebra.commutes a D).symm).add_right ((Commute.refl D).smul_right s)
  by_cases hu : IsUnit (algebraMap ℂ (Operator H) z - operatorHomotopy A a s)
  · rcases hu with ⟨v, hv⟩
    change Commute D (Ring.inverse _)
    rw [← hv, Ring.inverse_unit]
    exact (show Commute D (v : Operator H) from hv.symm ▸ hc).units_inv_right
  · simp only [homotopyResolvent, Ring.inverse_non_unit _ hu]
    exact Commute.zero_right _

theorem hasDerivAt_homotopyResolvent [CompleteSpace H] (A : Operator H)
    {a z : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : z ∉ numericalClosure A) :
    HasDerivAt (fun r : ℝ => homotopyResolvent A a r z)
      (homotopyResolvent A a s z * (A - algebraMap ℂ (Operator H) a) *
        homotopyResolvent A a s z) s := by
  have hu := homotopy_resolvent_isUnit A ha hs hz
  have h₁ : HasFDerivAt Ring.inverse _
      (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) :=
    hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have h₂ : HasDerivAt (fun r : ℝ => algebraMap ℂ (Operator H) z - operatorHomotopy A a r)
      (-(A - algebraMap ℂ (Operator H) a)) s := by
    simpa only [operatorHomotopy, one_smul, zero_add, zero_sub, id_eq] using!
      (((hasDerivAt_id s).smul_const (A - algebraMap ℂ (Operator H) a)).const_add
        (algebraMap ℂ (Operator H) a)).const_sub (algebraMap ℂ (Operator H) z)
  simpa only [homotopyResolvent, Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ← Ring.inverse_unit hu.unit, hu.unit_spec,
    mul_neg, neg_mul, neg_neg] using! h₁.comp_hasDerivAt s h₂

theorem hasDerivAt_homotopyResolvent_path [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => homotopyResolvent A a s (Γ.path r))
      (-(deriv Γ.path t) • (homotopyResolvent A a s (Γ.path t)) ^ 2) t := by
  have hu := homotopy_resolvent_isUnit A ha hs (Γ.avoids t ht).2
  have h₁ := spectrum.hasDerivAt_resolvent_const_left (𝕜 := ℂ) hu
  have h₂ : HasDerivAt Γ.path (deriv Γ.path t) t :=
    (Γ.smooth.differentiable (by norm_num) t).hasDerivAt
  have h := (h₁.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t h₂
  simpa [homotopyResolvent, resolvent, neg_smul, Function.comp_def] using! h

theorem continuousOn_homotopyResolvent_path [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (fun p : ℝ × ℝ => homotopyResolvent A a p.1 (Γ.path p.2))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
  (continuousOn_homotopyResolvent A ha).comp
    ((continuous_fst.prodMk (Γ.smooth.continuous.comp continuous_snd)).continuousOn)
    (fun p hp => ⟨hp.1, (Γ.avoids p.2 hp.2).2⟩)

theorem continuousOn_homotopyKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (Function.uncurry (homotopyKernel A a Γ.toSmoothContour))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hr := continuousOn_homotopyResolvent_path A Γ ha
  exact (Γ.smooth.continuous_deriv_one.comp continuous_snd).continuousOn.smul
    ((hr.mul continuousOn_const).mul hr)

theorem intervalIntegrable_homotopyKernel_left [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => homotopyKernel A a Γ.toSmoothContour s t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hc := (continuousOn_homotopyKernel A Γ ha).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, ht⟩)
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le zero_le_one, Function.comp_def, Function.uncurry_def] using! hc

theorem intervalIntegrable_homotopyKernel_right [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (homotopyKernel A a Γ.toSmoothContour s)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hc := (continuousOn_homotopyKernel A Γ ha).comp
    (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le zero_le_one, Function.comp_def, Function.uncurry_def] using! hc

theorem integral_homotopyKernel_left [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) =
      deriv Γ.path t • homotopyResolvent A a 1 (Γ.path t) -
        deriv Γ.path t • homotopyResolvent A a 0 (Γ.path t) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => deriv Γ.path t • homotopyResolvent A a r (Γ.path t)) _
    (intervalIntegrable_homotopyKernel_left A Γ ha ht)
  intro s hs
  exact (hasDerivAt_homotopyResolvent A ha (by simpa using hs) (Γ.avoids t ht).2).const_smul
    (deriv Γ.path t)

theorem hasDerivAt_homotopyKernel_primitive [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => -((A - algebraMap ℂ (Operator H) a) *
        homotopyResolvent A a s (Γ.path r)))
      (homotopyKernel A a Γ.toSmoothContour s t) t := by
  have h := (hasDerivAt_homotopyResolvent_path A Γ ha hs ht).const_mul
    (A - algebraMap ℂ (Operator H) a) |>.neg
  have hc := (commute_homotopyResolvent A a s (Γ.path t)).eq
  simpa only [homotopyKernel, mul_smul_comm, neg_smul, mul_neg, neg_neg,
    sq, ← mul_assoc, hc] using! h

theorem integral_homotopyKernel_right [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) = 0 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_homotopyKernel_primitive A Γ ha hs (by simpa using ht))
    (intervalIntegrable_homotopyKernel_right A Γ ha hs)
  simpa only [Γ.closed, sub_self] using he

theorem integral_integral_homotopyKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) = 0 := by
  have hc := continuousOn_homotopyKernel A Γ ha
  have hi := (hc.integrableOn_compact (μ := MeasureTheory.volume) (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hFub := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := homotopyKernel A a Γ.toSmoothContour)
    (a := (0 : ℝ)) (b := 1) (c := 0) (d := 1) (by simpa using! hi)
  rw [← hFub]
  calc
    _ = ∫ _s in (0 : ℝ)..1, (0 : Operator H) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact integral_homotopyKernel_right A Γ ha (by simpa using hs)
    _ = 0 := by simp

theorem integral_resolvent_homotopy [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t • Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - A)) =
      ∫ t in (0 : ℝ)..1, deriv Γ.path t •
        Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - algebraMap ℂ (Operator H) a) := by
  have hint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (fun t => deriv Γ.path t • homotopyResolvent A a s (Γ.path t))
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hc := (continuousOn_homotopyResolvent_path A Γ ha).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using!
      Γ.smooth.continuous_deriv_one.continuousOn.smul hc
  have he : (∫ t in (0 : ℝ)..1, deriv Γ.path t • homotopyResolvent A a 1 (Γ.path t)) =
      ∫ t in (0 : ℝ)..1, deriv Γ.path t • homotopyResolvent A a 0 (Γ.path t) := by
    apply sub_eq_zero.mp
    rw [← intervalIntegral.integral_sub (hint 1 ⟨zero_le_one, le_rfl⟩) (hint 0 ⟨le_rfl, zero_le_one⟩)]
    convert integral_integral_homotopyKernel A Γ ha using 1
    apply intervalIntegral.integral_congr
    intro t ht
    exact (integral_homotopyKernel_left A Γ ha (by simpa using ht)).symm
  simpa only [homotopyResolvent, operatorHomotopy_one, operatorHomotopy_zero] using he

theorem ring_inverse_algebraMap (z : ℂ) :
    Ring.inverse (algebraMap ℂ (Operator H) z) = z⁻¹ • (1 : Operator H) := by
  by_cases hz : z = 0
  · simp [hz]
  have hu : IsUnit (algebraMap ℂ (Operator H) z) :=
    (isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ (Operator H))
  have he := (Ring.inverse_mul_eq_iff_eq_mul (algebraMap ℂ (Operator H) z)
    1 (z⁻¹ • (1 : Operator H)) hu).mpr (by
      rw [← Algebra.algebraMap_eq_smul_one, ← map_mul, mul_inv_cancel₀ hz, map_one])
  simpa only [mul_one] using he

theorem contourEval_one [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) :
    contourEval A Γ.toSmoothContour (fun _ => 1) = 1 := by
  nontriviality H
  obtain ⟨a, ha⟩ := numericalClosure_nonempty A
  unfold contourEval
  simp only [mul_one]
  rw [integral_resolvent_homotopy A Γ ha]
  simp only [← map_sub, ring_inverse_algebraMap, smul_smul,
    intervalIntegral.integral_smul_const, smul_smul]
  change Γ.toSmoothContour.index a • (1 : Operator H) = 1
  rw [Γ.index_inside a ha, one_smul]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic continuity, pole-free rational evaluation, and tensor norm bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isUnit_polynomial_aeval [CompleteSpace H] [Nontrivial H]
    (A : Operator H) (p : Polynomial ℂ)
    (hp : ∀ z ∈ numericalClosure A, p.eval z ≠ 0) :
    IsUnit (Polynomial.aeval A p) := by
  apply spectrum.isUnit_of_zero_notMem ℂ
  rw [spectrum.map_polynomial_aeval A p]
  rintro ⟨z, hz, heq⟩
  exact hp z (spectrum_subset_numericalClosure A hz) heq

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ResolventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent Bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuousOn_contourKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) :
    ContinuousOn (contourKernel A Γ.toSmoothContour) (Icc (0 : ℝ) 1) := by
  apply Γ.smooth.continuous_deriv_one.continuousOn.smul
  exact (continuousOn_resolvent A).comp Γ.smooth.continuous.continuousOn
    (fun t ht => (Γ.avoids t ht).2)

theorem contourEval_eq_kernel (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) :
    contourEval A Γ f = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∫ t in (0 : ℝ)..1, f (Γ.path t) • contourKernel A Γ t := by
  unfold contourEval contourKernel
  simp only [smul_smul, mul_comm (f _)]

theorem intervalIntegrable_contourIntegrand [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace) :
    IntervalIntegrable (fun t => f (Γ.path t) • contourKernel A Γ.toSmoothContour t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hfc : ContinuousOn (fun t => f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    hf.comp Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)
  have hcont := hfc.smul (continuousOn_contourKernel A Γ)
  rw [← uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hcont
  exact hcont.intervalIntegrable

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Polynomials. -/

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SmoothContour.integral_deriv_mul_pow (Γ : SmoothContour) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * (Γ.path t) ^ n) = 0 := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hder (t : ℝ) : HasDerivAt (fun r : ℝ => (n + 1 : ℂ)⁻¹ * Γ.path r ^ (n + 1))
      (deriv Γ.path t * Γ.path t ^ n) t := by
    have h := ((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.pow (n + 1)).const_mul
      (n + 1 : ℂ)⁻¹
    convert! h using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, mul_comm]
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * Γ.path t ^ n)
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Γ.smooth.continuous_deriv_one.mul (Γ.smooth.continuous.pow n)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hi
  simpa only [Γ.closed, sub_self] using he

theorem smul_resolvent_eq [CompleteSpace H] (A : Operator H) {z : ℂ}
    (hz : z ∉ numericalClosure A) :
    z • Ring.inverse (algebraMap ℂ (Operator H) z - A) =
      1 + A * Ring.inverse (algebraMap ℂ (Operator H) z - A) := by
  have hu : IsUnit (algebraMap ℂ (Operator H) z - A) := by
    change z ∈ resolventSet ℂ A
    by_contra he
    exact hz (spectrum_subset_numericalClosure A he)
  have he := Ring.mul_inverse_cancel _ hu
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at he
  exact sub_eq_iff_eq_add.mp he

theorem contourEval_mul_id_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0) :
    contourEval A Γ.toSmoothContour (fun z => z * f z) =
      A * contourEval A Γ.toSmoothContour f := by
  let p := fun t : ℝ => f (Γ.path t) • contourKernel A Γ.toSmoothContour t
  let q := fun t : ℝ => deriv Γ.path t * f (Γ.path t)
  let L := ContinuousLinearMap.mul ℂ (Operator H) A
  have hfc : ContinuousOn (fun t => f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    hf.comp Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)
  have hp : ContinuousOn p (Icc (0 : ℝ) 1) := hfc.smul (continuousOn_contourKernel A Γ)
  have hq : ContinuousOn q (Icc (0 : ℝ) 1) := Γ.smooth.continuous_deriv_one.continuousOn.mul hfc
  have hip : IntervalIntegrable p MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_contourIntegrand A Γ hf
  have hiL : IntervalIntegrable (fun t => L (p t)) MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one, Function.comp_def] using!
      L.continuous.comp_continuousOn hp
  have hiq : IntervalIntegrable (fun t => q t • (1 : Operator H))
      MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using! hq.smul continuousOn_const
  have halg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (Γ.path t * f (Γ.path t)) • contourKernel A Γ.toSmoothContour t =
        q t • (1 : Operator H) + L (p t) := by
    have he := smul_resolvent_eq A (Γ.avoids t ht).2
    have hscalar : Γ.path t * f (Γ.path t) * deriv Γ.path t =
        (deriv Γ.path t * f (Γ.path t)) * Γ.path t := by ring
    dsimp only [contourKernel, p, q, L]
    rw [smul_smul, hscalar, ← smul_smul, he, smul_add]
    congr 1
    simp only [ContinuousLinearMap.mul_apply', mul_smul_comm, smul_smul]
    rw [mul_comm (f (Γ.path t))]
  rw [contourEval_eq_kernel, contourEval_eq_kernel]
  have hi : (∫ t in (0 : ℝ)..1, (Γ.path t * f (Γ.path t)) • contourKernel A Γ.toSmoothContour t) =
      L (∫ t in (0 : ℝ)..1, p t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, q t • (1 : Operator H) + L (p t) :=
        intervalIntegral.integral_congr (fun t ht => halg t (by simpa using ht))
      _ = (∫ t in (0 : ℝ)..1, q t) • (1 : Operator H) + L (∫ t in (0 : ℝ)..1, p t) := by
        rw [intervalIntegral.integral_add hiq hiL, intervalIntegral.integral_smul_const,
          L.intervalIntegral_comp_comm hip]
      _ = _ := by rw [show (∫ t in (0 : ℝ)..1, q t) = 0 from hzero, zero_smul, zero_add]
  rw [hi]
  exact (map_smul L _ _).symm

theorem contourEval_pow [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (n : ℕ) :
    contourEval A Γ.toSmoothContour (fun z => z ^ n) = A ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using contourEval_one A Γ
  | succ n ih =>
    have he := contourEval_mul_id_of_integral_eq_zero A Γ
      (continuous_pow n).continuousOn (Γ.toSmoothContour.integral_deriv_mul_pow n)
    simpa only [pow_succ', ih] using he

theorem contourEval_const_mul (A : Operator H) (Γ : SmoothContour) (c : ℂ) (f : ℂ → ℂ) :
    contourEval A Γ (fun z => c * f z) = c • contourEval A Γ f := by
  simp only [contourEval_eq_kernel, mul_smul, intervalIntegral.integral_smul]
  exact smul_comm _ _ _

theorem contourEval_sum [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) Γ.toSmoothContour.trace) :
    contourEval A Γ.toSmoothContour (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, contourEval A Γ.toSmoothContour (f i) := by
  simp only [contourEval_eq_kernel, Finset.sum_smul]
  rw [intervalIntegral.integral_finsetSum (fun i hi => intervalIntegrable_contourIntegrand A Γ (hf i hi)),
    Finset.smul_sum]

theorem contourEval_polynomial [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (p : Polynomial ℂ) :
    contourEval A Γ.toSmoothContour p.eval = Polynomial.aeval A p := by
  simp_rw [Polynomial.eval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  rw [contourEval_sum A Γ (Finset.range (p.natDegree + 1))
    (fun k z => p.coeff k * z ^ k)
    (fun k _ => (continuous_const.mul (continuous_pow k)).continuousOn)]
  apply Finset.sum_congr rfl
  intro k _
  rw [contourEval_const_mul, contourEval_pow]

theorem contourEval_congr (A : Operator H) (Γ : SmoothContour) {f g : ℂ → ℂ}
    (hfg : EqOn f g Γ.trace) : contourEval A Γ f = contourEval A Γ g := by
  unfold contourEval
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hfg (show Γ.path t ∈ Γ.trace from
    mem_image_of_mem _ (by simpa using ht))]

theorem SmoothContour.integral_deriv_div_eq_zero (Γ : SmoothContour) {a : ℂ}
    (ha : Γ.index a = 0) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - a)) = 0 := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact (mul_eq_zero.mp ha).resolve_left hc

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalContours
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Contours. -/

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SmoothContour.integral_deriv_mul_inv_pow_succ_succ (Γ : SmoothContour)
    {a : ℂ} (ha : a ∉ Γ.trace) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 2)) = 0 := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hnz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    exact ha ((sub_eq_zero.mp he) ▸ mem_image_of_mem Γ.path ht)
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r : ℝ => -(n + 1 : ℂ)⁻¹ * ((Γ.path r - a)⁻¹) ^ (n + 1))
        (deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 2)) t := by
    have h := ((((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.sub_const a).inv
      (hnz t ht)).pow (n + 1)).const_mul (-(n + 1 : ℂ)⁻¹)
    convert! h using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    simp only [Pi.inv_apply, div_eq_mul_inv, ← inv_pow]
    have hscalar : -(n + 1 : ℂ)⁻¹ * ((n + 1) * (Γ.path t - a)⁻¹ ^ n *
        (-deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ 2)) =
        ((n + 1 : ℂ)⁻¹ * (n + 1)) * deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 2) := by
      rw [pow_add]
      ring
    rw [hscalar, inv_mul_cancel₀ hn, one_mul]
  have hc : ContinuousOn (fun t => (Γ.path t - a)⁻¹) (Icc (0 : ℝ) 1) :=
    (Γ.smooth.continuous.sub continuous_const).continuousOn.inv₀ hnz
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 2))
      MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using!
      Γ.smooth.continuous_deriv_one.continuousOn.mul (hc.pow (n + 2))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => -(n + 1 : ℂ)⁻¹ * ((Γ.path t - a)⁻¹) ^ (n + 1))
    (fun t ht => hder t (by simpa using ht)) hi
  simpa only [Γ.closed, sub_self] using he

theorem SmoothContour.integral_deriv_mul_inv_pow (Γ : SmoothContour) {a : ℂ}
    (ha : a ∉ Γ.trace) (hind : Γ.index a = 0) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 1)) = 0 := by
  cases n with
  | zero => simpa only [zero_add, pow_one, div_eq_mul_inv] using
      Γ.integral_deriv_div_eq_zero hind
  | succ n => exact Γ.integral_deriv_mul_inv_pow_succ_succ ha n

theorem SmoothContour.integral_deriv_mul_polynomial (Γ : SmoothContour) (p : Polynomial ℂ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * p.eval (Γ.path t)) = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · have he (k : ℕ) : (fun t => deriv Γ.path t * (p.coeff k * Γ.path t ^ k)) =
        fun t => p.coeff k * (deriv Γ.path t * Γ.path t ^ k) := by ext t; ring
    simp_rw [he, intervalIntegral.integral_const_mul, Γ.integral_deriv_mul_pow, mul_zero]
    simp
  · intro k _
    exact (Γ.smooth.continuous_deriv_one.mul
      (continuous_const.mul (Γ.smooth.continuous.pow k))).intervalIntegrable _ _

theorem polynomial_quotient_partialFractions (p q : Polynomial ℂ) (hq : q.Monic)
    (S : Set ℂ) (hS : ∀ z ∈ S, q.eval z ≠ 0) :
    ∃ (p₀ : Polynomial ℂ) (c : (a : ℂ) → Fin (q.roots.count a) → ℂ),
      ∀ z ∈ S, p.eval z / q.eval z = p₀.eval z +
        ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a),
          c a j * ((z - a)⁻¹) ^ (j.1 + 1) := by
  classical
  let φ : Polynomial ℂ →+* (S → ℂ) :=
    RingHom.pi (fun z : S => Polynomial.evalRingHom (z : ℂ))
  let : Algebra (Polynomial ℂ) (S → ℂ) := φ.toAlgebra
  let gi : ℂ → S → ℂ := fun a z => ((z : ℂ) - a)⁻¹
  have hmap (p : Polynomial ℂ) (z : S) :
      algebraMap (Polynomial ℂ) (S → ℂ) p z = p.eval (z : ℂ) := rfl
  have hgi (a : ℂ) (ha : a ∈ q.roots.toFinset) :
      gi a * algebraMap (Polynomial ℂ) (S → ℂ) (Polynomial.X - Polynomial.C a) = 1 := by
    ext z
    change ((z : ℂ) - a)⁻¹ * ((Polynomial.X - Polynomial.C a).eval (z : ℂ)) = 1
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply inv_mul_cancel₀
    intro he
    exact hS z z.property ((sub_eq_zero.mp he) ▸
      ((Polynomial.mem_roots hq.ne_zero).mp (Multiset.mem_toFinset.mp ha)))
  obtain ⟨p₀, r, hr, he⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := S → ℂ) (s := q.roots.toFinset) p
    (g := fun a => Polynomial.X - Polynomial.C a)
    (fun a _ => Polynomial.monic_X_sub_C a)
    (fun _ _ _ _ hne => Polynomial.pairwise_coprime_X_sub_C Function.injective_id hne)
    (fun a => q.roots.count a) hgi
  have hconst (a : ℂ) (ha : a ∈ q.roots.toFinset) (j : Fin (q.roots.count a)) :
      r a j = Polynomial.C ((r a j).coeff 0) := by
    apply Polynomial.degree_le_zero_iff.mp
    have h := hr a ha j
    rw [Polynomial.degree_X_sub_C] at h
    exact Order.le_of_lt_succ h
  refine ⟨p₀, fun a j => (r a j).coeff 0, fun z hz => ?_⟩
  have hden : q = ∏ a ∈ q.roots.toFinset, (Polynomial.X - Polynomial.C a) ^ q.roots.count a := by
    exact ((IsAlgClosed.splits q).eq_prod_roots_of_monic hq).trans
      (Finset.prod_multiset_map_count _ _)
  have hez := congrFun he (⟨z, hz⟩ : S)
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply,
    Pi.add_apply, Finset.sum_apply, hmap, gi] at hez
  have hnume : ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a),
        (r a j).eval z * ((z - a)⁻¹) ^ (j.1 + 1) =
      ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a),
        (r a j).coeff 0 * ((z - a)⁻¹) ^ (j.1 + 1) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro j _
    rw [hconst a ha j, Polynomial.eval_C, Polynomial.coeff_C_zero]
  rw [← hnume, ← hez]
  conv_lhs => rw [hden]
  simp only [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, div_eq_mul_inv, Finset.prod_inv_distrib, inv_pow]

theorem SmoothContour.integral_deriv_mul_quotient (Γ : SmoothContour)
    (p q : Polynomial ℂ) (hq : q.Monic)
    (hnz : ∀ z ∈ Γ.trace, q.eval z ≠ 0)
    (hind : ∀ a ∈ q.roots, Γ.index a = 0) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * (p.eval (Γ.path t) / q.eval (Γ.path t))) = 0 := by
  classical
  obtain ⟨p₀, c, he⟩ := polynomial_quotient_partialFractions p q hq Γ.trace hnz
  have ha (a : ℂ) (ha : a ∈ q.roots.toFinset) : a ∉ Γ.trace := by
    intro he
    exact hnz a he ((Polynomial.mem_roots hq.ne_zero).mp (Multiset.mem_toFinset.mp ha))
  have hc (a : ℂ) (ha' : a ∈ q.roots.toFinset) :
      ContinuousOn (fun t : ℝ => (Γ.path t - a)⁻¹) (Icc (0 : ℝ) 1) := by
    apply (Γ.smooth.continuous.sub continuous_const).continuousOn.inv₀
    intro t ht he
    exact ha a ha' ⟨t, ht, sub_eq_zero.mp he⟩
  have hi (a : ℂ) (ha' : a ∈ q.roots.toFinset) (j : Fin (q.roots.count a)) :
      IntervalIntegrable (fun t : ℝ => deriv Γ.path t *
        (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1))) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using!
      Γ.smooth.continuous_deriv_one.continuousOn.mul (continuousOn_const.mul ((hc a ha').pow _))
  have hiinner (a : ℂ) (ha' : a ∈ q.roots.toFinset) :
      IntervalIntegrable (fun t : ℝ => ∑ j : Fin (q.roots.count a), deriv Γ.path t *
        (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1))) MeasureTheory.volume 0 1 := by
    exact IntervalIntegrable.congr (fun t _ => Finset.sum_apply t _ _)
      (IntervalIntegrable.sum Finset.univ (fun j _ => hi a ha' j))
  have hisum : IntervalIntegrable (fun t : ℝ =>
      ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a), deriv Γ.path t *
        (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1))) MeasureTheory.volume 0 1 := by
    exact IntervalIntegrable.congr (fun t _ => Finset.sum_apply t _ _)
      (IntervalIntegrable.sum q.roots.toFinset hiinner)
  have hip : IntervalIntegrable (fun t => deriv Γ.path t * p₀.eval (Γ.path t))
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Γ.smooth.continuous_deriv_one.mul (p₀.continuous.comp Γ.smooth.continuous)).intervalIntegrable 0 1
  calc
    _ = ∫ t in (0 : ℝ)..1, deriv Γ.path t * p₀.eval (Γ.path t) +
        ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a), deriv Γ.path t *
          (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [he (Γ.path t) (mem_image_of_mem _ (by simpa using ht))]
      simp only [mul_add, Finset.mul_sum]
    _ = 0 := by
      rw [intervalIntegral.integral_add hip hisum, Γ.integral_deriv_mul_polynomial, zero_add,
        intervalIntegral.integral_finsetSum hiinner]
      apply Finset.sum_eq_zero
      intro a ha'
      rw [intervalIntegral.integral_finsetSum (fun j _ => hi a ha' j)]
      apply Finset.sum_eq_zero
      intro j _
      have heq : (fun t : ℝ => deriv Γ.path t * (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1))) =
          fun t => c a j * (deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (j.1 + 1)) := by
        ext t
        ring
      rw [heq, intervalIntegral.integral_const_mul,
        Γ.integral_deriv_mul_inv_pow (ha a ha') (hind a (Multiset.mem_toFinset.mp ha')), mul_zero]

theorem contourEval_pow_mul_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : ∀ n : ℕ, (∫ t in (0 : ℝ)..1,
      deriv Γ.path t * (Γ.path t ^ n * f (Γ.path t))) = 0) (n : ℕ) :
    contourEval A Γ.toSmoothContour (fun z => z ^ n * f z) =
      A ^ n * contourEval A Γ.toSmoothContour f := by
  induction n with
  | zero => simp only [pow_zero, one_mul]
  | succ n ih =>
    have he := contourEval_mul_id_of_integral_eq_zero A Γ (f := fun z => z ^ n * f z)
      ((continuous_pow n).continuousOn.mul hf) (hzero n)
    simpa only [← mul_assoc, ← pow_succ', ih] using he

theorem contourEval_polynomial_mul_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : ∀ n : ℕ, (∫ t in (0 : ℝ)..1,
      deriv Γ.path t * (Γ.path t ^ n * f (Γ.path t))) = 0) (p : Polynomial ℂ) :
    contourEval A Γ.toSmoothContour (fun z => p.eval z * f z) =
      Polynomial.aeval A p * contourEval A Γ.toSmoothContour f := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Polynomial.aeval_eq_sum_range]
  rw [contourEval_sum A Γ (Finset.range (p.natDegree + 1))
    (fun k z => (p.coeff k * z ^ k) * f z)
    (fun k _ => (continuousOn_const.mul (continuous_pow k).continuousOn).mul hf)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [mul_assoc]
  rw [contourEval_const_mul, contourEval_pow_mul_of_integral_eq_zero A Γ hf hzero,
    smul_mul_assoc]

theorem CalculusContour.inside_subset {K U : Set ℂ} (Γ : CalculusContour K U) : K ⊆ U := by
  intro z hz
  by_contra he
  exact one_ne_zero ((Γ.index_inside z hz).symm.trans (Γ.index_outside z he))

theorem contourEval_quotient [CompleteSpace H] [Nontrivial H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    (p q : Polynomial ℂ) (hq : q.Monic) (hqu : ∀ z ∈ U, q.eval z ≠ 0) :
    contourEval A Γ.toSmoothContour (fun z => p.eval z / q.eval z) =
      Polynomial.aeval A p * Ring.inverse (Polynomial.aeval A q) := by
  have hqt (z : ℂ) (hz : z ∈ Γ.toSmoothContour.trace) : q.eval z ≠ 0 := by
    obtain ⟨t, ht, rfl⟩ := hz
    exact hqu _ (Γ.avoids t ht).1
  have hind (a : ℂ) (ha : a ∈ q.roots) : Γ.toSmoothContour.index a = 0 := by
    apply Γ.index_outside
    intro hau
    exact hqu a hau ((Polynomial.mem_roots hq.ne_zero).mp ha)
  have hzero (n : ℕ) : (∫ t in (0 : ℝ)..1,
      deriv Γ.path t * (Γ.path t ^ n * (p.eval (Γ.path t) / q.eval (Γ.path t)))) = 0 := by
    have hi := Γ.toSmoothContour.integral_deriv_mul_quotient
      (Polynomial.X ^ n * p) q hq hqt hind
    simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, mul_div_assoc] using hi
  have hf : ContinuousOn (fun z => p.eval z / q.eval z) Γ.toSmoothContour.trace :=
    p.continuous.continuousOn.div q.continuous.continuousOn hqt
  have he := contourEval_polynomial_mul_of_integral_eq_zero A Γ hf hzero q
  have heq : contourEval A Γ.toSmoothContour (fun z => q.eval z * (p.eval z / q.eval z)) =
      Polynomial.aeval A p := by
    calc
      _ = contourEval A Γ.toSmoothContour p.eval := by
        apply contourEval_congr
        intro z hz
        exact mul_div_cancel₀ _ (hqt z hz)
      _ = _ := contourEval_polynomial A Γ p
  have hu : IsUnit (Polynomial.aeval A q) :=
    isUnit_polynomial_aeval A q (fun z hz => hqu z (Γ.inside_subset hz))
  apply hu.mul_left_cancel
  calc
    _ = Polynomial.aeval A p := he.symm.trans heq
    _ = Polynomial.aeval A q * (Polynomial.aeval A p * Ring.inverse (Polynomial.aeval A q)) := by
      rw [← mul_assoc, ((Commute.all q p).map (Polynomial.aeval A)).eq,
        mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]

theorem contourEval_rational [CompleteSpace H] [Nontrivial H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (r : RatFunc ℂ)
    (hr : ∀ z ∈ U, r.denom.eval z ≠ 0) :
    contourEval A Γ.toSmoothContour (fun z => RatFunc.eval (RingHom.id ℂ) z r) =
      rationalEval A r := by
  simpa only [rationalEval, RatFunc.eval, Polynomial.eval₂_id] using
    contourEval_quotient A Γ r.num r.denom (RatFunc.monic_denom r) hr

theorem holomorphicEval_rational [CompleteSpace H] [Nontrivial H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (r : RatFunc ℂ)
    (hr : ∀ z ∈ U, r.denom.eval z ≠ 0) :
    holomorphicEval A U (fun z => RatFunc.eval (RingHom.id ℂ) z r) = rationalEval A r := by
  unfold holomorphicEval
  rw [dite_eq_left (show Nonempty (CalculusContour (numericalClosure A) U) from ⟨Γ⟩)]
  exact contourEval_rational A _ r hr

theorem matrixHolomorphicEval_matrixRationalFunction_oai [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m : ℕ} (R : RationalMatrix m) (hR : PolesOutside U R) :
    matrixHolomorphicEval A U (matrixRationalFunction R) = matrixRationalEval A R := by
  unfold matrixHolomorphicEval matrixRationalEval matrixRationalFunction
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [holomorphicEval_rational A Γ (R i j) (hR i j)]

end CrouzeixHilbert

end

end OAI
end

theorem solution.{u} : type_of% @OAI.CrouzeixHilbert.matrixHolomorphicEval_matrixRationalFunction_oai.{u} := @OAI.CrouzeixHilbert.matrixHolomorphicEval_matrixRationalFunction_oai.{u}

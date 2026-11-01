-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:53:27.526769+00:00
-- url     : https://prove2.me/submissions/f8d01384-31cc-4451-9d12-d5ccc7ffa9c4

import Mathlib
import Definitions.Def_OAIQ075A018
import Definitions.Def_OAIQ075A033

section
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `IsSelfAdjoint.norm_le_max_of_le_of_le`: a selfadjoint element squeezed between `a` and `b`
has norm at most `max ‖a‖ ‖b‖` (Kadison similarity, oaiq-075). -/
theorem _root_.IsSelfAdjoint.norm_le_max_of_le_of_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b x : A} (hlo : a ≤ x) (hhi : x ≤ b) (hx : IsSelfAdjoint x) :
    ‖x‖ ≤ max ‖a‖ ‖b‖ := by
  by_cases! nontriv : Nontrivial A
  swap
  · have : x = 0 := Subsingleton.elim _ _
    simp [this]
  have hb : IsSelfAdjoint b := by
    have h1 : IsSelfAdjoint (b - x) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hhi)
    simpa using h1.add hx
  have ha : IsSelfAdjoint a := by
    have h1 : IsSelfAdjoint (x - a) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hlo)
    simpa using hx.sub h1
  have hbx : x ≤ algebraMap ℝ A ‖b‖ := hhi.trans hb.le_algebraMap_norm_self
  have hax : -(algebraMap ℝ A ‖a‖) ≤ x := ha.neg_algebraMap_norm_le_self.trans hlo
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hx with h | h
  · exact ((le_algebraMap_iff_spectrum_le hx).mp hbx _ h).trans (le_max_right _ _)
  · have hax' : algebraMap ℝ A (-‖a‖) ≤ x := by simpa using hax
    have := (algebraMap_le_cfc_iff (R := ℝ) id (-‖a‖) x).mp (by rwa [cfc_id ℝ x hx]) _ h
    simp only [id] at this
    exact (by linarith : ‖x‖ ≤ ‖a‖).trans (le_max_left _ _)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ArcFourier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered arc, its exact second moment, and its nonzero Fourier
coefficients, computed using normalized angular Lebesgue integration. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Set

private theorem intervalIntegrable_indicator_of
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} {s : Set ℝ}
    (hf : IntervalIntegrable f volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private theorem integral_indicator_subinterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) :
    (∫ x in a..b, (Ioc c d).indicator f x) = ∫ x in c..d, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset, ← intervalIntegral.integral_of_le hcd]
  exact Ioc_subset_Ioc hac hdb

theorem centeredArc_integral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (∫ x in -Real.pi..Real.pi, centeredArc θ x) = 0 := by
  simp only [centeredArc]
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_indicator_of intervalIntegrable_const measurableSet_Ioc)
    intervalIntegrable_const,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- Nonzero frequency integration over a symmetric arc. -/
theorem integral_arc_exponential (θ r : ℝ) (hr : r ≠ 0) :
    (∫ x in -θ..θ, Complex.exp ((r * x : ℝ) * Complex.I)) =
      (2 * Real.sin (r * θ) / r : ℝ) := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Complex.exp (x * Complex.I)) (a := -θ) (b := θ) hr
  rw [mul_neg, integral_exp_mul_I_eq_sin] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_inv, Complex.real_smul, div_eq_mul_inv, mul_comm] using h

@[simp] theorem arcFourierIntegral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    arcFourierIntegral θ 0 = 0 := by
  simp only [arcFourierIntegral, Int.cast_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, centeredArc_integral_zero hθ hπ]
  simp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralPolynomialMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_angularCharacter _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar and reflection-coset moments determine all polynomial moments
of the real part of a dihedral rotation. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

section Algebra
variable {A : Type*} [CStarAlgebra A]

theorem realPart_mul_rotation (w : Aˣ) (hw : star (w : A) = (↑w⁻¹ : A)) (l : ℤ) :
    (realPart (w : A) : A) * (↑(w ^ l) : A) =
      (1 / 2 : ℝ) • ((↑(w ^ (l + 1)) : A) + (↑(w ^ (l - 1)) : A)) := by
  have hplus : (w : A) * (↑(w ^ l) : A) = (↑(w ^ (l + 1)) : A) := by
    have h : w * w ^ l = w ^ (l + 1) := by
      simpa only [zpow_one, add_comm] using (zpow_add w 1 l).symm
    exact congrArg (fun a : Aˣ => (a : A)) h
  have hminus : (↑w⁻¹ : A) * (↑(w ^ l) : A) = (↑(w ^ (l - 1)) : A) := by
    rw [← Units.val_mul, ← zpow_neg_one, ← zpow_add]
    congr 2
    omega
  rw [realPart_apply_coe, smul_mul_assoc, add_mul, hw, hplus, hminus]
  simp only [one_div]

theorem realPart_pow_mul_rotation (w : Aˣ) (hw : star (w : A) = (↑w⁻¹ : A))
    (n : ℕ) (l : ℤ) :
    (realPart (w : A) : A) ^ (n + 1) * (↑(w ^ l) : A) =
      (1 / 2 : ℝ) •
        ((realPart (w : A) : A) ^ n * (↑(w ^ (l + 1)) : A) +
          (realPart (w : A) : A) ^ n * (↑(w ^ (l - 1)) : A)) := by
  rw [pow_succ, mul_assoc, realPart_mul_rotation w hw l, mul_smul_comm, mul_add]

end Algebra

theorem angularCharacter_continuous (l : ℤ) : Continuous (angularCharacter l) := by
  unfold angularCharacter
  fun_prop

theorem cosine_mul_angularCharacter (l : ℤ) (x : ℝ) :
    (Real.cos x : ℂ) * angularCharacter l x =
      (1 / 2 : ℂ) * (angularCharacter (l + 1) x + angularCharacter (l - 1) x) := by
  have hp : angularCharacter (l + 1) x =
      angularCharacter l x * Complex.exp ((x : ℂ) * Complex.I) := by
    rw [angularCharacter, angularCharacter, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : angularCharacter (l - 1) x =
      angularCharacter l x * Complex.exp (-(x : ℂ) * Complex.I) := by
    rw [angularCharacter, angularCharacter, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp, hm, ← mul_add, ← Complex.two_cos, ← Complex.ofReal_cos]
  ring

theorem angularPowerMoment_zero (l : ℤ) :
    angularPowerMoment 0 l = if l = 0 then 1 else 0 := by
  by_cases hl : l = 0
  · subst l
    simp [angularPowerMoment, angularCharacter]
    field_simp
    ring
  · simp only [angularPowerMoment, pow_zero, one_mul, angularCharacter]
    rw [integral_arc_exponential Real.pi l (by exact_mod_cast hl), Real.sin_int_mul_pi]
    simp [hl]

theorem angularPowerMoment_succ (n : ℕ) (l : ℤ) :
    angularPowerMoment (n + 1) l =
      (1 / 2 : ℝ) • (angularPowerMoment n (l + 1) + angularPowerMoment n (l - 1)) := by
  have hi (k : ℤ) : IntervalIntegrable
      (fun x : ℝ => (Real.cos x : ℂ) ^ n * angularCharacter k x)
      volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp Real.continuous_cos).pow n |>.mul
      (angularCharacter_continuous k)
  have hpoint : (fun x : ℝ => (Real.cos x : ℂ) ^ (n + 1) * angularCharacter l x) =
      fun x => (1 / 2 : ℂ) * ((Real.cos x : ℂ) ^ n * angularCharacter (l + 1) x +
        (Real.cos x : ℂ) ^ n * angularCharacter (l - 1) x) := by
    funext x
    rw [pow_succ, mul_assoc, cosine_mul_angularCharacter]
    ring
  rw [angularPowerMoment, hpoint, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi _) (hi _)]
  simp only [angularPowerMoment, Complex.real_smul]
  push_cast
  ring

section Moments
variable {A : Type*} [CStarAlgebra A]

/-- The Haar law supplies precisely the scalar angular moments of the
real part, including every shifted Fourier coefficient. -/
theorem trace_realPart_pow_rotation (τ : A →ₗ[ℂ] ℂ) (w : Aˣ)
    (hw : star (w : A) = (↑w⁻¹ : A))
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : A) = if l = 0 then 1 else 0)
    (n : ℕ) (l : ℤ) :
    τ ((realPart (w : A) : A) ^ n * (↑(w ^ l) : A)) = angularPowerMoment n l := by
  induction n generalizing l with
  | zero => simpa only [pow_zero, one_mul, angularPowerMoment_zero] using hhaar l
  | succ n ih =>
    rw [realPart_pow_mul_rotation w hw n l, τ.map_smul_of_tower,
      map_add, ih, ih, angularPowerMoment_succ]

/-- Vanishing on the entire reflection coset propagates to every polynomial
in the real part. -/
theorem trace_realPart_pow_rotation_reflection (τ : A →ₗ[ℂ] ℂ) (w : Aˣ) (d : A)
    (hw : star (w : A) = (↑w⁻¹ : A))
    (hcoset : ∀ l : ℤ, τ ((↑(w ^ l) : A) * d) = 0) (n : ℕ) (l : ℤ) :
    τ (((realPart (w : A) : A) ^ n * (↑(w ^ l) : A)) * d) = 0 := by
  induction n generalizing l with
  | zero => simpa only [pow_zero, one_mul] using hcoset l
  | succ n ih =>
    rw [realPart_pow_mul_rotation w hw n l, smul_mul_assoc, add_mul,
      τ.map_smul_of_tower, map_add, ih, ih, add_zero, smul_zero]

theorem trace_realPart_polynomial_rotation (τ : A →ₗ[ℂ] ℂ) (w : Aˣ)
    (hw : star (w : A) = (↑w⁻¹ : A))
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : A) = if l = 0 then 1 else 0)
    (p : Polynomial ℝ) (l : ℤ) :
    τ (Polynomial.aeval (realPart (w : A) : A) p * (↑(w ^ l) : A)) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ x in -Real.pi..Real.pi,
        ((p.eval (Real.cos x) : ℝ) : ℂ) * angularCharacter l x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hi (r : Polynomial ℝ) : IntervalIntegrable
        (fun x : ℝ => ((r.eval (Real.cos x) : ℝ) : ℂ) * angularCharacter l x)
        volume (-Real.pi) Real.pi := by
      apply Continuous.intervalIntegrable
      exact (Complex.continuous_ofReal.comp (r.continuous.comp Real.continuous_cos)).mul
        (angularCharacter_continuous l)
    simp only [map_add, add_mul, Polynomial.eval_add, Complex.ofReal_add]
    rw [hp, hq, intervalIntegral.integral_add (hi p) (hi q), smul_add]
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_mul_assoc, τ.map_smul_of_tower,
      trace_realPart_pow_rotation τ w hw hhaar]
    simp only [Polynomial.eval_monomial, Complex.ofReal_mul, Complex.ofReal_pow,
      mul_assoc, angularPowerMoment]
    rw [intervalIntegral.integral_const_mul]
    simp only [Complex.real_smul]
    ring

theorem trace_realPart_polynomial_rotation_reflection (τ : A →ₗ[ℂ] ℂ)
    (w : Aˣ) (d : A) (hw : star (w : A) = (↑w⁻¹ : A))
    (hcoset : ∀ l : ℤ, τ ((↑(w ^ l) : A) * d) = 0)
    (p : Polynomial ℝ) (l : ℤ) :
    τ ((Polynomial.aeval (realPart (w : A) : A) p * (↑(w ^ l) : A)) * d) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, hp, hq, add_zero]
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_mul_assoc, smul_mul_assoc, τ.map_smul_of_tower,
      trace_realPart_pow_rotation_reflection τ w d hw hcoset, smul_zero]

end Moments
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_AngularIntegralBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm control for the normalized angular Fourier integrals used in
the spectral-arc construction. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

theorem angularIntegral_const (c : ℂ) (l : ℤ) :
    angularIntegral (fun _ => c) l = c * angularPowerMoment 0 l := by
  simp only [angularIntegral, angularPowerMoment, pow_zero, one_mul,
    intervalIntegral.integral_const_mul, Complex.real_smul]
  ring

theorem angularIntegral_sub (f g : ℝ → ℂ) (l : ℤ)
    (hf : IntervalIntegrable (fun x => f x * angularCharacter l x)
      volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable (fun x => g x * angularCharacter l x)
      volume (-Real.pi) Real.pi) :
    angularIntegral (fun x => f x - g x) l = angularIntegral f l - angularIntegral g l := by
  simp only [angularIntegral, sub_mul]
  rw [intervalIntegral.integral_sub hf hg, smul_sub]

/-- Normalized angular integration is contractive for the uniform bound. -/
theorem angularIntegral_norm_le (f : ℝ → ℂ) (l : ℤ) {C : ℝ}
    (_hC : 0 ≤ C) (hf : ∀ x ∈ Set.Ioc (-Real.pi) Real.pi, ‖f x‖ ≤ C) :
    ‖angularIntegral f l‖ ≤ C := by
  have hb : ‖∫ x in -Real.pi..Real.pi, f x * angularCharacter l x‖ ≤
      C * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi) (C := C) (f := fun x => f x * angularCharacter l x) ?_
    · simpa only [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using h
    · intro x hx
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hx
      simpa only [norm_mul, norm_angularCharacter, mul_one] using hf x hx
  rw [angularIntegral, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi))]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

theorem angularIntegral_continuous_sub_bound (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (l : ℤ) {C : ℝ}
    (hC : 0 ≤ C) (hfg : ∀ x ∈ Set.Ioc (-Real.pi) Real.pi, ‖f x - g x‖ ≤ C) :
    ‖angularIntegral f l - angularIntegral g l‖ ≤ C := by
  rw [← angularIntegral_sub f g l
    ((hf.mul (angularCharacter_continuous l)).intervalIntegrable _ _)
    ((hg.mul (angularCharacter_continuous l)).intervalIntegrable _ _)]
  exact angularIntegral_norm_le _ l hC hfg

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralContinuousMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial approximation transfers the dihedral polynomial
moments to the continuous functional calculus of the real rotation. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A : Type*} [CStarAlgebra A]

/-- Polynomial approximation on the exact interval used for a selfadjoint
contraction, in the source algebra norm. -/
theorem exists_polynomial_near_cfc (a : A) (ha : IsSelfAdjoint a) (han : ‖a‖ ≤ 1)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-1) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ‖cfc f a - Polynomial.aeval a p‖ ≤ ε ∧
      ∀ x ∈ Set.Icc (-1) 1, |p.eval x - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f hf ε hε
  refine ⟨p, ?_, hp⟩
  by_cases hA : Subsingleton A
  · have hz : cfc f a - Polynomial.aeval a p = 0 := hA.elim _ _
    rw [hz, norm_zero]
    exact hε.le
  let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  have hs : spectrum ℝ a ⊆ Set.Icc (-1) 1 := by
    intro x hx
    exact abs_le.mp ((spectrum.norm_le_norm_of_mem hx).trans han)
  rw [← cfc_polynomial p a ha,
    ← cfc_sub f p.eval a (hf.mono hs) p.continuous.continuousOn]
  apply norm_cfc_le hε.le
  intro x hx
  simpa only [Real.norm_eq_abs, abs_sub_comm] using (hp x (hs hx)).le

/-- The zero reflection-coset functional extends from polynomials to every
continuous function of the real part. -/
theorem trace_cfc_realPart_rotation_reflection (τ : A →L[ℂ] ℂ) (w : Aˣ) (d : A)
    (hw : star (w : A) = (↑w⁻¹ : A)) (hwn : ‖(w : A)‖ ≤ 1)
    (hcoset : ∀ l : ℤ, τ ((↑(w ^ l) : A) * d) = 0)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-1) 1)) (l : ℤ) :
    τ ((cfc f (realPart (w : A) : A) * (↑(w ^ l) : A)) * d) = 0 := by
  let a : A := realPart (w : A)
  let b : A := (↑(w ^ l) : A) * d
  have han : ‖a‖ ≤ 1 := (realPart.norm_le (w : A)).trans hwn
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let M : ℝ := ‖τ‖ * ‖b‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨p, hp, _⟩ := exists_polynomial_near_cfc a (realPart (w : A)).property han f hf
    (div_pos hε hM)
  have hz : τ (Polynomial.aeval a p * b) = 0 := by
    simpa only [a, b, ← mul_assoc, ContinuousLinearMap.coe_coe] using
      trace_realPart_polynomial_rotation_reflection τ.toLinearMap w d hw hcoset p l
  have heq : τ ((cfc f a - Polynomial.aeval a p) * b) = τ (cfc f a * b) := by
    rw [sub_mul, map_sub, hz, sub_zero]
  rw [mul_assoc]
  change ‖τ (cfc f a * b)‖ ≤ 0 + ε
  rw [← heq, zero_add]
  calc
    _ ≤ ‖τ‖ * ‖(cfc f a - Polynomial.aeval a p) * b‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * (‖cfc f a - Polynomial.aeval a p‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖τ‖ * ((ε / M) * ‖b‖) := by gcongr
    _ ≤ ε := by
      have hle : ‖τ‖ * ‖b‖ ≤ M := by dsimp [M]; linarith
      calc
        _ = (ε / M) * (‖τ‖ * ‖b‖) := by ring
        _ ≤ (ε / M) * M := mul_le_mul_of_nonneg_left hle (div_pos hε hM).le
        _ = ε := div_mul_cancel₀ _ hM.ne'

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralHaarFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar law determines the continuous functional calculus of the real
part of the rotation, tested against every rotation power. -/

noncomputable section
namespace KadisonSimilarity

variable {A : Type*} [CStarAlgebra A]

theorem trace_cfc_realPart_rotation (τ : A →L[ℂ] ℂ) (w : Aˣ)
    (hw : star (w : A) = (↑w⁻¹ : A)) (hwn : ‖(w : A)‖ ≤ 1)
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : A) = if l = 0 then 1 else 0)
    (f : ℝ → ℝ) (hf : Continuous f) (l : ℤ) :
    τ (cfc f (realPart (w : A) : A) * (↑(w ^ l) : A)) =
      angularIntegral (fun x => (f (Real.cos x) : ℂ)) l := by
  let a : A := realPart (w : A)
  let b : A := (↑(w ^ l) : A)
  have han : ‖a‖ ≤ 1 := (realPart.norm_le (w : A)).trans hwn
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let K : ℝ := ‖τ‖ * ‖b‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ := ε / K
  have hδ : 0 < δ := div_pos hε hK
  obtain ⟨p, hp, hpOn⟩ := exists_polynomial_near_cfc a
    (realPart (w : A)).property han f hf.continuousOn hδ
  have hpoly : τ (Polynomial.aeval a p * b) =
      angularIntegral (fun x => ((p.eval (Real.cos x) : ℝ) : ℂ)) l := by
    simpa only [a, b, angularIntegral, ContinuousLinearMap.coe_coe] using
      trace_realPart_polynomial_rotation τ.toLinearMap w hw hhaar p l
  have heq : τ (cfc f a * b) - τ (Polynomial.aeval a p * b) =
      τ ((cfc f a - Polynomial.aeval a p) * b) := by rw [sub_mul, map_sub]
  have hop : ‖τ (cfc f a * b) - τ (Polynomial.aeval a p * b)‖ ≤
      ‖τ‖ * (δ * ‖b‖) := by
    rw [heq]
    calc
      _ ≤ ‖τ‖ * ‖(cfc f a - Polynomial.aeval a p) * b‖ := τ.le_opNorm _
      _ ≤ ‖τ‖ * (‖cfc f a - Polynomial.aeval a p‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖τ‖ * (δ * ‖b‖) := by gcongr
  have hint : ‖angularIntegral (fun x => ((p.eval (Real.cos x) : ℝ) : ℂ)) l -
      angularIntegral (fun x => (f (Real.cos x) : ℂ)) l‖ ≤ δ := by
    apply angularIntegral_continuous_sub_bound _ _
      (Complex.continuous_ofReal.comp (p.continuous.comp Real.continuous_cos))
      (Complex.continuous_ofReal.comp (hf.comp Real.continuous_cos)) l hδ.le
    intro x _
    have h := (hpOn (Real.cos x) ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩).le
    simpa only [Function.comp_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  change ‖τ (cfc f a * b) - angularIntegral (fun x => (f (Real.cos x) : ℂ)) l‖ ≤ 0 + ε
  rw [zero_add]
  calc
    _ = ‖(τ (cfc f a * b) - τ (Polynomial.aeval a p * b)) +
        (angularIntegral (fun x => ((p.eval (Real.cos x) : ℝ) : ℂ)) l -
          angularIntegral (fun x => (f (Real.cos x) : ℂ)) l)‖ := by rw [hpoly]; congr 1; ring
    _ ≤ ‖τ (cfc f a * b) - τ (Polynomial.aeval a p * b)‖ +
        ‖angularIntegral (fun x => ((p.eval (Real.cos x) : ℝ) : ℂ)) l -
          angularIntegral (fun x => (f (Real.cos x) : ℂ)) l‖ := norm_add_le _ _
    _ ≤ ‖τ‖ * (δ * ‖b‖) + δ := add_le_add hop hint
    _ = δ * K := by dsimp [K]; ring
    _ = ε := div_mul_cancel₀ ε hK.ne'

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeSupport_isStarProjection (B : H →L[ℂ] H) :
    IsStarProjection (rangeSupport B) :=
  ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩

theorem rangeSupport_mul (B : H →L[ℂ] H) : rangeSupport B * B = B := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

theorem upperSpectralCut_isStarProjection (A : H →L[ℂ] H) (t : ℝ) :
    IsStarProjection (upperSpectralCut A t) := rangeSupport_isStarProjection _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RegularizedPolarFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractive approximate polar factors inside the original C-star algebra.
These avoid any bidual extension in the row-bound argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positiveShiftReciprocal_continuous (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ => (t + ε)⁻¹) (spectrum ℝ h) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε)

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_selfAdjoint (h : A) (ε : ℝ) :
    IsSelfAdjoint (positiveShiftReciprocal h ε) := cfc_predicate _ h

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_commute (h : A) (ε : ℝ) :
    Commute (positiveShiftReciprocal h ε) h := (Commute.refl h).cfc_real _

theorem positiveShiftReciprocal_inverse (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    (h + ε • (1 : A)) * positiveShiftReciprocal h ε = 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  have hid : cfc (fun t : ℝ => t + ε) h = h + ε • (1 : A) := by
    rw [cfc_add h (fun t : ℝ => t) (fun _ => ε) continuousOn_id continuousOn_const,
      cfc_id' ℝ h hh.isSelfAdjoint, cfc_const ε h hh.isSelfAdjoint]
    simp only [Algebra.algebraMap_eq_smul_one]
  rw [positiveShiftReciprocal, ← hid, ← cfc_mul _ _ h (by fun_prop) hc]
  calc
    cfc (fun t : ℝ => (t + ε) * (t + ε)⁻¹) h = cfc (fun _ : ℝ => 1) h := by
      apply cfc_congr
      intro t ht
      exact mul_inv_cancel₀ (ne_of_gt
        (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε))
    _ = 1 := cfc_const_one ℝ h hh.isSelfAdjoint

theorem positiveShiftReciprocal_mul_norm_le (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ‖h * positiveShiftReciprocal h ε‖ ≤ 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  change ‖h * cfc (fun t : ℝ => (t + ε)⁻¹) h‖ ≤ 1
  conv_lhs => arg 1; arg 1; rw [← cfc_id' ℝ h hh.isSelfAdjoint]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + ε)⁻¹) h continuousOn_id hc]
  apply norm_cfc_le zero_le_one
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hh ht
  have hp : 0 < t + ε := add_pos_of_nonneg_of_pos ht0 hε
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
  change t / (t + ε) ≤ 1
  exact (div_le_one hp).mpr (by linarith)

/-- The regularized polar factor is contractive without leaving the algebra. -/
theorem norm_positiveShiftReciprocal_mul_le (x h : A) (hh : 0 ≤ h)
    (hsq : x * star x = h * h) {ε : ℝ} (hε : 0 < ε) :
    ‖positiveShiftReciprocal h ε * x‖ ≤ 1 := by
  let r := positiveShiftReciprocal h ε
  have hr : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hc : r * h = h * r := (positiveShiftReciprocal_commute h ε).eq
  have he : (r * x) * star (r * x) = (h * r) * (h * r) := by
    rw [star_mul, hr]
    calc
      (r * x) * (star x * r) = r * (x * star x) * r := by noncomm_ring
      _ = r * (h * h) * r := by rw [hsq]
      _ = (r * h) * (h * r) := by noncomm_ring
      _ = (h * r) * (h * r) := by rw [hc]
  have hsa : IsSelfAdjoint (h * r) :=
    (hh.isSelfAdjoint.commute_iff (positiveShiftReciprocal_selfAdjoint h ε)).mp
      (positiveShiftReciprocal_commute h ε).symm
  have heq : ‖r * x‖ ^ 2 = ‖h * r‖ ^ 2 := by
    rw [sq, ← CStarRing.norm_self_mul_star, he, hsa.norm_mul_self]
  have hn := positiveShiftReciprocal_mul_norm_le h hh hε
  nlinarith [norm_nonneg (r * x), norm_nonneg (h * r)]

/-- The error in the polar factorization has norm at most the regularizer. -/
theorem regularizedPolar_error (x h : A) (hh : 0 ≤ h)
    (hsq : x * star x = h * h) {ε : ℝ} (hε : 0 < ε) :
    ‖x - h * (positiveShiftReciprocal h ε * x)‖ ≤ ε := by
  let v := positiveShiftReciprocal h ε * x
  have hi := congrArg (fun z : A => z * x) (positiveShiftReciprocal_inverse h hh hε)
  have he : x - h * v = ε • v := by
    change (h + ε • (1 : A)) * positiveShiftReciprocal h ε * x = 1 * x at hi
    simp only [add_mul, smul_mul_assoc, one_mul, mul_assoc] at hi
    change h * v + ε • v = x at hi
    rw [← hi]
    abel
  change ‖x - h * v‖ ≤ ε
  rw [he, norm_smul, Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left
    (norm_positiveShiftReciprocal_mul_le x h hh hsq hε) hε.le).trans_eq (mul_one ε)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralSupportLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive resolvent approximations to the concrete range-support
projection. This gives the strong limit needed for the dihedral arc's
spectral moments, with operator norm bounded by one throughout. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem supportResolvent_norm_le (B : H →L[ℂ] H) (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) : ‖supportResolvent B ε‖ ≤ 1 :=
  positiveShiftReciprocal_mul_norm_le B hB hε

theorem supportResolvent_selfAdjoint (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (ε : ℝ) : IsSelfAdjoint (supportResolvent B ε) := by
  apply (hB.commute_iff (positiveShiftReciprocal_selfAdjoint B ε)).mp
  exact (positiveShiftReciprocal_commute B ε).symm

theorem supportResolvent_mul_support (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (ε : ℝ) : supportResolvent B ε * rangeSupport B = supportResolvent B ε := by
  have h : rangeSupport B * supportResolvent B ε = supportResolvent B ε := by
    rw [supportResolvent, ← mul_assoc, rangeSupport_mul]
  have hs := congrArg star h
  simpa only [star_mul, (rangeSupport_isStarProjection B).isSelfAdjoint.star_eq,
    (supportResolvent_selfAdjoint B hB ε).star_eq] using hs

theorem supportResolvent_range_error (B : H →L[ℂ] H) (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) (y : H) :
    ‖supportResolvent B ε (B y) - B y‖ ≤ ε * ‖y‖ := by
  have he := regularizedPolar_error B B hB
    (by rw [hB.isSelfAdjoint.star_eq]) hε
  have he' : ‖supportResolvent B ε * B - B‖ ≤ ε := by
    rw [norm_sub_rev]
    simpa only [supportResolvent, mul_assoc] using he
  calc
    _ = ‖(supportResolvent B ε * B - B) y‖ := rfl
    _ ≤ ‖supportResolvent B ε * B - B‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖y‖ := mul_le_mul_of_nonneg_right he' (norm_nonneg _)

/-- The positive resolvents converge strongly to the actual range projection. -/
theorem supportResolvent_tendsto (B : H →L[ℂ] H) (hB : 0 ≤ B)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => supportResolvent B (ε n) x) atTop (𝓝 (rangeSupport B x)) := by
  have hequi : Equicontinuous (fun n x => supportResolvent B (ε n) x) :=
    (LipschitzWith.uniformEquicontinuous _ 1 (fun n =>
      ContinuousLinearMap.lipschitzWith_of_opNorm_le (supportResolvent_norm_le B hB (hε n)))).equicontinuous
  have hclosed : IsClosed {y : H |
      Tendsto (fun n => supportResolvent B (ε n) y) atTop (𝓝 y)} :=
    hequi.isClosed_setOfPred_tendsto continuous_id
  have hrange : (B.range : Set H) ⊆ {y : H |
      Tendsto (fun n => supportResolvent B (ε n) y) atTop (𝓝 y)} := by
    rintro _ ⟨y, rfl⟩
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => supportResolvent_range_error B hB (hε n) y)
    simpa only [zero_mul] using hlim.mul_const ‖y‖
  have hx := (closure_minimal hrange hclosed)
    ((operatorRangeClosure B).starProjection_apply_mem x)
  change Tendsto (fun n => supportResolvent B (ε n) (rangeSupport B x)) atTop
    (𝓝 (rangeSupport B x)) at hx
  have heq (n : ℕ) : supportResolvent B (ε n) (rangeSupport B x) =
      supportResolvent B (ε n) x :=
    congrArg (fun T : H →L[ℂ] H => T x) (supportResolvent_mul_support B hB.isSelfAdjoint (ε n))
  simpa only [heq] using hx

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArcResolvents
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous functions approximating the open arc spectral projection. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology
open Filter

theorem spectralCutFunction_continuous (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (spectralCutFunction c ε) := by
  unfold spectralCutFunction
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact ne_of_gt (add_pos_of_nonneg_of_pos (posPart_nonneg _) hε)

theorem spectralCutFunction_nonneg (c t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ spectralCutFunction c ε t :=
  div_nonneg (posPart_nonneg _) (add_pos_of_nonneg_of_pos (posPart_nonneg _) hε).le

theorem spectralCutFunction_le_one (c t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    spectralCutFunction c ε t ≤ 1 := by
  apply (div_le_one (add_pos_of_nonneg_of_pos (posPart_nonneg _) hε)).mpr
  linarith

theorem spectralCutFunction_tendsto (c t : ℝ) (ε : ℕ → ℝ)
    (_hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => spectralCutFunction c (ε n) t) atTop
      (𝓝 (if c < t then 1 else 0)) := by
  by_cases hct : c < t
  · simp only [ite_eq_left hct]
    have ht : 0 < (t - c)⁺ := by rw [posPart_eq_self.mpr (sub_pos.mpr hct).le]; linarith
    have hc : Tendsto (fun _ : ℕ => (t - c)⁺) atTop (𝓝 ((t - c)⁺)) := tendsto_const_nhds
    have h := hc.div (hlim.const_add ((t - c)⁺)) (by simpa only [add_zero] using ht.ne')
    change Tendsto (fun n => (t - c)⁺ / ((t - c)⁺ + ε n)) atTop
      (𝓝 ((t - c)⁺ / ((t - c)⁺ + 0))) at h
    simpa only [spectralCutFunction, Pi.div_apply, add_zero, div_self ht.ne'] using h
  · have ht : (t - c)⁺ = 0 := posPart_eq_zero.mpr (sub_nonpos.mpr (le_of_not_gt hct))
    simpa only [spectralCutFunction, ht, zero_div, ite_eq_right hct] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveShift_cfc (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) (c : ℝ) :
    cfc (fun t : ℝ => (t - c)⁺) a = (a - c • 1)⁺ := by
  have hs : cfc (fun t : ℝ => t - c) a = a - c • 1 := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => c) a continuousOn_id continuousOn_const,
      cfc_id' ℝ a ha, cfc_const c a ha, Algebra.algebraMap_eq_smul_one]
  rw [CFC.posPart_def, cfcₙ_eq_cfc, ← hs]
  exact cfc_comp' (fun t : ℝ => t⁺) (fun t => t - c) a
    (by fun_prop) (by fun_prop) ha

/-- The actual operators in the strong support approximation are evaluations
of the scalar continuous cut functions. -/
theorem supportResolvent_positiveShift_eq_cfc (a : H →L[ℂ] H)
    (ha : IsSelfAdjoint a) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    supportResolvent (a - c • 1)⁺ ε = cfc (spectralCutFunction c ε) a := by
  let B := (a - c • 1)⁺
  have hB : 0 ≤ B := CFC.posPart_nonneg _
  have hres : supportResolvent B ε = cfc (fun t : ℝ => t / (t + ε)) B := by
    rw [supportResolvent, positiveShiftReciprocal]
    conv_lhs => arg 1; rw [← cfc_id' ℝ B hB.isSelfAdjoint]
    rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + ε)⁻¹) B
      continuousOn_id (positiveShiftReciprocal_continuous B hB hε)]
    rfl
  rw [hres]
  change cfc (fun t : ℝ => t / (t + ε)) (a - c • 1)⁺ = _
  rw [← positiveShift_cfc a ha c]
  exact (cfc_comp' (fun t : ℝ => t / (t + ε)) (fun t : ℝ => (t - c)⁺) a
    (by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      obtain ⟨x, _, rfl⟩ := ht
      exact ne_of_gt (add_pos_of_nonneg_of_pos (posPart_nonneg _) hε))
    (by fun_prop) ha).symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_AngularCutLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded convergence of the angular cut functions and the elementary
identification of the limiting open angular arc. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter Set
open scoped Topology

theorem angularIntegral_cut_tendsto (c : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (l : ℤ) :
    Tendsto (fun n => angularIntegral
      (fun x => (spectralCutFunction c (ε n) (Real.cos x) : ℂ)) l) atTop
      (𝓝 (angularIntegral (fun x => if c < Real.cos x then 1 else 0) l)) := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have ht : Tendsto (fun n => ∫ x in -Real.pi..Real.pi,
        (spectralCutFunction c (ε n) (Real.cos x) : ℂ) * angularCharacter l x) atTop
      (𝓝 (∫ x in -Real.pi..Real.pi,
        (if c < Real.cos x then 1 else 0) * angularCharacter l x)) := by
    simp only [intervalIntegral.integral_of_le hπ]
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    · intro n
      exact ((Complex.continuous_ofReal.comp
        ((spectralCutFunction_continuous c (hε n)).comp Real.continuous_cos)).mul
        (angularCharacter_continuous l)).aestronglyMeasurable
    · change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (-Real.pi) Real.pi) volume
      simpa only [uIoc_of_le hπ] using
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
          volume (-Real.pi) Real.pi).1
    · intro n
      filter_upwards [] with x
      rw [norm_mul, norm_angularCharacter, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (spectralCutFunction_nonneg c _ (hε n))]
      exact spectralCutFunction_le_one c _ (hε n)
    · filter_upwards [] with x
      have h := (Complex.continuous_ofReal.tendsto _).comp
        (spectralCutFunction_tendsto c (Real.cos x) ε hε hlim)
      by_cases hc : c < Real.cos x <;>
        simpa only [Function.comp_apply, hc, ite_true, ite_false,
          Complex.ofReal_one, Complex.ofReal_zero] using h.mul_const (angularCharacter l x)
  exact ht.const_smul ((2 * Real.pi)⁻¹ : ℝ)

theorem cos_gt_iff_mem_open_arc {θ x : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hx : x ∈ Icc (-Real.pi) Real.pi) :
    Real.cos θ < Real.cos x ↔ x ∈ Ioo (-θ) θ := by
  have hxπ : |x| ≤ Real.pi := abs_le.mpr hx
  have h := Real.strictAntiOn_cos.lt_iff_gt ⟨hθ, hθπ⟩ ⟨abs_nonneg x, hxπ⟩
  rw [Real.cos_abs] at h
  simpa only [mem_Ioo, abs_lt] using h

theorem angularIntegral_centered_cut {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (l : ℤ) :
    angularIntegral (fun x => (if Real.cos θ < Real.cos x then 1 else 0) -
      (θ / Real.pi : ℂ)) l = arcFourierIntegral θ l := by
  unfold angularIntegral arcFourierIntegral
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    (volume.restrict (uIoc (-Real.pi) Real.pi)).ae_ne θ] with x hx hne
  rw [uIoc_of_le (by linarith [Real.pi_pos])] at hx
  have hcos := cos_gt_iff_mem_open_arc hθ hθπ (show x ∈ Icc (-Real.pi) Real.pi from ⟨hx.1.le, hx.2⟩)
  have hm : Real.cos θ < Real.cos x ↔ x ∈ Ioc (-θ) θ := by
    rw [hcos]
    exact and_congr_right fun _ => ⟨fun h => h.le, fun h => lt_of_le_of_ne h hne⟩
  by_cases hi : x ∈ Ioc (-θ) θ
  · simp only [hm.mpr hi, ite_true, centeredArc, indicator_of_mem hi, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_div, angularCharacter]
  · simp only [not_congr hm |>.mpr hi, ite_false, centeredArc, indicator_of_notMem hi,
      Complex.ofReal_sub, Complex.ofReal_zero, Complex.ofReal_div, angularCharacter]

theorem angularIntegral_cut_eq {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (l : ℤ) :
    angularIntegral (fun x => if Real.cos θ < Real.cos x then 1 else 0) l =
      arcFourierIntegral θ l + (θ / Real.pi : ℂ) * angularPowerMoment 0 l := by
  let S : Set ℝ := {x | Real.cos θ < Real.cos x}
  have hS : MeasurableSet S := (isOpen_lt continuous_const Real.continuous_cos).measurableSet
  have hc : IntervalIntegrable (angularCharacter l) volume (-Real.pi) Real.pi :=
    (angularCharacter_continuous l).intervalIntegrable _ _
  have hcut : IntervalIntegrable
      (fun x => (if Real.cos θ < Real.cos x then 1 else 0) * angularCharacter l x)
      volume (-Real.pi) Real.pi := by
    have hi : IntervalIntegrable (S.indicator (angularCharacter l)) volume (-Real.pi) Real.pi :=
      ⟨hc.1.indicator hS, hc.2.indicator hS⟩
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    by_cases hx : Real.cos θ < Real.cos x <;> simp [S, indicator, hx]
  have hconst : IntervalIntegrable
      (fun x => (θ / Real.pi : ℂ) * angularCharacter l x) volume (-Real.pi) Real.pi :=
    hc.const_mul _
  have h := angularIntegral_sub (fun x => if Real.cos θ < Real.cos x then 1 else 0)
    (fun _ => (θ / Real.pi : ℂ)) l hcut hconst
  rw [angularIntegral_centered_cut hθ hθπ l, angularIntegral_const] at h
  exact (sub_eq_iff_eq_add).mp h.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeDihedral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar and reflection-coset moments of two free centered symmetries,
derived directly from alternating-centered-word freeness. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

private theorem pairedWord_append_alternating
    (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R)
    {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0) (n : ℕ) :
    AlternatingCenteredWord τ P Q true (pairedWord d s n ++ [d]) := by
  induction n with
  | zero => exact .cons (by simpa using hd) hd0 (.nil false)
  | succ n ih => exact .cons (by simpa using hd) hd0 (.cons (by simpa using hs) hs0 ih)

/-- The odd alternating words, which form the reflection coset, also vanish. -/
theorem ScalarFree.trace_pair_power_mul_first
    {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0)
    (n : ℕ) : τ ((d * s) ^ n * d) = 0 := by
  have ha := pairedWord_append_alternating τ P Q hd hs hd0 hs0 n
  have hnonempty : pairedWord d s n ++ [d] ≠ [] := by simp
  obtain ⟨x, xs, heq⟩ := List.exists_cons_of_ne_nil hnonempty
  rw [heq] at ha
  have ht := hf true x xs ha
  rw [← heq, List.prod_append, pairedWord_prod] at ht
  simpa using ht

/-- Two free centered symmetries have a product whose nonzero integer
moments vanish. -/
theorem free_symmetry_haar_moments
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
    (d s : Rˣ) (hd : (d : R) ∈ P) (hs : (s : R) ∈ Q)
    (hd0 : τ (d : R) = 0) (hs0 : τ (s : R) = 0)
    (hdinv : d⁻¹ = d) (hsinv : s⁻¹ = s) (l : ℤ) :
    τ (↑((d * s) ^ l) : R) = if l = 0 then 1 else 0 := by
  cases l with
  | ofNat n =>
    cases n with
    | zero => simpa using hτ
    | succ n =>
      change τ (↑((d * s) ^ ((n + 1 : ℕ) : ℤ)) : R) =
        if ((n + 1 : ℕ) : ℤ) = 0 then 1 else 0
      rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mul, ite_eq_right (by omega)]
      exact hf.trace_pair_power hd hs hd0 hs0 (Nat.succ_pos n)
  | negSucc n =>
    simp only [Int.negSucc_ne_zero, zpow_negSucc]
    rw [← inv_pow, mul_inv_rev, hdinv, hsinv,
      Units.val_pow_eq_pow_val, Units.val_mul]
    exact hf.symm.trace_pair_power hs hd hs0 hd0 (Nat.succ_pos _)

/-- Every reflection-coset word has zero trace. -/
theorem free_symmetry_coset_moments
    (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
    (d s : Rˣ) (hd : (d : R) ∈ P) (hs : (s : R) ∈ Q)
    (hd0 : τ (d : R) = 0) (hs0 : τ (s : R) = 0)
    (hdinv : d⁻¹ = d) (hsinv : s⁻¹ = s) (l : ℤ) :
    τ ((↑((d * s) ^ l) : R) * (s : R)) = 0 := by
  cases l with
  | ofNat n =>
    cases n with
    | zero => simpa using hs0
    | succ n =>
      have hss : s * s = 1 := by simpa only [hsinv] using inv_mul_cancel s
      have hword : (d * s) ^ (n + 1) * s = (d * s) ^ n * d := by
        rw [pow_succ]
        simp only [mul_assoc, hss, mul_one]
      change τ ((↑((d * s) ^ ((n + 1 : ℕ) : ℤ)) : R) * (s : R)) = 0
      rw [zpow_natCast, ← Units.val_mul, hword, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_mul]
      exact hf.trace_pair_power_mul_first hd hs hd0 hs0 n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, mul_inv_rev, hdinv, hsinv,
      Units.val_pow_eq_pow_val, Units.val_mul]
    exact hf.symm.trace_pair_power_mul_first hs hd hs0 hd0 (n + 1)

omit [Algebra ℂ R] [StarModule ℂ R] in
/-- The product of two selfadjoint involutions is unitary. -/
theorem free_symmetry_product_star (d s : Rˣ)
    (hd : star d = d) (hs : star s = s) (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) :
    star (d * s) = (d * s)⁻¹ := by
  rw [star_mul, hd, hs, mul_inv_rev, hdi, hsi]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralPositiveDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered dihedral corner is generated in L² by the positive
compressed rotation powers. Apply the bounded centered corner map to the
ordinary rotation/reflection word span; no bounded approximation theorem
or corner-freeness hypothesis is needed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry
variable (G : TracialCornerGeometry P H)

/-- For two involutions, the first one reverses their product. -/
theorem free_symmetry_rotation_conjugation (d s : Pˣ)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) : d * (d * s) = (d * s)⁻¹ * d := by
  have hdd : d * d = 1 := by simpa only [hdi] using inv_mul_cancel d
  calc
    d * (d * s) = s := by rw [← mul_assoc, hdd, one_mul]
    _ = (d * s)⁻¹ * d := by
      rw [mul_inv_rev, hdi, hsi, mul_assoc, hdd, mul_one]

/-- The reflection-coset moments used by the centered corner map follow
from the scalar-freeness moments. -/
theorem free_symmetry_first_coset_moments
    (D A : StarSubalgebra ℂ P) (hf : ScalarFree G.trace D A)
    (d s : Pˣ) (hd : (d : P) ∈ D) (hs : (s : P) ∈ A)
    (hd0 : G.trace (d : P) = 0) (hs0 : G.trace (s : P) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) (l : ℤ) :
    G.trace ((↑((d * s) ^ l) : P) * (d : P)) = 0 := by
  have hss : s * s = 1 := by simpa only [hsi] using inv_mul_cancel s
  have heq : (d * s) ^ (l + 1) * s = (d * s) ^ l * d := by
    rw [zpow_add, zpow_one, mul_assoc, mul_assoc, hss, mul_one]
  have hval := congrArg (fun u : Pˣ => (u : P)) heq
  simp only [Units.val_mul] at hval
  rw [← hval]
  exact free_symmetry_coset_moments G.trace D A hf d s hd hs hd0 hs0 hdi hsi (l + 1)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralArcProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete projection underlying the centered dihedral arc.  Its
Fourier moments are separate from the operator construction: the projection
is the open spectral cut of the real part of the rotation at `cos θ`.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Spectral cuts preserve every star commutation relation. -/
theorem upperSpectralCut_commutes (A T : H →L[ℂ] H) (t : ℝ)
    (h : Commute A T) (hs : Commute A (star T)) :
    Commute (upperSpectralCut A t) T := by
  apply rangeSupport_commutes
  · exact (h.sub_left ((Commute.one_left T).smul_left t)).cfcₙ_real (fun x => x⁺)
  · exact (hs.sub_left ((Commute.one_left (star T)).smul_left t)).cfcₙ_real
      (fun x => x⁺)

/-- Centering a projection by any scalar in `[0,1]` keeps norm at most one. -/
theorem norm_projection_sub_scalar_le_one (p : H →L[ℂ] H)
    (hp : IsStarProjection p) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖p - r • 1‖ ≤ 1 := by
  have hp1 : p ≤ 1 := sub_nonneg.mp hp.one_sub.nonneg
  have hrl : r • (1 : H →L[ℂ] H) ≤ 1 := by
    simpa only [one_smul] using
      smul_le_smul_of_nonneg_right hr1 (zero_le_one : (0 : H →L[ℂ] H) ≤ 1)
  have hru : 0 ≤ r • (1 : H →L[ℂ] H) := smul_nonneg hr zero_le_one
  have hlo : -(1 : H →L[ℂ] H) ≤ p - r • 1 := by
    calc
      _ ≤ -(r • (1 : H →L[ℂ] H)) := neg_le_neg hrl
      _ ≤ p - r • 1 := by simpa only [zero_sub] using sub_le_sub_right hp.nonneg _
  have hhi : p - r • 1 ≤ (1 : H →L[ℂ] H) :=
    (sub_le_self _ hru).trans hp1
  have hself : IsSelfAdjoint (p - r • 1) :=
    hp.isSelfAdjoint.sub ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one _))
  have hn : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact (IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hself).trans
    (by simpa only [norm_neg, max_self] using hn)

theorem dihedralArcProjection_isStarProjection (w : H →L[ℂ] H) (θ : ℝ) :
    IsStarProjection (dihedralArcProjection w θ) := upperSpectralCut_isStarProjection _ _

theorem centeredDihedralArc_selfAdjoint (w : H →L[ℂ] H) (θ : ℝ) :
    IsSelfAdjoint (centeredDihedralArc w θ) :=
  (dihedralArcProjection_isStarProjection w θ).isSelfAdjoint.sub
    ((IsSelfAdjoint.all (θ / Real.pi)).smul (IsSelfAdjoint.one _))

theorem centeredDihedralArc_norm_le (w : H →L[ℂ] H)
    {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    ‖centeredDihedralArc w θ‖ ≤ 1 :=
  norm_projection_sub_scalar_le_one _ (dihedralArcProjection_isStarProjection w θ)
    (div_nonneg hθ Real.pi_pos.le) ((div_le_one Real.pi_pos).mpr hπ)

theorem dihedralArcProjection_mem (P : VonNeumannAlgebra H)
    (w : H →L[ℂ] H) (hw : w ∈ P) (θ : ℝ) : dihedralArcProjection w θ ∈ P := by
  have hstar : star w ∈ P := star_mem hw
  apply upperSpectralCut_mem
  rw [realPart_apply_coe, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact P.toStarSubalgebra.smul_mem (P.toStarSubalgebra.add_mem hw hstar) _

theorem centeredDihedralArc_mem (P : VonNeumannAlgebra H)
    (w : H →L[ℂ] H) (hw : w ∈ P) (θ : ℝ) : centeredDihedralArc w θ ∈ P := by
  apply P.toStarSubalgebra.sub_mem (dihedralArcProjection_mem P w hw θ)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact P.toStarSubalgebra.smul_mem P.one_mem _

/-- Normality makes the rotation commute with the real spectral variable. -/
theorem realPart_commutes_rotation (w : H →L[ℂ] H)
    (hw : Commute w (star w)) : Commute (realPart w : H →L[ℂ] H) w := by
  rw [realPart_apply_coe]
  exact ((Commute.refl w).add_left hw.symm).smul_left _

/-- Reflection interchanges the two summands of the real spectral variable. -/
theorem realPart_commutes_reflection (w d : H →L[ℂ] H)
    (hd : d * d = 1) (h : d * w = star w * d) :
    Commute (realPart w : H →L[ℂ] H) d := by
  have h' : d * star w = w * d := by
    calc
      d * star w = d * star w * (d * d) := by rw [hd, mul_one]
      _ = (d * (star w * d)) * d := by simp only [mul_assoc]
      _ = (d * (d * w)) * d := by rw [← h]
      _ = w * d := by rw [← mul_assoc d d w, hd, one_mul]
  rw [realPart_apply_coe]
  apply Commute.smul_left
  change (w + star w) * d = d * (w + star w)
  simp only [add_mul, mul_add, h, h', add_comm]

theorem centeredDihedralArc_commutes_rotation (w : H →L[ℂ] H)
    (hw : Commute w (star w)) (θ : ℝ) : Commute (centeredDihedralArc w θ) w := by
  apply Commute.sub_left _ ((Commute.one_left w).smul_left _)
  apply upperSpectralCut_commutes
  · exact realPart_commutes_rotation w hw
  · rw [realPart_apply_coe]
    exact (hw.add_left (Commute.refl (star w))).smul_left _

theorem centeredDihedralArc_commutes_reflection (w d : H →L[ℂ] H)
    (hd : d * d = 1) (hs : star d = d) (h : d * w = star w * d) (θ : ℝ) :
    Commute (centeredDihedralArc w θ) d := by
  apply Commute.sub_left _ ((Commute.one_left d).smul_left _)
  apply upperSpectralCut_commutes
  · exact realPart_commutes_reflection w d hd h
  · rw [hs]
    exact realPart_commutes_reflection w d hd h

omit [CompleteSpace H] in
/-- Once the projection's trace is known, its centered second moment is
forced algebraically; no separate spectral calculation is necessary. -/
theorem centeredProjection_second_moment (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (p : H →L[ℂ] H) (hp : p * p = p) (r : ℂ)
    (hτ : τ 1 = 1) (ht : τ p = r) :
    τ ((p - r • 1) * (p - r • 1)) = r * (1 - r) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    mul_one, one_mul, hp, map_sub, map_smul, hτ, ht, smul_eq_mul]
  ring

omit [CompleteSpace H] in
/-- Vanishing of the reflection-coset moments also controls the square. -/
theorem centeredProjection_square_reflection (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (p d : H →L[ℂ] H) (hp : p * p = p) (r : ℂ)
    (hτd : τ d = 0) (hτpd : τ (p * d) = 0) :
    τ (((p - r • 1) * (p - r • 1)) * d) = 0 := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    mul_one, one_mul, hp, map_sub, map_smul, hτd, hτpd,
    smul_zero, sub_self]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralCutMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from the continuous Haar functional calculus to the actual
open spectral projection, using its bounded strong resolvent limit. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem upperSpectralCut_vectorTrace_tendsto (Ω : H) (a b : H →L[ℂ] H) (c : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => vectorTrace Ω (supportResolvent (a - c • 1)⁺ (ε n) * b)) atTop
      (𝓝 (vectorTrace Ω (upperSpectralCut a c * b))) := by
  change Tendsto (fun n => inner ℂ Ω (supportResolvent (a - c • 1)⁺ (ε n) (b Ω)))
    atTop (𝓝 (inner ℂ Ω (rangeSupport (a - c • 1)⁺ (b Ω))))
  let B : H →L[ℂ] H := (a - c • 1)⁺
  have hB : 0 ≤ B := CFC.posPart_nonneg (a - c • 1)
  have ht := supportResolvent_tendsto B hB ε hε hlim (b Ω)
  exact ((innerSL ℂ Ω).continuous.tendsto (rangeSupport B (b Ω))).comp ht

private theorem regularizer_pos (n : ℕ) : 0 < regularizer n := by
  unfold regularizer
  positivity

private theorem regularizer_tendsto : Tendsto regularizer atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

theorem dihedralArcProjection_rotation_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
    (θ : ℝ) (l : ℤ) :
    vectorTrace Ω (dihedralArcProjection (w : H →L[ℂ] H) θ * (↑(w ^ l) : H →L[ℂ] H)) =
      angularIntegral (fun x => if Real.cos θ < Real.cos x then 1 else 0) l := by
  have hleft := upperSpectralCut_vectorTrace_tendsto Ω (realPart (w : H →L[ℂ] H))
    (↑(w ^ l) : H →L[ℂ] H) (Real.cos θ) regularizer regularizer_pos regularizer_tendsto
  have heq (n : ℕ) :
      vectorTrace Ω (supportResolvent ((realPart (w : H →L[ℂ] H) : H →L[ℂ] H) -
          Real.cos θ • 1)⁺ (regularizer n) * (↑(w ^ l) : H →L[ℂ] H)) =
        angularIntegral (fun x => (spectralCutFunction (Real.cos θ) (regularizer n)
          (Real.cos x) : ℂ)) l := by
    rw [supportResolvent_positiveShift_eq_cfc _ (realPart (w : H →L[ℂ] H)).property
      _ (regularizer_pos n)]
    exact trace_cfc_realPart_rotation (vectorTrace Ω) w hw hwn hhaar _
      (spectralCutFunction_continuous _ (regularizer_pos n)) l
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft
    (angularIntegral_cut_tendsto (Real.cos θ) regularizer regularizer_pos regularizer_tendsto l)

theorem dihedralArcProjection_reflection_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (d : H →L[ℂ] H) (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hcoset : ∀ l : ℤ, vectorTrace Ω ((↑(w ^ l) : H →L[ℂ] H) * d) = 0)
    (θ : ℝ) (l : ℤ) :
    vectorTrace Ω ((dihedralArcProjection (w : H →L[ℂ] H) θ *
      (↑(w ^ l) : H →L[ℂ] H)) * d) = 0 := by
  have hleft := upperSpectralCut_vectorTrace_tendsto Ω (realPart (w : H →L[ℂ] H))
    ((↑(w ^ l) : H →L[ℂ] H) * d) (Real.cos θ) regularizer regularizer_pos regularizer_tendsto
  have heq (n : ℕ) : vectorTrace Ω
      (supportResolvent ((realPart (w : H →L[ℂ] H) : H →L[ℂ] H) - Real.cos θ • 1)⁺
        (regularizer n) * ((↑(w ^ l) : H →L[ℂ] H) * d)) = 0 := by
    rw [supportResolvent_positiveShift_eq_cfc _ (realPart (w : H →L[ℂ] H)).property
      _ (regularizer_pos n)]
    simpa only [mul_assoc] using trace_cfc_realPart_rotation_reflection
      (vectorTrace Ω) w d hw hwn hcoset _
      (spectralCutFunction_continuous _ (regularizer_pos n)).continuousOn l
  simp only [heq] at hleft
  have hzero : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0) := tendsto_const_nhds
  simpa only [dihedralArcProjection, upperSpectralCut, mul_assoc] using
    tendsto_nhds_unique hleft hzero

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ConcreteDihedralSpectralArc
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the published spectral-arc input for an actual finite
dihedral von Neumann algebra with its vector trace. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centeredDihedralArc_rotation_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (l : ℤ) :
    vectorTrace Ω (centeredDihedralArc (w : H →L[ℂ] H) θ * (↑(w ^ l) : H →L[ℂ] H)) =
      arcFourierIntegral θ l := by
  rw [centeredDihedralArc, sub_mul, smul_mul_assoc, one_mul, map_sub,
    ContinuousLinearMap.map_smul_of_tower,
    dihedralArcProjection_rotation_moment Ω w hw hwn hhaar,
    angularIntegral_cut_eq hθ hθπ, angularPowerMoment_zero, hhaar]
  simp only [Complex.real_smul, Complex.ofReal_div]
  ring

theorem centeredDihedralArc_reflection_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (d : H →L[ℂ] H) (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hcoset : ∀ l : ℤ, vectorTrace Ω ((↑(w ^ l) : H →L[ℂ] H) * d) = 0)
    (θ : ℝ) (l : ℤ) :
    vectorTrace Ω ((centeredDihedralArc (w : H →L[ℂ] H) θ *
      (↑(w ^ l) : H →L[ℂ] H)) * d) = 0 := by
  rw [centeredDihedralArc, sub_mul, sub_mul, smul_mul_assoc, one_mul,
    smul_mul_assoc, map_sub, ContinuousLinearMap.map_smul_of_tower,
    dihedralArcProjection_reflection_moment Ω w d hw hwn hcoset, hcoset,
    smul_zero, sub_zero]

/-- The centered arc exists in the specified von Neumann algebra, with all
moments derived from the Haar and reflection-coset laws. -/
theorem concreteDihedralSpectralArcInput (Ω : H) (P : VonNeumannAlgebra H)
    (w d : (H →L[ℂ] H)ˣ) (hwP : (w : H →L[ℂ] H) ∈ P)
    (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hd : (d : H →L[ℂ] H) * (d : H →L[ℂ] H) = 1)
    (hds : star (d : H →L[ℂ] H) = (d : H →L[ℂ] H))
    (hconj : (d : H →L[ℂ] H) * (w : H →L[ℂ] H) =
      star (w : H →L[ℂ] H) * (d : H →L[ℂ] H))
    (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, vectorTrace Ω ((↑(w ^ l) : H →L[ℂ] H) * (d : H →L[ℂ] H)) = 0) :
    DihedralSpectralArcInput (vectorTrace Ω).toLinearMap P.toStarSubalgebra w d := by
  intro θ hθ hθπ
  have hcomm : Commute (w : H →L[ℂ] H) (star (w : H →L[ℂ] H)) := by
    change (w : H →L[ℂ] H) * star (w : H →L[ℂ] H) =
      star (w : H →L[ℂ] H) * (w : H →L[ℂ] H)
    simp only [hw, ← Units.val_mul, mul_inv_cancel, inv_mul_cancel, Units.val_one]
  have ht1 : vectorTrace Ω 1 = 1 := by simpa only [zpow_zero, Units.val_one, ite_true] using hhaar 0
  have htp : vectorTrace Ω (dihedralArcProjection (w : H →L[ℂ] H) θ) =
      (θ / Real.pi : ℂ) := by
    have ht := dihedralArcProjection_rotation_moment Ω w hw hwn hhaar θ 0
    rw [zpow_zero, Units.val_one, mul_one, angularIntegral_cut_eq hθ hθπ,
      arcFourierIntegral_zero hθ hθπ, angularPowerMoment_zero] at ht
    simpa only [ite_true, mul_one, zero_add] using ht
  have htd : vectorTrace Ω (d : H →L[ℂ] H) = 0 := by
    simpa only [zpow_zero, Units.val_one, one_mul] using hcoset 0
  have htpd : vectorTrace Ω (dihedralArcProjection (w : H →L[ℂ] H) θ * (d : H →L[ℂ] H)) = 0 := by
    simpa only [zpow_zero, Units.val_one, mul_one] using
      dihedralArcProjection_reflection_moment Ω w (d : H →L[ℂ] H) hw hwn hcoset θ 0
  refine ⟨{
    element := centeredDihedralArc (w : H →L[ℂ] H) θ
    mem := centeredDihedralArc_mem P _ hwP θ
    selfAdjoint := (centeredDihedralArc_selfAdjoint _ θ).star_eq
    norm_le := centeredDihedralArc_norm_le _ hθ hθπ
    commute_rotation := centeredDihedralArc_commutes_rotation _ hcomm θ
    commute_reflection := centeredDihedralArc_commutes_reflection _ _ hd hds hconj θ
    rotation_moment := centeredDihedralArc_rotation_moment Ω w hw hwn hhaar hθ hθπ
    reflection_moment := centeredDihedralArc_reflection_moment Ω w (d : H →L[ℂ] H) hw hwn hcoset θ
    square_moment := ?_
    square_reflection_moment := ?_
  }⟩
  · have ht := centeredProjection_second_moment (vectorTrace Ω).toLinearMap
      (dihedralArcProjection (w : H →L[ℂ] H) θ)
      (dihedralArcProjection_isStarProjection _ θ).isIdempotentElem.eq (θ / Real.pi : ℂ) ht1 htp
    simp only [centeredDihedralArc, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      ContinuousLinearMap.coe_coe] using ht
  · have ht := centeredProjection_square_reflection (vectorTrace Ω).toLinearMap
      (dihedralArcProjection (w : H →L[ℂ] H) θ) (d : H →L[ℂ] H)
      (dihedralArcProjection_isStarProjection _ θ).isIdempotentElem.eq (θ / Real.pi : ℂ) htd htpd
    simp only [centeredDihedralArc, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_div, ContinuousLinearMap.coe_coe] using ht

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_GeneratedDihedralAlgebras
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two auxiliary algebras in the spectral test are the actual bounded
L² closures of their algebraic generators. Their inclusions and the density
premises in the free-corner theorem follow from this construction. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

theorem second_mem_generatedDihedralAlgebra (d s : P) :
    s ∈ G.generatedDihedralAlgebra d s :=
  G.le_l2GeneratedAlgebra _ (StarAlgebra.subset_adjoin ℂ _ (by simp))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArcTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faithful-coordinate transport of the spectral arc. Only the actual
generated subalgebra must have a von Neumann range. -/

noncomputable section
namespace KadisonSimilarity

section Transport
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem starAlgHom_unit_zpow (ρ : A →⋆ₐ[ℂ] B) (u : Aˣ) (l : ℤ) :
    ρ (↑(u ^ l) : A) = (↑((Units.map ρ.toAlgHom.toMonoidHom u) ^ l) : B) :=
  congrArg (fun v : Bˣ => (v : B)) (map_zpow (Units.map ρ.toAlgHom.toMonoidHom) u l)

/-- An arc in a faithful represented subalgebra is an arc in the source,
with exactly the same trace moments. -/
theorem dihedralSpectralArcInput_of_injective
    (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ) (ρ : A →⋆ₐ[ℂ] B)
    (hρ : Function.Injective ρ) (hτ : ∀ a, τB (ρ a) = τA a)
    (C : StarSubalgebra ℂ A) (w d : Aˣ)
    (hinput : DihedralSpectralArcInput τB (C.map ρ)
      (Units.map ρ.toAlgHom.toMonoidHom w) (Units.map ρ.toAlgHom.toMonoidHom d)) :
    DihedralSpectralArcInput τA C w d := by
  intro θ hθ hθπ
  obtain ⟨F⟩ := hinput θ hθ hθπ
  obtain ⟨a, ha, heq⟩ := F.mem
  change a ∈ C at ha
  change ρ a = F.element at heq
  have hwp (l : ℤ) := starAlgHom_unit_zpow ρ w l
  refine ⟨{
    element := a
    mem := ha
    selfAdjoint := ?_
    norm_le := ?_
    commute_rotation := ?_
    commute_reflection := ?_
    rotation_moment := ?_
    reflection_moment := ?_
    square_moment := ?_
    square_reflection_moment := ?_
  }⟩
  · apply hρ
    rw [map_star ρ, heq, F.selfAdjoint]
  · rw [← NonUnitalStarAlgHom.norm_map ρ hρ a, heq]
    exact F.norm_le
  · apply hρ
    simp only [map_mul ρ, heq]
    exact F.commute_rotation.eq
  · apply hρ
    simp only [map_mul ρ, heq]
    exact F.commute_reflection.eq
  · intro l
    rw [← hτ, map_mul ρ, heq, hwp]
    exact F.rotation_moment l
  · intro l
    simp only [← hτ, map_mul ρ, heq, hwp]
    exact F.reflection_moment l
  · rw [← hτ, map_mul ρ, heq]
    exact F.square_moment
  · simp only [← hτ, map_mul ρ, heq]
    exact F.square_reflection_moment

end Transport
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_NormalSpectralArc
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The abstract spectral-arc input follows once its generated algebra has
the actual faithful normal range. The ambient algebra need not be presented
in those coordinates. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem dihedralSpectralArcInput_of_normal_range
    (τ : A →ₗ[ℂ] ℂ) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hρ : Function.Injective ρ)
    (Ω : H) (hτ : ∀ a, vectorTrace Ω (ρ a) = τ a)
    (C : StarSubalgebra ℂ A) (P : VonNeumannAlgebra H)
    (hrange : C.map ρ = P.toStarSubalgebra) (w d : Aˣ) (hwC : (w : A) ∈ C)
    (hw : star (w : A) = (↑w⁻¹ : A)) (hwn : ‖(w : A)‖ ≤ 1)
    (hd : (d : A) * (d : A) = 1) (hds : star (d : A) = (d : A))
    (hconj : (d : A) * (w : A) = star (w : A) * (d : A))
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : A) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, τ ((↑(w ^ l) : A) * (d : A)) = 0) :
    DihedralSpectralArcInput τ C w d := by
  apply dihedralSpectralArcInput_of_injective τ (vectorTrace Ω).toLinearMap ρ hρ hτ C w d
  rw [hrange]
  apply concreteDihedralSpectralArcInput Ω P
  · change ρ (w : A) ∈ P.toStarSubalgebra
    rw [← hrange]
    exact ⟨(w : A), hwC, rfl⟩
  · change star (ρ (w : A)) = ρ (↑w⁻¹ : A)
    rw [← map_star ρ, hw]
  · change ‖ρ (w : A)‖ ≤ 1
    rw [NonUnitalStarAlgHom.norm_map ρ hρ]
    exact hwn
  · change ρ (d : A) * ρ (d : A) = 1
    rw [← map_mul ρ, hd, map_one]
  · change star (ρ (d : A)) = ρ (d : A)
    rw [← map_star ρ, hds]
  · change ρ (d : A) * ρ (w : A) = star (ρ (w : A)) * ρ (d : A)
    rw [← map_star ρ, ← map_mul ρ, ← map_mul ρ, hconj]
  · intro l
    rw [← starAlgHom_unit_zpow ρ w l]
    exact (hτ _).trans (hhaar l)
  · intro l
    rw [← starAlgHom_unit_zpow ρ w l]
    change vectorTrace Ω (ρ (↑(w ^ l) : A) * ρ (d : A)) = 0
    rw [← map_mul ρ, hτ, hcoset]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialNormalSpan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed star subalgebra of a finite von Neumann algebra generates
exactly the bounded elements in the closure of its trace vectors. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonSimilarity.ambient_closed
variable (S : StarSubalgebra ℂ M.toStarSubalgebra) [IsClosed (S : Set M.toStarSubalgebra)]

theorem tracialSeedVonNeumann_le : tracialSeedVonNeumann S ≤ M := by
  intro T hT
  change T ∈ representationVonNeumannAlgebra (tracialSeedRepresentation S) at hT
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
  rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
  intro b hb
  apply hT b
  rintro _ ⟨a, rfl⟩
  exact hb _ a.val.property

theorem seed_mem_tracialSeedVonNeumann (a : S) :
    ((a : M.toStarSubalgebra) : H →L[ℂ] H) ∈ tracialSeedVonNeumann S :=
  mem_representationVonNeumannAlgebra (tracialSeedRepresentation S) a

theorem normal_mem_iff_traceVector_mem_seed_closure (τ : TracialRepresentation M)
    (x : M.toStarSubalgebra) :
    (x : H →L[ℂ] H) ∈ tracialSeedVonNeumann S ↔
      baseVector τ x ∈ closure (baseVector τ '' (S : Set M.toStarSubalgebra)) := by
  constructor
  · intro hx
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a, _, ha, _⟩ := twoVectorKaplanskyInput (tracialSeedRepresentation S)
      (x : H →L[ℂ] H) hx τ.vector τ.vector (ε / 2) (by positivity)
    refine ⟨baseVector τ (a : M.toStarSubalgebra), ⟨a, a.property, rfl⟩, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact ha.trans_lt (by linarith)
  · intro hx
    apply mem_of_traceVector_mem_closure τ (tracialSeedVonNeumann_le S) x
    apply closure_mono _ hx
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, seed_mem_tracialSeedVonNeumann S ⟨a, ha⟩, rfl⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GeneratedNormalRange
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded L²-generated algebra has a normal range whenever the
ambient tracial geometry has a faithful normal left range. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

namespace TracialCornerGeometry
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem exists_l2Generated_normal_range (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) (S : StarSubalgebra ℂ A) :
    ∃ N : VonNeumannAlgebra H, (G.l2GeneratedAlgebra S).map G.left = N.toStarSubalgebra := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  let τ := G.normalTracialRepresentation h1 hf M hrange
  let S₀ := S.topologicalClosure
  let S₁ : StarSubalgebra ℂ M.toStarSubalgebra := S₀.map e.toStarAlgHom
  have hS₀ : IsClosed (S₀ : Set A) := S.isClosed_topologicalClosure
  let : IsClosed (S₀ : Set A) := hS₀
  have hS₁ : IsClosed (S₁ : Set M.toStarSubalgebra) := by
    change IsClosed (e '' (S₀ : Set A))
    exact (StarAlgEquiv.isometry e).isClosedEmbedding.isClosedMap _ hS₀
  let : IsClosed (S₁ : Set M.toStarSubalgebra) := hS₁
  let N := tracialSeedVonNeumann S₁
  have hN : N ≤ M := tracialSeedVonNeumann_le S₁
  have hv (a : A) : Generator.Tracial.baseVector τ (e a) = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  have hset : Generator.Tracial.baseVector τ '' (S₁ : Set M.toStarSubalgebra) =
      Set.range (G.baseAlgebraVectors S₀) := by
    ext v
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, ha, heq⟩ := hb
      change e a = b at heq
      subst b
      exact ⟨⟨a, ha⟩, (hv a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e (a : A), ⟨(a : A), a.property, rfl⟩, hv (a : A)⟩
  have hmem (a : A) : G.left a ∈ N ↔ a ∈ G.l2GeneratedAlgebra S := by
    have h := normal_mem_iff_traceVector_mem_seed_closure S₁ τ (e a)
    rw [hv, hset] at h
    exact h
  refine ⟨N, ?_⟩
  ext T
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (hmem a).mpr ha
  · intro hT
    have hTM : T ∈ G.left.range := by
      rw [hrange]
      exact hN hT
    obtain ⟨a, rfl⟩ := hTM
    exact ⟨a, (hmem a).mp hT, rfl⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_NormalFreeDihedral
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generated free dihedral algebra inherits its normal realization
from the ambient tracial geometry. Its spectral input is therefore a
consequence of the two free centered symmetries. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem generated_dihedral_spectralInput_oai
    (h1 : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (D B : StarSubalgebra ℂ A) (hfree : ScalarFree G.trace D B)
    (d s : Aˣ) (hd : (d : A) ∈ D) (hs : (s : A) ∈ B)
    (hd0 : G.trace (d : A) = 0) (hs0 : G.trace (s : A) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s)
    (hds : star d = d) (hss : star s = s) :
    DihedralSpectralArcInput G.trace
      (G.generatedDihedralAlgebra (d : A) (s : A)) (d * s) d := by
  obtain ⟨N, hN⟩ := G.exists_l2Generated_normal_range h1 hfaithful M hrange
    (StarAlgebra.adjoin ℂ ({(d : A), (s : A)} : Set A))
  have hw : star (↑(d * s) : A) = (↑(d * s)⁻¹ : A) := by
    exact congrArg (fun u : Aˣ => (u : A))
      (free_symmetry_product_star d s hds hss hdi hsi)
  apply dihedralSpectralArcInput_of_normal_range G.trace G.left
    (G.left_injective hfaithful) (G.vector 1) G.trace_eq_vectorTrace
    (G.generatedDihedralAlgebra (d : A) (s : A)) N hN (d * s) d
  · exact (G.generatedDihedralAlgebra (d : A) (s : A)).mul_mem
      (G.first_mem_generatedDihedralAlgebra (d : A) (s : A))
      (G.second_mem_generatedDihedralAlgebra (d : A) (s : A))
  · exact hw
  · nontriviality A
    have hn : ‖(↑(d * s) : A)‖ * ‖(↑(d * s) : A)‖ = 1 := by
      rw [← CStarRing.norm_star_mul_self, hw, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, norm_one]
    nlinarith [norm_nonneg (↑(d * s) : A)]
  · simpa only [hdi, Units.val_mul, Units.val_one] using
      congrArg (fun u : Aˣ => (u : A)) (inv_mul_cancel d)
  · exact congrArg (fun u : Aˣ => (u : A)) hds
  · rw [hw]
    exact congrArg (fun u : Aˣ => (u : A)) (free_symmetry_rotation_conjugation d s hdi hsi)
  · exact free_symmetry_haar_moments G.trace h1 D B hfree d s hd hs hd0 hs0 hdi hsi
  · exact G.free_symmetry_first_coset_moments D B hfree d s hd hs hd0 hs0 hdi hsi

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput_oai.{u_1, u_2}

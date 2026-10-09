-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentAmplificationLiveEnergy.original_masked_child_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:18:31.280674+00:00
-- url     : https://prove2.me/submissions/df61a3f7-b71f-4281-b9c1-d8045a95535a

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section
-- module Solutions.OAIHecke.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open Polynomial

/-- Backport (Mathlib d13f23b), with Mathlib's own proof. -/
theorem IsCoprime.dvd_mul_left_iff {R : Type*} [CommSemiring R] {x y z : R} (H : IsCoprime x y) :
    x ∣ y * z ↔ x ∣ z :=
  ⟨H.dvd_of_dvd_mul_left, fun h ↦ h.mul_left y⟩
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

end EisensteinSchwartzPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert (preTransparency := .instances) hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

theorem actual_eisenstein_periodic_summable (f : 𝓢(ℂ, ℂ))
    {R : Type*} [Fintype R] (q : O → R) (P : R → ℂ) :
    Summable (fun z : O => P (q z) * f (eisEmbedding z)) := by
  classical
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun a _ => norm_nonneg (P a)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((actual_eisenstein_summable_norm f).mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP (q z)) (norm_nonneg _)

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Physical
namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _

attribute [local irreducible] markedPhysicalProbe

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Support
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

theorem support_reconstruct (I : Ideal O) (hI : I ≠ 0) (S : Finset (Ideal O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportResidual_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]

theorem extracted_residual_coprime (I J : Ideal O) (S : Finset (Ideal O)) :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by
    intro P hP hQ
    exact (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)

theorem supportExtract_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp only [supportExtract, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportResidual_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  simp only [supportResidual, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportExtract_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportExtract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

theorem supportExtract_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportExtract, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportExtract_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

theorem supportResidual_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportResidual, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportResidual_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Fourier
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

theorem residueGauss_supported_mk (d : O)
    (hd : CanonicalQuadraticSieve.Supported (Ideal.span {d})) (h : O) :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

end SevenEighths.CenteredMomentFourier
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.GaussEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentGaussEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentFourier
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem gaussRow_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => gaussRow a ha z * star (gaussRow b hb z) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P : Residue (a * b) → ℂ := fun x =>
    normalizedResidueGauss a (supported_element_ne_zero a ha)
      (supportedModulusCharacter a ha) (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (normalizedResidueGauss b (supported_element_ne_zero b hb)
      (supportedModulusCharacter b hb) (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) P
  simpa only [P, frequencyReduction_mk, normalizedResidueGauss,
    residueGauss_supported_mk, scaledRadialTest_apply, gaussRow] using hs

theorem gaussPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) :
    ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [gaussPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gaussEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  exact (hasSum_sum (fun i _ =>
    (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

end SevenEighths.CenteredMomentGaussEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSectors
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonSectors
open CenteredMomentCompleteCommon CenteredMomentSupport IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem supportExtract_of_subset (I : Ideal O) (hI : I≠0) (S : Finset (Ideal O))
    (hS : primeSupport I⊆S) : supportExtract I S=I := by
  unfold supportExtract
  rw [Multiset.filter_eq_self.mpr (fun P hP => hS (Multiset.mem_toFinset.mpr hP))]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_of_disjoint (I : Ideal O) (S : Finset (Ideal O))
    (hS : Disjoint (primeSupport I) S) : supportExtract I S=1 := by
  unfold supportExtract
  rw [Multiset.filter_eq_nil.mpr (fun P hP => Finset.disjoint_left.mp hS (Multiset.mem_toFinset.mpr hP))]
  rfl

end SevenEighths.CenteredMomentCommonSectors

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocation
open CenteredMomentSupport CenteredMomentCommonSectors
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem extract_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportExtract (C*a) (primeSupport C)=C := by
  rw [supportExtract_mul C a hC ha,
    supportExtract_of_subset C hC _ (Finset.Subset.refl _),
    supportExtract_of_disjoint a _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa).symm,
    mul_one]

theorem residual_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportResidual (C*a) (primeSupport C)=a := by
  apply mul_left_cancel₀ hC
  have he := support_reconstruct (C*a) (mul_ne_zero hC ha) (primeSupport C)
  rwa [extract_coprime_product C a hC ha hCa] at he

theorem tuple_products {ι : Type*} [Fintype ι] (v : ι → Ideal O) (C a : Ideal O)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hv : ∏ i,v i=C*a) :
    (∏ i,supportExtract (v i) (primeSupport C))=C ∧
      (∏ i,supportResidual (v i) (primeSupport C))=a := by
  have hv0 : ∏ i,v i≠0 := hv.symm ▸ mul_ne_zero hC ha
  have hi (i : ι) : v i≠0 := Finset.prod_ne_zero_iff.mp hv0 i (Finset.mem_univ _)
  constructor
  · rw [← supportExtract_prod Finset.univ v (fun i _ => hi i),hv]
    exact extract_coprime_product C a hC ha hCa
  · rw [← supportResidual_prod Finset.univ v (fun i _ => hi i),hv]
    exact residual_coprime_product C a hC ha hCa

theorem residual_factor_coprime (C I : Ideal O) (hC : C≠0) :
    IsCoprime C (supportResidual I (primeSupport C)) := by
  have hh := extracted_residual_coprime C I (primeSupport C)
  rwa [supportExtract_of_subset C hC _ (Finset.Subset.refl _)] at hh

end SevenEighths.CenteredMomentCommonAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonAllocationBox
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationBox
open CenteredMomentCommonAllocation CenteredMomentSupport CenteredMomentCommonSectors
open CenteredMomentFirstSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem residualBoxes_image (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) :
    (residualBoxes S C B hB).image (fun v i => B i*v i)=sourceFiber S C B := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have hui := Fintype.mem_piFinset.mp hu
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact (mem_residualPool (B i) (hB i) (S i) _).mp (Finset.mem_filter.mp (hui i)).1
    · intro i
      have hp := Finset.mem_filter.mp (hui i)
      have hsrc := (mem_residualPool (B i) (hB i) (S i) _).mp hp.1
      have hu0 : u i≠0 := right_ne_zero_of_mul (hS i _ hsrc)
      rw [supportExtract_mul _ _ (hB i) hu0,supportExtract_of_subset _ (hB i) _ (hBs i),
        supportExtract_of_disjoint _ _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hu0).mpr hp.2).symm,mul_one]
  · intro hv
    obtain ⟨hv,hvB⟩ := Finset.mem_filter.mp hv
    have hvi := Fintype.mem_piFinset.mp hv
    let u := fun i => supportResidual (v i) (primeSupport C)
    have hi (i : ι) : B i*u i=v i := by
      rw [← hvB i]
      exact support_reconstruct _ (hS i _ (hvi i)) _
    refine Finset.mem_image.mpr ⟨u,?_,funext hi⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_residualPool (B i) (hB i) (S i) _).mpr
      rw [hi]
      exact hvi i
    · exact residual_factor_coprime C (v i) hC

theorem sourceFiber_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,F v)=
      ∑ u∈residualBoxes S C B hB,F (fun i => B i*u i) := by
  rw [← residualBoxes_image S hS C hC B hB hBs,Finset.sum_image]
  intro u hu v hv he
  funext i
  exact mul_left_cancel₀ (hB i) (congrFun he i)

theorem sourceFiber_product_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (hprod : ∏ i,B i=C)
    (a : Ideal O) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)=
      ∑ u∈residualBoxes S C B hB,if (∏ i,u i)=a then F (fun i => B i*u i) else 0 := by
  rw [sourceFiber_sum S hS C hC B hB hBs]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.prod_mul_distrib,hprod,mul_right_inj' hC]

end SevenEighths.CenteredMomentCommonAllocationBox

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonAllocationSum
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocation CenteredMomentCommonAllocationBox CenteredMomentSupport
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem sum_source_fibers (S : ι → Finset (Ideal O)) (C : Ideal O)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,F v)=∑ B∈allocationLabels S C,∑ v∈sourceFiber S C B,F v := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=Fintype.piFinset S) (t:=allocationLabels S C)
    (g:=fun v i => supportExtract (v i) (primeSupport C))
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) F
  symm
  convert (preTransparency := .instances) hh using 1
  apply Finset.sum_congr rfl
  intro B hB
  congr 1
  ext v
  simp only [sourceFiber,Finset.mem_filter,funext_iff]

theorem sum_actual_allocations (S : ι → Finset (Ideal O))
    (C a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B∈actualAllocations S C,
        ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0 := by
  rw [sum_source_fibers S C]
  symm
  apply Finset.sum_filter_of_ne
  intro B hB hn
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hp : (∏ i,v i)=C*a := by
    by_contra hh
    exact hne (if_neg hh)
  have he := (tuple_products v C a hC ha hCa hp).1
  have hb := (Finset.mem_filter.mp hv).2
  simpa only [hb] using he

theorem original_coefficient_allocated (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B : actualAllocations S C,
        ∑ u∈residualBoxes S C B
          (allocation_data S C B (Finset.mem_filter.mp B.property).1).1,
          if (∏ i,u i)=a then F (fun i => B.val i*u i) else 0 := by
  rw [sum_actual_allocations S C a hC ha hCa F]
  rw [← Finset.sum_coe_sort (actualAllocations S C)
    (fun B => ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)]
  apply Finset.sum_congr rfl
  intro B hB
  exact sourceFiber_product_sum S hS C hC B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).2
    (Finset.mem_filter.mp B.property).2 a F

end SevenEighths.CenteredMomentCommonAllocationSum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonProfile
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem remaining_product (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    finiteTupleProduct u=finiteTupleProduct (remainingTuple B u) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,remainingTuple,
    Sum.elim_inl,Sum.elim_inr]
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => u (Sum.inl i))]
  congr 1
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply hf i
  intro hBi
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBi⟩)

theorem slot_profiles_split (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (β : ι → Ideal O → ℂ) :
    (∏ i,β i (B (Sum.inl i)*u (Sum.inl i)))=
      (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),β i (B (Sum.inl i)))*
        ∏ i : liveIndices B,β i.val (u (Sum.inl i.val)) := by
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => β i (u (Sum.inl i)))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1)
    (fun i => β i (B (Sum.inl i)*u (Sum.inl i))),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hf i (Finset.mem_filter.mp hi).2,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]

theorem profile_common_allocation (B u : Tuple ι) (C R s : Ideal O)
    (hB : finiteTupleProduct B=C) (hsC : s∣C)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
        profileCoefficient R (fun i : liveIndices B => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 (remainingTuple B u) := by
  have hprod : finiteTupleProduct (fun i => B i*u i)=C*finiteTupleProduct (remainingTuple B u) := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct u=_
    rw [hB,remaining_product B u hf]
  have hdiv : s∣C*finiteTupleProduct (remainingTuple B u) := dvd_mul_of_dvd_left hsC _
  unfold profileCoefficient
  rw [slot_profiles_split B u hf (fun i I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)),hprod]
  simp only [hdiv,ite_true,one_dvd,mul_one,remainingTuple_slot,remainingTuple_plain,
    IsCoprime.mul_left_iff]
  rw [mul_assoc B₁,mul_assoc B₂]
  by_cases hC : IsCoprime C R <;>
    by_cases hu : IsCoprime (finiteTupleProduct (remainingTuple B u)) R <;>
    simp_all only [true_and,false_and,ite_true,ite_false,mul_zero,zero_mul,mul_one]
  ring

end SevenEighths.CenteredMomentCommonProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceCommonMask
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceCommonMask
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem profile_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hne : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (finiteTupleProduct v) R ∧ s∣finiteTupleProduct v := by
  constructor
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero,zero_mul])
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero])

end SevenEighths.CenteredMomentSourceCommonMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonPuncture
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPuncture
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O

 theorem residualBoxes_filter {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0) :
    residualBoxes S C B hB=
      (Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i))).filter
        (fun u => IsCoprime C (∏ i,u i)) := by
  ext u
  simp only [residualBoxes,Fintype.mem_piFinset,Finset.mem_filter,
    IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  exact forall_and

theorem residualBoxes_sum {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (F : (ι → Ideal O) → ℂ) :
    (∑ u∈residualBoxes S C B hB,F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        (if IsCoprime C (∏ i,u i) then 1 else 0)*F u := by
  rw [residualBoxes_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp

theorem profileCoefficient_puncture {ι : Type*} [Fintype ι]
    (C R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    (if IsCoprime C (finiteTupleProduct v) then 1 else 0)*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  unfold profileCoefficient
  rw [IsCoprime.mul_right_iff,show IsCoprime C (finiteTupleProduct v) ↔ IsCoprime (finiteTupleProduct v) C from isCoprime_comm]
  by_cases hC : IsCoprime (finiteTupleProduct v) C <;>
    by_cases hR : IsCoprime (finiteTupleProduct v) R <;> simp [hC,hR]

end SevenEighths.CenteredMomentCommonPuncture

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RemainingBox
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem restore_remaining (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    restoreTuple B (remainingTuple B u)=u := by
  funext i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · rfl
    · exact (hf i (by simpa [liveIndices] using hi)).symm
  · rfl

theorem remaining_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (u : Tuple ι) (hu : u∈Fintype.piFinset S) :
    remainingTuple B u∈Fintype.piFinset (remainingSets B S) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · exact Fintype.mem_piFinset.mp hu (Sum.inl i.val)
  · exact Fintype.mem_piFinset.mp hu (Sum.inr j)

theorem restore_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (v : Tuple (liveIndices B)) (hv : v∈Fintype.piFinset (remainingSets B S)) :
    restoreTuple B v∈Fintype.piFinset S := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · exact Fintype.mem_piFinset.mp hv (Sum.inl ⟨i,hi⟩)
    · exact hg i (by simpa [liveIndices] using hi)
  · exact Fintype.mem_piFinset.mp hv (Sum.inr j)

theorem remaining_box_sum (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) := by
  apply Finset.sum_bij (fun u _ => remainingTuple B u)
  · exact fun u hu => remaining_mem B S u hu
  · intro u hu v hv he
    have hu' := restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))
    have hv' := restore_remaining B v (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hv _))
    rw [← hu',← hv',he]
  · intro v hv
    exact ⟨restoreTuple B v,restore_mem B S hg v hv,remaining_restore B v⟩
  · intro u hu
    rw [restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))]

theorem remaining_box_sum_gate (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      if (∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) else 0 := by
  split_ifs with hg
  · exact remaining_box_sum B S hf hg F
  · have he : Fintype.piFinset S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      apply hg
      intro i hi
      have hui := Fintype.mem_piFinset.mp hu (Sum.inl i)
      rwa [hf i hi _ hui] at hui
    rw [he,Finset.sum_empty]

end SevenEighths.CenteredMomentRemainingBox

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceLiveAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveAllocation
open CenteredMomentRemainingBox CenteredMomentCommonProfile CenteredMomentCommonPuncture
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem prime_residual_frozen (B : Tuple ι) (hB : ∀ i,B i≠0)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) :
    ∀ i,B (Sum.inl i)≠1 → ∀ I∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)),I=1 := by
  intro i hi I hI
  have hprime := hp i _ ((mem_residualPool _ _ _ _).mp hI)
  rcases hprime.irreducible.isUnit_or_isUnit rfl with h|h
  · exact False.elim (hi (by simpa only [Ideal.isUnit_iff,Ideal.one_eq_top] using h))
  · simpa only [Ideal.isUnit_iff,Ideal.one_eq_top] using h

theorem allocation_frozen_gate (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal O) (B : Tuple ι)
    (hB : B∈CenteredMomentCommonAllocationSum.allocationLabels S C) :
    ∀ i,B (Sum.inl i)≠1 → B (Sum.inl i)∈S (Sum.inl i) := by
  classical
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hB
  intro i hi
  have hvi : v (Sum.inl i)∈S (Sum.inl i) := by
    have hh := hv
    simp only [Fintype.mem_piFinset] at hh
    exact hh (Sum.inl i)
  have he := congrFun hvB (Sum.inl i)
  change CenteredMomentSupport.supportExtract (v (Sum.inl i))
    (IdealMobiusDivisorSum.primeSupport C)=B (Sum.inl i) at he
  rw [CenteredMomentSupport.supportExtract_prime _ (hp i _ hvi)] at he
  split_ifs at he with hm
  · rwa [he] at hvi
  · exact False.elim (hi he.symm)

theorem residual_source_profile (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s : Ideal O)
    (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (F : Tuple (liveIndices B) → ℂ) :
    (∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)*
        F (remainingTuple B u))=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
      (if (∀ i,B (Sum.inl i)≠1 → B (Sum.inl i)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B (fun i => residualPool (B i) (hB i) (S i))),
          profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
            (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
            (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v*F v else 0) := by
  let T := fun i => residualPool (B i) (hB i) (S i)
  have hf := prime_residual_frozen B hB S hp
  let A := (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0)
  let G := fun v : Tuple (liveIndices B) =>
    profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
      (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
      (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v*F v
  rw [residualBoxes_sum]
  calc
    _ = ∑ u∈Fintype.piFinset T,A*G (remainingTuple B u) := by
      apply Finset.sum_congr
      · ext u;simp only [Fintype.mem_piFinset];rfl
      · intro u hu
        have hfu : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 :=
          fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _)
        rw [profile_common_allocation B u C R s hprod hsC hfu]
        change (if IsCoprime C (finiteTupleProduct u) then 1 else 0)*
          (A*_ * F (remainingTuple B u))=_
        rw [remaining_product B u hfu]
        dsimp only [G]
        rw [← profileCoefficient_puncture C R]
        ring
    _ = A*(∑ u∈Fintype.piFinset T,G (remainingTuple B u)) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [remaining_box_sum_gate B T hf]
      simp only [remaining_restore,T,mem_residualPool,mul_one]
      rfl

end SevenEighths.CenteredMomentSourceLiveAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceLiveColumn
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveColumn
open CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceLiveColumn.instDecidableEqSumFinOfNatNat_solutions
theorem residual_source_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ u∈residualBoxes S C B hB,if finiteTupleProduct u=a then
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i) else 0)=
      frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B hB)
          (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  have hh := residual_source_profile S hp B hB C R s hprod hsC ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (fun v => if finiteTupleProduct v=a then 1 else 0)
  rw [if_pos (allocation_frozen_gate S hp C B hlabel)] at hh
  calc
    _ = ∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)*
        (if finiteTupleProduct (remainingTuple B u)=a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 := by
        intro i hi
        have hui := hu
        simp only [residualBoxes,Fintype.mem_piFinset] at hui
        exact prime_residual_frozen B hB S hp i hi _
          (Finset.mem_filter.mp (hui (Sum.inl i))).1
      rw [remaining_product B u hf]
      split_ifs <;> simp
    _ = _ := hh.trans (by
      unfold frozenCoefficient finiteColumnCoefficient liveBox liveProfile
      rw [Finset.sum_filter]
      congr 1
      apply Finset.sum_congr
      · ext v;simp only [Fintype.mem_piFinset]
      intro v hv
      split_ifs <;> simp)

theorem original_source_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)=
      ∑ B : actualAllocations S C,
        frozenCoefficient B C R ν Wslot P*
          finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
            (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  simp only [finiteColumnCoefficient, Finset.sum_filter]
  have halloc := original_coefficient_allocated S hS C a hC ha hCa
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  change (∑ v ∈ Fintype.piFinset S, if finiteTupleProduct v = C * a then
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v else 0) = _ at halloc
  rw [halloc]
  apply Finset.sum_congr rfl
  intro B hB
  have h := residual_source_column S hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s a
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2 hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp only [finiteColumnCoefficient, Finset.sum_filter] at h
  exact h

end SevenEighths.CenteredMomentSourceLiveColumn

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LiveSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentLiveSupport
open CenteredMomentSourceLiveColumn CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentFirstSectors CenteredMomentSourceCommonMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentLiveSupport.instDecidableEqSumFinOfNatNat_definitions
theorem restore_frozen (B : Tuple ι) (v : Tuple (liveIndices B)) :
    ∀ i,B (Sum.inl i)≠1 → restoreTuple B v (Sum.inl i)=1 := by
  intro i hi
  simp only [restoreTuple,Sum.elim_inl]
  rw [dif_neg (by simpa [liveIndices] using hi)]

theorem restore_product (B : Tuple ι) (v : Tuple (liveIndices B)) :
    finiteTupleProduct (restoreTuple B v)=finiteTupleProduct v := by
  rw [remaining_product B _ (restore_frozen B v),remaining_restore]

theorem restored_original_mem (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal O)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (hlabel : B∈allocationLabels S C)
    (v : Tuple (liveIndices B)) (hv : v∈liveBox S B hB) :
    (fun i => B i*restoreTuple B v i)∈Fintype.piFinset S := by
  have hg : ∀ i,B (Sum.inl i)≠1 →
      (1:Ideal O)∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)) := by
    intro i hi
    rw [mem_residualPool,mul_one]
    exact allocation_frozen_gate S hp C B hlabel i hi
  have hu := restore_mem B (fun i => residualPool (B i) (hB i) (S i)) hg v (by simpa only [liveBox,Fintype.mem_piFinset] using hv)
  apply Fintype.mem_piFinset.mpr
  intro i
  simp only [Fintype.mem_piFinset] at hu
  exact (mem_residualPool _ _ _ _).mp (hu i)

theorem live_column_original_support (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (hne : finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a≠0) :
    C*a∈finiteColumns (Fintype.piFinset S) ∧ a≠0 ∧ IsCoprime C a := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,ha⟩ := Finset.mem_filter.mp hv
  have hm := profile_nonzero_masks (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v hvn
  rw [ha,IsCoprime.mul_right_iff] at hm
  have hsrc := restored_original_mem S hp C B hB hlabel v hv
  have he : finiteTupleProduct (fun i => B i*restoreTuple B v i)=C*a := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct (restoreTuple B v)=_
    rw [hprod,restore_product,ha]
  have hn : C*a≠0 := by
    rw [← he,finiteTupleProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hS i _ (Fintype.mem_piFinset.mp hsrc i))
  exact ⟨Finset.mem_image.mpr ⟨_,hsrc,he⟩,right_ne_zero_of_mul hn,hm.1.2.symm⟩

end SevenEighths.CenteredMomentLiveSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LiveDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentLiveDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem finite_column_mem {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (a : Ideal O) (ha : finiteColumnCoefficient S β a≠0) : a∈finiteColumns S := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_image.mpr ⟨v,hv,he⟩

 theorem sum_same_support (S T : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (hST : ∀ I∈S,c I≠0 → I∈T) (hTS : ∀ I∈T,c I≠0 → I∈S) :
    (∑ I∈S,c I*f I)=∑ I∈T,c I*f I := by
  have hs : (∑ I∈S∩T,c I*f I)=∑ I∈S,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hI,hST I hI h⟩)
    rw [hc,zero_mul]
  have ht : (∑ I∈S∩T,c I*f I)=∑ I∈T,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hTS I hI h,hI⟩)
    rw [hc,zero_mul]
  exact hs.symm.trans ht

theorem source_gaussPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*primaryGaussRow I z := by
  unfold gaussPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*primaryGaussRow I z)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [primaryGaussRow,dif_pos (Finset.mem_filter.mp I.property).2]
  rfl

variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentLiveDomain.instDecidableEqSumFinOfNatNat_solutions
theorem live_column_sum (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    (∑ I∈supportedColumns (residualPool C hC.1 (finiteColumns (Fintype.piFinset S))),c I*f I)=
      ∑ I∈supportedColumns (finiteColumns (liveBox S B hB)),c I*f I := by
  dsimp only
  apply sum_same_support
  · intro I hI hn
    exact Finset.mem_filter.mpr ⟨finite_column_mem _ _ I hn,(Finset.mem_filter.mp hI).2⟩
  · intro I hI hn
    have hh := live_column_original_support S hS hp B hB C R I hlabel hprod
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn
    exact Finset.mem_filter.mpr ⟨(mem_residualPool C hC.1 _ I).mpr hh.1,(Finset.mem_filter.mp hI).2⟩

theorem live_gaussPolynomial (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) z=
      gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_gaussPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using live_column_sum S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*primaryGaussRow I z)

theorem live_gaussEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  unfold gaussEnergy
  apply tsum_congr
  intro z
  exact congrArg (fun x : ℂ => ((‖x‖^2:ℝ):ℂ)*W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K))
    (live_gaussPolynomial S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ f z)

end SevenEighths.CenteredMomentLiveDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSmoothedWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem gaussEnergy_hasSum_re {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖gaussPolynomial S a ha c z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (gaussEnergy S a ha c U K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c U K hK).hasSum
  simpa only [gaussEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hs

theorem finite_weighted_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖gaussPolynomial S a ha c z‖^2*(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)≤
      (gaussEnergy S a ha c U K).re :=
  sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hU z)) (gaussEnergy_hasSum_re S a ha c U K hK)

end SevenEighths.CenteredMomentSmoothedWindowEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceAllocationEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceAllocationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

 theorem gaussPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*gaussPolynomial S a ha (d B) z := by
  simp only [gaussPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentSourceAllocationEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceSmoothedAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceSmoothedAllocation
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentSourceAllocationEnergy CenteredMomentSourceLiveColumn
open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

theorem smoothed_allocation_energy {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (gaussEnergy S a ha (fun i => ∑ B,b B*d B i) W K).re≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(gaussEnergy S a ha (d B) W K).re := by
  have hs := gaussEnergy_hasSum_re S a ha (fun i => ∑ B,b B*d B i) W K hK
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        (‖gaussPolynomial S a ha (d B) z‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*gaussPolynomial S a ha (d B) z)) (hW z)
      rw [gaussPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using h
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        ∑ z∈rows,‖gaussPolynomial S a ha (d B) z‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_weighted_le_gaussEnergy S a ha (d B) W K hK hW rows) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentSourceSmoothedAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentOriginalChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentSourceSmoothedAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentOriginalChildEnergy.instDecidableEqSumFinOfNatNat_solutions
theorem original_source_punctured_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s I : Ideal O) (hC : C≠0) (hI : I≠0) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)=
      ∑ B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I := by
  by_cases hc : IsCoprime C I
  · rw [if_pos hc]
    exact original_source_column S hS hp C R s I hC hI hc hsC ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂
  · rw [if_neg hc]
    symm
    apply Finset.sum_eq_zero
    intro B hB
    have hz : finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
        (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I=0 := by
      by_contra hn
      exact hc (live_column_original_support S hS hp B
        (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R I
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn).2.2
    rw [hz,mul_zero]

end SevenEighths.CenteredMomentOriginalChildEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationLiveMask
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationLiveMask
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentOriginalChildEnergy CenteredMomentRemainingBox CenteredMomentCommonProfile
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationLiveMask.instDecidableEqSumFinOfNatNat_definitions
theorem profile_mask (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v*
        (if s∣finiteTupleProduct v then 1 else 0) := by
  simp only [profileCoefficient,one_dvd,ite_true,mul_one]

theorem column_mask (S : Finset (Tuple ι)) (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O) :
    finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I=
      finiteColumnCoefficient S
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1) I*
          (if s∣I then 1 else 0) := by
  unfold finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [profile_mask,(Finset.mem_filter.mp hv).2]

theorem original_masked_live_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s I : Ideal O) (hC : C≠0) (hI : I≠0) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)=
      ∑ B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I := by
  have he := original_source_punctured_column S hS hp C R 1 I hC hI (one_dvd C)
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  rw [column_mask,hsc.dvd_mul_left_iff]
  have hh := congrArg (fun z : ℂ => z*(if s∣I then 1 else 0)) he
  rw [Finset.sum_mul] at hh
  convert (preTransparency := .instances) hh using 1
  · split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro B hB
    rw [maskedLiveProfile,column_mask]
    dsimp only [liveProfile]
    ring

end SevenEighths.CenteredMomentAmplificationLiveMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationLiveEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationLiveEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentSourceSmoothedAllocation
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationLiveEnergy.instDecidableEqSumFinOfNatNat_definitions
theorem masked_live_gaussEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  have he (I : Ideal O) : finiteColumnCoefficient (liveBox S B hB)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I=
      finiteColumnCoefficient (liveBox S B hB)
        (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*
          (if s∣I then 1 else 0) := column_mask _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp_rw [he,mul_assoc]
  exact live_gaussEnergy S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => (if s∣I then 1 else 0)*f I) W K

theorem original_masked_child_energy_oai (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q) =>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I=
      ∑ B,b B*d B I := by
    rw [original_masked_live_column S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,d,mul_assoc]
  have h := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  have he' := funext he
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤_
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceGaussEnergy] using
    congrArg (fun x : ℂ => ‖frozenCoefficient B C R ν Wslot P‖^2*x.re)
    (masked_live_gaussEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K)

end SevenEighths.CenteredMomentAmplificationLiveEnergy

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentAmplificationLiveEnergy.original_masked_child_energy_oai.{u_1} := @OAI.SevenEighths.CenteredMomentAmplificationLiveEnergy.original_masked_child_energy_oai.{u_1}

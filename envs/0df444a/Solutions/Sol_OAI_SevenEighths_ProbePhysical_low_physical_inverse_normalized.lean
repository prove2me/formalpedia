-- Prove2me | solution 1 for OAI.SevenEighths.ProbePhysical.low_physical_inverse_normalized
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:37:56.895414+00:00
-- url     : https://prove2.me/submissions/5bf21777-205d-408f-a18c-79d708bcc21f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_low_original_completed_energy

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
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

namespace DyadicTransfer

theorem annularCutoff_eq_zero_of_le_half (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    {y : ℝ} (hy : y ≤ 1 / 2) : annularCutoff φ y = 0 := by
  have hy1 : y ≤ 1 := by linarith
  have h2y : 2 * y ≤ 1 := by linarith
  simp [annularCutoff, hsmall y hy1, hsmall (2 * y) h2y]

end DyadicTransfer

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

theorem rayCharacter_eq_of_mod_four (χ : RayCharacter) (a b : O) (h : (4 : O) ∣ a - b) :
    rayCharacter χ a = rayCharacter χ b := by
  unfold rayCharacter
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

end RayFourExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.BranchScaling
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

namespace InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open ConcretePrimeRowBridge (idealGenerator)

local instance instFintypeUnitsO_r30282e_1 : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
lemma sourceLabelUnit_spec (f : O) : f=(sourceLabelUnit f : O)*idealGenerator (Ideal.span {f}) :=
  Classical.choose_spec (exists_label_unit f (Ideal.span {f}) rfl)

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Row
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

end SevenEighths.ProbeRow
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Calibration
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_span (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    Ideal.span {(calibrationForSet S hS).generator} = ∏ P ∈ S, P := by
  change Ideal.span {finitePrimeModulus (fun P : S => P.val)} = _
  rw [span_finitePrimeModulus]
  exact Finset.prod_coe_sort S (fun P : Ideal O => P)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem CalibrationData.residueMonoid_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

theorem calibrationForSet_coprime_of_excluded (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (a : O)
    (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    IsCoprime (calibrationForSet S hS).generator a := by
  apply (calibrationForSet_coprime_iff S hS a).mpr
  intro P hP ha
  apply hmask P hP
  exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma elementNorm_mul (a b : ActualEisensteinCubic.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.TuplePrime
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CanonicalSlots
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma canonicalSlotSupport_nonzero (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (a : O) (ha : a∈canonicalSlotSupport T) : a≠0 := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact supported_primaryGenerator_ne_zero P.val (hT P hP)

lemma canonicalSlotEquiv_span (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : Ideal.span {(canonicalSlotEquiv T hT P).val}=P.val.val :=
  span_primaryGenerator_of_supported _ (hT P.val P.property)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianPartition
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy
lemma gaussianAnnulus_contDiff : ContDiff ℝ ∞ gaussianAnnulus := by
  unfold gaussianAnnulus annularCutoff gaussianCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).sub
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPeriod
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact D.numeratorSupported.1

lemma periodicCalibrationXi_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (a : O) : ‖periodicCalibrationXi C B D a‖≤1 := by
  rw [periodicCalibrationXi,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported a)

lemma periodicCalibrationXi_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (periodicCalibrationXi C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change C.residueMonoid x*_ = C.residueMonoid y*_
  congr 1
  · apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)

lemma lowBaseModulus_ne_zero (η : HeckeFamily.Character) (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : lowBaseModulus η C B D≠0 := by
  unfold lowBaseModulus
  apply mul_ne_zero
  · exact mul_ne_zero η.modulus_ne_bot (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
      (calibrationRowModulus_ne_zero C B hB D))
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowPeriodicBase_periodic (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) :
    FactorsModulo (lowBaseModulus η C B D) (lowPeriodicBase η C B D s hs χ) := by
  intro x y hxy
  have h4 : (4:O)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy)
  have hη : targetMonoid η x=targetMonoid η y := by
    apply congrArg η.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hc := periodicCalibrationXi_periodic C B D x y (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  change ((rayMonoid χ x*targetMonoid η x)*star (periodicCalibrationXi C B D x))*
      sexticReciprocityPhase s x=
    ((rayMonoid χ y*targetMonoid η y)*star (periodicCalibrationXi C B D y))*sexticReciprocityPhase s y
  rw [hη,hc,sexticReciprocityPhase_congr_right s x y h4]
  have hr : rayMonoid χ x=rayMonoid χ y := rayCharacter_eq_of_mod_four χ x y h4
  rw [hr]

lemma lowPeriodicBase_norm (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (a : O) : ‖lowPeriodicBase η C B D s hs χ a‖≤1 := by
  have hr : ‖rayMonoid χ a‖≤1 := FiniteRayExpansion.norm_char_le_one χ _
  change ‖((rayMonoid χ a*targetMonoid η a)*star (periodicCalibrationXi C B D a))*sexticReciprocityPhase s a‖≤1
  simp only [norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) hr).trans (targetMonoid_norm_le_one η a))).trans (periodicCalibrationXi_norm C B D a))).trans (sexticReciprocityPhase_norm s a)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPuncture
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_generator_dvd (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (a : O) (ha : Ideal.span {a}∈S) : a∣(calibrationForSet S hS).generator := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
  rw [calibrationForSet_span]
  exact Finset.dvd_prod_of_mem (fun P : Id=>P) ha

lemma calibration_generator_bad (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    λ₀∣(calibrationForSet S hS).generator ∧ (2:O)∣(calibrationForSet S hS).generator := by
  constructor
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl rfl
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr trivial

lemma supported_of_coprime_bad (B n : O) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (hc : IsCoprime B n) : Supported (Ideal.span {n}) := by
  apply supported_span_iff n |>.mpr
  constructor
  · exact PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp
      (hc.of_isCoprime_of_dvd_left hBL)
  · have h2 : IsCoprime (-2:O) n := (hc.of_isCoprime_of_dvd_left hB2).neg_left
    have hn := negative_two_prime.irreducible.coprime_iff_not_dvd.mp h2
    simpa only [neg_dvd] using hn

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianSeminorm
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open Filter Set
namespace SevenEighths.ProbePhysical

lemma gaussianFixedWindow_small (y : ℝ) (hy : y≤1/2) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_small y hy,zero_div]
lemma gaussianFixedWindow_large (y : ℝ) (hy : 2≤y) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_large y hy,zero_div]
lemma gaussianFixedWindow_contDiff : ContDiff ℝ ∞ gaussianFixedWindow := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have hf : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_sqrt hy.ne')
    unfold gaussianFixedWindow
    simp only [div_eq_mul_inv]
    exact gaussianAnnulus_contDiff.contDiffAt.mul (hf.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianFixedWindow_small x hx.le

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowActualEnergies
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

lemma lowNumeratorRows_mem (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) (m : O) :
    m∈lowNumeratorRows a b ha hb Q hQ ↔ lowOuterCutoff a b (elementNorm m/Q)≠0 := by
  simp only [lowNumeratorRows,Set.Finite.mem_toFinset,Function.mem_support]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSelectedSum
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSelectedInverseRow_correction {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) :
    lowSelectedInverseRow F c η S hS D T t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        ∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0) := by
  unfold lowSelectedInverseRow lowMarkedInverseRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro k hk
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSlotMarks
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSelectedIdeal_eq_product {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) :
    lowSelectedIdeal slots J b=∏i : SelectedSlot J,Ideal.span {(b i).val} := by
  change CanonicalRowCompletion.principalIdealHom (∏i : SelectedSlot J,(b i).val)=_
  exact map_prod CanonicalRowCompletion.principalIdealHom _ _

lemma lowSelectedIdeal_dvd_iff {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) : lowSelectedIdeal slots J b∣A ↔ ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A := by
  rw [lowSelectedIdeal_eq_product]
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem (fun i : SelectedSlot J=>Ideal.span {(b i).val}) (Finset.mem_univ i)).trans h
  · exact Fintype.prod_dvd_of_coprime hcop

lemma lowSelectedIdeal_mark {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) :
    (if lowSelectedIdeal slots J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_dvd_iff slots J b hcop]
  by_cases h : ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [if_neg (fun hall=>hi (hall i))]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

lemma lowCanonicalSelectedPrime_mem {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    lowCanonicalSelectedPrime T hT J b i∈T i.val :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).property

lemma lowCanonicalSelectedPrime_span {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    Ideal.span {(b i).val}=(lowCanonicalSelectedPrime T hT J b i).val := by
  have hh := canonicalSlotEquiv_span (T i.val) (hT i.val)
    ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i))
  simpa only [Equiv.apply_symm_apply,lowCanonicalSelectedPrime] using hh

lemma lowCanonicalSelectedPrime_injective {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Function.Injective (lowCanonicalSelectedPrime T hT J b) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  exact Finset.disjoint_left.mp (hdis hne) (lowCanonicalSelectedPrime_mem T hT J b i)
    (hij.symm ▸ lowCanonicalSelectedPrime_mem T hT J b j)

lemma lowCanonicalSelected_coprime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})) := by
  intro i j hij
  rw [lowCanonicalSelectedPrime_span T hT J b i,lowCanonicalSelectedPrime_span T hT J b j]
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSlotWeights
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow FourierBridge
local notation "O" => ActualEisensteinCubic.O

lemma lowSelectedWeight_eq_product {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    lowSelectedWeight η slots J W P t b=
      ∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val := by
  have he : HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val)=
      ∏i : SelectedSlot J,HeckeFamily.elementCoeff η (b i).val := map_prod (targetMonoid η) _ _
  unfold lowSelectedWeight lowSingleSlotWeight
  rw [he,star_prod]
  simp only [Finset.prod_mul_distrib,mul_assoc]

lemma lowSingleSlotWeight_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖≤‖W (elementNorm a/P)‖ := by
  rw [lowSingleSlotWeight,norm_mul,norm_mul,norm_star,logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPeriodSupport
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma lowCalibrationGood_dvd (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator) : D.numeratorGood∣C.generator := by
  refine ⟨D.numeratorUnit.val*λ₀^D.numeratorLambda*(2:O)^D.numeratorTwo,?_⟩
  have hh := D.numeratorFactor
  simp only [one_pow,one_mul] at hh
  change C.generator=D.numeratorUnit.val*λ₀^D.numeratorLambda*(2:O)^D.numeratorTwo*D.numeratorGood at hh
  exact hh.trans (by ring)

theorem lowBaseModulus_coprime (η : HeckeFamily.Character) (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator)
    (hLam : λ₀∣C.generator) (h2 : (2:O)∣C.generator)
    (n : O) (hcn : IsCoprime C.generator n) (hη : HeckeFamily.elementCoeff η n≠0) :
    IsCoprime (Ideal.span {n}) (lowBaseModulus η C C.generator D*Ideal.span {(72:O)}) := by
  have heta : IsCoprime (Ideal.span {n}) η.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hη)
  have hcal : IsCoprime (Ideal.span {n}) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hcn.symm
  have hgood : IsCoprime (Ideal.span {n}) (Ideal.span {D.numeratorGood}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (hcn.of_isCoprime_of_dvd_left (lowCalibrationGood_dvd C D)).symm
  have htwo : IsCoprime n (2:O) := (hcn.of_isCoprime_of_dvd_left h2).symm
  have hs := supported_of_coprime_bad C.generator n hLam h2 hcn
  have hnine := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n ((supported_span_iff n).mp hs).1).symm
  have hseventy : IsCoprime n (72:O) := by
    convert (preTransparency := .instances) (htwo.pow_right : IsCoprime n ((2:O)^3)).mul_right hnine using 1 ;norm_num
  have h72 : IsCoprime (Ideal.span {n}) (Ideal.span {(72:O)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hseventy
  have h4 : IsCoprime (Ideal.span {n}) (Ideal.span {(4:O)}) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    convert (preTransparency := .instances) htwo.pow_right (n:=2) using 1 ;norm_num
  unfold lowBaseModulus calibrationRowModulus
  exact (heta.mul_right (hcal.mul_right
    (((isCoprime_one_right).mul_right hcal).mul_right h72 |>.mul_right hgood))).mul_right h4 |>.mul_right h72

theorem lowSingleSlotWeight_zero_of_period (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (P t : ℝ) (n : O) (hcn : IsCoprime (calibrationForSet S hS).generator n)
    (hperiod : ¬IsCoprime (Ideal.span {n})
      (lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator
        (calibrationLowData S hS)*Ideal.span {(72:O)})) :
    lowSingleSlotWeight η W P t n=0 := by
  have heta : HeckeFamily.elementCoeff η n=0 := by
    by_contra hh
    exact hperiod (lowBaseModulus_coprime η _ _ (calibration_generator_bad S hS hbad).1
      (calibration_generator_bad S hS hbad).2 n hcn hh)
  simp [lowSingleSlotWeight,heta]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPeriodFilter
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sum_tuple_filter_zero {ι α : Type*} [Fintype ι] [DecidableEq α]
    (T : ι→Finset α) (good : ι→α→Prop) [∀i,DecidablePred (good i)]
    (c : ι→α→ℂ) (hc : ∀i a,a∈T i→¬good i a→c i a=0) (F : (ι→α)→ℂ) :
    (∑p : ∀i,T i,(∏i,c i (p i).val)*F (fun i=>(p i).val))=
      ∑p : ∀i,(T i).filter (good i),(∏i,c i (p i).val)*F (fun i=>(p i).val) := by
  let forget : (∀i,(T i).filter (good i))→(∀i,T i) := fun p i=>⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩
  have hinj : Function.Injective forget := by
    intro p q h
    funext i
    exact Subtype.ext (congrArg (fun a=> (a i).val) h)
  let H : (∀i,T i)→ℂ := fun p=>(∏i,c i (p i).val)*F (fun i=>(p i).val)
  have hz (p : ∀i,T i) (hp : p∉Finset.univ.image forget) : H p=0 := by
    by_contra hh
    have hn : ∀i,good i (p i).val := by
      intro i
      by_contra hbad
      have hc0 := hc i (p i).val (p i).property hbad
      have hprod : (∏j,c j (p j).val)=0 := Finset.prod_eq_zero (Finset.mem_univ i) hc0
      exact hh (by dsimp [H];rw [hprod,zero_mul])
    let q : ∀i,(T i).filter (good i) := fun i=>⟨(p i).val,Finset.mem_filter.mpr ⟨(p i).property,hn i⟩⟩
    exact hp (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩)
  have he := Finset.sum_subset (Finset.subset_univ (Finset.univ.image forget))
    (fun p hp hnot=>hz p hnot)
  change (∑p,H p)=_
  rw [←he,Finset.sum_image (fun p _ q _ h=>hinj h)]

lemma canonical_prime_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (P : PrimeIdeal) (hP : CanonicalQuadraticSieve.Supported P.val) (hout : P.val∉S) :
    IsCoprime (calibrationForSet S hS).generator (CompletedGauss.primaryGenerator P.val) := by
  apply calibrationForSet_coprime_of_excluded S hS
  intro Q hQ hdiv
  rw [span_primaryGenerator_of_supported P.val hP] at hdiv
  have hpmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have he : P.val=Q := Ideal.IsMaximal.eq_of_le hpmax (hS Q hQ).ne_top (Ideal.dvd_iff_le.mp hdiv)
  exact hout (he.symm ▸ hQ)

lemma lowPeriodPrimeList_subset (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) :
    lowPeriodPrimeList η S hS T⊆T := Finset.filter_subset _ _

lemma lowPeriodPrimeList_disjoint {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→Finset PrimeIdeal)
    (hT : Pairwise (fun i j=>Disjoint (T i) (T j))) :
    Pairwise (fun i j=>Disjoint (lowPeriodPrimeList η S hS (T i)) (lowPeriodPrimeList η S hS (T j))) := by
  intro i j hij
  exact (hT hij).mono (lowPeriodPrimeList_subset η S hS _) (lowPeriodPrimeList_subset η S hS _)

theorem low_canonical_polynomial_period_filter {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→PrimeIdeal)→ℂ) :
    (∑p : ∀i,T i,(∏i,lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator (p i).val.val))*F (fun i=>(p i).val))=
      ∑p : ∀i,lowPeriodPrimeList η S hS (T i),
        (∏i,lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator (p i).val.val))*F (fun i=>(p i).val) := by
  apply sum_tuple_filter_zero T (fun i P=>IsCoprime P.val (lowPeriodIdeal η S hS))
    (fun i P=>lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator P.val)) _ F
  intro i P hP hnot
  apply lowSingleSlotWeight_zero_of_period η S hS hbad (W i) (Y i) t _
    (canonical_prime_calibration_coprime S hS P (hT i P hP) (hout i P hP))
  change ¬IsCoprime (Ideal.span {CompletedGauss.primaryGenerator P.val}) (lowPeriodIdeal η S hS)
  rwa [span_primaryGenerator_of_supported P.val (hT i P hP)]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.PunctureAbsorption
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem rowTwist_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0) :
    rowTwist Ψ (m*B) f z=rowTwist Ψ m f z := by
  ext n
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ (m*B) f z n hn,rowTwist_extract_sixth_mask Ψ m f z n hn]
    by_cases hb : IsCoprime B n
    · change Ψ n*(if IsCoprime (m*B) n then (1:ℂ) else 0)*_=
        Ψ n*(if IsCoprime m n then (1:ℂ) else 0)*_
      simp only [IsCoprime.mul_left_iff,hb,and_true]
    · rw [hΨzero n hb]
      simp only [zero_mul]
  · rw [rowTwist_zero_of_not_supported Ψ (m*B) f z n
        (dvd_mul_of_dvd_left hmLam B) (dvd_mul_of_dvd_left hm2 B) hn,
      rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowTruePeriodPuncture
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss RayFourExpansion SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRayPeriodicBase_support (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : physicalRayPeriodicBase η S hS σ χ n≠0) :
    IsCoprime (Ideal.span {n}) (lowPeriodIdeal η S hS) := by
  let C := calibrationForSet S hS
  let D := calibrationLowData S hS
  change ((rayMonoid χ n*HeckeFamily.elementCoeff η n)*
    star (C.residueMonoid n*CanonicalRowCompletion.actualPeriodicRow 1 C.generator
      D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n))*
      _≠0 at hn
  have ha := left_ne_zero_of_mul hn
  have heta := right_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hres := left_ne_zero_of_mul (star_ne_zero.mp (right_ne_zero_of_mul ha))
  have hc : IsCoprime C.generator n := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    exact ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
      (C.residue.apply_ne_zero_iff.mp hres)).symm
  exact lowBaseModulus_coprime η C D (calibration_generator_bad S hS hbad).1
    (calibration_generator_bad S hS hbad).2 n hc heta

lemma lowPeriodIdeal_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS≠0 := by
  unfold lowPeriodIdeal
  apply mul_ne_zero
  · exact lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowTruePeriodGenerator_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowTruePeriodGenerator η S hS≠0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero _ (lowPeriodIdeal_ne_zero η S hS)

lemma lowTruePeriodGenerator_span (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Ideal.span {lowTruePeriodGenerator η S hS}=lowPeriodIdeal η S hS :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma physicalRayPeriodicBase_zero_true_puncture (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : ¬IsCoprime (lowTruePeriodGenerator η S hS) n) :
    physicalRayPeriodicBase η S hS σ χ n=0 := by
  by_contra hh
  apply hn
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [lowTruePeriodGenerator_span]
  exact (physicalRayPeriodicBase_support η S hS hbad σ χ n hh).symm

theorem physical_row_absorb_true_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) :
    rowTwist (physicalRayPeriodicBase η S hS σ χ)
      ((calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS) f z=
    rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z := by
  exact InverseReflectedPhase.rowTwist_absorb_puncture _ _ _ f z
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2
    (physicalRayPeriodicBase_zero_true_puncture η S hS hbad σ χ)

lemma lowReflectionPeriod_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionPeriod η S hS≠0 :=
  lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _

lemma lowReflectionPeriod_actual (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo (lowReflectionPeriod η S hS) (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩

lemma lowReflectionMask_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionMask η S hS≠0 :=
  mul_ne_zero (calibrationForSet S hS).generator_ne_zero (lowTruePeriodGenerator_ne_zero η S hS)

lemma lowReflectionMask_bad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ConcretePrimeRowBridge.goodLambda∣lowReflectionMask η S hS ∧ (2:O)∣lowReflectionMask η S hS := by
  exact ⟨dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).1 _,
    dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).2 _⟩

lemma lowReflectionMask_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS∣Ideal.span {lowReflectionMask η S hS} := by
  rw [lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,lowTruePeriodGenerator_span]
  exact dvd_mul_left _ _

lemma physical_markedCompletedT_absorb_true_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) (W : ℝ→ℂ) (X : ℝ) (mark : Id→ℂ) :
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) f z) W X mark=
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z) W X mark := by
  rw [lowReflectionMask,physical_row_absorb_true_period η S hS hbad σ χ]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowActualIdealLists
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowPrimeIdealList_prime (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : Prime I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact P.property

lemma lowPrimeIdealList_supported (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (I : Id) (hI : I∈lowPrimeIdealList T) : Supported I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

lemma lowPrimeIdealList_maximal (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : I.IsMaximal :=
  (Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI)).isMaximal (lowPrimeIdealList_prime T I hI).ne_zero

lemma lowPrimeIdealList_good_odd (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (I : Id) (hI : I∈lowPrimeIdealList T) :
    ConcretePrimeRowBridge.goodLambda∉I ∧ ringChar (O⧸I)≠2 := by
  have hs := lowPrimeIdealList_supported T hT I hI
  exact hs.2 I ((Ideal.mem_normalizedFactors_iff hs.1).mpr
    ⟨Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI),le_rfl⟩)

lemma lowPrimeIdealList_disjoint {ι : Type*} (T : ι→Finset PrimeIdeal)
    (hT : Pairwise (fun i j=>Disjoint (T i) (T j))) :
    Pairwise (fun i j=>Disjoint (lowPrimeIdealList (T i)) (lowPrimeIdealList (T j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro I hI hJ
  obtain ⟨P,hP,hPI⟩ := Finset.mem_image.mp hI
  obtain ⟨Q,hQ,hQI⟩ := Finset.mem_image.mp hJ
  have he : P=Q := Subtype.ext (hPI.trans hQI.symm)
  exact Finset.disjoint_left.mp (hT hij) hP (he.symm ▸ hQ)

lemma lowPrimeIdealList_norm (T : Finset PrimeIdeal) (H : ℝ)
    (hT : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤H) (I : Id) (hI : I∈lowPrimeIdealList T) :
    (Ideal.absNorm I:ℝ)≤H := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

theorem low_actual_ideal_polynomial {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→Id)→ℂ) :
    (∑p : ∀i,canonicalSlotSupport (T i),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (p i).val)*F (fun i=>Ideal.span {(p i).val}))=
    ∑p : ∀i,lowPrimeIdealList (lowPeriodPrimeList η S hS (T i)),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val) := by
  let E := Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))
  rw [←Equiv.sum_comp E]
  simp only [E,Equiv.piCongrRight_apply,Pi.map_apply,canonicalSlotEquiv_val]
  have hspan (p : ∀i,T i) (i : ι) : Ideal.span {primaryGenerator (p i).val.val}=(p i).val.val :=
    span_primaryGenerator_of_supported _ (hT i _ (p i).property)
  simp_rw [hspan]
  rw [low_canonical_polynomial_period_filter η S hS hbad T hT hout W Y t (fun p=>F (fun i=>(p i).val))]
  exact Equiv.sum_comp (Equiv.piCongrRight (fun i=>lowPrimeListEquiv (lowPeriodPrimeList η S hS (T i))))
    (fun p=>(∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val))

lemma low_actual_ideal_weight_bound (η : HeckeFamily.Character) (W : ℝ→ℂ)
    (hW : ∀x,‖W x‖≤1) (Y t : ℝ) (I : Id) :
    ‖lowSingleSlotWeight η W Y t (primaryGenerator I)‖≤1 :=
  (lowSingleSlotWeight_norm η W Y t _).trans (hW _)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowInverseEnergy
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open RayFourExpansion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowCorrectionEnergy_nonneg : 0≤lowCorrectionEnergy :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

lemma fixed_correction_energy {ι κ : Type*} [Fintype ι] (R : Finset κ) (c : ι→ℂ) (F : ι→κ→ℂ) :
    (∑m∈R,‖∑χ : ι,c χ*F χ m‖^2)≤
      (∑χ : ι,‖c χ‖^2)*∑χ : ι,∑m∈R,‖F χ m‖^2 := by
  calc
    _≤∑m∈R,(∑χ : ι,‖c χ‖^2)*(∑χ : ι,‖F χ m‖^2) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        _≤(∑χ : ι,‖c χ‖*‖F χ m‖)^2 := by
          apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>by positivity))).mpr
          simpa only [norm_mul] using norm_sum_le Finset.univ (fun χ=>c χ*F χ m)
        _≤_ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _=_ := by rw [←Finset.mul_sum,Finset.sum_comm]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowElementRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

attribute [local instance] OAI.SevenEighths.ProbePhysical.instFintypeUnitsO
lemma lowIdealRowElement_point (m : O) : lowIdealRowElement (lowElementRowPoint m)=m :=
  (InitialMeanSquare.sourceLabelUnit_spec m).symm

lemma lowElementRowPoint_injective : Function.Injective lowElementRowPoint :=
  Function.LeftInverse.injective lowIdealRowElement_point

lemma lowIdealRows_nonzero (R : Finset O) (hR : ∀m∈R,m≠0) (I : Id) (hI : I∈lowIdealRows R) : I≠0 := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact Ideal.span_singleton_eq_bot.not.mpr (hR m hm)

lemma lowIdealRows_norm_bound (R : Finset O) (Q : ℝ) (hR : ∀m∈R,elementNorm m≤Q)
    (I : Id) (hI : I∈lowIdealRows R) : (Ideal.absNorm I:ℝ)≤Q := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact hR m hm

theorem low_element_energy_le_units (R : Finset O) (_hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,‖F m‖^2)≤∑u : Oˣ,∑I∈lowIdealRows R,‖F (u.val*idealGenerator I)‖^2 := by
  let P : Finset (Oˣ×Id) := Finset.univ×ˢlowIdealRows R
  have hsub : R.image lowElementRowPoint⊆P := by
    intro p hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨m,hm,rfl⟩⟩
  have he : (∑m∈R,‖F m‖^2)=∑p∈R.image lowElementRowPoint,‖F (lowIdealRowElement p)‖^2 := by
    rw [Finset.sum_image (fun m _ n _ h=>lowElementRowPoint_injective h)]
    simp only [lowIdealRowElement_point]
  rw [he]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _=>sq_nonneg ‖F (lowIdealRowElement p)‖)
  simpa only [P,Finset.sum_product,lowIdealRowElement] using hh

lemma low_rowTwist_label_one (Ψ : O→*ℂ) (m : O) (u : Oˣ) (I : Id) :
    CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)=
      CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id))
        (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I) := by
  have he : (InitialMeanSquare.sourceLabelUnit (1:O)).val*idealGenerator (1:Id)=1 := by
    simpa only [Ideal.span_singleton_one,Ideal.one_eq_top] using (InitialMeanSquare.sourceLabelUnit_spec (1:O)).symm
  have harg : m^6*(idealGenerator (1:Id))^4*
      (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I)=m^6*1^4*(u.val*idealGenerator I) := by
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,one_pow]
    calc
      _=m^6*((InitialMeanSquare.sourceLabelUnit (1:O)).val*idealGenerator (1:Id))^4*(u.val*idealGenerator I) := by ring
      _=_ := by rw [he];ring
  unfold CanonicalRowCompletion.rowTwist
  rw [harg]

lemma low_units_label_one_sum (F : (O→*ℂ)→ℝ) (Ψ : O→*ℂ) (m : O) (I : Id) :
    (∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)))=
      ∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)) := by
  simp_rw [low_rowTwist_label_one]
  exact Equiv.sum_comp (Equiv.mulLeft ((InitialMeanSquare.sourceLabelUnit (1:O))^4))
    (fun u : Oˣ=>F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)))

lemma low_element_rowTwist_energy (R : Finset O) (hR : ∀z∈R,z≠0)
    (Ψ : O→*ℂ) (m : O) (F : (O→*ℂ)→ℂ) :
    (∑z∈R,‖F (CanonicalRowCompletion.rowTwist Ψ m 1 z)‖^2)≤
      ∑u : Oˣ,∑I∈lowIdealRows R,
        ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2 := by
  apply (low_element_energy_le_units R hR (fun z=>F (CanonicalRowCompletion.rowTwist Ψ m 1 z))).trans_eq
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun (u : Oˣ) (I : Id)=>
    ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2)]
  apply Finset.sum_congr rfl
  intro I hI
  exact low_units_label_one_sum (fun Ψ=>‖F Ψ‖^2) Ψ m I

lemma lowNumeratorRows_nonzero (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : z≠0 := by
  intro he
  have hh := (lowNumeratorRows_mem a b ha hb Q hQ z).mp hz
  rw [he,elementNorm,Ideal.span_singleton_zero,Ideal.absNorm_bot,Nat.cast_zero,zero_div] at hh
  exact hh (lowOuterCutoff_small a b ha 0 (by positivity))

lemma lowNumeratorRows_norm_bound (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : elementNorm z≤2*b*Q := by
  have hh := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ z).mp hz)).2
  exact (div_le_iff₀ hQ).mp hh

lemma low_unit_card : Fintype.card Oˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowActualReflectedEnergy
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

attribute [local instance] OAI.SevenEighths.ProbePhysical.instFintypeUnitsO_1
theorem lowSelectedInverseRow_actual_ideal {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (z : O) :
    lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        lowActualIdealPolynomial
          (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
          (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X := by
  rw [lowSelectedInverseRow_correction]
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  simp_rw [lowSelectedWeight_eq_product]
  have hm (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0) := by
    funext A
    exact lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b) A
  simp_rw [hm,←physical_markedCompletedT_absorb_true_period η S hS hbad σ χ]
  convert (preTransparency := .instances) low_actual_ideal_polynomial η S hS hbad (fun i : SelectedSlot J=>T i.val)
    (fun i=>hT i.val) (fun i=>hout i.val) (fun i=>W i.val) (fun i=>Y i.val) t
    (fun p=>InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
      (fun A=>∏i : SelectedSlot J,if p i∣A then (1:ℂ) else 0)) using 1
  · congr 1
    ext p
    simp
  · rfl

theorem lowSelectedInverseRow_actual_reflected_energy {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
    lowCorrectionEnergy*∑χ : RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
      ‖lowActualIdealPolynomial
        (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) X‖^2 := by
  simp_rw [lowSelectedInverseRow_actual_ideal η S hS hbad T hT hout hdis J W Y X t σ]
  apply (fixed_correction_energy R ProbeCompleted.correctionCoeff _).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (lowReflectionMask η S hS) (fun Ψ=>lowActualIdealPolynomial
      (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
      (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I)) Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma elementNorm_finset_prod {ι : Type*} (F : Finset ι) (p : ι→O) :
    elementNorm (∏i∈F,p i)=∏i∈F,elementNorm (p i) := by
  induction F using Finset.induction_on with
  | empty => simp [elementNorm_one]
  | @insert i F hi ih => simp only [Finset.prod_insert hi,elementNorm_mul,ih]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowLength_sum {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) :
    lowUnselectedLength ell J+lowSelectedLength ell J=∑i,ell i := by
  rw [lowUnselectedLength,lowSelectedLength,Finset.sum_coe_sort]
  exact Finset.sum_add_sum_compl J ell

lemma lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤1/6 ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤1/6-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowUnselectedProduct_norm_lower {K : ℕ} (ell : Fin K→ℝ)
    (a Z : ℝ) (ha : 0<a) (hZ : 0<Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→a*Z^(ell i)≤elementNorm x)
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    (min 1 a)^K*Z^(lowUnselectedLength ell J)≤elementNorm (∏i : J,(p i).val) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤a^J.card*Z^(lowUnselectedLength ell J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_of_le_one (le_of_lt (lt_min zero_lt_one ha)) (min_le_left _ _) hc).trans
        (pow_le_pow_left₀ (by positivity) (min_le_right _ _) _)
    _=∏i : J,a*Z^(ell i.val) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := Finset.prod_le_prod (fun _ _=>by positivity) (fun i _=>hslots i.val _ (p i).property)

lemma lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)=
      elementNorm C.generator*Z^(5/6:ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(17/48:ℝ)*Z^(23/48:ℝ)=Z^(5/6:ℝ) := by rw [←Real.rpow_add hZ];norm_num
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^(5/6-2*d:ℝ) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^(5/6:ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring

lemma lowSelectedCaps_product {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (J : Finset (Fin K)) (Z b : ℝ) (hZ : 1≤Z) :
    (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤
      (max 1 b)^K*Z^(lowSelectedLength ell J) := by
  have hc : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  calc
    _≤∏i : SelectedSlot J,max 1 b*Z^(ell i.val) := by
      apply Finset.prod_le_prod (fun _ _=>le_trans zero_le_one (le_max_left _ _))
      intro i hi
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i.val))
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _=(max 1 b)^(Fintype.card (SelectedSlot J))*Z^(lowSelectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma lowUnselectedProduct_norm_upper_nominal {K : ℕ} (ell : Fin K→ℝ)
    (b Z : ℝ) (hZ : 0<Z) (slots : Fin K→Finset ActualEisensteinCubic.O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(p i).val)≤(max 1 b)^K*Z^(lowUnselectedLength ell J) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,max 1 b*Z^(ell i.val) := Finset.prod_le_prod
      (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>(hslots i.val _ (p i).property).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    _=(max 1 b)^J.card*Z^(lowUnselectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

theorem eventually_low_selected_caps {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ ∀J : Finset (Fin K),
      (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤Z^(lowSelectedLength ell J+ε/2) := by
  have hp : 0<ε/2 := by linarith
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hp).eventually (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro J
  apply (lowSelectedCaps_product ell hell J Z b hZ.le).trans
  calc
    _≤Z^(ε/2)*Z^(lowSelectedLength ell J) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];congr 1;ring

lemma lowCentralShift_scale (Z T ell0 : ℝ) (hZ : 1<Z) (hT : 0<T) :
    Z^(1+ell0+lowCentralShift Z T ell0)=T := by
  rw [lowCentralShift,show 1+ell0+(Real.logb Z T-1-ell0)=Real.logb Z T by ring]
  exact Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hT

lemma lowCentralShift_bound (Z T ell ε : ℝ) (hZ : 1<Z) (hT : 0<T) (hε : 0≤ε)
    (hlo : Z^(1+ell-ε/2)≤T) (hhi : T≤Z^(1+ell+ε/2)) :
    |lowCentralShift Z T (ell+ε/2)|≤ε := by
  have he := lowCentralShift_scale Z T (ell+ε/2) hZ hT
  rw [←he,Real.rpow_le_rpow_left_iff hZ] at hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowInverseNormalize
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma low_inverse_power_cancel (Z d α : ℝ) (hZ : 0<Z) :
    Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma low_inverse_sqrt_normalized (q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0<q) (hC : 0≤C) (_hB : 0≤B) (hZ : 0<Z) (hL : 0<L) (hH : 1≤H)
    (hE : 0≤E) (hEL : E≤C*H^n*Z^(5/6-2*d+α)) (hLB : L≤B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^(5/6:ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^(5/6:ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^(5/6-2*d+α))/(q*Z^(5/6:ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^(5/6-2*d+α))*L^2/(q*Z^(5/6:ℝ)) := by field_simp
      _≤(C*H^n*Z^(5/6-2*d+α))*(B*Z^d)^2/(q*Z^(5/6:ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)) := by ring
      _=_ := by rw [low_inverse_power_cancel Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSelectedBound
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

attribute [local instance] OAI.SevenEighths.ProbePhysical.instFintypeUnitsO_2
lemma gaussianFixedWindow_support : Function.support gaussianFixedWindow⊆Set.Icc (1/2:ℝ) 2 := by
  intro y hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))

lemma lowReflectionMask_bad_ideals (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ∀P∈fixedBadPrimes,P∣Ideal.span {lowReflectionMask η S hS}*(1:Id) := by
  intro P hP
  rw [mul_one,lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,calibrationForSet_span]
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun P : Id=>P) (hbad hP)) _

theorem low_selected_physical_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
    ∀(Z d ell0 shift : ℝ),Z₀≤Z→0≤d→d≤1/6→0≤ell0→ell0≤1/6-d+ε→|shift|≤ε→
    ∀(R : Finset O),(∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*d))→
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
    ∀(J : Finset (Fin K))(H : SelectedSlot J→ℝ),
      (∀i,1≤H i)→(∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i)→(∏i,H i)≤Z^ell0→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) (Z^(1+ell0+shift)) t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((5/6-2*d)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := InverseReflectedPhase.low_original_completed_energy
    (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
    (1:Id) squarefree_one (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
    (lowReflectionMask_bad η S hS hbad).1 (lowReflectionMask_bad η S hS hbad).2
    (lowReflectionMask_period η S hS) (lowReflectionMask_bad_ideals η S hS hbad)
    (1/2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy+1)*((Fintype.card RayCharacter:ℝ)+1)*6*C
  have hC0 : 0<C0 := by have hh := lowCorrectionEnergy_nonneg;dsimp [C0];positivity
  refine ⟨degree,C0,Z₀,hC0,hZ₀,?_⟩
  intro Z d ell0 shift hZ hd hd1 hell hellcap hshift R hR T hT hout hdis J H hH1 hH hprod W hW Y t σ
  let L := fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList η S hS (T i.val)⊆T i.val := Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) : ∀P∈lowPeriodPrimeList η S hS (T i.val),Supported P.val :=
    fun P hP=>hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j=>Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint η S hS _
      (fun i j hij=>hdis (fun h=>hij (Subtype.ext h))))
  have hparents : ∀I∈lowIdealRows R,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) :=
    fun I hI=>⟨lowIdealRows_nonzero R (fun z hz=>(hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz=>(hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  have hrow (χ : RayCharacter) (u : Oˣ) :
      (∑I∈lowIdealRows R,‖lowActualIdealPolynomial L
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z^(1+ell0+shift))‖^2)≤
          C*(1+‖t‖)^degree*Z^((5/6-2*d)+507*ε) := by
    convert (preTransparency := .instances) he Z d ell0 shift hZ hd hd1 hell hellcap hshift (lowIdealRows R) hparents hcard L H
      hlists (fun i=>lowPrimeIdealList_maximal _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i=>lowPrimeIdealList_prime _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i=>lowPrimeIdealList_norm _ _ (fun P hP=>hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ) (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u t
      (fun i P=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator P.val))
      (fun i P=>low_actual_ideal_weight_bound η (W i.val) (hW i.val) (Y i.val) t P.val) using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT hout hdis J W Y
    (Z^(1+ell0+shift)) t σ R (fun z hz=>(hR z hz).1)).trans
  have hh := Finset.sum_le_sum (fun χ (_ : χ∈(Finset.univ:Finset RayCharacter))=>
    Finset.sum_le_sum (fun u (_ : u∈(Finset.univ:Finset Oˣ))=>hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,low_unit_card] at hm
  simp only [Nat.cast_ofNat,Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0≤(Fintype.card RayCharacter:ℝ) := Nat.cast_nonneg _
  have hzpos : 0≤Z^((5/6-2*d)+507*ε) := Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0≤(1+|t|)^degree := by positivity
  calc
    _=(lowCorrectionEnergy*(Fintype.card RayCharacter:ℝ)*6*C)*(1+|t|)^degree*
        Z^((5/6-2*d)+507*ε) := by ring
    _≤_ := by gcongr <;> linarith

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowNominalEnergy
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_selected_nominal_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (Ck b ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(R : Finset O),
      (∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*lowUnselectedLength ell J))→
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((5/6-2*lowUnselectedLength ell J)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_selected_physical_energy η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  obtain ⟨hd,hd1,hs,hscap⟩ := lowLength_bounds ell hell hsum J
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+ε/2) hc.1 hX
  rw [←hscale]
  apply he Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
    (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J (fun i=>max 1 (b*Z^(ell i.val)))
    (fun i=>le_max_left _ _)
    (fun i P hP=>(hnorm i.val P hP).trans (le_max_right _ _)) (hc.2 J) W hW Y t σ

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPhysicalInverseBound
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_physical_inverse_normalized_oai (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b aCut bCut ε : ℝ) (ha : 0<a) (haCut : 0<aCut) (hbCut : 0<bCut)
    (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J),
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
      ∀(hX0 : 0<Z^(17/48:ℝ)/L)(hY0 : 0<Z^(23/48:ℝ)/L),
      (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) aCut bCut haCut hbCut
          (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) hX0 hY0
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
            η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t)≤
        C*(1+‖t‖)^degree*Z^(507*ε/2) := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0<q := calibration_elementNorm_pos _
  have hc : 0<c := by dsimp [c];positivity
  have hB : 0<B := by dsimp [B];positivity
  let Ck := 2*bCut*(q/c^2)
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,C,ZC,hbound⟩ := low_selected_nominal_energy η S hS hbad ell hell hsum Ck b ε hCk hε hε1
  let C0 := ((Fintype.card RayRing:ℝ)+1)*Real.sqrt (C*B^2/q)/(2*Real.pi)
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
  dsimp only
  let L := elementNorm (∏i : J,(p i).val)
  let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
  intro hX0 hY0
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hL : 0<L := lowUnselectedProduct_norm_pos _
    (fun i n hn=>canonicalSlotSupport_nonzero _ (hT i) n hn) J p
  have hnormE (i : Fin K) (n : O) (hn : n∈canonicalSlotSupport (T i)) :
      a*Z^(ell i)≤elementNorm n ∧ elementNorm n≤b*Z^(ell i) := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hLlo : c*Z^(lowUnselectedLength ell J)≤L :=
    lowUnselectedProduct_norm_lower ell a Z ha hz _ (fun i n hn=>(hnormE i n hn).1) J p
  have hLhi : L≤B*Z^(lowUnselectedLength ell J) :=
    lowUnselectedProduct_norm_upper_nominal ell b Z hz _ (fun i n hn=>(hnormE i n hn).2) J p
  have hQ : 0<Q := lowPhysicalScale_pos _ _ _ hX0 hY0
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
    η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t
  have hrows : ∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*lowUnselectedLength ell J) := by
    intro z hzR
    refine ⟨lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ z hzR,?_⟩
    apply (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ z hzR).trans
    have hh := mul_le_mul_of_nonneg_left
      (lowPhysicalScale_nominal_bound (calibrationForSet S hS) Z L c (lowUnselectedLength ell J) hz hc hLlo)
      (show 0≤2*bCut by positivity)
    simpa only [Ck,mul_assoc] using hh
  have he (σ : RayRing) : (∑z∈R,‖row σ z‖^2)≤
      C*(1+‖t‖)^degree*Z^(5/6-2*lowUnselectedLength ell J+507*ε) :=
    hZ.2 T hT hout hdis (fun i P hP=>(hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW (fun i=>Z^(ell i)) t σ
  have hn (σ : RayRing) : Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q≤
      Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(507*ε/2) := by
    dsimp only [Q]
    rw [lowPhysicalScale_source _ Z L hz]
    exact low_inverse_sqrt_normalized q C B Z L (lowUnselectedLength ell J) (507*ε) (1+‖t‖)
      (∑z∈R,‖row σ z‖^2) degree hq ZC.le hB.le hz hL (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (he σ) hLhi
  change (Real.sqrt Q)⁻¹/(2*Real.pi)*(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2))≤_
  calc
    _=(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q)/(2*Real.pi) := by
      rw [←Finset.sum_div]
      ring
    _≤(∑σ : RayRing,Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(507*ε/2))/(2*Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _=>hn σ)) (by positivity)
    _≤_ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [C0]
      calc
        _=((Fintype.card RayRing:ℝ)*Real.sqrt (C*B^2/q)/(2*Real.pi))*(1+|t|)^degree*Z^(507*ε/2) := by ring
        _≤_ := by gcongr ; linarith

end SevenEighths.ProbePhysical
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbePhysical.low_physical_inverse_normalized_oai := @OAI.SevenEighths.ProbePhysical.low_physical_inverse_normalized_oai

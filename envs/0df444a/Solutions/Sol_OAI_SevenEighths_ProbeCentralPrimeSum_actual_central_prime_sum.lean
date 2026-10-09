-- Prove2me | solution 1 for OAI.SevenEighths.ProbeCentralPrimeSum.actual_central_prime_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:25:10.245977+00:00
-- url     : https://prove2.me/submissions/b4a1c17c-4356-4b23-b980-9ad353a1ec85

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_ProbeCentralAllSlots_actual_three_branch_slots
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_buffered_rectangle_reciprocal_bound
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_calibrated_prime_slots_separate
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_continuedCorrection_first_subpower

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorBounds
namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

section QuotientBounds

variable {R : Type*} [CommRing R]

theorem quotient_inf_card_le_mul (I J : Ideal R) [Finite (R ⧸ I)] [Finite (R ⧸ J)] :
    Nat.card (R ⧸ I ⊓ J) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  let f : R ⧸ I ⊓ J →+* (R ⧸ I) × (R ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

end QuotientBounds

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem absNorm_inf_le_mul (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    (I ⊓ J).absNorm ≤ I.absNorm * J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_inf_card_le_mul I J

end

end SevenEighths.FiniteConductor

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

lemma prod_primeSet {M : Type*} [CommMonoid M] (I : Ideal ActualEisensteinCubic.O) (f : Ideal ActualEisensteinCubic.O→M) :
    (∏P∈primeSet I,f P.val)=∏P∈primeSupport I,f P := by
  unfold primeSet
  rw [Finset.prod_image]
  · exact Finset.prod_attach (primeSupport I) f
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

end

open ActualEisensteinCubic

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

end SmoothMobiusCorrection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ReciprocalBound
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖CubicEisenstein.fullIdealWeight s I‖ ≤
      ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖ := by
  by_cases hI : I = 0
  · simp [hI, CubicEisenstein.fullIdealWeight]
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [CubicEisenstein.fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

end SevenEighths.HeckeReciprocalBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.StripActual
namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set MeasureTheory
namespace SevenEighths.HeckeStripActual
open HeckeFamily HeckePrimitive

variable (c : O) [NeZero c]

theorem LFunction_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖LFunction η s‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series η hs1, IdealEuler.series]
  have hsum := IdealEuler.weighted_summable_norm (idealCoeff η) (idealCoeff_norm_le_one η) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖idealCoeff η I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I)).trans
    (HeckeReciprocalBound.normWeight_le_of_re_ge hs I)

end SevenEighths.HeckeStripActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Conductor
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => HeckeFamily.O

theorem rawRow_conductor (u : FreeRow) :
    (rawRow u).modulus.absNorm≤ conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  have hb := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).1
  change (rawRow u).modulus.absNorm≤_ at hb
  simpa [rowConductorBound,conductorConstant,fixedSourcePrincipal,HeckeRayFamily.character,
    Character.ofResidue] using hb

theorem rowCharacter_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).modulus.absNorm≤
      conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((rawRow u).modulus*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (rawRow_conductor u)

theorem targetRow_conductor (η : Character) (u : FreeRow) :
    (targetRow η u).modulus.absNorm≤η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Finite (O ⧸ (rawRow u).modulus) := Ring.HasFiniteQuotients.finiteQuotient (rawRow u).modulus_ne_bot
  change (η.modulus⊓(rawRow u).modulus).absNorm≤_
  calc
    _ ≤ η.modulus.absNorm*(rawRow u).modulus.absNorm :=
      FiniteConductor.absNorm_inf_le_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left η.modulus.absNorm (rawRow_conductor u)

theorem targetRow_excluded_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) :
    ((targetRow η u).excludePrimes S hS).modulus.absNorm≤
      η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((targetRow η u).modulus*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (targetRow_conductor η u)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRowRadicalConductor
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem fixedConductorConstant_pos (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : 0 < fixedConductorConstant S := by
  have hnorm (I : Ideal O) (hI : I ≠ 0) : 0 < I.absNorm :=
    Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  unfold fixedConductorConstant ProbeHighRowFamily.conductorConstant
  exact mul_pos (mul_pos
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr ProbeHighRowFamily.rowMaskElement_ne_zero))
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))))
    (hnorm _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))

end SevenEighths.ProbeRowRadicalConductor

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RowReflectedAllocation
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ComplexConjugate
open Set Complex
namespace SevenEighths.ProbeRowReflectedAllocation
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeFiniteDeletion HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma original_row_conductor_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((rowCharacter S hS u).modulus.absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm := by
  exact_mod_cast (by simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm]
    using rowCharacter_conductor S hS u)

lemma original_row_deletion_radical_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm :=
  by
    let χ := rowCharacter S hS u
    have hd : radical χ.modulus ∣ χ.modulus := by
      unfold radical SmoothMobiusCorrection.primeProduct
      rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O => J)]
      exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
    have hn : ((radical χ.modulus).absNorm : ℝ) ≤ χ.modulus.absNorm := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
    exact hn.trans (original_row_conductor_le S hS u)

end SevenEighths.ProbeRowReflectedAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralRepeatedProduct
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedProduct
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CompletedGauss ProbeRowReflectedAllocation
open HeckeDeletionBounds HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

lemma rowCost_nonneg (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : 0≤ rowCost S hS u a e eps T := by
  unfold rowCost presentationComplexity HeckeLogarithmic.complexity
  positivity

end SevenEighths.ProbeCentralRepeatedProduct

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralCosts
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

lemma centralRowScalar_split (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) :
    centralRowScalar S hS hmax η u x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      centralRemainingScalar S hS η u x w z := by
  unfold centralRowScalar centralRemainingScalar
  ring

theorem centralRemainingScalar_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : SourceExclusions S),FirstTail (4*e) S →
      ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤C*
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps := by
  obtain ⟨Ch,hCh,hh⟩ := continuedCorrection_first_subpower eps heps
  obtain ⟨Cr,hCr,hr⟩ := buffered_rectangle_reciprocal_bound e eps he he' heps
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨(L+1)*Cr*Ch,by positivity,?_⟩
  intro S hS hfirst η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L+1 :=
    (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2)
      (by simp only [Complex.mul_re];rw [hz];norm_num)).trans (by linarith)
  have hc := hh (4*e) S hS hfirst η u x w z
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith)
  have hrec := hr (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
    (Sum.inl false) x (by rw [hx]) (by rw [hx];linarith) hxi
  simp only [sourceDetectorFamily_denominator] at hrec
  unfold centralRemainingScalar
  rw [norm_mul,norm_mul]
  apply (mul_le_mul (mul_le_mul hl hrec (norm_nonneg _) (by linarith)) hc (norm_nonneg _)
    (mul_nonneg (by linarith) (mul_nonneg hCr.le (Real.rpow_nonneg (by
      unfold presentationComplexity HeckeLogarithmic.complexity;positivity) _)))).trans
  exact le_of_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma rowNorm_ge_one (u : FreeRow) : 1≤ rowNorm u := by
  unfold rowNorm
  have hn : (Ideal.span {u.val}:Ideal O)≠⊥ := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralRowCost
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeCentralRepeatedProduct
open ProbeRowReflectedAllocation ProbeRowRadicalConductor HeckeReciprocalGrowth HeckeDeletionBounds
local notation "O" => HeckeFamily.O

private lemma cost_power_identity (N L A R eps : ℝ) (hN : 0<N) (hL : 0<L) :
    N^A*N^R*L^2*(2*N^2*L^2)^eps=
      (2:ℝ)^eps*N^(A+R+2*eps)*L^(2+2*eps) := by
  have hp : (2*N^2*L^2)^eps=(2:ℝ)^eps*N^(2*eps)*L^(2*eps) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
    rw [←Real.rpow_two N,←Real.rpow_two L,←Real.rpow_mul hN.le,←Real.rpow_mul hL.le]
  rw [hp]
  calc
    _ = (2:ℝ)^eps*(N^A*N^R*N^(2*eps))*(L^2*L^(2*eps)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN,←Real.rpow_add hN,←Real.rpow_two L,←Real.rpow_add hL]

theorem central_rowCost_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (e eps : ℝ) (he : 0<e) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow) (a H : ℝ),51/100≤a → a≤1 → 0≤H →
      rowCost S hS u a e eps H≤
        C*rowNorm u^(a-1/2+12*e+4*eps)*(3+H)^(2+2*eps) := by
  let F : ℝ := fixedConductorConstant S
  have hF : 1≤F := by
    dsimp [F]
    exact_mod_cast fixedConductorConstant_pos S hS
  have hFp : 0<F := zero_lt_one.trans_le hF
  refine ⟨(2:ℝ)^eps*F^(1/2+12*e+4*eps),by positivity,?_⟩
  intro u a H ha ha1 hH
  let N : ℝ := F*rowNorm u
  let L : ℝ := 3+H
  let A : ℝ := a-1/2+6*e
  let R : ℝ := 6*e+2*eps
  have hn : 0< rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hN : 0<N := mul_pos hFp hn
  have hL : 0<L := by dsimp [L];linarith
  have hA : 0≤A := by dsimp [A];linarith
  have hR : 0≤R := by dsimp [R];positivity
  have hrad : ((radical (rowCharacter S hS u).modulus).absNorm:ℝ)≤N :=
    original_row_deletion_radical_le S hS u
  have hq : ((rowCharacter S hS u).modulus.absNorm:ℝ)≤N := original_row_conductor_le S hS u
  have hc : presentationComplexity (rowCharacter S hS u) H≤2*N^2*L^2 := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    rw [abs_of_nonneg hH]
    calc
      _ ≤ N*(2*N*L^2) := by
        apply mul_le_mul hrad _ (by positivity) hN.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) (sq_nonneg L)
      _ = _ := by ring
  have hrpow := Real.rpow_le_rpow (show (0:ℝ)≤(radical (rowCharacter S hS u).modulus).absNorm by positivity) hrad hR
  have hcpow := Real.rpow_le_rpow (show 0≤presentationComplexity (rowCharacter S hS u) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity) hc heps.le
  have hbound : rowCost S hS u a e eps H≤N^A*N^R*L^2*(2*N^2*L^2)^eps := by
    unfold rowCost
    apply mul_le_mul _ hcpow (Real.rpow_nonneg (by
      unfold presentationComplexity HeckeLogarithmic.complexity;positivity) _) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg hN.le _)
  rw [cost_power_identity N L A R eps hN hL] at hbound
  have hexp : A+R+2*eps=a-1/2+12*e+4*eps := by dsimp [A,R];ring
  rw [hexp] at hbound
  apply hbound.trans
  dsimp only [N]
  rw [Real.mul_rpow hFp.le hn.le]
  have hf := Real.rpow_le_rpow_of_exponent_le hF
    (show a-1/2+12*e+4*eps≤1/2+12*e+4*eps by linarith)
  calc
    _ = ((2:ℝ)^eps*F^(a-1/2+12*e+4*eps))*rowNorm u^(a-1/2+12*e+4*eps)*L^(2+2*eps) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn.le _)
      exact mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg (by norm_num) _)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma presentationComplexity_norm_bound (χ : Character) (H : ℝ) :
    presentationComplexity χ H≤2*(χ.modulus.absNorm:ℝ)^2*(3+|H|)^2 := by
  have hd : radical χ.modulus∣χ.modulus := by
    unfold radical SmoothMobiusCorrection.primeProduct
    rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O=>J)]
    exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
  have hn : ((radical χ.modulus).absNorm:ℝ)≤χ.modulus.absNorm := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
  unfold presentationComplexity HeckeLogarithmic.complexity
  calc
    _ ≤ (χ.modulus.absNorm:ℝ)*(2*χ.modulus.absNorm*(3+|H|)^2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by ring

lemma target_complexity_norm_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H : ℝ) (hH : 0≤H) :
    presentationComplexity ((targetRow η u).excludePrimes S hS) H≤
      2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2 := by
  have hn : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤
      (fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u := by
    unfold rowNorm
    exact_mod_cast (by simpa only [fixedConductorConstant,mul_assoc,mul_comm,mul_left_comm] using
      targetRow_excluded_conductor S hS η u)
  apply (presentationComplexity_norm_bound _ H).trans
  rw [abs_of_nonneg hH]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) (by unfold rowNorm;positivity)).mpr hn) (by norm_num)

lemma target_complexity_power_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H eps : ℝ) (hH : 0≤H) (heps : 0≤eps) :
    (presentationComplexity ((targetRow η u).excludePrimes S hS) H)^eps≤
      (2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps) := by
  have hb := Real.rpow_le_rpow (show 0≤presentationComplexity ((targetRow η u).excludePrimes S hS) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity)
    (target_complexity_norm_bound S hS η u H hH) heps
  apply hb.trans_eq
  rw [show 2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2=
    (2*(fixedConductorConstant S:ℝ)^2)*(η.modulus.absNorm:ℝ)^2*rowNorm u^2*(3+H)^2 by ring]
  rw [Real.mul_rpow (by unfold rowNorm;positivity) (by positivity),
    Real.mul_rpow (by positivity) (by unfold rowNorm;positivity),Real.mul_rpow (by positivity) (by positivity)]
  rw [←Real.rpow_two (η.modulus.absNorm:ℝ),←Real.rpow_two (rowNorm u),←Real.rpow_two (3+H),
    ←Real.rpow_mul (by positivity : (0:ℝ)≤η.modulus.absNorm),
    ←Real.rpow_mul (rowNorm_ge_one u |>.trans' (by norm_num : (0:ℝ)≤1)),
    ←Real.rpow_mul (by linarith : 0≤3+H)]

theorem centralRemainingScalar_arithmetic_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(3*eps)*(3+H)^(2*eps) := by
  obtain ⟨C,hC,hbound⟩ := centralRemainingScalar_bound e eps he he' heps
  have hF : 0<(fixedConductorConstant S:ℝ) := by exact_mod_cast fixedConductorConstant_pos S hS.prime
  refine ⟨C*(2*(fixedConductorConstant S:ℝ)^2)^eps,by positivity,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hb := hbound S hS hfirst η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  apply hb.trans
  have hc := target_complexity_power_bound S hS.prime η u H eps hh heps.le
  have hn : 0< rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  calc
    _ ≤ C*rowNorm u^eps*((2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      rw [show 3*eps=eps+2*eps by ring,Real.rpow_add hn]
      ring

theorem central_remaining_rowCost_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps H≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+H)^(2+4*eps) := by
  obtain ⟨C0,hC0,h0⟩ := centralRemainingScalar_arithmetic_bound e eps he he' heps S hS hfirst
  obtain ⟨C1,hC1,h1⟩ := central_rowCost_bound S hS.prime e eps he heps
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hn : 0< rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hL : 0<3+H := by linarith
  have h0' := h0 η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have h1' := h1 u a H ha ha1 hh
  apply (mul_le_mul h0' h1' (ProbeCentralRepeatedProduct.rowCost_nonneg S hS.prime u a e eps H)
    (by positivity)).trans_eq
  have hnp : rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps)=
      rowNorm u^(a-1/2+12*e+7*eps) := by rw [←Real.rpow_add hn];congr 1;ring
  have hlp : (3+H)^(2*eps)*(3+H)^(2+2*eps)=(3+H)^(2+4*eps) := by
    rw [←Real.rpow_add hL];congr 1;ring
  calc
    _ = C0*C1*(η.modulus.absNorm:ℝ)^(2*eps)*
        (rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps))*
        ((3+H)^(2*eps)*(3+H)^(2+2*eps)) := by ring
    _ = _ := by rw [hnp,hlp]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralPrimeSum
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralPrimeSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralAllSlots
local notation "O" => HeckeFamily.O

theorem actual_central_prime_sum_oai (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j P,P∈T j→P.val∉S),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      |x.im|≤(3*i+2:ℕ)*T0 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
        (fun j=>hPS j (P j).val (P j).property) W Y x w z‖ ≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Ca,hCa,hall⟩ := actual_three_branch_slots N e eps c d B he he1 heps hc hd hB
  obtain ⟨Cb,hCb,hcost⟩ := central_remaining_rowCost_bound e eps he he1 heps S hS hfirst
  refine ⟨Ca*Cb,mul_pos hCa hCb,?_⟩
  intro u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hPS hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hxi hwi p hp hphase
  let hs : ∀j P,P∈T j→Supported P.val := fun j P hP=>outside_prime_supported S hS.bad P (hPS j P hP)
  have hinj (P : ∀j,T j) : Function.Injective (fun j=>(P j).val) := by
    intro j l hh
    change (P j).val=(P l).val at hh
    by_contra hne
    exact Finset.disjoint_left.mp (hdis j l hne) (P j).property (by rw [hh];exact (P l).property)
  have ha' := hall S hS.prime hmax hS.bad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
    W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  have hc' := hcost η u twists T0 a ((3*i+2:ℕ)*T0) i hT0 ha ha1 le_rfl hbin x w z hx hw hz hxi
  have hN : 0< rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hy : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (zero_le_one.trans (hY j)) _)
  have hpp : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hinj W Y a e x w z
    hfirst ha ha1 he he1.le hx hw hz hQ hη hsmall,centralRowScalar_split,norm_mul,norm_mul]
  have hn := mul_le_mul_of_nonneg_left ha' (norm_nonneg (centralRemainingScalar S hS η u x w z))
  have hc'' := mul_le_mul_of_nonneg_right hc'
    (show 0≤Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) by positivity)
  have hpow : rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1))=
      rowNorm u^(a-1/2+12*e+eps*(N+8)) := by
    rw [←Real.rpow_add hN]
    congr 1
    ring
  calc
    _ = ‖centralRemainingScalar S hS η u x w z‖*
      (‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖) := by ring
    _ ≤ ‖centralRemainingScalar S hS η u x w z‖*
      (Ca*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0)*
        rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hn
    _ = (‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by ring
    _ ≤ (Cb*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+(3*i+2:ℕ)*T0)^(2+4*eps))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hc''
    _ = _ := by
      calc
        _ = Ca*Cb*(η.modulus.absNorm:ℝ)^(2*eps)*(rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1)))*
          (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hpow]
end SevenEighths.ProbeCentralPrimeSum

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.ProbeCentralPrimeSum.actual_central_prime_sum_oai.{u_1} := @OAI.SevenEighths.ProbeCentralPrimeSum.actual_central_prime_sum_oai.{u_1}

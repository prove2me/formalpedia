-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous.actual_main_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:55:06.471208+00:00
-- url     : https://prove2.me/submissions/879829aa-5577-4f0e-a171-a99a26726017

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalMainGaussian_actual_main_gaussian_from_bands

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
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

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

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

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CompleteCommon
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem commonPart_ne_zero (I J : Ideal O) : commonPart I J ≠ 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_ne_zero _ _

theorem reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

theorem residualPart_self (I : Ideal O) : residualPart I I = 1 := by
  simp only [residualPart, Finset.sdiff_self, Finset.prod_empty]

theorem commonPart_self (I : Ideal O) (hI : I ≠ 0) : commonPart I I = I := by
  have h := reconstruct I I hI
  rw [residualPart_self, mul_one] at h
  exact h.symm

end SevenEighths.CenteredMomentCompleteCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstFamily
open CenteredMomentFirstColumns CenteredMomentPrimitive CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem first_displayed_norm (η : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) :
    (η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}).absNorm =
    η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏ P∈E,P.val).absNorm*(Ideal.span {activeConductor I J}).absNorm) := by
  rw [← Ideal.span_singleton_mul_span_singleton,primeSubsetGenerator,span_idealGenerator]
  simp only [map_mul]

end SevenEighths.CenteredMomentFirstCanonicalFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondLedger
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondLedger
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentPartition CenteredMomentProductCRT ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

section Global
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem log_norm_power_product (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c : ι → ℕ) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) =
      ∑ i, (c i : ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]
  rw [Real.logb_prod _ _ (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)))]
  simp only [Real.logb_pow]

omit [Fintype ι] [DecidableEq ι] in
theorem log_norm_radical (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (S : Finset ι) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) =
      ∑ i ∈ S, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,Nat.cast_prod]
  exact Real.logb_prod _ _ (fun i _ => Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))

end Global

end SevenEighths.CenteredMomentSecondLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonical
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonPrime_supported_ideal (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported P.val :=
  supported_of_dvd P.val C hC
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))

theorem commonPrime_span (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Ideal.span {commonPrime C D P}=P.val :=
  primary_span_supported P.val (commonPrime_supported_ideal C D hC P)

theorem commonPrime_supported (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact commonPrime_supported_ideal C D hC P

theorem commonPart_eq_left (C D : Ideal O) (hC : C≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) : commonPart C D=C := by
  have hs : commonSupport C D=commonSupport C C := by
    change CompletedGauss.primeSupport C∩CompletedGauss.primeSupport D=
      CompletedGauss.primeSupport C∩CompletedGauss.primeSupport C
    rw [hCD]
  calc
    commonPart C D=commonPart C C := by unfold commonPart;rw [hs]
    _=C := commonPart_self C hC

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalLedger
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentForcing
local notation "O" => ActualEisensteinCubic.O

theorem span_finset_product {ι : Type*} (S : Finset ι) (p : ι→O) :
    Ideal.span {∏ i∈S,p i}=∏ i∈S,Ideal.span {p i} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi,
      ←Ideal.span_singleton_mul_span_singleton,ih]

theorem commonFrequencyGenerator_span (C D : Ideal O) (_hC : Supported C) :
    Ideal.span {commonFrequencyGenerator C D}=
      commonIdeal (commonPrime C D) (leftExponent C D) (rightExponent C D) := by
  simp only [commonFrequencyGenerator,span_finset_product,←Ideal.span_singleton_pow,commonIdeal]

end SevenEighths.CenteredMomentSecondCanonicalLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstScale
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem active_norm_pos (I J : Ideal O) :
    0<(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ) := by
  apply norm_pos
  exact Ideal.span_singleton_eq_bot.not.mpr (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)

end SevenEighths.CenteredMomentFirstScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DescentLedger
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentSecondLedger CenteredMomentPartitionNorm
local notation "O" => ActualEisensteinCubic.O

section ActualSecond
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_log_ge_unit (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (unitIdeal p U) : ℝ) ≤
      Real.logb Z (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  rw [unitIdeal,log_norm_radical p hp,commonIdeal,log_norm_power_product p hp]
  calc
    _ ≤ ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro i hi hni
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
        Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
      have hm : (1:ℝ) ≤ (min (c i) (d i) : ℕ) := by exact_mod_cast le_min (hc i) (hd i)
      nlinarith

end ActualSecond

end SevenEighths.CenteredMomentDescentLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonRawScale
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem plainNorm_pos (B : Tuple ι) (hB : ∀ i,B i≠0) : 0<plainNorm B := by
  unfold plainNorm
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB _))

omit [Fintype ι] in
theorem frozenScale_pos (B : Tuple ι) (P : ι → ℝ) (hP : ∀ i,0<P i) (i : ι) :
    0<frozenScale B P i := by
  unfold frozenScale
  split_ifs
  · exact zero_lt_one
  · exact hP i

theorem rawReduction_pos (B : Tuple ι) (hB : ∀ i,B i≠0) (P : ι → ℝ) (hP : ∀ i,0<P i) :
    0< rawReduction B P := mul_pos (plainNorm_pos B hB) (Finset.prod_pos (fun i _ => frozenScale_pos B P hP i))

theorem slot_scale_split (B : Tuple ι) (P : ι → ℝ) :
    (∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)=∏ i,P i := by
  rw [Finset.prod_coe_sort (liveIndices B) P]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1) P]
  unfold frozenScale liveIndices
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  ring

theorem raw_scale_identity (B : Tuple ι) (hB : ∀ i,B i≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B T P*rawReduction B P=T*∏ i,P i := by
  unfold remainingRaw rawReduction
  have h := slot_scale_split B P
  calc
    _ = T*((∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)) := by
      field_simp [(plainNorm_pos B hB).ne']
    _ = _ := by rw [h]

theorem product_norm (B : Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct B):ℝ)=plainNorm B*∏ i,(Ideal.absNorm (B (Sum.inl i)):ℝ) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,map_mul,map_prod,
    Nat.cast_mul,Nat.cast_prod,plainNorm]
  ring

theorem frozen_window_ne_zero (B : Tuple ι) (C R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (hne : frozenCoefficient B C R ν Wslot P≠0) (i : ι) (hi : B (Sum.inl i)≠1) :
    Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i)≠0 := by
  have hp := (mul_ne_zero_iff.mp hne).1
  have hx := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  exact (mul_ne_zero_iff.mp hx).2

theorem actual_reduction_norm (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (hP : ∀ i,0<P i)
    (a b : ℝ) (ha : 0<a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (hne : frozenCoefficient B C R ν Wslot P≠0) :
    (min 1 a)^Fintype.card ι*rawReduction B P≤(Ideal.absNorm C:ℝ) ∧
      (Ideal.absNorm C:ℝ)≤(max 1 b)^Fintype.card ι*rawReduction B P := by
  have hi (i : ι) : min 1 a*frozenScale B P i≤(Ideal.absNorm (B (Sum.inl i)):ℝ) ∧
      (Ideal.absNorm (B (Sum.inl i)):ℝ)≤ max 1 b*frozenScale B P i := by
    by_cases h : B (Sum.inl i)=1
    · simp only [frozenScale,h,ite_true,map_one,Nat.cast_one,mul_one]
      exact ⟨min_le_left _ _,le_max_left _ _⟩
    · have hs := hW i (frozen_window_ne_zero B C R ν Wslot P hne i h)
      rw [frozenScale,if_neg h]
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (hP i).le)
          ((le_div_iff₀ (hP i)).mp hs.1),
        le_trans ((div_le_iff₀ (hP i)).mp hs.2)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (hP i).le)⟩
  rw [←hprod,product_norm]
  constructor
  · have hh := Finset.prod_le_prod (s:=Finset.univ)
      (fun i _ => mul_nonneg (le_of_lt (lt_min zero_lt_one ha)) (frozenScale_pos B P hP i).le)
      (fun i _ => (hi i).1)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'
  · have hh := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => Nat.cast_nonneg (Ideal.absNorm (B (Sum.inl i))))
      (fun i _ => (hi i).2)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'

end SevenEighths.CenteredMomentCommonRawScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonRadialData
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma Input.slot_support (s:Input ι) (i:ι) : Function.support (s.W i)⊆Set.Icc s.lower s.upper :=
  fun _x hx=>⟨(s.lower_le i).trans (s.support i hx).1,((s.support i hx).2).trans (s.upper_ge i)⟩

end SevenEighths.CenteredMomentCommonRadialData

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowBudget
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy

theorem profileMoment_nonneg (J : ℕ) : 0≤profileMoment J :=
  integral_nonneg (fun w=>by positivity)

theorem heightEnvelope_pos (t : ℝ) : 0<heightEnvelope t := by unfold heightEnvelope;positivity

end SevenEighths.CenteredMomentSecondWindowBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dirichlet
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

variable [NeZero q]

end SevenEighths.HeckeDirichlet

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentFirstAmplificationChoice
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentSectorLocalization CenteredMomentPrimePool
open CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal
local notation "O" => ActualEisensteinCubic.O

theorem ballProfile_one (x : ℝ) (hx : 0≤x) (hx1 : x≤1) : ballProfile x=1 := by
  simp only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1,Complex.ofReal_one]

open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open ConcretePrimeRowBridge CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFactor

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical ActualEisensteinCubic

end SevenEighths.CenteredMomentFirstAmplificationChoice

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplificationChildSourceCaps
open ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEq_solutions_r6966ea_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
lemma norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤I.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma allocation_product (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2

lemma allocation_ne (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←allocation_product s C B]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

theorem common_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)=
      CenteredMomentAmplificationChildInput.volume s/rawReduction B.val s.P := by
  have hh:=raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  change _ = CenteredMomentAmplificationChildInput.volume s at hh
  rw [←hh]
  congr 1
  unfold CenteredMomentAmplificationChildInput.volume child commonData remainingRaw plainNorm
  dsimp only
  ring

lemma live_card_le (B : Tuple ι) : Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa only [Fintype.card_coe] using (Finset.card_le_univ (liveIndices B))

theorem common_volume_le (N : ℕ) (b : ℝ) (hb : 1≤b) (s : Input ι)
    (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)≤
      b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ) := by
  have hc:=norm_ge_one C (allocation_ne s C B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx=>⟨(s.slot_support i hx).1,((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn':(C.absNorm:ℝ)≤b^N*rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  rw [common_volume]
  apply (div_le_div_iff₀ hr (zero_lt_one.trans_le hc)).mpr
  nlinarith [CenteredMomentAmplificationChildInput.volume_pos s]

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalLedger
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFirstPhysicalLedger
open CenteredMomentFirstScale CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O

theorem nominal_log (I J E : Ideal O) (hE : E≠0)
    (Z H X : ℝ) (hH : 0<H) (hX : 0<X) :
    Real.logb Z (firstNominalScale I J E H X)=
      2*Real.logb Z X-Real.logb Z ((commonPart I J).absNorm:ℝ)-
        Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)+
        Real.logb Z (E.absNorm:ℝ)-Real.logb Z H := by
  have hc:=norm_pos _ (commonPart_ne_zero I J)
  have hd:=norm_pos _ (commonPart_ne_zero J I)
  have he:=norm_pos E hE
  have hr:=active_norm_pos I J
  unfold firstNominalScale
  rw [Real.logb_div (mul_pos (mul_pos he hr) (sq_pos_of_pos hX)).ne'
      (mul_pos (mul_pos hH hc) hd).ne',
    Real.logb_mul (mul_pos he hr).ne' (sq_pos_of_pos hX).ne',
    Real.logb_mul he.ne' hr.ne',Real.logb_pow,
    Real.logb_mul (mul_pos hH hc).ne' hd.ne',Real.logb_mul hH.ne' hc.ne']
  push_cast
  ring

end SevenEighths.CenteredMomentFirstPhysicalLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

lemma physicalBlock_live_rows (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

end SevenEighths.CenteredMomentSecondLiveBlock

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicRowSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
local notation "O"=>HeckeFamily.O

 theorem mem_dyadicRows (rows:Finset O)(n:Fin 4→ℤ)(z:O):
    z∈dyadicRows rows n ↔ z∈rows ∧ dyadicWeight (n 1) (normValue z)≠0:=
  Finset.mem_filter

 theorem dyadicRows_norm (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):
    dyadicScale (n 1)/4<normValue z ∧ normValue z<dyadicScale (n 1):=
  dyadicWeight_support (n 1) ((mem_dyadicRows rows n z).mp hz).2

 theorem dyadicRows_nonzero (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):z≠0:=by
  have hn:0<normValue z:=(div_pos (dyadicScale_pos (n 1)) (by norm_num)).trans
    (dyadicRows_norm rows n z hz).1
  intro he
  simp only [he,normValue_eq_embedding,map_zero,norm_zero,zero_pow (by decide : 2≠0)] at hn
  exact (lt_irrefl 0) hn

 theorem physicalBlock_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows rows n) W K n:=by
  unfold physicalBlock dyadicRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hd:dyadicWeight (n 1) (normValue z)=0
  · simp only [hd,ne_eq,not_true_eq_false,mul_zero,zero_mul,
      Complex.ofReal_zero,Finset.sum_const_zero,ite_self]
  · simp only [hd,ne_eq,not_false_eq_true,ite_true]

 theorem physicalBlock_live_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows (liveRows C D U R rows) n) W K n:=
  (physicalBlock_live_rows η t S β C D hC hD U R rows W K n).trans
    (physicalBlock_dyadic_rows η t S β C D hC hD U R _ W K n)

end SevenEighths.CenteredMomentSecondDyadicRowSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondActualWidth
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActualWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondRadicalBudget CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentSupport CenteredMomentDescentLedger
open CenteredMomentPartitionNorm CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem actual_common_log_ge_unit (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤Real.logb Z (normValue (commonFrequencyGenerator C D)) := by
  have hh:=common_log_ge_unit (commonPrime C D) (commonPrime_supported C D hC)
    (leftExponent C D) (rightExponent C D) (leftExponent_pos C D) (rightExponent_pos C D) U Z hZ
  rw [←commonFrequencyGenerator_span C D hC] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,normValue] using hh

end SevenEighths.CenteredMomentSecondActualWidth

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondChildRadialWidth
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondChildRadialWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondActualWidth
local notation "O" => HeckeFamily.O

theorem physicalBlock_live_dyadic_witness (η:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z∈liveRows C D U R rows ∧ z∈dyadicRows rows n ∧
      z≠0 ∧ dyadicScale (n 1)<4*normValue z := by
  rw [physicalBlock_live_dyadic_rows η t S β C D hC hD U R rows W K n] at hne
  unfold physicalBlock at hne
  obtain ⟨z,hz,_⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hl,hd⟩:=(mem_dyadicRows _ n z).mp hz
  have hz':z∈dyadicRows rows n:=(mem_dyadicRows rows n z).mpr
    ⟨(Finset.mem_filter.mp hl).1,hd⟩
  exact ⟨z,hl,hz',dyadicRows_nonzero rows n z hz',by
    have hh:=(dyadicRows_norm rows n z hz').1
    linarith⟩

section Family
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)

include h hK hne

theorem dyadic_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ)) := by
  obtain ⟨z,hzl,_,hz0,hscale⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  have hw:=(h.physical_budget t S β R rows W K hK n hne χ).2 Z hZ z hzl
  have hh:=Real.logb_le_logb_of_le hZ (dyadicScale_pos (n 1)) hscale.le
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) (normValue_pos z hz0).ne'] at hh
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*(fixedFactor:ℝ))=
      Real.logb Z (4:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul (by norm_num : (4:ℝ)≠0) (by positivity : 4*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

omit h hK hne in

theorem radial_support_bound (Φ:ℝ→ℂ)(b:ℝ)
    (hs:Function.support Φ⊆Set.Iic b)(y:O)
    (hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y≤b*dyadicScale (n 1) :=
  (div_le_iff₀ (dyadicScale_pos (n 1))).mp (hs hy)

theorem radial_radius_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hh:=dyadic_log_budget h t S β R rows W K hK n hne Z hZ χ
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*(fixedFactor:ℝ))=
      Real.logb Z b+Real.logb Z (16*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hb.ne' (by positivity : 16*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [Real.logb_mul hb.ne' (dyadicScale_pos (n 1)).ne',hf]
  linarith

end Family

end SevenEighths.CenteredMomentSecondChildRadialWidth

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplifiedChildWidth
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedChildWidth
open ActualEisensteinCubic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondActualWidth
open CenteredMomentSecondCanonical CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem modulus_pos (η:Character) : 0<(η.modulus.absNorm:ℝ) :=
  norm_pos _ η.modulus_ne_bot

theorem canonical_modulus_log (η ρ:Character)(m:O)(hm:m≠0)
    (I J:Ideal O)(A:Finset (CommonIndex I J))(Z:ℝ)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    Real.logb Z (ρ.modulus.absNorm:ℝ)=
      Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((∏P∈A,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
  have he:0<((∏P∈A,P.val).absNorm:ℝ) := by
    apply norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [hmod,first_displayed_norm]
  push_cast
  rw [Real.logb_mul (mul_pos (mul_pos (modulus_pos η) (span_pos m hm))
      (span_pos 72 (by norm_num))).ne' (mul_pos he (active_norm_pos I J)).ne',
    Real.logb_mul (mul_pos (modulus_pos η) (span_pos m hm)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (modulus_pos η).ne' (span_pos m hm).ne',
    Real.logb_mul he.ne' (active_norm_pos I J).ne']
  ring

theorem main_nominal_bound (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)
    (A:Finset (CommonIndex I J))(K X Z σ δ reserve:ℝ)
    (hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    2*Real.logb Z (X/(commonPart I J).absNorm)-
      Real.logb Z (mainCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve)+
      Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)-
      2*σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [Real.logb_div hX.ne' (norm_pos _ (commonPart_ne_zero I J)).ne',
    mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    nominalLog,CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX,
    canonical_modulus_log η ρ m hm I J A Z hmod]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) (0:ℝ)]

theorem physical_radial_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C D))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hw:=radial_radius_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W L hL n hne Z hZ χ b hb
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (div_pos (sq_pos_of_pos hH) hL).ne',
    Real.logb_div (sq_pos_of_pos hH).ne' hL.ne',Real.logb_pow] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      2*Real.logb Z H-Real.logb Z L+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
    push_cast at hl
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : (16:ℝ)*b*fixedFactor≠0)]
    congr 1
    ring
  rw [hf]
  linarith

theorem physical_declared_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  linarith

theorem first_fixed_log_le (Z:ℝ)(hZ:1<Z) :
    Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)≤Real.logb Z presentationFactor := by
  apply Real.logb_le_logb_of_le hZ (span_pos 72 (by norm_num))
  have hf:(1:ℝ)≤fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact le_mul_of_one_le_right (span_pos 72 (by norm_num)).le hf

theorem fixedWidthThreshold_spec (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    1<fixedWidthThreshold b Csec σ hb hCs hσ ∧
    ∀Z:ℝ,fixedWidthThreshold b Csec σ hb hCs hσ≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose_spec

section ActualSource
variable (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
  (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
  (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})

local notation "cc" => Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)
local notation "dd" => Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)
local notation "kk" => nominalLog I J (∏P∈A,Subtype.val P) K X Z
local notation "Lm" => mainCommonRadius Z dd kk cc σ δ reserve
local notation "Hx" => X/Ideal.absNorm (commonPart I J)
local notation "parentWidth" => Real.logb Z K+Real.logb Z (Ideal.absNorm (Character.modulus η):ℝ)+Real.logb Z (Ideal.absNorm (Ideal.span (Singleton.singleton m)):ℝ)
include σ δ reserve hm hK hX hZ hmod

theorem main_nominal_fixed :
    2*Real.logb Z Hx-Real.logb Z Lm+Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-2*σ-δ-reserve := by
  have hh:=main_nominal_bound η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  linarith [first_fixed_log_le Z hZ]

theorem main_declared_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_declared_width_drop {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤ reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=main_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

end ActualSource
end SevenEighths.CenteredMomentAmplifiedChildWidth

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedChildWidth
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondDyadicRowSupport CenteredMomentSecondRadicalBudget
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstScale CenteredMomentAmplifiedChildWidth
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι]

local instance instDecidableEq_solutions_r6966ea_2 {α:Type*}:DecidableEq α:=Classical.decEq _
lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ) := by
  intro x hx
  by_cases h:0≤x
  · exact (ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

theorem actual_ball_witness (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z≠0 ∧ ballProfile (normValue z/dyadicScale (n 1))=1 := by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  refine ⟨z,hz0,ballProfile_one _ (div_nonneg (normValue_pos z hz0).le (dyadicScale_pos _).le) ?_⟩
  exact (div_le_one (dyadicScale_pos _)).mpr (dyadicRows_norm rows n z hz).2.le

lemma main_nominal_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t K:ℝ)(hK:0<K)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    nominal (child s C R B τ t) K≤geometry N b*((volume s/(C.absNorm:ℝ))^2/K) := by
  have hv:=common_volume_le N b hb s hc hs C R B τ t hne
  have hC:=CenteredMomentAmplificationChildSourceCaps.norm_ge_one C (allocation_ne s C B)
  have hh:0≤volume s/(C.absNorm:ℝ):=div_nonneg (volume_pos s).le (by positivity)
  have hv':volume (child s C R B τ t)≤b^N*(volume s/(C.absNorm:ℝ)):=by simpa only [mul_div_assoc] using hv
  have hp:volume (child s C R B τ t)^2≤(b^N)^2*(volume s/(C.absNorm:ℝ))^2:=by
    nlinarith [volume_pos (child s C R B τ t),mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hh]
  exact (div_le_div_of_nonneg_right hp hK.le).trans_eq (by unfold geometry;ring)

lemma mainRadius_eq (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ):
    mainRadius C D E K V Z σ δ reserve=
      mainCommonRadius Z (Real.logb Z ((commonPart D C).absNorm:ℝ))
        (nominalLog C D (∏P∈E,P.val) K V Z)
        (Real.logb Z ((commonPart C D).absNorm:ℝ)) σ δ reserve := by
  rw [commonPart_eq_left C D hC.1 hCD,commonPart_eq_left D C hD.1 hCD.symm]
  simp only [mainRadius,nominalLog,primeSubsetGenerator,span_idealGenerator]

lemma threshold_gt_one (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ):1<threshold N b σ hb hσ :=
  (fixedWidthThreshold_spec 2 (geometry N b) σ (by norm_num) (geometry_pos N b hb) hσ).1

theorem main_child_width (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ)
    (Z:ℝ)(hlarge:threshold N b σ hb hσ≤Z)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C D R:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (hB:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (K δ reserve ξ q Mparent:ℝ)(hK:0<K)(hδ:0≤δ)(hr:0≤ reserve)(hξ:ξ≤σ/4)
    (hη:(s.η.modulus.absNorm:ℝ)≤Z^q)(hparent:Real.logb Z K+q≤Mparent)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)(hC₂:Supported C₂)(hD₂:Supported D₂)
    (U:Finset (CommonIndex C₂ D₂))(family:RayCharacter→Character)
    (hf:Family τ C₂ D₂ hC₂ hD₂ U family)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hne:physicalBlock τ t S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (nominal (child s C R B τ t) (mainRadius C D E K (volume s) Z σ δ reserve)) Z ξ)
      rows W (mainRadius C D E K (volume s) Z σ δ reserve) n≠0)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)<Mparent-σ/2 := by
  have hZ:1<Z:=(threshold_gt_one N b σ hb hσ).trans_le hlarge
  let L:=mainRadius C D E K (volume s) Z σ δ reserve
  have hL:0<L:=by unfold L mainRadius mainCommonRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have he:=mainRadius_eq C D hC hD hCD E K (volume s) Z σ δ reserve
  have hscale:=main_nominal_cap N b hb s hc hs C R B τ t L hL hB
  have hhscale:nominal (child s C R B τ t) L≤geometry N b*
      ((volume s/((commonPart C D).absNorm:ℝ))^2/L):=by
    simpa only [commonPart_eq_left C D hC.1 hCD] using hscale
  obtain ⟨z,hz,hball⟩:=actual_ball_witness τ t S β C₂ D₂ hC₂ hD₂ U _ rows W L n hne
  have hw:=main_declared_width_drop s.η τ fixedBadMask fixedBadMask_ne_zero C D E
    K (volume s) Z σ δ reserve hK (volume_pos s) hZ hmod hf t S β rows W
    (nominal (child s C R B τ t) L) (geometry N b) ξ (nominal_pos _ L hL)
    (geometry_pos N b hb) (by simpa only [←he] using hhscale) n
    (by simpa only [←he] using hne) χ ballProfile 2 (by norm_num) ball_support z hz
    (by rw [hball];exact one_ne_zero) rfl q hη hσ hδ hr hξ hlarge
  have hlog:Real.logb Z (dyadicScale (n 1))≤Real.logb Z (max 1 (2*dyadicScale (n 1))):=by
    apply Real.logb_le_logb_of_le hZ (dyadicScale_pos _)
    exact (by linarith [dyadicScale_pos (n 1)]:dyadicScale (n 1)≤2*dyadicScale (n 1)).trans (le_max_right _ _)
  linarith

end SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialPointwise CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma mass_one (s : Input ι) : 1≤ mass s :=
  Finset.one_le_prod (fun i _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma mass_nonneg (s : Input ι) : 0≤ mass s := zero_le_one.trans (mass_one s)

end SevenEighths.CenteredMomentFirstChildProfileControl

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondInputCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity
open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonHeightEnvelope
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.instDecidableEq_definitions
lemma lowerFactor_pos (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower):
    0<lowerFactor N slotLower plainLower:=by unfold lowerFactor;positivity

end SevenEighths.CenteredMomentSecondInputCapacitySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparated
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparated
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalMainSeparated.instDecidableEqSumFinOfNatNat_definitions
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalMainSeparated.instFiniteQuotientOIdeal
theorem actual_main_separated_gaussian
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve cost asource:ℝ,0<K → 1≤ cost → 0<asource →
    0≤delta → 0≤ reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input (R0*C) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc t
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kmain t
          (cost*(τ.modulus.absNorm:ℝ)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalMainGaussian.actual_main_gaussian_from_bands (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  let Zw:=CenteredMomentEnergyAmplifiedChildWidth.threshold N upper sigma hupper hsigma
  refine ⟨Kc,hKc,max Zi Zw,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZw:Zw≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZiZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma.le hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  apply hbound χ₀ m hm hml hm2 ?_ r hr1 hr2 hr3 hr4
  intro q hq U dyad hphysical χ
  have hs:=commonLabels_supported (activeSource Scols β) _ _ q.property
  have hη:(src.η.modulus.absNorm:ℝ)≤Z^(Real.logb Z (src.η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz)
      (norm_pos src.η.modulus src.η.modulus_ne_bot)]
  have hh:=CenteredMomentEnergyAmplifiedChildWidth.main_child_width N upper sigma hupper hsigma
    Z hZw src hcard hupperSrc C D R0 hC hD hCD E B τ t hB hmod K delta reserve ξ
    (Real.logb Z (src.η.modulus.absNorm:ℝ)) Mwidth hK hdelta hreserve hξsmall hη hMwidth
    (activeSource Scols β) β q.val.1 q.val.2 hs.1 hs.2 U (family q U) (hfamily q U)
    _ CenteredMomentFirstAmplificationChoice.ballProfile (fun i=>(dyad i:ℤ)) hphysical χ
  exact hh.le.trans hdrop

end SevenEighths.CenteredMomentEnergyCanonicalMainSeparated

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondChildPowerBudget CenteredMomentSecondSourceSeededPowerDescent
open CenteredMomentSecondSourcePowerDescent CenteredMomentSecondWindowBudget
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O

lemma coefficients_mul {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(J:ℕ)(Q:Ideal O)(K t epsilon seed:ℝ)(f g:Fin 4→ℝ):
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed (fun j=>f j*g j) j=
      CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed f j*g j:=by
  intro j
  fin_cases j <;> simp [CenteredMomentSecondChildPowerBudget.coefficients] <;> ring

lemma coefficients_mono {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(J:ℕ)(Q:Ideal O)(K t epsilon seed:ℝ)(f g:Fin 4→ℝ)
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤K)(hseed:0≤ seed)
    (hfg:∀j,f j≤g j):
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed f j≤
      CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed g j:=by
  have h0:=hfg 0
  have h1:=hfg 1
  have h2:=hfg 2
  have h3:=hfg 3
  intro j
  fin_cases j <;> simp only [CenteredMomentSecondChildPowerBudget.coefficients, Fin.isValue, Matrix.cons_val,  Fin.reduceFinMk]
  · gcongr
  · have he:0≤CenteredMomentFirstChildProfileControl.exceptionalConstant N upper J Q K:=by
      unfold CenteredMomentFirstChildProfileControl.exceptionalConstant
      positivity
    gcongr
  · gcongr
  · gcongr

theorem seeded_factors_main (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
    ell deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (_hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤ radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(ell+deficit/6+paid);
    ∀j,seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t (cost*q)
        E E r loProduct wlo seed J J Sf W j≤
      fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W j*
        mainPowers q Z radius ell deficit paid saving r j:=by
  dsimp only
  have hEp:0≤Ebase*Z^(ell+deficit/6+paid):=mul_nonneg hE (Real.rpow_nonneg hZ.le _)
  have hsqrt:Real.sqrt ((Ebase*Z^(ell+deficit/6+paid))*(Ebase*Z^(ell+deficit/6+paid)))=
      Ebase*Z^(ell+deficit/6+paid):=by rw [←pow_two,Real.sqrt_sq hEp]
  have hneg:(loProduct*wlo*wlo)^(-2/3:ℝ)≤loFloor^(-2/3:ℝ):=
    Real.rpow_le_rpow_of_nonpos hlo hloProduct (by norm_num)
  intro j
  fin_cases j
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk,hsqrt]
    exact le_of_eq (by ring)
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_sub hZ]
    have hbase:0≤Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)/Z^(2*max r 0/3)*radius^(5/6:ℝ):=by positivity
    have hh:=mul_le_mul_of_nonneg_left hneg hbase
    have hpow:Z^(-2*max r 0/3)=(Z^(2*max r 0/3))⁻¹:=by
      rw [show -2*max r 0/3=-(2*max r 0/3) by ring,Real.rpow_neg hZ.le]
    convert (preTransparency := .instances) hh using 1 <;> (try rw [hpow]) <;> ring
  · simp [seededFactors,physicalFactors,fixedFactors,mainPowers,mul_comm,mul_left_comm,mul_assoc]
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    exact le_of_eq (by ring)

theorem main_coefficients {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(Jprofile:ℕ)(Q:Ideal O)(Kfix:ℝ)
    (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      ell deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤Kfix)(hseed:0≤ seed)
    (hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤ radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(ell+deficit/6+paid);
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W);
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t (cost*q)
        E E r loProduct wlo seed J J Sf W) j≤
      H j*mainPowers q Z radius ell deficit paid saving r j:=by
  dsimp only
  have hh:=coefficients_mono N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _ _
    hu hb1 hb2 hK hseed
    (seeded_factors_main Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      ell deficit paid r loProduct wlo loFloor seed J Sf W hCm hCe hZ hE hradius hlo hloProduct)
  intro j
  exact (hh j).trans_eq (coefficients_mul N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _ _ j)

end SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceInputTailUniform CenteredMomentFirstReferenceEnergy
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
lemma slot_product_le (s:Input ι)(N:ℕ)(C:ℝ)(hC:1≤C)
    (hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C): (∏i,s.M i)≤C ^N := by
  calc
    _≤∏_i:ι,C:=Finset.prod_le_prod (fun i _=>(s.M_ge_one i).trans' zero_le_one) (fun i _=>hM i)
    _=C ^(Fintype.card ι):=by simp
    _≤C ^N:=pow_le_pow_right₀ hC hN

omit [DecidableEq ι] in
lemma lower_product (s:Input ι)(N:ℕ)(a:ℝ)(ha:0<a)
    (hN:Fintype.card ι≤N)(hlo:∀i,a≤ s.lo i):
    (min 1 a)^N≤∏i,s.lo i := by
  have hm:0≤ min 1 a:=le_min zero_le_one ha.le
  calc
    _≤(min 1 a)^(Fintype.card ι):=pow_le_pow_of_le_one hm (min_le_left _ _) hN
    _=∏_i:ι,min 1 a:=by simp
    _≤∏i,s.lo i:=Finset.prod_le_prod (fun _ _=>hm) (fun i _=>(min_le_right _ _).trans (hlo i))

local notation "O"=>HeckeFamily.O
end SevenEighths.CenteredMomentEnergyOriginalProfileControl

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparatedPower
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower.instDecidableEqSumFinOfNatNat_definitions
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower.instFiniteQuotientOIdeal
theorem actual_main_separated_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve cost asource:ℝ,0<K → 1≤ cost → 0<asource →
    0≤delta → 0≤ reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input (R0*C) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n);
    let Hweights:=coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J
      (internalQ Q η₀) Kc t εsrc (seed.absNorm:ℝ)
      (fixedFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap cost Ebase t
        (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
        (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile);
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,Hweights j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalMainSeparated.actual_main_separated_gaussian (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kc,hKc,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  have hg:=hbound χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n)
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hE:0≤Ebase:=by dsimp [Ebase];have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile;positivity
  have hloProd:=CenteredMomentEnergyOriginalProfileControl.lower_product
    (child src C R0 B τ t) N lower hlower ((live_card_le B.val).trans hcard)
    (fun i=>hlowerSrc.trans (src.lower_le i.val))
  have hlo:CenteredMomentSecondInputCapacitySource.lowerFactor N lower a≤
      (∏i,(child src C R0 B τ t).lo i)*a*a:=by
    unfold CenteredMomentSecondInputCapacitySource.lowerFactor
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hloProd (sq_nonneg a)
  have hcoef:=CenteredMomentEnergyFirstGaussianCoefficients.main_coefficients
    N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc
    Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    t (τ.modulus.absNorm:ℝ) cost Ebase (sigma/3)
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid r
    (∏i,(child src C R0 B τ t).lo i) a
    (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
    (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile
    (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _)) hKc.le (Nat.cast_nonneg _) hCm.le hCe hz hE
    (by unfold mainCommonRadius;positivity)
    (CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain) hlo
  have hexp:
      (Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh)=
      sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))/6+paid :=by
    dsimp [paid];ring
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hh:=mul_le_mul_of_nonneg_right (hcoef j)
    (Real.rpow_nonneg (volume_pos (child src C R0 B τ t)).le (powers εsrc j))
  simpa only [CenteredMomentEnergyChildEnvelopeFitting.coefficient,hexp,Ebase,paid] using hh

end SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondWindowBudget
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

private lemma control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(h:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

private lemma zero_control_le {a b:ℝ}(p:Profiles a b)(U:Finset (ℕ×ℕ))(h:(0,0)∈U):
    SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1)≤p.control U:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) h) (p.profile 1)) (apply_nonneg _ _) (sourceControl_nonneg _ _)

theorem actual_weights {a b:ℝ}(N:ℕ)(upper b1 b2 Amax loFloor:ℝ)
    (Cm Ce Cd Ct Cc cost epsilon delta theta B:ℝ)
    (Jprofile Jchild degree:ℕ)(Sp Tchild Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(_hAmax:0≤Amax)(hlo:0<loFloor)
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hCc:0≤Cc)(hcost:0≤ cost):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀Q:Ideal O,∀Kfix:ℝ,0≤Kfix→∃C:ℝ,0<C ∧
    ∀p:Profiles a b,∀Z t height A seed C0 C1:ℝ,
      0<Z→0≤height→0≤A→A≤Amax→1≤ seed→0≤C0→0≤C1→
    let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree;
    ∀j:Fin 4,
      coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
        (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed Jchild Sf W) j≤
      C*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J*Z^(losses epsilon delta theta B j)/seed:=by
  let U:=insert (0,0) (Sp∪Tchild)
  let J:=degree+(Jchild+Jchild)+2*Jprofile
  refine ⟨U,J,?_⟩
  intro Q Kfix hK
  let Hconst:ℝ:=(1+2*Real.pi)^2
  let D0:=Cm*cost*Cc*diagonalControl W*(profileMoment Jchild)^2*
    Hconst^(Jchild+Jchild)*(2*(b1*b2)*upper^N*Amax^2)*(upper^N*b1*b2)
  let D1:=Ce*loFloor^(-2/3:ℝ)*exceptionalConstant N upper Jprofile Q Kfix*Amax^4
  let D2:=Cd*‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖*4*(1+upper^N*b^2)^(1+epsilon)
  let D3:=Ct*Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hd:=diagonalControl_nonneg W
  have hmoment:=profileMoment_nonneg Jchild
  have hSf:0≤Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  have hExc:0≤exceptionalConstant N upper Jprofile Q Kfix:=by
    unfold exceptionalConstant
    positivity
  have hD0:0≤D0:=by dsimp [D0,Hconst];positivity
  have hD1:0≤D1:=by dsimp [D1];positivity
  have hD2:0≤D2:=by dsimp [D2];positivity
  have hD3:0≤D3:=mul_nonneg hCt hSf
  let C:=1+D0+D1+D2+D3
  have hC:0<C:=by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro p Z t height A seed C0 C1 hZ hheight hA hAA hseed hC0 hC1
  dsimp only
  let H:=1+|t|+height
  have hH:1≤H:=by dsimp [H];linarith [abs_nonneg t]
  have hH0:0≤H:=zero_le_one.trans hH
  have hseed0:0≤ seed:=zero_le_one.trans hseed
  have hS:Sp⊆U:=by intro x hx;simp [U,hx]
  have hT:Tchild⊆U:=by intro x hx;simp [U,hx]
  have h00:(0,0)∈U:=by simp [U]
  have hp:=p.control_nonneg U
  have hpS:=p.control_nonneg Sp
  have hpT:=p.control_nonneg Tchild
  have hSpc: (p.control Sp)^2≤(p.control U)^2:=
    (sq_le_sq₀ hpS hp).mpr (control_mono p hS)
  have hTpc: (p.control Tchild)^2≤(p.control U)^2:=
    (sq_le_sq₀ hpT hp).mpr (control_mono p hT)
  have h00c:(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2≤(p.control U)^2:=
    (sq_le_sq₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp).mpr (zero_control_le p U h00)
  have hAp: A^2≤Amax^2:=pow_le_pow_left₀ hA hAA 2
  have hA4: A^4≤Amax^4:=pow_le_pow_left₀ hA hAA 4
  have hh:1+height≤H:=by dsimp [H];linarith [abs_nonneg t]
  have ht:1+‖t‖≤H:=by dsimp [H];linarith
  have henv0:0≤heightEnvelope t:=(heightEnvelope_pos t).le
  have henv:heightEnvelope t≤Hconst*H:=by
    have hx:1+|t|+2*Real.pi≤(1+2*Real.pi)*H:=by
      dsimp [H]
      nlinarith [Real.pi_pos,abs_nonneg t,
        mul_nonneg (le_of_lt Real.pi_pos) (abs_nonneg t)]
    have hy:=mul_le_mul_of_nonneg_right hx (show 0≤1+2*Real.pi by positivity)
    convert (preTransparency := .instances) hy using 1 <;> dsimp [heightEnvelope,Hconst] ; ring
  have henvp:heightEnvelope t^(Jchild+Jchild)≤Hconst^(Jchild+Jchild)*H^(Jchild+Jchild):=by
    simpa only [mul_pow] using pow_le_pow_left₀ (heightEnvelope_pos t).le henv (Jchild+Jchild)
  have hheightp:(1+height)^degree≤H^degree:=pow_le_pow_left₀ (by positivity) hh degree
  have htp:(1+‖t‖)^(2*Jprofile)≤H^J:=
    (pow_le_pow_left₀ (by positivity) ht (2*Jprofile)).trans
      (pow_le_pow_right₀ hH (by dsimp [J];omega))
  have hjoin:H^degree*H^(Jchild+Jchild)≤H^J:=by
    rw [←pow_add]
    exact pow_le_pow_right₀ hH (by dsimp [J];omega)
  have hHone:1≤H^J:=one_le_pow₀ hH
  have hC01:0≤C0+C1:=add_nonneg hC0 hC1
  have hCplus:0≤C0+C1+1:=by positivity
  have hD (j:Fin 4): (![D0,D1,D2,D3] j)≤C:=by
    fin_cases j <;> simp only [Matrix.cons_val,Fin.reduceFinMk] <;> dsimp [C] <;> linarith
  have hbase (d:ℝ)(hd0:0≤d)(hdC:d≤C)(ell:ℝ):
      d*(C0+C1+1)*(p.control U)^2*H^J*Z^ell/seed≤
      C*(C0+C1+1)*(p.control U)^2*H^J*Z^ell/seed:=by
    apply div_le_div_of_nonneg_right _ hseed0
    gcongr
  intro j
  fin_cases j
  · apply le_trans _ (hbase D0 hD0 (hD 0) (2*delta+epsilon))
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤Cm*Z^(2*delta+epsilon)*cost*
          (Cc*(C0+C1)*diagonalControl W*(p.control U)^2*H^degree)*
          (Hconst^(Jchild+Jchild)*H^(Jchild+Jchild))*profileMoment Jchild*profileMoment Jchild*
          (2*(b1*b2)*upper^N*Amax^2)*(upper^N*b1*b2):=by gcongr
      _=D0*(C0+C1)*(p.control U)^2*(H^degree*H^(Jchild+Jchild))*Z^(2*delta+epsilon):=by dsimp [D0];ring
      _≤D0*(C0+C1)*(p.control U)^2*H^J*Z^(2*delta+epsilon):=by gcongr
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hD0)
            (sq_nonneg (p.control U))) (pow_nonneg hH0 J))
        (Real.rpow_nonneg hZ.le _)
  · apply le_trans _ (hbase D1 hD1 (hD 1) (2*epsilon+2*delta+2*(5*B+1)*theta))
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)*loFloor^(-2/3:ℝ)*
          exceptionalConstant N upper Jprofile Q Kfix*(p.control U)^2*H^J*Amax^4:=by gcongr
      _=D1*(p.control U)^2*H^J*Z^(2*epsilon+2*delta+2*(5*B+1)*theta):=by dsimp [D1];ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD1 (le_add_of_nonneg_left hC01))
            (sq_nonneg (p.control U))) (pow_nonneg hH0 J))
        (Real.rpow_nonneg hZ.le _)
  · apply le_trans _ (hbase D2 hD2 (hD 2) 0)
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_zero,mul_one]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤D2*(p.control U)^2:=by
        convert (preTransparency := .instances) mul_le_mul_of_nonneg_left h00c hD2 using 1 ; dsimp only [D2] ; ring
      _≤D2*(C0+C1+1)*(p.control U)^2*H^J:=by
        calc
          _≤D2*(C0+C1+1)*(p.control U)^2:=mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD2 (le_add_of_nonneg_left hC01)) (sq_nonneg _)
          _≤_:=le_mul_of_one_le_right (by positivity) hHone
  · apply le_trans _ (hbase D3 hD3 (hD 3) 0)
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_zero,mul_one]
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤D3*(p.control U)^2:=mul_le_mul_of_nonneg_left h00c hD3
      _≤D3*(C0+C1+1)*(p.control U)^2*H^J:=by
        calc
          _≤D3*(C0+C1+1)*(p.control U)^2:=mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD3 (le_add_of_nonneg_left hC01)) (sq_nonneg _)
          _≤_:=le_mul_of_one_le_right (by positivity) hHone

end SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalMainHomogeneous
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous.instDecidableEqSumFinOfNatNat_definitions
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous.instFiniteQuotientOIdeal
theorem actual_main_homogeneous_oai
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤ reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalMainSeparatedPower.actual_main_separated_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  have hlo:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain
  obtain ⟨Uprofile,Jheight,hweights⟩:=
    CenteredMomentEnergyFirstGaussianProfileWeights.actual_weights (a:=a) (b:=b)
      N upper (max 1 b) (max 1 b) ((max 1 Mslot)^N)
      (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a)
      Cm Ce Cd Ct Cc cost εsrc δsrc θsrc Bcap J (dc+degree+4*n) (dc+degree+4*n)
      Sp T Sf CenteredMomentFirstAmplificationChoice.ballProfile
      (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)) (by positivity) hlo
      hCm.le hCe hCd.le hCt.le hCc.le (zero_le_one.trans hcost)
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hwbound⟩:=hweights (internalQ Q η₀) Kc hKc.le
  refine ⟨Cbound,hCbound,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  let input:=child src C R0 B τ t
  let Scols:=finiteColumns (Fintype.piFinset input.pools)
  let β:=coefficient input (R0*C) seed
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β rfl rfl
  have hg:=hbound 1 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hmass:mass src≤(max 1 Mslot)^N:=
    CenteredMomentEnergyOriginalProfileControl.slot_product_le src N (max 1 Mslot)
      (le_max_left _ _) hcard (fun i=>(hMs i).trans (le_max_right _ _))
  have hnseed:1≤(seed.absNorm:ℝ):=norm_ge_one seed hseed0
  have hh:=hwbound p Z t height (mass src) (seed.absNorm:ℝ) C₀ C₁
    hz hheight (mass_nonneg src) hmass hnseed hC₀ hC₁
  dsimp only at hh
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos input).le _)
  apply mul_le_mul_of_nonneg_right (hh j)
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold mainCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous.actual_main_homogeneous_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous.actual_main_homogeneous_oai.{u_1}

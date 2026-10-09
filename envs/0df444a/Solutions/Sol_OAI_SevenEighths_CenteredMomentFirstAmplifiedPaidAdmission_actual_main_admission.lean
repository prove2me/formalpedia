-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission.actual_main_admission
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:38:08.500508+00:00
-- url     : https://prove2.me/submissions/f27f1597-4927-4afc-8100-b8519e69b543

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028

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

theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm

end SevenEighths.CenteredMomentCanonicalFirst

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

theorem left_ideal_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P)=C := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_left_product,commonPart_eq_left C D hC.1 hCD]

theorem right_ideal_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P)=D := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_right_product,commonPart_eq_left D C hD.1 hCD.symm]

theorem left_generator_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)=primaryGenerator C := by
  have he := congrArg primaryGeneratorHom (left_ideal_product C D hC hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

theorem right_generator_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)=primaryGenerator D := by
  have he := congrArg primaryGeneratorHom (right_ideal_product C D hC hD hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalFrequency
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondLedger
open CenteredMomentPartition CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C) :
    commonFrequencyGenerator C D≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (supported_element_ne_zero _ (commonPrime_supported C D hC P))

theorem commonFrequencyGenerator_dvd (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    commonFrequencyGenerator C D∣primaryGenerator C ∧
    commonFrequencyGenerator C D∣primaryGenerator D := by
  rw [←left_generator_product C D hC hCD,←right_generator_product C D hC hD hCD]
  constructor
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _=>pow_dvd_pow _ (min_le_left _ _))
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _=>pow_dvd_pow _ (min_le_right _ _))

end SevenEighths.CenteredMomentSecondCanonicalFrequency

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT
open CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem nonunitFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))

end SevenEighths.CenteredMomentSecondCanonicalNonunit

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyInputParentCapacity
open CenteredMomentEnergyBands CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput
variable {ι:Type*} [Fintype ι]

lemma raw_log_le_length (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    Real.logb Z X≤length Z X :=
  Real.logb_le_logb_of_le hZ hX (le_max_right _ _)

theorem input_volume_log (s:Input ι)(Z:ℝ):
    Real.logb Z (volume s)=Real.logb Z s.X₁+Real.logb Z s.X₂+
      ∑i,Real.logb Z (s.P i) := by
  rw [volume,Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _=>s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',
    Real.logb_prod _ _ (fun i _=>(s.P_pos i).ne')]

theorem input_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [input_volume_log]
  have h1:=raw_log_le_length Z s.X₁ hZ s.X₁_pos
  have h2:=raw_log_le_length Z s.X₂ hZ s.X₂_pos
  nlinarith

end SevenEighths.CenteredMomentEnergyInputParentCapacity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentEligibleEnergy
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma common_slot_logs_le (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤ s.P i) :
    (∑i : CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤
      ∑i,Real.logb Z (s.P i) := by
  rw [Finset.sum_coe_sort (CenteredMomentCommonProfile.liveIndices B.val) (fun i : ι=>Real.logb Z (s.P i))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

end SevenEighths.CenteredMomentAllocatedChildCapacity

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

local instance instDecidableEq_solutions_rfeea75_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstExceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentFirstScale IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

lemma commonPart_of_equal_support (C D:Ideal O)(hC:C≠0)
    (hCD:primeSupport C=primeSupport D):commonPart C D=C := by
  have he:commonPart C D=commonPart C C:=by
    simp only [commonPart,commonSupport,←hCD]
  exact he.trans (commonPart_self C hC)

lemma nominal_equal_support (C D E:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(K V:ℝ):
    firstNominalScale C D E K V=
      (E.absNorm:ℝ)*(Ideal.span {activeConductor C D}).absNorm*V^2/
        (K*(C.absNorm:ℝ)*D.absNorm) := by
  rw [firstNominalScale,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentFirstExceptionalPrefactor

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePresentation
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily
local notation "O"=>ActualEisensteinCubic.O

theorem fixedPresentationCost_pos : 0<fixedPresentationCost:=by
  apply mul_pos
  · exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using fixedBadMask_ne_zero))
  · exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simp))

theorem fixed_presentation_norm (η τ:Character)(C D:Ideal O)(E:Finset (CommonIndex C D))
    (hM:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (τ.modulus.absNorm:ℝ)=fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=by
  rw [hM,←Ideal.span_singleton_mul_span_singleton]
  simp only [map_mul,Nat.cast_mul,eisEmbedding_norm_sq_eq_absNorm_span,fixedPresentationCost]
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalizationActual
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedNormalizationActual
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstMixedAllowance
open CenteredMomentDescentLedger CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentFirstScale ConcreteTraceCRT
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O"=>HeckeFamily.O

theorem actual_reference_width (η τ:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(K Z:ℝ)(_hK:0<K)(_hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    Real.logb Z K+Real.logb Z (τ.modulus.absNorm:ℝ)-
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost:=by
  have hE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR:=active_norm_pos C D
  have hq:=norm_pos _ η.modulus_ne_bot
  have hfixed:=fixedPresentationCost_pos
  rw [fixed_presentation_norm η τ C D E hmod]
  simp only [eisEmbedding_norm_sq_eq_absNorm_span]
  simp (disch := positivity) only [Real.logb_mul]
  ring

end SevenEighths.CenteredMomentFirstMixedNormalizationActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityRadius
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacityRadius
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstPhysicalSource
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstCanonicalFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstScale ConcreteTraceCRT
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
local notation "O"=>HeckeFamily.O

lemma enlarged_gain_extraction (c d w wo sigma branch delta reserve:ℝ)
    (_hw:0≤w)(hwo:wo≤2*w):
    -d+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve≤
      -min c d+branch*sigma+delta+reserve := by
  have h:max (d-c-2*w+wo) 0≤d-min c d:=by
    apply max_le <;> linarith [min_le_left c d,min_le_right c d]
  linarith

theorem actual_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red w wo cost gain:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hred:0< red)(hcost:0<cost)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    Real.logb Z (Z^(K0+gain))-
      Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^wo)-Real.logb Z (V/(red*Z^w))=
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        Real.logb Z red-c-d+gain+w-wo-
        Real.logb Z fixedPresentationCost-Real.logb Z cost := by
  have hc:=norm_pos C hC.1
  have hd:=norm_pos D hD.1
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR:=active_norm_pos C D
  have hz:0<Z:=zero_lt_one.trans hZ
  have hh:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  dsimp only
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow,
    Real.logb_rpow hz hZ.ne'] at hh ⊢
  norm_num at hh ⊢
  linarith

theorem actual_main_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red sigma delta reserve:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hred:0< red)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-
      Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z (V/red)≤
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        (Real.logb Z red-c)-min c d+2*sigma+delta+reserve-
        Real.logb Z fixedPresentationCost := by
  have hh:=actual_reference_shift η τ C D hC hD hCD E K V Z red 0 0 1
    (max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)) 0+2*sigma+delta+reserve)
    hK hV hZ hred (by norm_num) hmod
  have hg:=enlarged_gain_extraction (Real.logb Z (C.absNorm:ℝ))
    (Real.logb Z (D.absNorm:ℝ)) 0 0 sigma 2 delta reserve (by norm_num) (by norm_num)
  dsimp only at hh ⊢
  simp only [Real.rpow_zero,mul_one,one_mul,Real.logb_one,add_zero,sub_zero] at hh hg
  change _≤_
  rw [mainCommonRadius]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh ⊢
  norm_num at hg
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedCapacityRadius

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFirstSourceConductorCaps
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSecondHeightFamily
local notation "O"=>ActualEisensteinCubic.O

lemma divisor_norm_le (I C : Ideal O) (hC : C≠0) (h : I∣C) :
    (I.absNorm:ℝ)≤C.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm h)

end SevenEighths.CenteredMomentFirstSourceConductorCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceDyadicShell
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSourceDyadicShell
open CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma raw_window_lower (C I:Ideal O) (hC:C≠0) (a H:ℝ) (ha:0<a) (n:ℤ)
    (hL:a*H≤(Ideal.absNorm (C*I):ℝ))
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    H/(Ideal.absNorm C:ℝ)≤dyadicScale n/a := by
  have hc:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hs:=(dyadicWeight_support n hw).2.le
  simp only [map_mul,Nat.cast_mul] at hL
  apply (div_le_div_iff₀ hc ha).mpr
  nlinarith

end SevenEighths.CenteredMomentSourceDyadicShell

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceBlockWindows
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceBlockWindows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

 theorem physicalBlock_column_witnesses (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃I:sectorPool C hC.1 S,∃J:sectorPool D hD.1 S,
      β (C*I)≠0 ∧ β (D*J)≠0 ∧
      dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)≠0 ∧
      dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ)≠0 := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hcoeff: (β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J)≠0:=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hterm).1).2
    have hl:β (C*I)≠0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hcoeff).1).1
    have hr:β (D*J)≠0:=by
      intro hh
      exact hcoeff (by rw [hh,zero_mul,star_zero,mul_zero])
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    exact ⟨I,J,hl,hr,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2,(mul_ne_zero_iff.mp hw).2⟩
  · exact False.elim (hz rfl)

 theorem physicalBlock_scale_lower (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (a H:ℝ) (ha:0<a) (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    H/(Ideal.absNorm C:ℝ)≤dyadicScale (n 2)/a ∧
      H/(Ideal.absNorm D:ℝ)≤dyadicScale (n 3)/a := by
  obtain ⟨I,J,hI,hJ,hwi,hwj⟩:=physicalBlock_column_witnesses η t S β C D hC hD U R rows W K n hne
  exact ⟨raw_window_lower C I hC.1 a H ha (n 2) (hlower _ hI) hwi,
    raw_window_lower D J hD.1 a H ha (n 3) (hlower _ hJ) hwj⟩

end SevenEighths.CenteredMomentSourceBlockWindows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalLedger
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalLedger
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSourceBlockWindows
open CenteredMomentSupport CenteredMomentHeckeColumnWindow
open CenteredMomentForcing
open CenteredMomentSecondSectorFrequency CenteredMomentFirstWholeKernel
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

lemma common_product_pos (C D:Ideal O) (hC:Supported C) (V:Finset (CommonIndex C D)) :
    (0:ℝ)<Ideal.absNorm (∏P∈V,P.val) := by
  rw [map_prod,Nat.cast_prod]
  apply Finset.prod_pos
  intro P hP
  rw [←commonPrime_span C D hC P]
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (commonPrime_supported C D hC P).1)

end SevenEighths.CenteredMomentSecondPhysicalLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCapacitySourceShift
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondCapacitySourceShift
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondPhysicalLedger
open CenteredMomentSectorLocalization CenteredMomentSourceBlockWindows
open CenteredMomentSecondRadicalBudget
open CenteredMomentSupport CenteredMomentSecondWholeKernel ConcretePrimeRowBridge CenteredMomentSourceRow
local notation "O"=>HeckeFamily.O

theorem effective_upper (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    dyadicScale (n 0)≤4*secondEffectiveScale C D
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K:=by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    have h0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1
    have hh:=(dyadicWeight_support (n 0) h0).1
    linarith
  · exact False.elim (hz rfl)

lemma adjusted_row_lower (k h x y:ℝ)(hk:0<k)(hh:0<h)(hx:0<x)(hy:0<y):
    x*y/k≤h*max 1 (1/(k*h/(x*y))):=by
  calc
    _=h*(1/(k*h/(x*y))):=by field_simp
    _≤_:=mul_le_mul_of_nonneg_left (le_max_right _ _) hh.le

lemma scalar_capacity_shift (Z F q U V H K a c d k h x y:ℝ)
    (hZ:1<Z)(hF:0<F)(hq:0<q)(hU:1≤U)(hV:0<V)(hH:0<H)(hK:0<K)(ha:0<a)
    (hc:0<c)(hd:0<d)(hk:0<k)(hh:0<h)(hx:0<x)(hy:0<y)
    (g:ℝ)(hg:0<g)(hgc:g≤ c)
    (hscale:k≤4*(K*g*V/(c*d)))(hleft:a*H/c≤x)(hright:a*H/d≤y):
    Real.logb Z (H/c)-Real.logb Z (F*q*U*V*h*max 1 (1/(k*h/(x*y))))≤
      Real.logb Z K-Real.logb Z q-Real.logb Z H+Real.logb Z (4/(F*a^2)):=by
  have hu:0<U:=zero_lt_one.trans_le hU
  have hl:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hc) hleft
  have hr:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hd) hright
  have hs:=Real.logb_le_logb_of_le hZ hk hscale
  have hg':=Real.logb_le_logb_of_le hZ hg hgc
  have hu':0≤Real.logb Z U:=Real.logb_nonneg hZ hU
  have hrow:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos hx hy) hk)
    (adjusted_row_lower k h x y hk hh hx hy)
  have hm:0< max 1 (1/(k*h/(x*y))):=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow] at hl hr hs hrow ⊢
  linarith

theorem actual_capacity_shift_reference (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z qref:ℝ)(n:Fin 4→ℤ)
    (hq:0<qref)(hK:0<K)(hH:0<H)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(C.absNorm:ℝ))-Real.logb Z (adjustedEnvelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=by
  have hc:=CenteredMomentFirstScale.norm_pos C hC.1
  have hd:=CenteredMomentFirstScale.norm_pos D hD.1
  have hg:=CenteredMomentFirstScale.norm_pos (Ideal.span {commonFrequencyGenerator C D})
    (Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero C D hC))
  have hv:=CenteredMomentFirstScale.norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hu1:1≤((∏P∈U,P.val).absNorm:ℝ):=by exact_mod_cast (show 1≤(∏P∈U,P.val).absNorm from by exact_mod_cast hu)
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hdiv:Ideal.span {commonFrequencyGenerator C D}∣C:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD hCD).1
    simpa only [primary_span_supported C hC] using hh
  have hgc:=CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ C hC.1 hdiv
  have hh:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤dyadicScale (n 2):=by
    have hv':=(le_div_iff₀ ha).mp hh.1
    convert (preTransparency := .instances) hv' using 1 ; ring
  have hr:a*H/(D.absNorm:ℝ)≤dyadicScale (n 3):=by
    have hv':=(le_div_iff₀ ha).mp hh.2
    convert (preTransparency := .instances) hv' using 1 ; ring
  have hs:=effective_upper η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hs
  exact scalar_capacity_shift Z (fixedFactor:ℝ) qref
    ((∏P∈U,P.val).absNorm:ℝ) ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ)
    H K a (C.absNorm:ℝ) (D.absNorm:ℝ) (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hZ hf hq hu1 hv hH hK ha hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    ((Ideal.span {commonFrequencyGenerator C D}).absNorm:ℝ) hg hgc hs hl hr

theorem actual_capacity_shift_reference_right (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z qref:ℝ)(n:Fin 4→ℤ)
    (hq:0<qref)(hK:0<K)(hH:0<H)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(D.absNorm:ℝ))-Real.logb Z (adjustedEnvelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=by
  have hc:=CenteredMomentFirstScale.norm_pos C hC.1
  have hd:=CenteredMomentFirstScale.norm_pos D hD.1
  have hg:=CenteredMomentFirstScale.norm_pos (Ideal.span {commonFrequencyGenerator C D})
    (Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero C D hC))
  have hv:=CenteredMomentFirstScale.norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hu1:1≤((∏P∈U,P.val).absNorm:ℝ):=by exact_mod_cast (show 1≤(∏P∈U,P.val).absNorm from by exact_mod_cast hu)
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hdiv:Ideal.span {commonFrequencyGenerator C D}∣D:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD hCD).2
    simpa only [primary_span_supported D hD] using hh
  have hgc:=CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ D hD.1 hdiv
  have hh:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤dyadicScale (n 2):=by
    have hv':=(le_div_iff₀ ha).mp hh.1
    convert (preTransparency := .instances) hv' using 1 ; ring
  have hr:a*H/(D.absNorm:ℝ)≤dyadicScale (n 3):=by
    have hv':=(le_div_iff₀ ha).mp hh.2
    convert (preTransparency := .instances) hv' using 1 ; ring
  have hs:=effective_upper η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hs
  have hs':dyadicScale (n 0)≤4*(K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((D.absNorm:ℝ)*C.absNorm)):=by
    simpa only [mul_comm (C.absNorm:ℝ) (D.absNorm:ℝ)] using hs
  have hh':=scalar_capacity_shift Z (fixedFactor:ℝ) qref
    ((∏P∈U,P.val).absNorm:ℝ) ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ)
    H K a (D.absNorm:ℝ) (C.absNorm:ℝ) (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 3)) (dyadicScale (n 2)) hZ hf hq hu1 hv hH hK ha hd hc
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    ((Ideal.span {commonFrequencyGenerator C D}).absNorm:ℝ) hg hgc hs' hr hl
  simpa only [adjustedEnvelopeRef,mul_comm (dyadicScale (n 3)) (dyadicScale (n 2))] using hh'

end SevenEighths.CenteredMomentSecondCapacitySourceShift

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacitySource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

local instance instDecidableEq_solutions_rfeea75_2 {κ:Type*}:DecidableEq κ:=Classical.decEq _
theorem frozen_reduction_log (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (Z:ℝ)(hZ:1<Z)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0):
    Real.logb Z (rawReduction B.val s.P)-Real.logb Z (C.absNorm:ℝ)≤
      -(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower) := by
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have ha:0< min 1 s.lower:=lt_min zero_lt_one s.lower_pos
  have hh:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower s.upper s.lower_pos s.slot_support hne).1
  have hl:=Real.logb_le_logb_of_le hZ (mul_pos (pow_pos ha _) hr) hh
  rw [Real.logb_mul (pow_pos ha _).ne' hr.ne',Real.logb_pow] at hl
  nlinarith

theorem inherited_affine_parent (s:Input ι)(C _R:Ideal O)(B:actualAllocations s.pools C)
    (Z κ M:ℝ)(hZ:1<Z)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤M := by
  have hp:=CenteredMomentEnergyInputParentCapacity.input_affine_capacity s Z κ M hZ hcap
  have hs:=CenteredMomentAllocatedChildCapacity.common_slot_logs_le s C B Z hZ hP
  have hh:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedCapacitySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityCommon
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplifiedCapacitySource CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondNonexceptionalScalar
open CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentAllocatedChildCapacity CenteredMomentFirstScale
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

local instance instDecidableEq_solutions_rfeea75_3 {κ:Type*}:DecidableEq κ:=Classical.decEq _
lemma envelope_pos (qref:ℝ)(hq:0<qref)(C D:Ideal O)(hC:Supported C)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):0<envelopeRef qref C D U n:=by
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hu:=CenteredMomentSecondPhysicalLedger.common_product_pos C D hC U
  have hv:=norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hn:=dyadicScale_pos (n 1)
  unfold envelopeRef
  positivity

lemma adjusted_log (Z qref:ℝ)(hq:0<qref)(C D:Ideal O)(hC:Supported C)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):
    Real.logb Z (adjustedEnvelopeRef qref C D U n)=
      Real.logb Z (envelopeRef qref C D U n)+Real.logb Z (ratioPenalty n):=by
  exact Real.logb_mul (envelope_pos qref hq C D hC U n).ne'
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'

theorem common_raw_reference_shift (s:Input ι)(υ:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (B:actualAllocations s.pools C)(hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) C R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) C R0 B υ t hB
  have hc:=norm_pos C hC.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s C R0 B υ t)) hu
  have hb:0< max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) C R0 B)=volume (child s C R0 B υ t):=rfl
  rw [he]
  linarith

theorem common_raw_reference_shift_right (s:Input ι)(υ:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (B:actualAllocations s.pools D)(hB:frozenCoefficient B.val D R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) D R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference_right υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) D R0 B υ t hB
  have hc:=norm_pos D hD.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s D R0 B υ t)) hu
  have hb:0< max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) D R0 B)=volume (child s D R0 B υ t):=rfl
  rw [he]
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentFirstAmplifiedCapacitySource
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedChildCapacity

local instance instDecidableEq_solutions_rfeea75_4 {κ:Type*}:DecidableEq κ:=Classical.decEq _
lemma sourceReserve_nonneg {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal O)(Z delta reserve cost a:ℝ):0≤ sourceReserve s childInput C D Z delta reserve cost a :=
  le_max_right _ _

lemma common_affine (s:Input ι)(C:Ideal O)(B:actualAllocations s.pools C)
    (Z κ A M:ℝ)(hZ:1<Z)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hp:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M):
    A+(6*κ-1)*(∑i:liveIndices B.val,Real.logb Z (s.P i.val))≤M := by
  have hs:=common_slot_logs_le s C B Z hZ hP
  have hm:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

theorem actual_main_admission_oai (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (child s C R0 B τ t)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C₂ D₂ hC₂ hD₂ U R rows W
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (child s C R0 B τ t).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (child s C R0 B τ t).ν (child s C R0 B τ t).W (child s C R0 B τ t).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤Mdecl):
    let input:=child s C R0 B τ t;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*(sigma/3)+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0<cost*(τ.modulus.absNorm:ℝ):=mul_pos hcost hq
  have hf:=inherited_affine_parent s C R0 B Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(child s C R0 B τ t).P i:=fun i=>hP i.val
  have hparent:=common_affine (child s C R0 B τ t) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_main_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hmod
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0< mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by
    unfold mainCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (child s C R0 B τ t) υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ))-
      Real.logb Z (volume (child s C R0 B τ t))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
  rw [common_volume,Real.logb_mul hcost.ne' hq.ne'] at hg
  dsimp only at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission.actual_main_admission_oai.{u_1} := @OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission.actual_main_admission_oai.{u_1}

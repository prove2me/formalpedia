-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ.actual_physical_exceptional_block
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:09:21.819205+00:00
-- url     : https://prove2.me/submissions/0a260c45-8694-4103-ae4b-c2d518425fab

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptionalCommon_actual_canonical_common_window
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptionalFixedQ_actual_original_exceptional_block
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondExceptionalKernel_actual_exceptional_block_bound

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.UnitRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeUnitRows
open HeckeFamily CanonicalUnitEuler CanonicalRowCompletion
open ActualEisensteinCubic CubicRamified ConcreteTraceCRT
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "ω" => HeckeFamily.omega
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_unit_thirty_six (n : O) (hn : Supported (Ideal.span {n})) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(36 : O)}) n) := by
  have hs := (supported_span_iff n).mp hn
  have hneg2 : IsCoprime (-2 : O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using hs.2)
  have h2 : IsCoprime n (2 : O) := (hneg2.of_isCoprime_of_dvd_left ⟨-1, by ring⟩).symm
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n hs.1).symm
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.isCoprime_span_singleton_iff]
  convert (preTransparency := .instances) (h2.pow_right : IsCoprime n ((2 : O)^2)).mul_right h9 using 1 ; norm_num

theorem elementCoeff_character (u : Oˣ) (n : O) :
    elementCoeff (character u) n = unitSupplement u n := by
  rw [character, HeckeRowClosure.elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · change 0 = if Supported (Ideal.span {n}) then _ else 0
    rw [if_neg (fun hs => hn (supported_unit_thirty_six n hs))]

end SevenEighths.HeckeUnitRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PartitionNorm
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartitionNorm
open CenteredMomentPartition CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem commonIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) : 0 < (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  apply Finset.prod_pos
  intro i hi
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

omit [Fintype ι] [DecidableEq ι] in
theorem unitIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (U : Finset ι) : 0 < (Ideal.absNorm (unitIdeal p U) : ℝ) := by
  simp only [unitIdeal, map_prod, Nat.cast_prod]
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

theorem partitionNormalizer_mul_unit_norm (p : ι → O) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U * (Ideal.absNorm (unitIdeal p U) : ℝ) =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [unitIdeal, commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  have hU : (∏ i ∈ U, (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∏ i, if i ∈ U then (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 1 := by simp
  rw [hU, partitionNormalizer, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hmem : i ∈ U
  · simp only [if_pos hmem]
    rw [← pow_succ, Nat.sub_add_cancel (le_min (hc i) (hd i))]
  · simp only [if_neg hmem, Nat.sub_zero, mul_one]

theorem partitionNormalizer_eq_norm_ratio (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) / Ideal.absNorm (unitIdeal p U) := by
  apply (eq_div_iff (unitIdeal_norm_pos p hp U).ne').mpr
  exact partitionNormalizer_mul_unit_norm p c d hc hd U

end SevenEighths.CenteredMomentPartitionNorm

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

 theorem supported_residualPool (C : Ideal O) (hC : Supported C) (S : Finset (Ideal O)) :
    supportedColumns (residualPool C hC.1 S)=residualPool C hC.1 (supportedColumns S) := by
  ext I
  simp only [supportedColumns,Finset.mem_filter,mem_residualPool]
  rw [supported_mul_iff]
  tauto

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentLiveDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem heightCost_pos (t θ : ℝ) : 0<heightCost t θ := by
  unfold heightCost
  positivity

end SevenEighths.CenteredMomentHeckeWindowEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sectorElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Ideal.span {sectorElement C hC S a}=a :=
  primary_span_supported a (sectorPool_supported C hC S a)

end SevenEighths.CenteredMomentSecondSectorColumns

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Scale
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentScale
open CenteredMomentSmooth EisensteinSchwartzPoisson

theorem logarithmic_kernel_argument (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K₀ * H₀ / (A₀ * B₀)) *
      Real.exp (Real.log (K / K₀) + Real.log (H / H₀) -
        Real.log (A / A₀) - Real.log (B / B₀)) = K * H / (A * B) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add,
    Real.exp_log (div_pos hK hK₀), Real.exp_log (div_pos hH hH₀),
    Real.exp_log (div_pos hA hA₀), Real.exp_log (div_pos hB hB₀)]
  field_simp

theorem rootWindow_log_ratio (V : ℝ → ℂ) (A A₀ : ℝ) (hA : 0 < A) (hA₀ : 0 < A₀) :
    rootWindow V (Real.log (A / A₀)) =
      (Real.sqrt A₀ : ℂ) * V (Real.log (A / A₀)) / (Real.sqrt A : ℂ) := by
  rw [rootWindow, Real.exp_log (div_pos hA hA₀), Real.sqrt_div hA.le, Complex.ofReal_div]
  field_simp

theorem wholeKernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
      (Real.log (K / K₀)) (Real.log (H / H₀))
      (Real.log (A / A₀)) (Real.log (B / B₀)) =
      (((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) /
        ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ))) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) := by
  rw [wholeKernel, rootWindow_log_ratio _ A A₀ hA hA₀,
    rootWindow_log_ratio _ B B₀ hB hB₀,
    logarithmic_kernel_argument K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  ring

end SevenEighths.CenteredMomentScale

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

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedDetectorAmplitude
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedDetectorAmplitude
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRawEnergy CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentDetectorDictionary
open ConcretePrimeRowBridge CenteredMomentDivisorRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma slotControl_nonneg (s:Data ι):0≤ slotControl s:=by
  unfold slotControl
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>(zero_le_one.trans (s.M_ge_one i))))
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _)))

end SevenEighths.CenteredMomentAllocatedDetectorAmplitude

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RestrictedDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

theorem source_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*CanonicalRowCompletion.idealRowHom z I := by
  unfold rowPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*CanonicalRowCompletion.idealRowHom z I)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2]

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentRestrictedDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSectorEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentRestrictedSource CenteredMomentRestrictedDomain CenteredMomentRestrictedEnergy
open CenteredMomentLiveDomain CenteredMomentFirstSectors RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sector_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C : Ideal O) (hC : Supported C) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I : sectorPool C hC.1 S => c I) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) => if IsCoprime C (I:Ideal O) then c I else 0) z := by
  rw [source_rowPolynomial (residualPool C hC.1 S)
    (fun I => if IsCoprime C I then c I else 0) z]
  unfold rowPolynomial
  simp only [sectorElement_span]
  rw [Finset.sum_coe_sort (sectorPool C hC.1 S) (fun I => c I*idealRowHom z I)]
  rw [sectorPool,Finset.sum_filter,supported_residualPool C hC S]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

end SevenEighths.CenteredMomentSecondSectorEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalSourceShell
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalSourceShell
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalAllocationShell
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma profileMass_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):0≤profileMass s v p q J:=by
  unfold profileMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
    (slotControl_nonneg s)) (slotControl_nonneg v)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end SevenEighths.CenteredMomentExceptionalSourceShell

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonExceptionalCost
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalCost
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma frozenProfile_nonneg (s:Input ι):0≤frozenProfile s:=by
  unfold frozenProfile
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

end SevenEighths.CenteredMomentCommonExceptionalCost

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSymmetry
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalSymmetry
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma same_raw_better_cap (r c d:ℝ):
    max (max (r-c) 0) (max (r-d) 0)=max (r-min c d) 0:=by
  rcases le_total c d with h|h
  · rw [min_eq_left h,max_eq_left (max_le_max_right 0 (by linarith))]
  · rw [min_eq_right h,max_eq_right (max_le_max_right 0 (by linarith))]

end SevenEighths.CenteredMomentCommonExceptionalSymmetry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ConjugateWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentConjugateWindow
open FourierBridge CenteredMomentSmooth

theorem star_logPhase (t u : ℝ) : star (logPhase t u)=logPhase (-t) u := by
  simp only [logPhase,Complex.star_def,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  congr 1
  push_cast
  ring

theorem star_columnPhase (V : ℝ → ℂ) (u t : ℝ) :
    star (columnPhase V u t)=columnPhase (fun x => star (V x)) u (-t) := by
  rw [columnPhase,star_mul,star_logPhase,columnPhase,mul_comm]
  congr 1
  simp only [rootWindow,Complex.star_def,map_div₀,Complex.conj_ofReal]

end SevenEighths.CenteredMomentConjugateWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentScale CenteredMomentSmooth
open CenteredMomentFirstWholeKernel CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem secondEffectiveScale_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : 0<secondEffectiveScale C D A K := by
  apply div_pos (mul_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hA))))
  exact mul_pos (CenteredMomentFirstScale.norm_pos C hC) (CenteredMomentFirstScale.norm_pos D hD)

theorem primary_norm_sq (I : Ideal O) (hI : Supported I) :
    ‖eisEmbedding (primaryGenerator I)‖^2=(Ideal.absNorm I:ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,primary_span_supported I hI]

theorem second_kernel_argument (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (K : ℝ) :
    K*‖eisEmbedding (A*h)‖^2/
      ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2=
      secondEffectiveScale C D A K*‖eisEmbedding h‖^2/((Ideal.absNorm a:ℝ)*(Ideal.absNorm b:ℝ)) := by
  simp only [map_mul,norm_mul,mul_pow,primary_norm_sq (C*a) ((supported_mul_iff _ _).mpr ⟨hC,ha⟩),
    primary_norm_sq (D*b) ((supported_mul_iff _ _).mpr ⟨hD,hb⟩),map_mul,Nat.cast_mul,secondEffectiveScale]
  ring

theorem common_normalized_kernel (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (k H a b C D K K₀ H₀ A₀ B₀ : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b)
    (hC : 0<C) (hD : 0<D) (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    (K:ℂ)/((Real.sqrt (C*a):ℂ)*(Real.sqrt (D*b):ℂ))*
      windows V k H a b K₀ H₀ A₀ B₀*paperRadialFourier W (k*H/(a*b))=
      (K:ℂ)/((Real.sqrt C:ℂ)*(Real.sqrt D:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (H/H₀)) (Real.log (a/A₀)) (Real.log (b/B₀)) := by
  rw [wholeKernel_actual W V k H a b K₀ H₀ A₀ B₀ hk hH ha hb hK₀ hH₀ hA₀ hB₀]
  rw [Real.sqrt_mul hC.le a,Real.sqrt_mul hD.le b]
  simp only [Complex.ofReal_mul,windows]
  have hc : (Real.sqrt C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hC).ne'
  have hd : (Real.sqrt D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'
  have haa : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hbb : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  field_simp

theorem second_frequency_whole_kernel (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (hA : A≠0) (hh : h≠0) (K : ℝ) (hK : 0<K)
    (F : ℂ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let k := secondEffectiveScale C D A K
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*a):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*b):ℝ):ℂ)))*F*
      windows V k (‖eisEmbedding h‖^2) (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) K₀ H₀ A₀ B₀*
      paperRadialFourier W (K*‖eisEmbedding (A*h)‖^2/
        ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*F*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
          (Real.log ((Ideal.absNorm a:ℝ)/A₀)) (Real.log ((Ideal.absNorm b:ℝ)/B₀)) := by
  dsimp only
  rw [second_kernel_argument C D a b hC hD ha hb]
  simp only [map_mul,Nat.cast_mul]
  have he := common_normalized_kernel W V (secondEffectiveScale C D A K) (‖eisEmbedding h‖^2)
    (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) (Ideal.absNorm C:ℝ) (Ideal.absNorm D:ℝ)
    K K₀ H₀ A₀ B₀ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))
    (CenteredMomentFirstScale.norm_pos a ha.1) (CenteredMomentFirstScale.norm_pos b hb.1)
    (CenteredMomentFirstScale.norm_pos C hC.1) (CenteredMomentFirstScale.norm_pos D hD.1)
    hK₀ hH₀ hA₀ hB₀
  convert (preTransparency := .instances) congrArg (fun z : ℂ => F*z) he using 1 <;> ring

end SevenEighths.CenteredMomentSecondWholeKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LogDyadic
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

theorem logAnnulus_log (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=>logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp only [Complex.ofReal_mul,actual_dyadic_log_window (n 0) k hk,
    actual_dyadic_log_window (n 1) H hH,actual_dyadic_log_window (n 2) a ha,
    actual_dyadic_log_window (n 3) b hb,windows]

end SevenEighths.CenteredMomentLogDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWindowSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentConjugateWindow
local notation "O" => ActualEisensteinCubic.O

theorem star_logAnnulus (x : ℝ) : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]

theorem star_logAnnulus_column (u t : ℝ) :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]

end SevenEighths.CenteredMomentSecondWindowSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondMaskedWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondMaskedWindow
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem masked_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (t : ℝ)
    (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J:sectorPool C hC.1 S=>β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  have hi : IsCoprime C (I:Ideal O) := (Finset.mem_filter.mp I.property).2
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,
    hτ I (sectorPool_supported C hC.1 S I) hi t]
  dsimp only [sectorElement]
  split_ifs <;> ring

end SevenEighths.CenteredMomentSecondMaskedWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeWindow
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWholeWindow
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem rowPolynomial_factor {α:Type*}(S:Finset α)(a:α→O)(c:α→ℂ)(v:ℂ)(z:O):
    rowPolynomial S a (fun i=>v*c i) z=v*rowPolynomial S a c z:=by
  simp only [rowPolynomial,Finset.mul_sum,mul_assoc]

end SevenEighths.CenteredMomentExceptionalWholeWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentCommonWindowColumn
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentCommonWindowColumn.instDecidableEqSumFinOfNatNat_solutions
theorem sourceGenerator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

end SevenEighths.CenteredMomentCommonWindowColumn

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedSource
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentReflectedSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CanonicalUnitEuler
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearSource CenteredMomentCommonPairedSource
open CenteredMomentFirstSectors CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
local notation "O" => HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_r3b16c1_1 {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
theorem unit_ideal (I:Ideal O)(hI:Supported I):
    idealCoeff (HeckeUnitRows.character (-1:Oˣ)) I=idealRowHom (-1) I:=by
  rw [←ConcretePrimeRowBridge.span_idealGenerator I,
    idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI.1),
    HeckeUnitRows.elementCoeff_character]
  change (if Supported (Ideal.span {ConcretePrimeRowBridge.idealGenerator I}) then _ else 0)=_
  rw [ConcretePrimeRowBridge.span_idealGenerator,if_pos hI]
  rfl

theorem reflected_height (η:Character)(t:ℝ)(I:Ideal O)(hI:Supported I):
    heightCoeff (reflected η) t I=heightCoeff η t I*idealRowHom (-1) I:=by
  rw [heightCoeff,reflected,idealCoeff_product,unit_ideal I hI,heightCoeff]
  ring

theorem reflected_row (η:Character)(m A z n:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    rowTwist (HeckeRowClosure.elementHom η) m 1 (A*(-z)) n=
      rowTwist (HeckeRowClosure.elementHom (reflected η)) m 1 (A*z) n:=by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 _ n hn,rowTwist_extract_sixth_mask _ m 1 _ n hn]
    simp only [one_pow,one_mul]
    change elementCoeff η n*coprimalityMask m n*idealRowHom (A*(-z)) (Ideal.span {n})=
      elementCoeff (reflected η) n*coprimalityMask m n*idealRowHom (A*z) (Ideal.span {n})
    rw [reflected,elementCoeff_product,HeckeUnitRows.elementCoeff_character]
    have hu:unitSupplement (-1:Oˣ) n=idealRowHom (-1) (Ideal.span {n}):=by
      change (if Supported (Ideal.span {n}) then idealRowHom (-1) (Ideal.span {n}) else 0)=_
      rw [if_pos hn]
    rw [hu,show A*(-z)=(-1)*(A*z) by ring,idealRowHom_argument_mul]
    ring
  · rw [CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn]

theorem reflected_inducing (η:Character)(Q:Ideal O)(m A z:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    CenteredExceptionalProfile.FixedInducingRow η Q m A (-z) ↔
      CenteredExceptionalProfile.FixedInducingRow (reflected η) Q m A z:=by
  unfold CenteredExceptionalProfile.FixedInducingRow
  simp_rw [←reflected_row η m A z _ hmLam hm2]

end SevenEighths.CenteredMomentReflectedSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSectorWindow
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonSectorWindow
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentSecondMaskedWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth CenteredMomentSecondWindowSource
open RayFourExpansion CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentCommonSectorWindow.instDecidableEqSumFinOfNatNat_definitions
omit [DecidableEq ι] in
theorem actual_sector_window (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t θ X:ℝ)(V:ℝ→ℂ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z=
      windowColumn s C hC R seed L τ t θ X V z:=by
  dsimp only
  simp_rw [masked_divisor_coefficient η τ χ A C hC hτ]
  rw [sector_rowPolynomial _ (fun I=>(if L∣I then finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)*
      heightCoeff τ t I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ) C hC z]
  unfold windowColumn
  rw [←rowPolynomial_factor]
  apply congrArg (fun c=>rowPolynomial Finset.univ (sourceGenerator (columns s C hC)) c z)
  funext I
  dsimp only [coefficient]
  split_ifs <;> simp_all ; ring

omit [DecidableEq ι] in
theorem window_neg (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):
    windowColumn s C hC R seed L η t θ X V (-z)=
      windowColumn s C hC R seed L (reflected η) t θ X V z:=by
  unfold windowColumn rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [reflected_height η t I (Finset.mem_filter.mp I.property).2,
    show -z=(-1)*z by ring,idealRowHom_argument_mul,sourceGenerator_span]
  ring

omit [DecidableEq ι] in
theorem actual_reflected_sector_window (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t θ X:ℝ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
        star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ)) (-z)=
      windowColumn s C hC R seed L (reflected τ) t (-θ) X logAnnulus z:=by
  dsimp only
  simp only [star_logAnnulus_column]
  rw [actual_sector_window s η τ χ A C hC R seed L t (-θ) X logAnnulus (-z) hτ,window_neg]

end SevenEighths.CenteredMomentCommonSectorWindow

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonAsymmetric
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma profileMass_nonneg {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):0≤profileMass R s v p q J:=by
  have hp:=Profiles.control_nonneg p R
  have hq:=Profiles.control_nonneg q R
  have hs:=slotControl_nonneg s
  have hv:=slotControl_nonneg v
  unfold profileMass
  positivity

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalHeight
namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentHeckeWindowEnergy
open CenteredMomentExceptionalAmplitudePair CenteredMomentAllocatedDetectorAmplitude
universe u

theorem heightCost_phase (t θ:ℝ):
    heightCost t θ≤(1+‖t‖)*(1+2*Real.pi)^2*(1+‖θ‖):=by
  have hc:0≤2*Real.pi:=by positivity
  have ht:0≤‖t‖:=norm_nonneg t
  have hθ:0≤‖θ‖:=norm_nonneg θ
  have hh:1+‖t‖+2*Real.pi*‖θ‖≤(1+‖t‖)*(1+2*Real.pi)*(1+‖θ‖):=by
    nlinarith [mul_nonneg hc ht,mul_nonneg ht hθ,mul_nonneg (mul_nonneg hc ht) hθ]
  exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq (by ring)

theorem mass_phase {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(w:ℝ)(J:ℕ):
    mass R s v p q s.t v.t w (-w) J≤
      (1+2*Real.pi)^(4*J)*profileMass R s.toData v.toData p q J*(1+‖w‖)^(2*J):=by
  have hp:=pow_le_pow_left₀ (heightCost_pos s.t w).le (heightCost_phase s.t w) J
  have hq:=pow_le_pow_left₀ (heightCost_pos v.t (-w)).le (heightCost_phase v.t (-w)) J
  rw [norm_neg] at hq
  have hh:=mul_le_mul hp hq (pow_nonneg (heightCost_pos v.t (-w)).le _) (by positivity)
  have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh (mul_nonneg (Profiles.control_nonneg p R) (Profiles.control_nonneg q R)))
      (slotControl_nonneg s.toData)) (slotControl_nonneg v.toData))
      (Real.sqrt_nonneg (volume s.toData))) (Real.sqrt_nonneg (volume v.toData))
  have hmass:mass R s v p q s.t v.t w (-w) J =
      p.control R*q.control R*(heightCost s.t w^J*heightCost v.t (-w)^J)*
        slotControl s.toData*slotControl v.toData*Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData):=by
    unfold mass
    ring
  rw [hmass]
  apply he.trans_eq
  simp only [profileMass,mul_pow,←pow_mul]
  rw [show 4*J=2*J+2*J by omega,show 2*J=J+J by omega]
  simp only [pow_add]
  ring
end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairDictionary
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalPairDictionary
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondExceptionalPairDictionary.instDecidableEqSumFinOfNatNat_definitions
lemma raw_pair (V:ℝ)(hV:0<V)(a b:ℂ):
    ‖a‖*‖b‖=V*‖(Real.sqrt V:ℂ)⁻¹*a‖*‖(Real.sqrt V:ℂ)⁻¹*b‖:=by
  have hs:0<Real.sqrt V:=Real.sqrt_pos.mpr hV
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  field_simp
  rw [Real.sq_sqrt hV.le]

omit [DecidableEq ι] in
theorem original_pair (s:Input ι)(η τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hτ₁:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ₁ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (hτ₂:∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
      heightCoeff τ₂ v I=heightCoeff η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)=
      volume s.toData*(∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L τ₁ t w X logAnnulus z‖*
        ‖windowColumn s D hD R seed L (reflected τ₂) t (-w) Y logAnnulus z‖):=by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  rw [mul_left_comm (volume s.toData) ‖(moebius L:ℂ)‖]
  apply congrArg (fun a:ℝ=>‖(moebius L:ℂ)‖*a)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [raw_pair (volume s.toData) (volume_pos s.toData)]
  rw [actual_sector_window s η τ₁ χ A C hC R seed L t w X logAnnulus z hτ₁,
    actual_reflected_sector_window s η τ₂ ξ A D hD R seed L t w Y z hτ₂]
  ring

end SevenEighths.CenteredMomentSecondExceptionalPairDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairBound
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalPairBound
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondExceptionalPairBound.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
lemma window_withHeight (s:Input ι)(τ η:Character)(v t θ X:ℝ)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(V:ℝ→ℂ)(z:O):
    windowColumn (withHeight s τ v) C hC R seed L η t θ X V z=
      windowColumn s C hC R seed L η t θ X V z:=rfl

end SevenEighths.CenteredMomentSecondExceptionalPairBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalPair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_r3b16c1_2 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
theorem actual_canonical_original_pair (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_common_window wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase Sprofile s s p p w J
  let F:=volume s.toData*(K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass Sprofile s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,CenteredMomentFiniteProfileExceptionalCommon.mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSecondDivisorSupport
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondExceptionalPairBound RayFourExpansion
local notation "O"=>HeckeFamily.O

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondDivisorSupport.instDecidableEqSumFinOfNatNat_definitions
theorem live_right_divisor_norm (D I L:Ideal O)(hD:D≠0)(hI:I≠0)
    (β:Ideal O→ℂ)(H:ℝ)(hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)
    (hne:β (D*I)≠0)(hLI:L∣I):
    (L.absNorm:ℝ)≤H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hnorm:(L.absNorm:ℝ)≤I.absNorm:=by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)) (map_dvd Ideal.absNorm hLI)
  have hb:=hβ (D*I) hne
  rw [map_mul,Nat.cast_mul] at hb
  apply hnorm.trans
  apply (le_div_iff₀ hDpos).mpr
  simpa only [mul_comm] using hb

theorem right_divisor_coefficient_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(I:sectorPool D hD.1 S):
    divisorCoefficient L (sectorElement D hD.1 S)
      (movingCoefficient A (sectorElement D hD.1 S)
        (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I=0:=by
  unfold divisorCoefficient
  rw [sectorElement_span]
  split_ifs with hd
  · have hz:β (D*I)=0:=by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (sectorPool_supported D hD.1 S I).1 β H hβ hn hd)
    simp only [movingCoefficient,hz,zero_mul]
  · rfl

theorem right_divisor_row_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(v:sectorPool D hD.1 S→ℂ)(z:O):
    rowPolynomial Finset.univ (sectorElement D hD.1 S)
      (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
        (movingCoefficient A (sectorElement D hD.1 S)
          (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v I) z=0:=by
  unfold rowPolynomial
  apply Finset.sum_eq_zero
  intro I hI
  exact mul_eq_zero_of_left
    (mul_eq_zero_of_left (right_divisor_coefficient_zero D hD S β H hβ L hL η t A ξ I) _) _

theorem originalPair_filter_right {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y H:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hβ:∀I:Ideal O,finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I≠0→
      (I.absNorm:ℝ)≤H):
    originalPair s η χ ξ A C D hC hD R seed t w X Y Ds rows=
      originalPair s η χ ξ A C D hC hD R seed t w X Y
        (Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ))) rows:=by
  unfold originalPair
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hL:(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [if_pos hL]
  · rw [if_neg hL]
    have hz:=right_divisor_row_zero D hD (finiteColumns (Fintype.piFinset s.pools))
      (finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed))
      H hβ L (lt_of_not_ge hL) η t A ξ
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro z hzr
    apply mul_eq_zero_of_right
    exact norm_eq_zero.mpr (hz _ _)

end SevenEighths.CenteredMomentSecondDivisorSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalScalar
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalScalar
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem normalizer_pos (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    0<normalizer C D U := by
  rw [normalizer,partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D)]
  exact div_pos (commonIdeal_norm_pos _ (commonPrime_supported C D hC) _ _)
    (unitIdeal_norm_pos _ (commonPrime_supported C D hC) _)

end SevenEighths.CenteredMomentSecondCanonicalScalar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalWindow
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorColumns
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic
local notation "O" => ActualEisensteinCubic.O

theorem physical_kernel_window (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (V : Fin 4→ℝ→ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    physicalKernel C D W K R (A*h) I J*
      windows V (secondEffectiveScale C D A K) (normValue h)
        (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) K₀ H₀ A₀ B₀=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log (secondEffectiveScale C D A K/K₀)) (Real.log (normValue h/H₀))
            (Real.log ((Ideal.absNorm I:ℝ)/A₀)) (Real.log ((Ideal.absNorm J:ℝ)/B₀)) := by
  have he := second_frequency_whole_kernel C D I J hC hD hI hJ A h hA hh K hK 1 W V
    K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
  dsimp only at he
  simp only [mul_one,normValue_eq_embedding] at he ⊢
  have hd : ‖eisEmbedding (CompletedGauss.primaryGenerator (C*I)*
      CompletedGauss.primaryGenerator (D*J))‖^2=
      (Ideal.absNorm (C*I):ℝ)*(Ideal.absNorm (D*J):ℝ) := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hC,hI⟩),
      primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hD,hJ⟩)]
  rw [hd] at he
  unfold physicalKernel
  rw [hd]
  simp only [normValue_eq_embedding]
  convert (preTransparency := .instances) congrArg (fun x : ℂ=>(retainedWeight R (‖eisEmbedding (A*h)‖^2):ℂ)*x) he using 1 <;> ring

theorem physical_kernel_dyadic (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (n : Fin 4→ℤ) :
    physicalKernel C D W K R (A*h) I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
        dyadicWeight (n 2) (Ideal.absNorm I:ℝ)*dyadicWeight (n 3) (Ideal.absNorm J:ℝ):ℝ):ℂ)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W (fun _=>logAnnulus)
            (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
            (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
            (Real.log (normValue h/dyadicScale (n 1)))
            (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
            (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  rw [actual_product_windows _ _ _ _ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (normValue_pos h hh) (CenteredMomentFirstScale.norm_pos I hI.1)
    (CenteredMomentFirstScale.norm_pos J hJ.1)]
  exact physical_kernel_window C D I J hC hD hI hJ A h hA hh W K R hK _ _ _ _ _
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)

end SevenEighths.CenteredMomentSecondPhysicalWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBlock
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical.instDecidableEqSumFinOfNatNat_solutions_1
lemma sourceBudget_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤K)(hZ:0≤Z)(hCr:0≤Cr):
    0≤ sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg Sprofile s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

theorem actual_original_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀X Y:ℝ,0<X → 0<Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0< rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=>logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_original_pair wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg Sprofile s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤_
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

private lemma physicalBlock_scalar (a b c d e f : ℂ) (hb : b ≠ 0) :
    c * d * (a * e * f) = a * b * (b⁻¹ * e * (c * d * f)) := by
  calc
    _ = a * e * (c * d * f) := by ring
    _ = a * (b * b⁻¹) * e * (c * d * f) := by rw [mul_inv_cancel₀ hb, mul_one]
    _ = _ := by ring

theorem physicalBlock_eq (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) :
    physicalBlock η t S β C D hC hD U R rows W K n=
      (outerScalar C D K n:ℂ)*(normalizer C D U:ℂ)*
        normalizedBlock η t S β C D hC hD U R rows W K n := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC) (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock normalizedBlock
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [physical_kernel_dyadic C D _ _ hC hD
    (sectorPool_supported C hC.1 S _) (sectorPool_supported D hD.1 S _)
    _ z hA (hrows z hz) W K R hK n]
  have hn : (normalizer C D U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalizer_pos C D hC U).ne'
  simp only [outerScalar,Complex.ofReal_div,Complex.ofReal_mul,retainedScalar,canonicalPartitionScalar]
  simp only [normalizer] at hn ⊢
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*z)
  · simp only [hp,ite_true]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact physicalBlock_scalar _ _ _ _ _ _ hn
  · simp only [hp,ite_false,mul_zero,zero_mul,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSecondPhysicalBlock

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQRows
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ.instDecidableEqSumFinOfNatNat_definitions_1
theorem actual_physical_exceptional_block_oai (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_original_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN H hβ hHD R Kphys hKphys n rK
  have hrK:0< rK:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hh:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN (dyadicScale (n 2)) (dyadicScale (n 3))
    (dyadicScale_pos _) (dyadicScale_pos _) H hβ hHD R
    (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1))) rK hrK
  change (1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar; positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  rw [physicalBlock_eq s.η s.t S β C D hC hD U R rows hn W Kphys hKphys n,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  calc
    _=(outerScalar C D Kphys n*normalizer C D U)*
        ((1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ.actual_physical_exceptional_block_oai.{u} := @OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ.actual_physical_exceptional_block_oai.{u}

-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstMixedWindow.original_four_budget_reference
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:38:50.501127+00:00
-- url     : https://prove2.me/submissions/6d98c6c5-b0aa-4870-af78-e8b51622642e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
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

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_canonicalGaussSum {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) :
    ‖canonicalGaussSum P hcop hgood j‖ = ‖eisEmbedding (finitePrimeModulus P)‖ := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let χ : ∀ i, MulChar (O ⧸ P i) ℂ := fun i => canonicalSextic (P i) (hgood i) ^ j i
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0
  have hχ : ∀ i, χ i ≠ 1 := fun i =>
    canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i)
    e χ ψ hχ (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun i => O ⧸ P i) e ψ hψ i)
  change ‖canonicalGaussSum P hcop hgood j‖ ^ 2 =
    (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq

theorem norm_canonicalNormalizedGauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) :
    ‖canonicalNormalizedGauss P hcop hgood j‖ = 1 := by
  have hn : ‖eisEmbedding (finitePrimeModulus P)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  rw [canonicalNormalizedGauss, norm_div,
    norm_canonicalGaussSum P hcop hgood hchar j hj0 hj6,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]

end ActualEisensteinCubic

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Active
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentActive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalRowCompletion CenteredMomentCanonical

theorem netExponent_ne_zero {ι : Type*} (B : Finset ι) (c d : ι → ℕ)
    (i : activeSupport B c d) : netExponent (c i.val) (d i.val) ≠ 0 :=
  (Finset.mem_filter.mp i.property).2

theorem netExponent_lt_six (c d : ℕ) : netExponent c d < 6 := Nat.mod_lt _ (by decide)

variable {ι : Type*}

open ConcreteTraceCRT EisensteinSchwartzPoisson

end SevenEighths.CenteredMomentActive
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RankinRadical
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinRadical
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O

theorem commonRadical_ne_zero (I J : Ideal O) : commonRadical I J ≠ 0 :=
  support_product_ne_zero Finset.inter_subset_left

end SevenEighths.CenteredMomentRankinRadical

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

theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonAllowance
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonAllowance
open CenteredMomentActive CenteredMomentSecondLedger CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem netExponent_self (c : ℕ) : netExponent c c = 0 := by
  unfold netExponent
  have h : c+5*c=6*c := by omega
  rw [h, Nat.mul_mod_right]

theorem local_allowance (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    max (3*(c:ℝ)-5*(d:ℝ)-activeIndicator c d) 0 / 6 +
      max (3*(d:ℝ)-5*(c:ℝ)-activeIndicator c d) 0 / 6 ≤
      (c:ℝ)+(d:ℝ)-2-activeIndicator c d := by
  have hc' : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold activeIndicator
  split_ifs with he
  · have hne : c ≠ d := by rintro rfl; exact he (netExponent_self c)
    have hgap : (c:ℝ)+1 ≤ d ∨ (d:ℝ)+1 ≤ c := by
      rcases lt_or_gt_of_ne hne with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    rcases hgap with hgap | hgap <;>
      rw [max_def,max_def] <;> split_ifs <;> linarith
  · rw [max_def,max_def]; split_ifs <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem weighted_positive_part (a w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (∑ i, a i*w i) 0 ≤ ∑ i, max (a i) 0*w i := by
  apply max_le
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hw i)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (hw i)

omit [DecidableEq ι] in
theorem weighted_allowance (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hd : ∀ i, 1 ≤ d i) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (3*(∑ i, (c i:ℝ)*w i)-5*(∑ i, (d i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 +
    max (3*(∑ i, (d i:ℝ)*w i)-5*(∑ i, (c i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 ≤
      (∑ i, (c i:ℝ)*w i)+(∑ i, (d i:ℝ)*w i)-
        2*(∑ i, w i)-(∑ i, activeIndicator (c i) (d i)*w i) := by
  have h₁ := weighted_positive_part (fun i => 3*(c i:ℝ)-5*(d i:ℝ)-activeIndicator (c i) (d i)) w hw
  have h₂ := weighted_positive_part (fun i => 3*(d i:ℝ)-5*(c i:ℝ)-activeIndicator (c i) (d i)) w hw
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (local_allowance (c i) (d i) (hc i) (hd i)) (hw i))
  simp only [sub_mul, add_mul, div_mul_eq_mul_div, mul_assoc,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    ] at h₁ h₂ hsum ⊢
  simp only [← Finset.sum_div] at hsum
  linarith

omit [DecidableEq ι] in
theorem actual_common_support_allowance (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (Z : ℝ) (hZ : 1 < Z) :
    let C := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)
    let D := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ)
    let P := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ)
    let R := Real.logb Z (Ideal.absNorm
      (∏ i ∈ activeSupport Finset.univ c d, Ideal.span {p i}) : ℝ)
    max (3*C-5*D-R) 0/6 + max (3*D-5*C-R) 0/6 ≤ C+D-2*P-R := by
  dsimp only
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
    log_norm_radical p hp,log_norm_radical p hp]
  simpa only [activeSupport,Finset.sum_filter,activeIndicator,ite_mul,one_mul,zero_mul]
    using weighted_allowance c d hc hd
      (fun i => Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ))
      (fun i => Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))))

end SevenEighths.CenteredMomentCommonAllowance

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

end SevenEighths.CenteredMomentSecondCanonical

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentFirstCanonicalAllowance
open ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentActive CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonAllowance
local notation "O" => ActualEisensteinCubic.O

theorem activeConductor_span_product (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [activeConductor, span_finitePrimeModulus]
  exact Finset.prod_coe_sort (s := ActiveIndex I J)
    (f := fun P : CommonIndex I J => P.val)

theorem active_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
      (leftExponent I J) (rightExponent I J), Ideal.span {commonPrime I J P}) =
      Ideal.span {activeConductor I J} := by
  simp_rw [commonPrime_span I J hI]
  exact (activeConductor_span_product I J).symm

theorem common_ideal_product (I J : Ideal O) :
    (∏ P : CommonIndex I J, P.val) = commonRadical I J := by
  exact Finset.prod_coe_sort (s := commonSupport I J) (f := fun P : Ideal O => P)

theorem common_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P : CommonIndex I J, Ideal.span {commonPrime I J P}) = commonRadical I J := by
  simp_rw [commonPrime_span I J hI]
  exact common_ideal_product I J

theorem actual_canonical_common_support_allowance
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z (C.absNorm : ℝ)
    let d := Real.logb Z (D.absNorm : ℝ)
    let p := Real.logb Z ((commonRadical C D).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_common_support_allowance (commonPrime C D)
    (commonPrime_supported C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) Z hZ
  dsimp only at h ⊢
  rw [left_ideal_product C D hC hCD, right_ideal_product C D hC hD hCD,
    common_generator_ideal_product C D hC, active_generator_ideal_product C D hC] at h
  exact h

theorem activeConductor_span_filter (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ (commonSupport I J).filter (fun P =>
        netExponent (CenteredExceptionalCount.valuation I P)
          (CenteredExceptionalCount.valuation J P) ≠ 0), P := by
  rw [activeConductor_span_product]
  simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
  exact Finset.prod_coe_sort (s := commonSupport I J)
    (f := fun P : Ideal O => if netExponent (CenteredExceptionalCount.valuation I P)
      (CenteredExceptionalCount.valuation J P) ≠ 0 then P else 1)

end SevenEighths.CenteredMomentFirstCanonicalAllowance

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedAllowance
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedAllowance
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstExceptionalPaidScales
local notation "O"=>ActualEisensteinCubic.O

lemma actual_allowance_sum (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(Z:ℝ)(hZ:1<Z):
    allowance C D Z+
      max (3*Real.logb Z (D.absNorm:ℝ)-5*Real.logb Z (C.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=
  actual_canonical_common_support_allowance C D hC hD hCD Z hZ

end SevenEighths.CenteredMomentFirstMixedAllowance

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

end SevenEighths.CenteredMomentSupportedZeroEnergy

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced
local notation "O"=>ActualEisensteinCubic.O

theorem scalar_norm (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀:ℝ)(hK:0<K)(_hA₀:0<A₀)(_hB₀:0<B₀):
    ‖scalar C D hC E K A₀ B₀‖=
      ‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖*Real.sqrt A₀*Real.sqrt B₀):=by
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero
      (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos he)
  unfold scalar
  rw [norm_mul,norm_div,norm_mul,
    norm_canonicalNormalizedGauss (activePrime C D) (activeCoprime C D) (activeGood C D hC)
      (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)]
  simp only [mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hk,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSourceLowerSupport
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma tuple_norm_product {ι:Type*} [Fintype ι] (v:Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct v):ℝ)=
      (∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ))*
      (Ideal.absNorm (v (Sum.inr 0)):ℝ)*(Ideal.absNorm (v (Sum.inr 1)):ℝ) := by
  simp only [finiteTupleProduct,map_prod,Nat.cast_prod,map_mul,Nat.cast_mul,Fintype.prod_sum_type,Fin.prod_univ_two]
  ring

 theorem profile_product_lower {ι:Type*} [Fintype ι]
    (R:Ideal O) (ν:ι→Ideal O→ℂ) (Wslot:ι→ℝ→ℂ) (P a:ι→ℝ)
    (W₁ W₂:ℝ→ℂ) (a₁ a₂ X₁ X₂ Y₁ Y₂ T:ℝ) (B₁ B₂ s:Ideal O)
    (hP:∀i,0<P i) (ha:∀i,0≤a i) (ha₁:0≤a₁) (ha₂:0≤a₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hB₁:B₁≠0) (hB₂:B₂≠0) (hXT:X₁*X₂=T) (hYT:Y₁*Y₂=T)
    (hs:∀i x,Wslot i x≠0→a i≤x)
    (hs₁:∀x,W₁ x≠0→a₁≤x) (hs₂:∀x,W₂ x≠0→a₂≤x)
    (v:Tuple ι) (hv:profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    (∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)≤
      (Ideal.absNorm (finiteTupleProduct v):ℝ) := by
  have hslot:∀i,Wslot i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/P i)≠0:=by
    intro i
    have hp: (∏j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))≠0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
    exact (mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _))).2
  have hrect:idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))≠0:=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  have hslots:(∏i,a i)*(∏i,P i)≤∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ):=by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun i _=>mul_nonneg (ha i) (hP i).le)
    intro i hi
    exact (le_div_iff₀ (hP i)).mp (hs i _ (hslot i))
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)<Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hplain:a₁*a₂*T≤(Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂*
      ((Ideal.absNorm (v (Sum.inr 0)):ℝ)*Ideal.absNorm (v (Sum.inr 1))) := by
    have hbranch (X Y:ℝ) (hX:0<X) (hY:0<Y) (hXY:X*Y=T)
        (hn:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X)*
          W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/Y)≠0) :
        a₁*a₂*T≤(Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂*
          ((Ideal.absNorm (v (Sum.inr 0)):ℝ)*Ideal.absNorm (v (Sum.inr 1))) := by
      have h1: a₁*X≤(Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ):=
        (le_div_iff₀ hX).mp (hs₁ _ (mul_ne_zero_iff.mp hn).1)
      have h2: a₂*Y≤(Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ):=
        (le_div_iff₀ hY).mp (hs₂ _ (mul_ne_zero_iff.mp hn).2)
      have hh:=mul_le_mul h1 h2 (mul_nonneg ha₂ hY.le) (Nat.cast_nonneg _)
      simp only [map_mul,Nat.cast_mul] at hh
      rw [←hXY]
      nlinarith
    unfold idealRectangle at hrect
    by_cases hx:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂)=0
    · have hy:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/Y₁)*
        W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/Y₂)≠0:=by
        intro hy
        exact hrect (by rw [hx,hy,sub_self])
      exact hbranch Y₁ Y₂ hY₁ hY₂ hYT hy
    · exact hbranch X₁ X₂ hX₁ hX₂ hXT hx
  have hT:0<T:=hXT ▸ mul_pos hX₁ hX₂
  have hp:=mul_le_mul hslots hplain (mul_nonneg (mul_nonneg ha₁ ha₂) hT.le)
    (Finset.prod_nonneg (fun _ _=>Nat.cast_nonneg _))
  rw [tuple_norm_product]
  have he:(∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)=
      ((∏i,a i)*(∏i,P i)*(a₁*a₂*T))/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))).mpr
  convert (preTransparency := .instances) hp using 1 ; ring

 theorem profile_column_lower {ι:Type*} [Fintype ι]
    (R:Ideal O) (ν:ι→Ideal O→ℂ) (Wslot:ι→ℝ→ℂ) (P a:ι→ℝ)
    (W₁ W₂:ℝ→ℂ) (a₁ a₂ X₁ X₂ Y₁ Y₂ T:ℝ) (B₁ B₂ s:Ideal O)
    (hP:∀i,0<P i) (ha:∀i,0≤a i) (ha₁:0≤a₁) (ha₂:0≤a₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hB₁:B₁≠0) (hB₂:B₂≠0) (hXT:X₁*X₂=T) (hYT:Y₁*Y₂=T)
    (hs:∀i x,Wslot i x≠0→a i≤x)
    (hs₁:∀x,W₁ x≠0→a₁≤x) (hs₂:∀x,W₂ x≠0→a₂≤x)
    (S:Finset (Tuple ι)) (I:Ideal O)
    (hI:finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) :
    (∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)≤
      (Ideal.absNorm I:ℝ) := by
  obtain ⟨v,hv,hv0,he⟩:=CenteredMomentSupportedZeroEnergy.finiteColumnCoefficient_witness S
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I hI
  have hh:=profile_product_lower R ν Wslot P a W₁ W₂ a₁ a₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP ha ha₁ ha₂ hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hXT hYT hs hs₁ hs₂ v hv0
  simpa only [he] using hh

end SevenEighths.CenteredMomentSourceLowerSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSourceSupport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstWholeKernel
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceLowerSupport CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstPhysicalSourceSupport.instDecidableEqSumFinOfNatNat_definitions
theorem nonzero_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ∃a:columns C C hC.1 S,∃b:columns C D hD.1 S,
      c (C*(a:Ideal O))≠0 ∧ c (D*(b:Ideal O))≠0 ∧
      V 2 (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))≠0 ∧
      V 3 (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀))≠0 := by
  unfold block at hn
  have hs:=right_ne_zero_of_mul hn
  obtain ⟨z,hz,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨a,ha,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨b,hb,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  dsimp only at hs
  split_ifs at hs with hab
  · have hprod:=left_ne_zero_of_mul (left_ne_zero_of_mul hs)
    have hc:=right_ne_zero_of_mul hprod
    have hw:=right_ne_zero_of_mul (left_ne_zero_of_mul hs)
    refine ⟨a,b,?_,?_,?_,?_⟩
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul hc)
    · have hh:=right_ne_zero_of_mul hc
      rw [star_ne_zero] at hh
      exact left_ne_zero_of_mul hh
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul hw)
    · exact right_ne_zero_of_mul hw
  · exact False.elim (hs rfl)

theorem original_column_lower {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(a₁ a₂:ℝ)(ha₁:0≤a₁)(ha₂:0≤a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hn:CenteredMomentOriginalCommonHarmonic.coefficient s R seed I≠0):
    (∏i,s.lo i)*a₁*a₂*volume s.toData≤(I.absNorm:ℝ) := by
  have hh:=profile_column_lower R s.ν s.W s.P s.lo s.W₁ s.W₂ a₁ a₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos
    (fun i=>(s.lo_pos i).le) ha₁ ha₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product (fun i x hx=>(s.support i hx).1)
    hs₁ hs₂ (Fintype.piFinset s.pools) I (by
      simpa only [CenteredMomentOriginalCommonHarmonic.coefficient] using hn)
  simpa only [map_one,Nat.cast_one,mul_one,div_one,volume,mul_assoc] using hh

lemma log_window_upper (N H M:ℝ)(hN:0<N)(hH:0<H)
    (hlog:|Real.log (N/H)|≤M):N≤Real.exp M*H := by
  have hl:Real.log (N/H)≤M:=(le_abs_self _).trans hlog
  have he:=Real.exp_le_exp.mpr hl
  rw [Real.exp_log (div_pos hN hH)] at he
  exact (div_le_iff₀ hH).mp he

theorem block_reference_lower (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ a T M:ℝ)
    (hA:0<A₀)(hB:0<B₀)(hsource:∀I,c I≠0→a*T≤(I.absNorm:ℝ))
    (hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    a*T≤(C.absNorm:ℝ)*Real.exp M*A₀ ∧
      a*T≤(D.absNorm:ℝ)*Real.exp M*B₀ := by
  obtain ⟨i,j,hi,hj,hwi,hwj⟩:=nonzero_columns η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀ hn
  have hiN:(0:ℝ)<(i:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C C hC.1 S i).1)
  have hjN:(0:ℝ)<(j:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD.1 S j).1)
  have hni:‖eisEmbedding (element C C hC.1 S i)‖^2=((i:Ideal O).absNorm:ℝ):=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hnj:‖eisEmbedding (element C D hD.1 S j)‖^2=((j:Ideal O).absNorm:ℝ):=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hli:=hwin 2 _ hwi
  have hlj:=hwin 3 _ hwj
  rw [hni] at hli
  rw [hnj] at hlj
  have hsi:=hsource _ hi
  have hsj:=hsource _ hj
  simp only [map_mul,Nat.cast_mul] at hsi hsj
  constructor
  · exact hsi.trans (by nlinarith [log_window_upper _ _ M hiN hA hli])
  · exact hsj.trans (by nlinarith [log_window_upper _ _ M hjN hB hlj])

lemma reference_sqrt_lower (NC ND A₀ B₀ a T M:ℝ)
    (hNC:0≤NC)(hND:0≤ND)(hA:0≤A₀)(_hB:0≤B₀)(ha:0≤a)(hT:0≤T)
    (hl:a*T≤NC*Real.exp M*A₀)(hr:a*T≤ND*Real.exp M*B₀):
    a*T≤Real.exp M*Real.sqrt (NC*ND)*(Real.sqrt A₀*Real.sqrt B₀) := by
  have hh:=mul_le_mul hl hr (mul_nonneg ha hT) (by positivity : 0≤NC*Real.exp M*A₀)
  have hs:(a*T)^2≤(NC*ND)*(Real.exp M)^2*(A₀*B₀):=by nlinarith [hh]
  have hsqrt:=Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq (mul_nonneg ha hT),
    Real.sqrt_mul (mul_nonneg (mul_nonneg hNC hND) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hNC hND),Real.sqrt_sq (Real.exp_pos M).le,
    Real.sqrt_mul hA] at hsqrt
  nlinarith [hsqrt]

end SevenEighths.CenteredMomentFirstPhysicalSourceSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstNonexceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalSourceSupport
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentSupportedCorrelation
local notation "O"=>ActualEisensteinCubic.O

lemma pair_conductor_root (q₁ q₂ B:ℝ)(_h₁:0≤q₁)(h₂:0≤q₂)
    (hB:0≤B)(hb₁:q₁≤B)(hb₂:q₂≤B):Real.sqrt (q₁*q₂)≤B := by
  have hh:=mul_le_mul hb₁ hb₂ h₂ hB
  have hs:=Real.sqrt_le_sqrt hh
  simpa only [←pow_two,Real.sqrt_sq hB] using hs

lemma scalar_conductor_algebra (s μ K T N E r C F q q₁ q₂:ℝ)
    (_hs:0≤ s)(hμ:0≤μ)(hK:0≤K)(_hT:0<T)(hN:0<N)(hE:0<E)(hr:0< r)
    (hC:0≤C)(hF:0≤F)(hq:0≤q)(h₁:0≤q₁)(h₂:0≤q₂)
    (hscalar:s*T≤μ*C*K*Real.sqrt N/(E*r))
    (hc₁:q₁≤F*q*E*r^2)(hc₂:q₂≤F*q*E*r^2):
    s*T/N*Real.sqrt (q₁*q₂)≤μ*C*F*K*q*(r/Real.sqrt N) := by
  have hroot:=pair_conductor_root q₁ q₂ (F*q*E*r^2) h₁ h₂ (by positivity) hc₁ hc₂
  calc
    _≤(μ*C*K*Real.sqrt N/(E*r))/N*(F*q*E*r^2):=
      mul_le_mul (div_le_div_of_nonneg_right hscalar hN.le) hroot
        (Real.sqrt_nonneg _) (by positivity)
    _=μ*C*F*K*q*(r/Real.sqrt N):=by
      have hn:Real.sqrt N≠0:=ne_of_gt (Real.sqrt_pos.mpr hN)
      have hn2:=Real.sq_sqrt hN.le
      field_simp
      linear_combination μ*C*K*F*q*hn2

theorem weighted_scalar_volume (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  have hs:=reference_sqrt_lower (C.absNorm:ℝ) (D.absNorm:ℝ) A₀ B₀ a T M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA.le hB.le ha.le hT.le hl hr
  have hden:0<Real.sqrt A₀*Real.sqrt B₀:=mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hratio:T/(Real.sqrt A₀*Real.sqrt B₀)≤Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a:=by
    apply (div_le_div_iff₀ hden ha).mpr
    nlinarith [hs]
  rw [scalar_norm C D hC E K A₀ B₀ hK hA hB]
  calc
    _=(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(T/(Real.sqrt A₀*Real.sqrt B₀)):=by ring
    _≤(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a):=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentFirstNonexceptionalPrefactor

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

theorem fixed_pair_presentation_caps (η τ₁ τ₂:Character)(C D:Ideal O)
    (E:Finset (CommonIndex C D))
    (hM₁:τ₁.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (hM₂:τ₂.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (τ₁.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (τ₂.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  ⟨(fixed_presentation_norm η τ₁ C D E hM₁).le,(fixed_presentation_norm η τ₂ C D E hM₂).le⟩

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem FixedPair.conductor_caps {η:Character}{C D:Ideal O}{hC:Supported C}
    {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}(F:FixedPair η C D hC E ξ₁ ξ₂):
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  fixed_pair_presentation_caps η F.left F.right C D E F.left_modulus F.right_modulus

variable {ι:Type*}[Fintype ι]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedRoot
open CanonicalQuadraticSieve CenteredMomentFirstMixedAllowance
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily
open CenteredMomentFirstScale CenteredMomentSupportedCorrelation
local notation "O"=>HeckeFamily.O

lemma active_span_swap (C D:Ideal O):
    Ideal.span {activeConductor D C}=Ideal.span {activeConductor C D}:=by
  rw [activeConductor_span_filter,activeConductor_span_filter,
    CenteredMomentCompleteCommon.commonSupport_comm D C]
  congr 1
  apply Finset.filter_congr
  intro P hP
  simp only [CenteredMomentActive.netExponent]
  omega

lemma allowance_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(Z:ℝ)(hZ:1<Z):
    allowance C D Z+allowance D C Z≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=by
  have hh:=actual_allowance_sum C D hC hD hCD Z hZ
  simpa only [allowance,active_span_swap C D] using hh

lemma allowance_root (Z C D P R b:ℝ)(hZ:1<Z)(hC:0<C)(hD:0<D)(hP:0<P)(hR:0<R)
    (hb:b≤Real.logb Z C+Real.logb Z D-2*Real.logb Z P-Real.logb Z R):
    Real.sqrt R/Real.sqrt (C*D)*Z^(b/2)≤1/P:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hlz:0<Real.log Z:=Real.log_pos hZ
  have hb':b≤(Real.log C+Real.log D-2*Real.log P-Real.log R)/Real.log Z:=by
    convert (preTransparency := .instances) hb using 1 ; simp only [Real.logb] ; ring
  have hh: b*Real.log Z≤Real.log C+Real.log D-2*Real.log P-Real.log R:=
    (le_div_iff₀ hlz).mp hb'
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_sqrt,
    Real.log_rpow,Real.log_one]
  nlinarith

lemma paired_reference_root (qL qR V C D Z bL bR EL ER:ℝ)
    (hqL:0<qL)(hqR:0<qR)(hV:0<V)(hC:0<C)(hD:0<D)(hZ:0<Z)
    (_hEL:0≤EL)(_hER:0≤ER):
    Real.sqrt ((qL*(V/C)^2*Z^bL*EL)*(qR*(V/D)^2*Z^bR*ER))=
      V^2/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2)*Real.sqrt (EL*ER):=by
  have hbase:Real.sqrt ((qL*(V/C)^2*Z^bL)*(qR*(V/D)^2*Z^bR))=
      V^2/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2):=by
    apply Real.log_injOn_pos
    · simp only [Set.mem_Ioi];positivity
    · simp only [Set.mem_Ioi];positivity
    · simp (disch := positivity) only [Real.log_sqrt,Real.log_mul,Real.log_div,
        Real.log_pow,Real.log_rpow]
      ring
  rw [show (qL*(V/C)^2*Z^bL*EL)*(qR*(V/D)^2*Z^bR*ER)=
    ((qL*(V/C)^2*Z^bL)*(qR*(V/D)^2*Z^bR))*(EL*ER) by ring,
    Real.sqrt_mul (by positivity),hbase]

theorem actual_fixed_reference_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(η:Character)(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair η C D hC E ξ₁ ξ₂)
    (K A₀ B₀ a T M Z EL ER:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)
    (ha:0<a)(hT:0<T)(hZ:1<Z)(hEL:0≤EL)(hER:0≤ER)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖/T*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(T/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(T/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have hF:0<fixedPresentationCost:=fixedPresentationCost_pos
  have hNC:0<(C.absNorm:ℝ):=norm_pos C hC.1
  have hND:0<(D.absNorm:ℝ):=norm_pos D hD.1
  have hNR:0<((Ideal.span {activeConductor C D}).absNorm:ℝ):=active_norm_pos C D
  have hP:0<((commonRadical C D).absNorm:ℝ):=norm_pos _ (commonRadical_ne_zero C D)
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖eisEmbedding (activeConductor C D)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hs:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) fixedPresentationCost
    (η.modulus.absNorm:ℝ) (F.left.modulus.absNorm:ℝ) (F.right.modulus.absNorm:ℝ)
    (norm_nonneg _) (norm_nonneg _) hK.le hT (mul_pos hNC hND)
    (sq_pos_of_pos he) hrpos (by positivity) fixedPresentationCost_pos.le (Nat.cast_nonneg _)
    hqL.le hqR.le (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr)
    F.conductor_caps.1 F.conductor_caps.2
  have haR:=allowance_root Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((commonRadical C D).absNorm:ℝ) ((Ideal.span {activeConductor C D}).absNorm:ℝ)
    (allowance C D Z+allowance D C Z) hZ hNC hND hP hNR
    (allowance_pair C D hC hD hCD Z hZ)
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at haR
  rw [paired_reference_root _ _ T _ _ Z _ _ EL ER hqL hqR hT hNC hND
    (zero_lt_one.trans hZ) hEL hER]
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=by
      field_simp
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)*
        (‖eisEmbedding (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _=(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        ((‖eisEmbedding (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm))*
          Z^((allowance C D Z+allowance D C Z)/2))*Real.sqrt (EL*ER):=by ring
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        (1/(commonRadical C D).absNorm)*Real.sqrt (EL*ER):=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haR (by positivity))
        (Real.sqrt_nonneg _)
    _=_:=by ring

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

theorem original_fixed_reference_pair {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z EL ER:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:0≤EL)(hER:0≤ER)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W U
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_fixed_reference_pair C D hC hD hCD E s.η ξ₁ ξ₂ F
    K A₀ B₀ _ _ M Z EL ER hK hA hB ha (volume_pos s.toData) hZ hEL hER hl hr

end SevenEighths.CenteredMomentFirstMixedRoot

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedWindow
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedWindow
open CenteredMomentFirstMixedRoot CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstNonexceptionalPrefactor
local notation "O"=>HeckeFamily.O

theorem original_four_budget_reference_oai {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z:ℝ)(EL ER:Fin 4→ℝ)(JL JR:ℕ)(height:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:∀i,0≤EL i)(hER:∀i,0≤ER i)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (∑i:Fin 4,∑j:Fin 4,
        windowBudget JL height ((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i)*
        windowBudget JR height ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER j))≤
      (‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
        (∑i:Fin 4,∑j:Fin 4,windowBudget JL height (EL i)*windowBudget JR height (ER j)) :=by
  dsimp only
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hh:=original_fixed_reference_pair s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
    m A t S C D hC hD hCD E ξ₁ ξ₂ F rows W U K K₀ H₀ A₀ B₀ M Z
    (EL i) (ER j) hK hA hB hZ (hEL i) (hER j) hwin hn
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have hCpos:=norm_pos C hC.1
  have hDpos:=norm_pos D hD.1
  have hV:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hei:=hEL i
  have herj:=hER j
  have hh':=mul_le_mul_of_nonneg_right hh
    (mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JL)
      (profileMoment_nonneg JL)) (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JR)
      (profileMoment_nonneg JR)))
  simp only [Real.sqrt_mul (by positivity : 0≤
    (F.left.modulus.absNorm:ℝ)*(volume s.toData/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i),
    Real.sqrt_mul (hEL i)] at hh'
  unfold windowBudget
  nlinarith only [hh']

end SevenEighths.CenteredMomentFirstMixedWindow

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentFirstMixedWindow.original_four_budget_reference_oai.{u_1} := @OAI.SevenEighths.CenteredMomentFirstMixedWindow.original_four_budget_reference_oai.{u_1}

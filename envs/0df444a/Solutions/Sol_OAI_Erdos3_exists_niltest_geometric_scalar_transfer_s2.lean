-- Prove2me | solution 1 for OAI.Erdos3.exists_niltest_geometric_scalar_transfer_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:14:40.525976+00:00
-- url     : https://prove2.me/submissions/853e3180-9f56-423c-beef-0df435fcc93b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_exists_allocated_affine_secondary_mesh_s2
import Theorems.Thm_OAI_Erdos3_exists_niltest_mesh_scalar_transfer_s2
import Theorems.Thm_OAI_Erdos3_ordinaryMesh_marginals_of_lengths_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSliceCost
namespace OAI

section

namespace Erdos3

theorem ResidueSliceLogCostLE.mono {σ : Type*} {H N : σ → ℕ} {lo a : σ → ℤ}
    {M : ℕ} {P Q : ℝ} (h : ResidueSliceLogCostLE H lo N M a P) (hPQ : P ≤ Q) :
    ResidueSliceLogCostLE H lo N M a Q := by
  intro j
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPQ))
    (Nat.cast_nonneg (H j))).trans (h j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SpectralLogBudget
namespace OAI

section

namespace Erdos3

theorem log_sixteen_div_le {epsilon A : ℝ} (hepsilon : 0 < epsilon)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) : Real.log (16 / epsilon) ≤ A + 4 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hb : 16 / epsilon ≤ Real.exp (A + 4) := by
    calc
      _ = 16 * epsilon⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4 * Real.exp A :=
        mul_le_mul h16 hinverse (inv_nonneg.mpr hepsilon.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 16 / epsilon) hb
  simpa only [Real.log_exp] using hlog

theorem CyclicCrootSisask.spectralIterations_le_logBudget {epsilon p A : ℝ}
    (hepsilon : 0 < epsilon) (hp : 0 ≤ p) (hA : 0 ≤ A)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) :
    (spectralIterations epsilon p : ℝ) ≤ 2 * (p + A + 4) + 2 := by
  have hlog := log_sixteen_div_le hepsilon hinverse
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (p + Real.log (16 / epsilon)) / Real.log 2 ≤ 2 * (p + A + 4) := by
    apply (div_le_iff₀ htwo).mpr
    have hm := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 2 * (p + A + 4))
    nlinarith
  have hm : (⌈(p + Real.log (16 / epsilon)) / Real.log 2⌉₊ : ℝ) ≤
      (⌈2 * (p + A + 4)⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hdiv
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * (p + A + 4))
  unfold spectralIterations
  push_cast
  linarith

theorem affineAllowance_inverse_le_exp {epsilon A : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) :
    (epsilon / (2 + epsilon))⁻¹ ≤ Real.exp (A + 2) := by
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [inv_div, div_eq_mul_inv]
  calc
    _ ≤ 3 * Real.exp A := mul_le_mul (by linarith) hinverse
      (inv_nonneg.mpr hepsilon.le) (by norm_num)
    _ ≤ Real.exp 2 * Real.exp A := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

theorem affineComparisonScale_bounds {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    0 ≤ affineComparisonScale ε L T C ∧
    L + T + 2 ≤ affineComparisonScale ε L T C ∧
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤ affineComparisonScale ε L T C ∧
    C ≤ affineComparisonScale ε L T C := by
  have hn : (0 : ℝ) ≤ (affineRemovalDepth T + affineComparisonTail ε L T : ℕ) := Nat.cast_nonneg _
  unfold affineComparisonScale
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem affineComparisonMoment_bounds {P : ℝ} (hP : 0 ≤ P) :
    2 ≤ affineComparisonMoment P ∧ Even (affineComparisonMoment P) ∧
    P ≤ (affineComparisonMoment P : ℝ) ∧ (affineComparisonMoment P : ℝ) ≤ P + 2 := by
  unfold affineComparisonMoment
  refine ⟨by omega, even_two_mul _, ?_, ?_⟩
  · have h := Nat.lt_floor_add_one (P / 2)
    push_cast
    linarith
  · have h := Nat.floor_le (by positivity : 0 ≤ P / 2)
    push_cast
    linarith

end Erdos3

end

section

namespace Erdos3

theorem affinePrimitiveLogBudget_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affinePrimitiveLogBudget P := by unfold affinePrimitiveLogBudget; positivity

theorem affineRemovalDepth_le_logBudget {T P : ℝ} (hT : 0 ≤ T) (hTP : T ≤ P) :
    (affineRemovalDepth T : ℝ) ≤ 2 * P + 10 := by
  have h := CyclicCrootSisask.spectralIterations_le_logBudget (epsilon := 1) (A := 0)
    (by norm_num) hT le_rfl (by simp)
  change (affineRemovalDepth T : ℝ) ≤ _ at h
  linarith

theorem affineComparisonTail_le_logBudget {epsilon L T P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLP : L ≤ P) (hTP : T ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) :
    (affineComparisonTail epsilon L T : ℝ) ≤ 8 * P + 22 := by
  have h := CyclicCrootSisask.spectralIterations_le_logBudget
    (epsilon := epsilon / (2 + epsilon)) (p := L + 2 * T + 4) (A := P + 2)
    (by positivity) (by positivity) (by positivity)
    (affineAllowance_inverse_le_exp hepsilon hepsilon1 hinverse)
  change (affineComparisonTail epsilon L T : ℝ) ≤ _ at h
  linarith

theorem affineComparisonPrimitive_bounds {epsilon L T C P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) :
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P ∧
      affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P ∧
      (affineComparisonMoment (affineComparisonScale epsilon L T C) : ℝ) ≤ affinePrimitiveLogBudget P + 2 := by
  have hj := affineRemovalDepth_le_logBudget hT hTP
  have ht := affineComparisonTail_le_logBudget hepsilon hepsilon1 hP hL hT hLP hTP hinverse
  have hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤
      10 * P + 32 := by push_cast; linarith
  have hs : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P := by
    unfold affineComparisonScale affinePrimitiveLogBudget
    linarith
  refine ⟨?_, hs, ?_⟩
  · unfold affinePrimitiveLogBudget
    linarith
  · have hm := (affineComparisonMoment_bounds (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1).2.2.2
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem periodPrimeCoordinates_card_pow_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) : 2 ^ (periodPrimeCoordinates prime M).card ≤ M := by
  classical
  let A := periodPrimeCoordinates prime M
  have hsub : A.image prime ⊆ M.primeFactors := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime i, (mem_periodPrimeCoordinates prime M i).mp hi, hM.ne'⟩
  have hcard : A.card ≤ M.primeFactors.card := by
    rw [← Finset.card_image_of_injective A hinj]
    exact Finset.card_le_card hsub
  calc
    2 ^ A.card ≤ 2 ^ M.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ = ∏ _p ∈ M.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ M.primeFactors, p := Finset.prod_le_prod' fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

theorem periodPrimeCoordinates_card_log_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) :
    (periodPrimeCoordinates prime M).card * Real.log 2 ≤ Real.log M := by
  have hpow : (2 : ℝ) ^ (periodPrimeCoordinates prime M).card ≤ M := by
    exact_mod_cast periodPrimeCoordinates_card_pow_le prime hprime hinj hM
  simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpow

theorem periodPrimeCoordinates_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) {B : ℝ} (hMB : (M : ℝ) ≤ Real.exp B) :
    ((periodPrimeCoordinates prime M).card : ℝ) ≤ 2 * B := by
  have h := (periodPrimeCoordinates_card_log_le prime hprime hinj hM).trans
    ((Real.log_le_iff_le_exp (by exact_mod_cast hM)).mpr hMB)
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht ⊢
    linarith
  have hc : (0 : ℝ) ≤ (periodPrimeCoordinates prime M).card := Nat.cast_nonneg _
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem mem_affineMandatoryPrimes {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (i : ι) :
    i ∈ affineMandatoryPrimes prime ξ P ↔ (prime i : ℝ) ≤ affineComparisonPrimeThreshold ξ P := by
  simp only [affineMandatoryPrimes, Finset.mem_filter, Finset.mem_univ, true_and]

theorem affineMandatoryPrimes_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hinj : Function.Injective prime) (ξ P : ℝ) (hP : 0 ≤ P) :
    ((affineMandatoryPrimes prime ξ P).card : ℝ) ≤ affineComparisonPrimeThreshold ξ P + 2 := by
  let n := ⌈affineComparisonPrimeThreshold ξ P⌉₊
  have hsub : (affineMandatoryPrimes prime ξ P).image prime ⊆ Finset.range (n + 1) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hle : (prime i : ℝ) ≤ (n : ℝ) :=
      ((mem_affineMandatoryPrimes prime ξ P i).mp hi).trans (Nat.le_ceil _)
    have hn : prime i ≤ n := by exact_mod_cast hle
    exact Finset.mem_range.mpr (by omega)
  have hc : (affineMandatoryPrimes prime ξ P).card ≤ n + 1 := by
    calc
      _ = ((affineMandatoryPrimes prime ξ P).image prime).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.range (n + 1)).card := Finset.card_le_card hsub
      _ = _ := Finset.card_range _
  have ht : 0 ≤ affineComparisonPrimeThreshold ξ P := by unfold affineComparisonPrimeThreshold; positivity
  have hn := Nat.ceil_lt_add_one ht
  have hc' : ((affineMandatoryPrimes prime ξ P).card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hc
  change (n : ℝ) < affineComparisonPrimeThreshold ξ P + 1 at hn
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem affineInitialPrimeMask_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {ξ P sourceLog siteLog : ℝ} {sourceM siteM : ℕ}
    (hP : 0 ≤ P) (hsourceM : 0 < sourceM) (hsiteM : 0 < siteM)
    (hsource : (sourceM : ℝ) ≤ Real.exp sourceLog) (hsite : (siteM : ℝ) ≤ Real.exp siteLog) :
    ((affineInitialPrimeMask prime ξ P sourceM siteM).card : ℝ) ≤
      affineComparisonPrimeThreshold ξ P + 2 + 2 * sourceLog + 2 * siteLog := by
  have hmandatory := affineMandatoryPrimes_card_le prime hinj ξ P hP
  have hs := periodPrimeCoordinates_card_le prime hprime hinj hsourceM hsource
  have ht := periodPrimeCoordinates_card_le prime hprime hinj hsiteM hsite
  have hcard : (affineInitialPrimeMask prime ξ P sourceM siteM).card ≤
      (affineMandatoryPrimes prime ξ P).card + (periodPrimeCoordinates prime sourceM).card +
        (periodPrimeCoordinates prime siteM).card := by
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hcard' : ((affineInitialPrimeMask prime ξ P sourceM siteM).card : ℝ) ≤
      ((affineMandatoryPrimes prime ξ P).card : ℝ) + ((periodPrimeCoordinates prime sourceM).card : ℝ) +
        ((periodPrimeCoordinates prime siteM).card : ℝ) := by exact_mod_cast hcard
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem affineSamplerPrimeMask_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {ξ P sourceLog siteLog parameterLog : ℝ} {sourceM siteM D : ℕ}
    (hP : 0 ≤ P) (hsourceM : 0 < sourceM) (hsiteM : 0 < siteM) (hD : 0 < D)
    (hsource : (sourceM : ℝ) ≤ Real.exp sourceLog) (hsite : (siteM : ℝ) ≤ Real.exp siteLog)
    (hparameter : (D : ℝ) ≤ Real.exp parameterLog) :
    ((affineSamplerPrimeMask prime ξ P sourceM siteM D).card : ℝ) ≤
      affineComparisonPrimeThreshold ξ P + 2 + 2 * sourceLog + 2 * siteLog + 2 * parameterLog := by
  have hbase := affineInitialPrimeMask_card_le (ξ := ξ) prime hprime hinj hP hsourceM hsiteM hsource hsite
  have hp := periodPrimeCoordinates_card_le prime hprime hinj hD hparameter
  have hcard : ((affineSamplerPrimeMask prime ξ P sourceM siteM D).card : ℝ) ≤
      ((affineInitialPrimeMask prime ξ P sourceM siteM).card : ℝ) +
        ((periodPrimeCoordinates prime D).card : ℝ) := by
    exact_mod_cast Finset.card_union_le (affineInitialPrimeMask prime ξ P sourceM siteM) (periodPrimeCoordinates prime D)
  linarith

end Erdos3

end

section

namespace Erdos3

theorem affineReferenceInput_bounds (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    2 ≤ affineReferenceInput epsilon U ∧ U ≤ affineReferenceInput epsilon U ∧
      affinePrimitiveLogBudget U ≤ affineReferenceInput epsilon U := by
  have hpow : 0 ≤ (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon :=
    pow_nonneg (by unfold affinePrimitiveLogBudget; positivity) _
  unfold affineReferenceInput affinePrimitiveLogBudget at *
  constructor
  · linarith
  constructor <;> linarith

theorem affineReferenceInput_mask_and_depth {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (D : ℕ) (hD : 0 < D) {epsilon L T C U : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hU : 0 ≤ U)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hLU : L ≤ U) (hTU : T ≤ U) (hCU : C ≤ U)
    (hepsInv : epsilon⁻¹ ≤ Real.exp U) (hDU : (D : ℝ) ≤ Real.exp U) :
    ((affineSamplerPrimeMask prime (epsilon / (2 + epsilon))
      (affineComparisonScale epsilon L T C) 1 1 D).card : ℝ) ≤ affineReferenceInput epsilon U ∧
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affineReferenceInput epsilon U ∧
    T + 4 ≤ affineReferenceInput epsilon U := by
  have hprim := affineComparisonPrimitive_bounds hepsilon hepsilon1 hU hL hT hC hLU hTU hCU hepsInv
  have hs := (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1
  have hm := affineSamplerPrimeMask_card_le (ξ := epsilon / (2 + epsilon)) prime hprime hinj hs
    (by norm_num : 0 < (1 : ℕ)) (by norm_num : 0 < (1 : ℕ)) hD
    (by simp : ((1 : ℕ) : ℝ) ≤ Real.exp 0) (by simp : ((1 : ℕ) : ℝ) ≤ Real.exp 0) hDU
  have hthreshold : affineComparisonPrimeThreshold (epsilon / (2 + epsilon))
      (affineComparisonScale epsilon L T C) ≤
      (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon := by
    exact pow_le_pow_left₀ (by linarith) (by linarith [hprim.2.1]) _
  have hbudget := affineReferenceInput_bounds epsilon hU
  refine ⟨?_, hprim.1.trans hbudget.2.2, ?_⟩
  · unfold affineReferenceInput
    norm_num at hm
    linarith [affinePrimitiveLogBudget_nonneg hU]
  · have hpow : 0 ≤ (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon :=
      pow_nonneg (by unfold affinePrimitiveLogBudget; positivity) _
    unfold affineReferenceInput affinePrimitiveLogBudget at *
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

theorem ResidueSliceUpperComparison.restrict_budget_and_error {I : Type*}
    [Fintype I] [DecidableEq I] {h g : (I → ℤ) → ℂ} {lo : I → ℤ} {N : I → ℕ}
    {originalBudget referenceBudget level originalError referenceError : ℝ}
    (hupper : ResidueSliceUpperComparison h g lo N originalBudget level originalError)
    (hbudget : referenceBudget ≤ originalBudget) (herror : originalError ≤ referenceError) :
    ResidueSliceUpperComparison h g lo N referenceBudget level referenceError := by
  intro cellLo cellN M a hM hsub hcost
  exact (hupper cellLo cellN M a hM hsub (hcost.mono hbudget)).trans (by linarith)

theorem ResidueSliceUpperComparison.from_exponential_budget {I : Type*}
    [Fintype I] [DecidableEq I] {h g : (I → ℤ) → ℂ} {lo : I → ℤ} {N : I → ℕ}
    {originalBudget referenceBudget level densityLog tail : ℝ}
    (hupper : ResidueSliceUpperComparison h g lo N originalBudget level (Real.exp (-originalBudget)))
    (hbudget : referenceBudget ≤ originalBudget) (hprecision : densityLog + tail + 4 ≤ originalBudget) :
    ResidueSliceUpperComparison h g lo N referenceBudget level (affineIncrementTolerance densityLog tail) := by
  exact hupper.restrict_budget_and_error hbudget (Real.exp_le_exp.mpr (by linarith))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueTruncationCap_nonneg (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) {eta : ℝ} (heta : 0 ≤ eta) : 0 ≤ residueTruncationCap ι b eta := by
  unfold residueTruncationCap
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedBoxPartitions_step {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    (normalizedBoxPartitions N H ρ hlarge hwhole i).step c = 1 := rfl

theorem normalizedBoxPartitions_lengths {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    ρ * H i / 4 ≤ ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ∧
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ≤ ρ * H i := by
  obtain ⟨_, _, hlo, hup⟩ := normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)
  have hl := comparableBoxPartitions_length N (fun j => ⌊ρ * H j / 2⌋₊)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).1)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).2.1) i c
  have hl' : (⌊ρ * H i / 2⌋₊ : ℝ) ≤
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) := by exact_mod_cast hl.1
  have hu' : ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) <
      2 * (⌊ρ * H i / 2⌋₊ : ℝ) := by exact_mod_cast hl.2
  exact ⟨hlo.trans hl', by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

theorem residueTruncationCap_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℕ) {P eta : ℝ} (hP : 0 ≤ P) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    residueTruncationCap ι b eta ≤ Real.exp ((b : ℝ) * (P + 2) + 1) := by
  have hc := lowDegreeCoordinateSets_card_le_exp hP hcount b
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ b ≤ Real.exp b := by
    calc
      _ ≤ (Real.exp 1) ^ b := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo b
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  unfold residueTruncationCap
  calc
    _ ≤ Real.exp ((b : ℝ) * (P + 1)) * Real.exp b * Real.exp 1 :=
      mul_le_mul (mul_le_mul hc hp (by positivity) (Real.exp_nonneg _))
        (by linarith : 1 + eta ≤ Real.exp 1) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem scalarTransferMarginalAccuracy_cost {targetLog capLog cap : ℝ}
    (hcap : cap ≤ Real.exp capLog) :
    scalarTransferMarginalAccuracy targetLog capLog * cap ≤ scalarTransferBaseAccuracy targetLog := by
  calc
    _ ≤ Real.exp (-(targetLog + capLog + 10)) * Real.exp capLog :=
      mul_le_mul_of_nonneg_left hcap (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem scalarTransfer_combined_error_le {epsilon level targetLog capLog cap : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (_hlevel : 0 ≤ level) (hlevel2 : level ≤ 2) (hcap0 : 0 ≤ cap)
    (hcap : cap ≤ Real.exp capLog) :
    100 * (1 + epsilon) * Real.exp (-scalarTransferTail targetLog / 2) +
      (1 + epsilon) * scalarTransferBaseAccuracy targetLog +
      (1 + (1 + epsilon) * level) *
        ((scalarTransferMarginalAccuracy targetLog capLog + scalarTransferMarginalAccuracy targetLog capLog) * cap +
          scalarTransferBaseAccuracy targetLog) ≤ Real.exp (-targetLog) / 2 := by
  let a := scalarTransferBaseAccuracy targetLog
  have ha : 0 < a := Real.exp_pos _
  have ht : Real.exp (-scalarTransferTail targetLog / 2) = a := by
    congr 1
    unfold scalarTransferTail
    ring
  have hm := scalarTransferMarginalAccuracy_cost (targetLog := targetLog) hcap
  have hsmall : (scalarTransferMarginalAccuracy targetLog capLog + scalarTransferMarginalAccuracy targetLog capLog) * cap + a ≤ 3 * a := by
    change scalarTransferMarginalAccuracy targetLog capLog * cap ≤ a at hm
    nlinarith
  have hsmall0 : 0 ≤ (scalarTransferMarginalAccuracy targetLog capLog + scalarTransferMarginalAccuracy targetLog capLog) * cap + a := by
    unfold scalarTransferMarginalAccuracy
    positivity
  have hcoeff : 1 + (1 + epsilon) * level ≤ 5 := by nlinarith
  have hprod := mul_le_mul hcoeff hsmall hsmall0 (by norm_num : (0 : ℝ) ≤ 5)
  have h512 : (512 : ℝ) ≤ Real.exp 10 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      512 ≤ (2 : ℝ) ^ 10 := by norm_num
      _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) htwo 10
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hpaid : 512 * a ≤ Real.exp (-targetLog) := by
    calc
      _ ≤ Real.exp 10 * a := mul_le_mul_of_nonneg_right h512 ha.le
      _ = _ := by dsimp only [a, scalarTransferBaseAccuracy]; rw [← Real.exp_add]; congr 1; ring
  rw [ht]
  change 100 * (1 + epsilon) * a + (1 + epsilon) * a + _ ≤ _
  have hc := mul_le_mul_of_nonneg_right hepsilon1 ha.le
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff
namespace OAI

section

namespace Erdos3

theorem adaptiveAffineShell_pos (A sourceDim siteDim : ℕ)
    (ε L T C modLog : ℝ) {totalShell : ℝ} (h : 0 < totalShell) :
    0 < adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog :=
  mul_pos h (Real.exp_pos _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AdaptiveShellLogBudget
namespace OAI

section

namespace Erdos3

theorem affineShellLogBudget_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineCountLogBudget P ∧ 0 ≤ affineShellLogBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hc : 0 ≤ affineCountLogBudget P := by unfold affineCountLogBudget; positivity
  exact ⟨hc, add_nonneg hP hc⟩

theorem adaptiveAffineCountLog_le_budget (A sourceDim siteDim : ℕ)
    {epsilon L T C modLog P : ℝ} (hP : 0 ≤ P) (hmod0 : 0 ≤ modLog)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hscale0 : 0 ≤ affineComparisonScale epsilon L T C)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P) :
    adaptiveAffineCountLog A sourceDim siteDim epsilon L T C modLog ≤ affineCountLogBudget P := by
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hi : affineComparisonScale epsilon L T C + (sourceDim : ℝ) * modLog +
      (siteDim : ℝ) * modLog + 1 ≤ affinePrimitiveLogBudget P + 2 * P ^ 2 + 1 := by nlinarith
  unfold adaptiveAffineCountLog affineCountLogBudget
  exact mul_le_mul hA hi (by positivity) hP

theorem adaptiveAffineShell_inverse_le_budget (A sourceDim siteDim : ℕ)
    {epsilon L T C modLog totalShell P : ℝ}
    (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P)
    (hcount : adaptiveAffineCountLog A sourceDim siteDim epsilon L T C modLog ≤ affineCountLogBudget P) :
    (adaptiveAffineShell A sourceDim siteDim epsilon L T C totalShell modLog)⁻¹ ≤
      Real.exp (affineShellLogBudget P) := by
  simp only [adaptiveAffineShell, mul_inv_rev, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp (affineCountLogBudget P) * Real.exp P :=
      mul_le_mul (Real.exp_le_exp.mpr hcount) htotalInv (inv_nonneg.mpr htotal.le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold affineShellLogBudget; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineSidePolynomialBudget
namespace OAI

section

namespace Erdos3

theorem affineDegreeBudgets_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineLocalDegreeInputBudget P ∧ 0 ≤ affineOuterDegreeInputBudget P ∧
      0 ≤ affineLocalDegreeBudget P ∧ 0 ≤ affineAdaptiveDegreeBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hS := (affineShellLogBudget_nonneg hP).2
  simp only [affineLocalDegreeInputBudget, affineOuterDegreeInputBudget, affineLocalDegreeBudget, affineAdaptiveDegreeBudget]
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem affineComparisonDegree_le_polynomialBudget (sourceDim siteDim : ℕ)
    {epsilon L T C shell modLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hshell : 0 < shell) (hshellInv : shell⁻¹ ≤ Real.exp (affineShellLogBudget P))
    (hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P) :
    (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) ≤ affineLocalDegreeBudget P := by
  let j := affineRemovalDepth T
  let tail := affineComparisonTail epsilon L T
  let scale := affineComparisonScale epsilon L T C
  let input := (j : ℝ) * (scale + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2) +
    epsilon + L + 2 * T + 10
  have hscale0 : 0 ≤ scale := (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hj : (j : ℝ) ≤ affinePrimitiveLogBudget P :=
    (Nat.cast_le.mpr (Nat.le_add_right j tail)).trans hsum
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hinner : scale + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2 ≤
      affinePrimitiveLogBudget P + 2 * P ^ 2 + 2 := by dsimp only [scale]; nlinarith
  have hmul := mul_le_mul hj hinner (by positivity) hH
  have hinput : input ≤ affineLocalDegreeInputBudget P := by
    dsimp only [input, affineLocalDegreeInputBudget]
    linarith
  have hinput0 : 0 ≤ input := by dsimp only [input]; positivity
  have hiter := CyclicCrootSisask.spectralIterations_le_logBudget hshell hinput0
    (affineShellLogBudget_nonneg hP).2 hshellInv
  have hiter' : (CyclicCrootSisask.spectralIterations shell input : ℝ) ≤
      2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2 := by linarith
  have hn : affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog ≤
      j + tail + CyclicCrootSisask.spectralIterations shell input := by
    dsimp only [affineComparisonDegree, affineFinalDegree, j, tail, input, scale]
    omega
  calc
    _ ≤ ((j + tail : ℕ) : ℝ) + (CyclicCrootSisask.spectralIterations shell input : ℝ) := by exact_mod_cast hn
    _ ≤ affinePrimitiveLogBudget P + (2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2) :=
      add_le_add hsum hiter'
    _ = _ := by unfold affineLocalDegreeBudget; ring

theorem affineGlobalComparisonDegree_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C shell modLog P : ℝ} (hP : 0 ≤ P) (hmod0 : 0 ≤ modLog)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hshell : 0 < shell) (hshellInv : shell⁻¹ ≤ Real.exp (affineShellLogBudget P))
    (hlocal : (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) ≤ affineLocalDegreeBudget P) :
    (affineGlobalComparisonDegree A sourceDim siteDim epsilon L T C shell modLog 0 : ℝ) ≤
      affineAdaptiveDegreeBudget P := by
  let input := (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hi : (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1 ≤ 2 * P ^ 2 + 1 := by nlinarith
  have hm := mul_le_mul hA hi (by positivity) hP
  have hinput : input ≤ affineOuterDegreeInputBudget P := by
    dsimp only [input, affineOuterDegreeInputBudget]
    linarith
  have hinput0 : 0 ≤ input := by dsimp only [input]; positivity
  have hiter := CyclicCrootSisask.spectralIterations_le_logBudget hshell hinput0
    (affineShellLogBudget_nonneg hP).2 hshellInv
  have hiter' : (CyclicCrootSisask.spectralIterations shell input : ℝ) ≤
      2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2 := by linarith
  have hn : affineGlobalComparisonDegree A sourceDim siteDim epsilon L T C shell modLog 0 ≤
      A + affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog +
        CyclicCrootSisask.spectralIterations shell input := by
    dsimp only [affineGlobalComparisonDegree, input]
    simp only [add_zero]
    omega
  calc
    _ ≤ (A : ℝ) + (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) +
        (CyclicCrootSisask.spectralIterations shell input : ℝ) := by exact_mod_cast hn
    _ ≤ P + affineLocalDegreeBudget P + (2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2) :=
      add_le_add (add_le_add hA hlocal) hiter'
    _ = _ := by unfold affineAdaptiveDegreeBudget; ring

theorem adaptiveAffineCutoff_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    (adaptiveAffineCutoff A sourceDim siteDim epsilon L T C totalShell modLog : ℝ) ≤
      affineAdaptiveDegreeBudget P := by
  have hp := affineComparisonPrimitive_bounds hepsilon hepsilon1 hP hL hT hC hLP hTP hCP hinverse
  have hcount := adaptiveAffineCountLog_le_budget A sourceDim siteDim hP hmod0 hA hsource hsite hmod
    (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1 hp.2.1
  have hs := adaptiveAffineShell_pos A sourceDim siteDim epsilon L T C modLog htotal
  have hsinv := adaptiveAffineShell_inverse_le_budget A sourceDim siteDim htotal htotalInv hcount
  have hlocal := affineComparisonDegree_le_polynomialBudget sourceDim siteDim hepsilon hepsilon1 hP
    hL hT hC hmod0 hLP hTP hsource hsite hmod hs hsinv hp.1 hp.2.1
  exact affineGlobalComparisonDegree_le_polynomialBudget A sourceDim siteDim hP hmod0 hA hsource hsite
    hmod hs hsinv hlocal

end Erdos3

end

section

namespace Erdos3

theorem affineComparisonRequiredOrder_le_budget (b : ℕ) {epsilon L T C P : ℝ}
    (hP : 0 ≤ P) (hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P)
    (hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P)
    (hmoment : (affineComparisonMoment (affineComparisonScale epsilon L T C) : ℝ) ≤ affinePrimitiveLogBudget P + 2) :
    (affineComparisonRequiredOrder b epsilon L T C : ℝ) ≤ affineOrderPolynomialBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hB := (affineDegreeBudgets_nonneg hP).2.2.2
  have hj : (affineRemovalDepth T : ℝ) ≤ affinePrimitiveLogBudget P :=
    (Nat.cast_le.mpr (Nat.le_add_right (affineRemovalDepth T) (affineComparisonTail epsilon L T))).trans hsum
  unfold affineComparisonRequiredOrder
  rw [Nat.cast_max]
  apply max_le
  · have hm := mul_le_mul hsum (add_le_add hmoment (le_refl (1 : ℝ)))
      (by positivity) hH
    push_cast at hm ⊢
    unfold affineOrderPolynomialBudget
    nlinarith
  · push_cast
    unfold affineOrderPolynomialBudget
    nlinarith [mul_nonneg hH (by linarith : 0 ≤ affinePrimitiveLogBudget P + 3)]

theorem affineComparisonAccuracyLog_le_budget (b : ℕ) {epsilon L T C P : ℝ}
    (hP : 0 ≤ P) (hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P)
    (hscale0 : 0 ≤ affineComparisonScale epsilon L T C)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P)
    (hLP : L ≤ P) (hTP : T ≤ P) :
    affineComparisonAccuracyLog b (affineComparisonScale epsilon L T C) L T ≤ affineAccuracyPolynomialBudget P := by
  have hB := (affineDegreeBudgets_nonneg hP).2.2.2
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ affineComparisonScale epsilon L T C + 3)
    (add_le_add hscale (le_refl (3 : ℝ))) 3
  have hm := mul_le_mul hb (add_le_add hscale (le_refl (2 : ℝ))) (by linarith) hB
  unfold affineComparisonAccuracyLog affineAccuracyPolynomialBudget
  nlinarith

theorem adaptiveAffineSideLog_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog dimLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P) (hdim : dimLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    adaptiveAffineSideLog A sourceDim siteDim epsilon L T C totalShell modLog dimLog ≤
      affineSidePolynomialBudget P := by
  let b := adaptiveAffineCutoff A sourceDim siteDim epsilon L T C totalShell modLog
  have hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P :=
    adaptiveAffineCutoff_le_polynomialBudget A sourceDim siteDim hepsilon hepsilon1 hP hL hT hC hmod0
      hLP hTP hCP hmod hA hsource hsite hinverse htotal htotalInv
  have hp := affineComparisonPrimitive_bounds hepsilon hepsilon1 hP hL hT hC hLP hTP hCP hinverse
  have ho := affineComparisonRequiredOrder_le_budget b hP hb hp.1 hp.2.2
  have ha := affineComparisonAccuracyLog_le_budget b hP hb
    (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1 hp.2.1 hLP hTP
  have hm := mul_le_mul hmod hA (Nat.cast_nonneg A) hP
  have horder := mul_le_mul hmod ho (Nat.cast_nonneg _) hP
  change modLog * A +
    (modLog * (affineComparisonRequiredOrder b epsilon L T C : ℝ) +
      affineComparisonAccuracyLog b (affineComparisonScale epsilon L T C) L T + dimLog + 1) + 2 ≤ _
  unfold affineSidePolynomialBudget
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCommonReferenceBudget
namespace OAI

section

namespace Erdos3

theorem affineSidePolynomialBudget_le_power {P : ℝ} (hP : 0 ≤ P) :
    affineSidePolynomialBudget P ≤ 65536 * (P + 3) ^ 4 := by
  apply le_of_sub_nonneg
  simp only [affineSidePolynomialBudget, affineOrderPolynomialBudget, affineAccuracyPolynomialBudget,
    affineAdaptiveDegreeBudget, affineLocalDegreeBudget, affineOuterDegreeInputBudget,
    affineLocalDegreeInputBudget, affineShellLogBudget, affineCountLogBudget, affinePrimitiveLogBudget]
  ring_nf
  positivity

theorem adaptiveAffineSideLog_le_power (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog dimLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P) (hdim : dimLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    adaptiveAffineSideLog A sourceDim siteDim epsilon L T C totalShell modLog dimLog ≤
      65536 * (P + 3) ^ 4 :=
  (adaptiveAffineSideLog_le_polynomialBudget A sourceDim siteDim hepsilon hepsilon1 hP hL hT hC hmod0
    hLP hTP hCP hmod hdim hA hsource hsite hinverse htotal htotalInv).trans (affineSidePolynomialBudget_le_power hP)

end Erdos3

end

section

namespace Erdos3

theorem affineCommonReferenceBudget_bounds {E : ℕ} (hE : 2 ≤ E) (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    0 ≤ affineCommonReferenceBudget E epsilon U ∧
    U ≤ affineCommonReferenceBudget E epsilon U ∧
    (⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊ : ℝ) ≤ affineCommonReferenceBudget E epsilon U := by
  have hb := affineReferenceInput_bounds epsilon hU
  have hbase : 0 ≤ affineReferenceInput epsilon U + 2 := by linarith [hb.1]
  have hpow : affineReferenceInput epsilon U + 2 ≤ (affineReferenceInput epsilon U + 2) ^ E := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ affineReferenceInput epsilon U + 2)
      (show 1 ≤ E by omega)
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ (affineReferenceInput epsilon U + 2) ^ E)
  unfold affineCommonReferenceBudget
  exact ⟨by positivity, by linarith [hb.2.1], by linarith [hb.1]⟩

theorem adaptiveAffineSideLog_reference_bound {E sourceDim siteDim : ℕ}
    {epsilon L T C totalShell modLog dimLog U : ℝ}
    (hE : 2 ≤ E) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hU : 0 ≤ U)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLU : L ≤ U) (hTU : T ≤ U) (hCU : C ≤ U) (hmod : modLog ≤ U) (hdim : dimLog ≤ U)
    (hsource : (sourceDim : ℝ) ≤ U) (hsite : (siteDim : ℝ) ≤ U)
    (hinverse : epsilon⁻¹ ≤ Real.exp U) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp U) :
    adaptiveAffineSideLog ⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊ sourceDim siteDim
      epsilon L T C totalShell modLog dimLog ≤ 65536 * (affineCommonReferenceBudget E epsilon U + 3) ^ 4 := by
  have hc := affineCommonReferenceBudget_bounds hE epsilon hU
  have he : Real.exp U ≤ Real.exp (affineCommonReferenceBudget E epsilon U) := Real.exp_le_exp.mpr hc.2.1
  exact adaptiveAffineSideLog_le_power _ sourceDim siteDim hepsilon hepsilon1 hc.1 hL hT hC hmod0
    (hLU.trans hc.2.1) (hTU.trans hc.2.1) (hCU.trans hc.2.1) (hmod.trans hc.2.1) (hdim.trans hc.2.1)
    hc.2.2 (hsource.trans hc.2.1) (hsite.trans hc.2.1) (hinverse.trans he) htotal (htotalInv.trans he)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

theorem scalarTransferAllocatedLogs_bounds (b : ℕ) {common p Z U : ℝ}
    (hcommon : 0 ≤ common) (hp : 0 ≤ p) (hZ : 0 ≤ Z) (hU : 0 ≤ U) :
    0 ≤ scalarTransferCapLog b Z ∧ 0 ≤ scalarTransferAccuracyLog b p Z ∧
    0 ≤ scalarTransferCellLog common b p Z U ∧
    65536 * (common + 3) ^ 4 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + scalarTransferAccuracyLog b p Z + U + 1 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + U + 1 ≤ scalarTransferCellLog common b p Z U := by
  have hc : 0 ≤ scalarTransferCapLog b Z := by unfold scalarTransferCapLog; positivity
  have ha : 0 ≤ scalarTransferAccuracyLog b p Z := by unfold scalarTransferAccuracyLog; positivity
  have hside : 0 ≤ 65536 * (common + 3) ^ 4 := by positivity
  have hb : 0 ≤ Z * (b : ℝ) := mul_nonneg hZ (Nat.cast_nonneg b)
  unfold scalarTransferCellLog
  exact ⟨hc, ha, by positivity, by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedMeshLengths
namespace OAI

section

namespace Erdos3

theorem normalizedMesh_scale_lower {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    Real.exp lengthLog ≤ delta * scale / 4 := by
  have hinv' := mul_le_mul_of_nonneg_left hinv hdelta.le
  rw [mul_inv_cancel₀ hdelta.ne'] at hinv'
  have hprod := mul_le_mul_of_nonneg_right hinv' (by positivity : 0 ≤ 4 * Real.exp lengthLog)
  have hsize := mul_le_mul_of_nonneg_left hscale hdelta.le
  rw [Real.exp_add] at hsize
  nlinarith

theorem normalizedBoxPartitions_exp_lengths {I : Type*}
    (N : I → ℕ) (scale : I → ℝ) (delta inverseLog lengthLog : ℝ)
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hscale : ∀ i, 4 * Real.exp (inverseLog + lengthLog) ≤ scale i)
    (hlarge : ∀ i, 4 ≤ delta * scale i) (hwhole : ∀ i, delta * scale i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N scale delta hlarge hwhole i).Label) :
    Real.exp lengthLog ≤ ((normalizedBoxPartitions N scale delta hlarge hwhole i).length c : ℝ) :=
  (normalizedMesh_scale_lower hdelta hinv (hscale i)).trans
    (normalizedBoxPartitions_lengths N scale delta hlarge hwhole i c).1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineNormalizedScales
namespace OAI

section

namespace Erdos3

theorem affinePhysicalScales_lower {H L Q : ℝ} {exponent : ℕ}
    (hL : 1 ≤ L) (hQ : 0 ≤ Q) (hexponent : 1 ≤ exponent)
    (hH : Q * L ^ exponent ≤ H) : Q ≤ H ∧ Q ≤ H / L := by
  have hpower : L ≤ L ^ exponent := by
    simpa only [pow_one] using pow_le_pow_right₀ hL hexponent
  have hQL : Q * L ≤ H := (mul_le_mul_of_nonneg_left hpower hQ).trans hH
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨?_, (le_div_iff₀ hLpos).mpr hQL⟩
  exact (by nlinarith : Q ≤ Q * L).trans hQL

theorem affineParameterScale_lower {L Q P : ℝ} {D : ℕ}
    (hD : 0 < D) (hQ : 0 ≤ Q) (hDlog : (D : ℝ) ≤ Real.exp P)
    (hL : Q * Real.exp P ≤ L) : Q ≤ L / (D : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
  exact (mul_le_mul_of_nonneg_left hDlog hQ).trans hL

theorem affineNormalizedScales_lower {I J : Type*} (H : I → ℝ)
    {L inverseLog lengthLog parameterLog : ℝ} {D exponent : ℕ}
    (hL : 1 ≤ L) (hD : 0 < D) (hexponent : 1 ≤ exponent)
    (hDlog : (D : ℝ) ≤ Real.exp parameterLog)
    (hparam : 4 * Real.exp (inverseLog + lengthLog + parameterLog) ≤ L)
    (hsite : ∀ i, 4 * Real.exp (inverseLog + lengthLog) * L ^ exponent ≤ H i) :
    (∀ i, 4 * Real.exp (inverseLog + lengthLog) ≤ H i) ∧
    (∀ z : Option J × I, 4 * Real.exp (inverseLog + lengthLog) ≤
      smoothPairCoefficientScale (H z.2) L z.1) ∧
    4 * Real.exp (inverseLog + lengthLog) ≤ L / (D : ℝ) := by
  have hQ : 0 ≤ 4 * Real.exp (inverseLog + lengthLog) := by positivity
  have hs (i) := affinePhysicalScales_lower hL hQ hexponent (hsite i)
  refine ⟨fun i => (hs i).1, ?_, ?_⟩
  · rintro ⟨j,i⟩
    cases j with
    | none => exact (hs i).1
    | some j => exact (hs i).2
  · apply affineParameterScale_lower hD hQ hDlog
    simpa only [Real.exp_add, mul_assoc] using hparam

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCostFromLogs
namespace OAI

section

namespace Erdos3

theorem physicalGridBudget_pay {rho A inverseLog ratioLog budget : ℝ}
    (hrho : 0 < rho) (hA : 0 ≤ A)
    (hinv : rho⁻¹ ≤ Real.exp inverseLog) (hratio : A ≤ Real.exp ratioLog)
    (hbudget : inverseLog + ratioLog + 2 ≤ budget) :
    4 * A * Real.exp (-budget) ≤ rho := by
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hprod : 4 * A * rho⁻¹ ≤ Real.exp (inverseLog + ratioLog + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp ratioLog * Real.exp inverseLog :=
        mul_le_mul (mul_le_mul h4 hratio hA (Real.exp_nonneg _)) hinv
          (inv_nonneg.mpr hrho.le) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have he : Real.exp (inverseLog + ratioLog + 2) * Real.exp (-budget) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hpaid := (mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg (-budget))).trans he
  have h := mul_le_mul_of_nonneg_right hpaid hrho.le
  calc
    4 * A * Real.exp (-budget) = (4 * A * rho⁻¹ * Real.exp (-budget)) * rho := by
      field_simp
    _ ≤ 1 * rho := h
    _ = rho := one_mul _

theorem normalized_physical_cell_width_log_budget {I : Type*}
    (N : I → ℕ) (H : I → ℝ) (rho A inverseLog ratioLog budget : ℝ)
    (hH : ∀ i, 0 ≤ H i) (hrho : 0 < rho) (hA : 0 ≤ A)
    (hlarge : ∀ i, 4 ≤ rho * H i) (hwhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    (hsize : ∀ i, (N i : ℝ) ≤ A * H i)
    (hinv : rho⁻¹ ≤ Real.exp inverseLog) (hratio : A ≤ Real.exp ratioLog)
    (hbudget : inverseLog + ratioLog + 2 ≤ budget)
    (i : I) (c : (normalizedBoxPartitions N H rho hlarge hwhole i).Label) :
    Real.exp (-budget) * (N i : ℝ) ≤
      ((normalizedBoxPartitions N H rho hlarge hwhole i).length c : ℝ) := by
  have hp := physicalGridBudget_pay hrho hA hinv hratio hbudget
  have hcost := mul_le_mul_of_nonneg_right hp (hH i)
  have hn := mul_le_mul_of_nonneg_left (hsize i) (Real.exp_nonneg (-budget))
  have hc := (normalizedBoxPartitions_lengths N H rho hlarge hwhole i c).1
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestScalarTransfer
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_geometric_scalar_transfer_s2_oai (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {I : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype I] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p epsilon Z U gridLog ratioLog meshLog level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ Z → 0 ≤ U → 0 ≤ meshLog →
    p ≤ U → scalarTransferTail (3 * p) ≤ U → Z ≤ U →
    gridLog + ratioLog + 2 ≤ U → epsilon⁻¹ ≤ Real.exp U →
    Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ U → (Fintype.card (Option J × I) : ℝ) ≤ U →
    (Fintype.card J : ℝ) ≤ U → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (Fintype.card ι : ℝ) ≤ Real.exp Z →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp Z) →
    ∀ (D : ℕ) (anchor : J → ℤ), 0 < D → (D : ℝ) ≤ Real.exp Z →
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let Aref := ⌈(pref + 2) ^ E⌉₊
    let b := adaptiveAffineCutoff Aref (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon p (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let _beta := scalarTransferMarginalAccuracy (3 * p) (scalarTransferCapLog b Z)
    let cellLog := scalarTransferCellLog common b p Z U
    (pref + 2) ^ E ≤ budget → p + scalarTransferTail (3 * p) + 4 ≤ budget →
    scalarTransferAccuracyLog b p Z ≤ meshLog →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ)
      (rho L C B A c sourceRatio parameterRatio : ℝ),
    0 < rho → 1 ≤ L → (∀ i, 0 < H i) → 0 ≤ C → 0 ≤ B → 0 ≤ A → 0 < c →
    0 ≤ sourceRatio → 0 ≤ parameterRatio → rho⁻¹ ≤ Real.exp gridLog → A ≤ Real.exp ratioLog →
    ∀ (hsiteLarge : ∀ i, 4 ≤ rho * H i) (hsiteWhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ)),
    (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ i, 4 * Real.exp (gridLog + max ((pref + 2) ^ E) cellLog) ≤ H i) →
    let P := normalizedBoxPartitions N H rho hsiteLarge hsiteWhole
    let hpos := normalizedBoxPartitions_positive N H rho hsiteLarge hsiteWhole
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z)
      (parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    (∀ i, c * H i ≤ ((sourceHi (none,i) - sourceLo (none,i) : ℤ) : ℝ)) →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    40 * (Fintype.card I : ℝ) * A / (rho * c) ≤ Real.exp meshLog →
    1 + (Fintype.card J : ℝ) * (C + B) ≤ Real.exp meshLog →
    sourceRatio ≤ Real.exp meshLog → parameterRatio ≤ Real.exp meshLog →
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      sourceRatio * ((sourceHi z - sourceLo z).toNat : ℝ)) →
    (∀ j, L / (D : ℝ) ≤ parameterRatio * ((parHi j - parLo j).toNat : ℝ)) →
    4 * Real.exp (4 * meshLog + 18 + cellLog + Z) ≤ L →
    (∀ i, 4 * Real.exp (4 * meshLog + 18 + cellLog) * L ^ (Fintype.card J + 1) ≤ H i) →
    (∀ w : (Option J × I → ℤ) → ℝ,
      (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
        0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights parLo parHi hpar).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
        (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hpos
          (fun i => prime i ^ power i) b (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤
        scalarTransferBaseAccuracy (3 * p)) →
    (∀ w : (Option J × I → ℤ) → ℝ,
      (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
        0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights parLo parHi hpar).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
        (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hpos
          (fun i => prime i ^ power i) b (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤
        scalarTransferBaseAccuracy (3 * p)) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, href⟩ := exists_niltest_mesh_scalar_transfer_s2.{u,v,w} s
  refine ⟨E, hE, ?_⟩
  intro ι I V J _ _ _ _ _ _ _ _ _ _ d nilmanifold p epsilon Z U gridLog ratioLog meshLog level budget
    hp hepsilon hepsilon1 hZ hU hmesh hpU htailU hZU hgridBudget hepsInv hlower hlevel
    hI hsourceDim hJdim hJ g hcomplexity prime power _ hprime hinj hcount hmoduli D anchor hD hDlog
    pref common Aref b beta cellLog hbudget hprecision haccMesh lo N H rho L C B A c sourceRatio parameterRatio
    hrho hL hH hC hB hA hc hsRatio hpRatio hrhoInv hAlog hsiteLarge hsiteWhole hsize hfirstScale
    P hpos hunit h hh hupper sourceLo sourceHi hsource parLo parHi hpar
    hbaseWidth hparamLo hparamHi hsourceLo hsourceHi hboundary hmovement hsLog hpLog hsourceWidth hparameterWidth
    hLscale hHscale heh heg outer hdom
  have hp0 : 0 ≤ p := by linarith
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hbase : 0 < scalarTransferBaseAccuracy (3 * p) := Real.exp_pos _
  have hbaseInv : (scalarTransferBaseAccuracy (3 * p))⁻¹ ≤ Real.exp U := by
    simp only [scalarTransferBaseAccuracy, Real.exp_neg, inv_inv]
    apply Real.exp_le_exp.mpr
    unfold scalarTransferTail at htailU
    linarith
  have hrefInput := affineReferenceInput_bounds epsilon hU
  have hmask := affineReferenceInput_mask_and_depth prime hprime hinj D hD hepsilon hepsilon1 hU
    hp0 hT hZ hpU htailU hZU hepsInv (hDlog.trans (Real.exp_le_exp.mpr hZU))
  have hcommon : 0 ≤ common := (affineCommonReferenceBudget_bounds hE epsilon hU).1
  have hlogs := scalarTransferAllocatedLogs_bounds b hcommon hp0 hZ hU
  have hcell : 0 ≤ cellLog := hlogs.2.2.1
  have hacc : 0 ≤ scalarTransferAccuracyLog b p Z := hlogs.2.1
  have hbeta : 0 < beta := Real.exp_pos _
  have hbeta1 : beta ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hacc)
  have hbetaInv : beta⁻¹ ≤ Real.exp meshLog := by
    change (Real.exp (-scalarTransferAccuracyLog b p Z))⁻¹ ≤ _
    rw [Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr haccMesh
  have hside := adaptiveAffineSideLog_reference_bound hE hepsilon hepsilon1 hU hp0 hT hZ hZ
    hpU htailU hZU hZU le_rfl hsourceDim hI hepsInv hbase hbaseInv
  have hsideCell : adaptiveAffineSideLog Aref (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon p (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z U ≤ cellLog :=
    hside.trans hlogs.2.2.2.1
  have hpair : Pairwise (fun i j => (prime i ^ power i).Coprime (prime j ^ power j)) := by
    intro i j hij
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (hinj h)))
  have hUexp : U ≤ Real.exp U := by linarith [Real.add_one_le_exp U]
  have hdimi : (Fintype.card I : ℝ) ≤ Real.exp U := hI.trans hUexp
  have hdimj : (Fintype.card J : ℝ) ≤ Real.exp U := hJdim.trans hUexp
  have hdimsource : (Fintype.card (Option J × I) : ℝ) ≤ Real.exp U := hsourceDim.trans hUexp
  have hfirst (i) (ci) : Real.exp (max ((pref + 2) ^ E) cellLog) ≤ ((P i).length ci : ℝ) :=
    normalizedBoxPartitions_exp_lengths N H rho gridLog _ hrho hrhoInv hfirstScale hsiteLarge hsiteWhole i ci
  have hcellSite (i) (ci) : Real.exp cellLog ≤ ((P i).length ci : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hfirst i ci)
  have hscales := affineNormalizedScales_lower (J := J) H hL hD (by omega : 1 ≤ Fintype.card J + 1)
    hDlog hLscale hHscale
  obtain ⟨S, T, hSstep, hSpos, hTstep, hTpos, hSlength, hTlength, hbad⟩ :=
    exists_allocated_affine_secondary_mesh_s2 sourceLo sourceHi hsource parLo parHi anchor hpar D hD
      lo N H (by linarith : 0 < L) hH hC hB hA hc hrho hsRatio hpRatio hmesh hcell hbeta
      hsiteLarge hsiteWhole hsize hbaseWidth hparamLo hparamHi hsourceLo hsourceHi
      hboundary hmovement hsLog hpLog hbetaInv hsourceWidth hparameterWidth hscales.2.1 hscales.2.2
  have hsiteClose := ordinaryMesh_marginals_of_lengths_s2 lo N P hpos (fun i => prime i ^ power i)
    hpair b Z U 0 cellLog 1 hZ le_rfl (by norm_num) hmoduli hdimi
    (by simpa only [add_zero] using hlogs.2.2.2.2.2) hcellSite
  have hparamClose := ordinaryMesh_marginals_of_lengths_s2 parLo (fun j => (parHi j - parLo j).toNat)
    T hTpos (fun i => prime i ^ power i) hpair b Z U (scalarTransferAccuracyLog b p Z) cellLog beta
    hZ hbeta1 le_rfl hmoduli hdimj hlogs.2.2.2.2.1 hTlength
  have hcap := residueTruncationCap_le_exp b hZ (by norm_num : (0 : ℝ) ≤ 1) le_rfl hcount
  have hcap0 := residueTruncationCap_nonneg ι b (by norm_num : (0 : ℝ) ≤ 1)
  have herror := scalarTransfer_combined_error_le (targetLog := 3 * p) hepsilon.le hepsilon1
    ((Real.exp_pos (-p)).le.trans hlower) hlevel hcap0 hcap
  apply href nilmanifold pref epsilon p (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z U U level
    hrefInput.1 hepsilon hp0 hT hZ hbase hZ (hZU.trans hrefInput.2.1) hU hU hmask.2.2 hlower hlevel
    (hI.trans hrefInput.2.1) hcount hdimi hdimsource hJ g
    (hcomplexity.mono (hpU.trans hrefInput.2.1)) prime power hprime hinj hmoduli D anchor hmask.1 hmask.2.1
    lo N P (normalizedBoxPartitions_step _ _ _ _ _) hpos hunit
    (normalized_physical_cell_width_log_budget N H rho A gridLog ratioLog pref
      (fun i => (hH i).le) hrho hA hsiteLarge hsiteWhole hsize hrhoInv hAlog
      (hgridBudget.trans hrefInput.2.1)) h hh (hupper.from_exponential_budget hbudget hprecision)
    sourceLo sourceHi S hSstep hSpos hsource ?_ ?_
    parLo parHi hpar T hTstep hTpos beta 1 beta (scalarTransferBaseAccuracy (3 * p))
    hbeta.le (by norm_num) hparamClose hsiteClose hbad heh heg p p outer hdom ?_
  · intro i ci
    exact (Real.exp_le_exp.mpr (max_le_max le_rfl hsideCell)).trans (hfirst i ci)
  · intro i ci
    exact (Real.exp_le_exp.mpr hsideCell).trans (hSlength i ci)
  · simpa only [beta, scalarTransferCapLog, b, Aref, show 2 * p + p = 3 * p by ring] using herror

end Erdos3

end

end OAI
end

theorem solution.{u, v, w, u_1} : type_of% @OAI.Erdos3.exists_niltest_geometric_scalar_transfer_s2_oai.{u, v, w, u_1} := @OAI.Erdos3.exists_niltest_geometric_scalar_transfer_s2_oai.{u, v, w, u_1}

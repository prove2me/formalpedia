-- Prove2me | solution 1 for OAI.Erdos3.affineReferenceInput_mask_and_depth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:55:33.230327+00:00
-- url     : https://prove2.me/submissions/1863f444-b2e9-4a16-8851-279b88203172

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_affineComparisonMoment_bounds
import Theorems.Thm_OAI_Erdos3_affineComparisonScale_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SpectralLogBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

end Erdos3.CyclicCrootSisask

end

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.affineReferenceInput_mask_and_depth.{u_1} := @OAI.Erdos3.affineReferenceInput_mask_and_depth.{u_1}

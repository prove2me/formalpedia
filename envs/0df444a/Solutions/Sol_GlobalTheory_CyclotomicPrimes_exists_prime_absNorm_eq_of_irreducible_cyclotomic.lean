-- Prove2me | solution 1 for GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:07.074166+00:00
-- url     : https://prove2.me/submissions/2a37a838-9e8b-4a52-8c44-bbb02c960ad7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousNormCharLFunctionNeZeroOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DedekindZetaEulerProductMulSubOneEntireNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeAbsNormEqOfIrreducibleCyclotomic
import Theorems.Thm_GlobalTheory_CyclotomicPrimes_summable_subset_union_finite
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_not_summable_class
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_two_le_absNorm
import Theorems.Thm_GlobalTheory_T_exists_continuous_normCharLFunction_ne_zero_one
import Theorems.Thm_GlobalTheory_T_exists_entire_sub_one_mul_euler_exp_ne_zero_one
import Theorems.Thm_GlobalTheory_T_exists_prime_norm_cyclotomicChar_ne_one
import Theorems.Thm_GlobalTheory_T_summable_inv_absNorm_primes_of_not_prime_norm
import Theorems.Thm_GlobalTheory_countable_ideal_and_summable_absNorm_rpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CyclotomicPrimes
namespace GlobalTheory.CyclotomicPrimes
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ (τ : (ZMod m)ˣ) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∃ P : HeightOneSpectrum (𝓞 K), P ∉ S ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = (τ : ZMod m) := by
  classical
  intro K _ _ m hm hirr τ S hS
  have : Fact m.Prime := ⟨hm⟩
  let cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ := fun P =>
    if h : ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = 0 then 1 else Units.mk0 _ h
  have hcl : ∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) := by
    intro P hP
    simp only [cl]
    rw [dif_neg (by rwa [ZMod.natCast_eq_zero_iff])]
    rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨Z, hZ, hZ1, hZs⟩ := GlobalTheory.T.exists_entire_sub_one_mul_euler_exp_ne_zero_one K
  refine GlobalTheory.Mem.RayPrimes.not_summable_class (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal)
    GlobalTheory.Mem.RayPrimes.two_le_absNorm cl
    (fun s hs => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2) ?_ Z hZ.continuous hZ1 ?_ τ ?_
  · intro χ hχ
    obtain ⟨P, u, hu, hχu⟩ := GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one K m hm hirr χ hχ
    have hP : ¬ m ∣ Ideal.absNorm P.asIdeal := by
      rw [← ZMod.natCast_eq_zero_iff, ← hu]; exact u.ne_zero
    refine GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one K m hm χ cl hcl ⟨P, hP, ?_⟩
    rwa [show cl P = u from Units.ext ((hcl P hP).trans hu.symm)]
  · intro s hs
    simpa using hZs s (by simpa using hs)
  · have hfin : (S ∪ {P : HeightOneSpectrum (𝓞 K) | Ideal.absNorm P.asIdeal ≤ m}).Finite :=
      hS.union ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) m).preimage
        (f := fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h))
    refine summable_subset_union_finite (fun P : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹)
      {P | ¬ (Ideal.absNorm P.asIdeal).Prime} _ {P | cl P = τ} hfin ?_ (GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm K)
    intro P hP
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_not] at hn hP
    have hd : ¬ m ∣ Ideal.absNorm P.asIdeal := fun h =>
      hn.2.2.ne ((Nat.prime_dvd_prime_iff_eq hm hn.1).1 h)
    exact hcon P hn.2.1 hn.1 (by rw [← hcl P hd, hP])
end GlobalTheory.CyclotomicPrimes

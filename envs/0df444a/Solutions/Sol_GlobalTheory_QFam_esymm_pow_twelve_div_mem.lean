-- Prove2me | solution 1 for GlobalTheory.QFam.esymm_pow_twelve_div_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:31.958579+00:00
-- url     : https://prove2.me/submissions/044d0c3c-aa15-4889-81d8-1d1646eefc32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqDiscriminantPowMulEvalJInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmPowTwelveDivDiscriminantMemSubring
import Theorems.Thm_GlobalTheory_T_exists_eq_discriminant_pow_mul_eval_jInvariant
import Theorems.Thm_GlobalTheory_T_isSLTwoPermutedModularFamily_algebra_closure
import Theorems.Thm_GlobalTheory_T_permutedModularFamily_sum_esymm_slash_invariant
import Theorems.Thm_GlobalTheory_T_qExpansionCoeffsInSubring_ring_closed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_DD_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f →
    (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ,
    (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by
  intro ι _ act w N f R τ₀ hN hact hf hq hj k
  have hF : IsFam act ((12 : ℕ) * (w : ℤ)) fun i τ => f i τ ^ 12 :=
    (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.2.2.1 w f 12 hf
  obtain ⟨-, -, -, -, hpow, hsp⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hqS : QAll (· ∈ R) N fun τ =>
      ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ ^ 12 :=
    (hsp (Finset ι) (Finset.powersetCard k Finset.univ) (fun t τ => ∏ i ∈ t, f i τ ^ 12)
      fun t _ => (hsp ι t (fun i τ => f i τ ^ 12) fun i _ => hpow (f i) 12 (hq i)).2).1
  have hw : ((k : ℤ) * (((12 : ℕ) : ℤ) * (w : ℤ))) = 12 * ((k * w : ℕ) : ℤ) := by
    push_cast; ring
  obtain ⟨P, hP, hPe⟩ := GlobalTheory.T.exists_eq_discriminant_pow_mul_eval_jInvariant R N (k * w) _ hN (fun γ => by
    have h := (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hF γ).2 k
    rw [hw] at h
    exact h) hqS
  have hD : DD τ₀ ^ (k * w) ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ₀)
  have hsum : (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) =
      (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12) / DD τ₀ ^ (k * w) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp ht).2, ← pow_mul,
      mul_comm w k]
  have h0 := hPe τ₀
  rw [hsum, h0, mul_div_cancel_left₀ _ hD, Polynomial.eval_eq_sum_range]
  exact R.sum_mem fun i _ => R.mul_mem (hP i) (R.pow_mem hj i)
end GlobalTheory.QFam

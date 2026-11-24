-- Prove2me | solution 1 for GlobalTheory.QFam.sum_esymm_slash
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:36.132863+00:00
-- url     : https://prove2.me/submissions/30b09056-6801-4632-b8de-410e88e005a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariant
import Theorems.Thm_GlobalTheory_QFam_IsFam_value_mul_denom
import Theorems.Thm_GlobalTheory_QFam_IsFam_esymm_slash

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
open GlobalTheory GlobalTheory.QFam
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
namespace GlobalTheory.QFam
namespace _root_.GlobalTheory.QFam
theorem _root_.solution : ∀ (ι : Type) [Fintype ι]
    (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ),
    _root_.GlobalTheory.QFam.ActBij act → _root_.GlobalTheory.QFam.IsFam act w f → ∀ γ : SL(2, ℤ),
      ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧
      ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
        fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by
  intro ι _ act w f hb h γ
  refine ⟨?_, fun k => h.esymm_slash hb γ k⟩
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => h.value_mul_denom i γ τ]
  exact e.sum_comp (fun i => f i τ)
end _root_.GlobalTheory.QFam
end GlobalTheory.QFam

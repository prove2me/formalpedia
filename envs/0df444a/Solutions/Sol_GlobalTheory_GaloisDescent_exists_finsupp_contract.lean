-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.exists_finsupp_contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:56:27.672198+00:00
-- url     : https://prove2.me/submissions/bdfb84bb-3229-4708-9aab-a75128d60e3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_induction_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul

set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) {ι : Type*} (e : Basis ι K L) (x : M) :
    ∃ c : ι →₀ V, (∀ i, c i = contract hf (e.coord i) x) ∧ x = c.sum fun i v => e i • f v := by
  refine induction_smul hf (p := fun x => ∃ c : ι →₀ V,
    (∀ i, c i = contract hf (e.coord i) x) ∧ x = c.sum fun i v => e i • f v) x
    ⟨0, by simp, by simp⟩ ?_ ?_
  · intro a v
    refine ⟨(e.repr a).mapRange (· • v) (zero_smul _ _), fun i => by simp, ?_⟩
    rw [Finsupp.sum_mapRange_index (by simp)]
    conv_lhs => rw [← e.linearCombination_repr a, Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    beta_reduce
    rw [map_smul, smul_assoc, smul_comm]
  · rintro x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩
    refine ⟨c + d, fun i => ?_, ?_⟩
    · rw [map_add, ← hc, ← hd, Finsupp.add_apply]
    · rw [Finsupp.sum_add_index' (by simp) (by simp), ← hx, ← hy]
end GlobalTheory.GaloisDescent

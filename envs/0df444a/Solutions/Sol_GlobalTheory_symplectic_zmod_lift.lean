-- Prove2me | solution 1 for GlobalTheory.symplectic_zmod_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:37.872241+00:00
-- url     : https://prove2.me/submissions/49758818-dc9a-42e6-96d1-2de05432184e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticZmodLift
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_symplecticGroupMap_zmod_surjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (h k : ℕ) (M : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) (ZMod k)),
    M ∈ Matrix.symplecticGroup (Fin h) (ZMod k) → ∃ N : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ,
      N ∈ Matrix.symplecticGroup (Fin h) ℤ ∧ N.map (Int.cast : ℤ → ZMod k) = M := by
  intro h k M hM
  obtain ⟨N, hN⟩ := symplecticGroupMap_zmod_surjective (Fin h) k ⟨M, hM⟩
  refine ⟨N.1, N.2, ?_⟩
  have := congrArg Subtype.val hN
  rw [coe_symplecticGroupMap] at this
  simpa using this
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.T.exists_maximal_height_succ_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:26:32.597088+00:00
-- url     : https://prove2.me/submissions/899fd626-8f39-46b7-aa2e-5558ae706de4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalHeightSuccDim
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalHeightSuccDimStatement
import Theorems.Thm_GlobalTheory_FibreMax_exists_isMaximal_height_ge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [FaithfulSMul k A] (d : ℕ), ringKrullDim (FractionRing k ⊗[k] A) = d → ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by
  first | exact @GlobalTheory.FibreMax.exists_isMaximal_height_ge | exact GlobalTheory.FibreMax.exists_isMaximal_height_ge | (intros; apply GlobalTheory.FibreMax.exists_isMaximal_height_ge <;> assumption)
end _root_.GlobalTheory.T

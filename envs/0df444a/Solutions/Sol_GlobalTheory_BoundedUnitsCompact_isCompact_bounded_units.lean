-- Prove2me | solution 1 for GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:29.573978+00:00
-- url     : https://prove2.me/submissions/f2fde23c-2be1-43e9-ae0e-6d2ec78996df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedEntriesIsCompact
import Theorems.Thm_GlobalTheory_BoundedUnitsCompact_boundedEntries_isCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BoundedUnitsCompact
namespace GlobalTheory.BoundedUnitsCompact
theorem _root_.solution {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] {n : ℕ} [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ (i j : Fin n), ‖(↑g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ (i j : Fin n), ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  have hK1 := boundedEntries_isCompact (F := F) (n := n) M
  have hK : IsCompact ({A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} ×ˢ
      (MulOpposite.op '' {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M})) :=
    hK1.prod (hK1.image MulOpposite.continuous_op)
  have hce := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  convert hce.isCompact_preimage hK using 1
  ext g
  simp [Units.embedProduct, -MulOpposite.op_inv]
end GlobalTheory.BoundedUnitsCompact

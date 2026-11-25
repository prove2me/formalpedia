-- Prove2me | solution 1 for GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:57.9198+00:00
-- url     : https://prove2.me/submissions/7c03bfdd-0df4-4f02-9a01-c20f1e722b4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtSpecProdSelfOfBasicOpenPreimageEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtSpecProdSelfOfBasicOpenPreimageEqStatement
import Theorems.Thm_P2M_GlobalTheory_AlgConn_hom_ext_of_two__of_basicOpen_d5662058710f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O → h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) → h = h' := by
  first | exact @GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | exact GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | (intros; apply GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen <;> assumption)
end _root_.GlobalTheory.T

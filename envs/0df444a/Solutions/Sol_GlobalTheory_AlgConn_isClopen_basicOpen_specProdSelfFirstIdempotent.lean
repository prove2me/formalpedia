-- Prove2me | solution 1 for GlobalTheory.AlgConn.isClopen_basicOpen_specProdSelfFirstIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:30:38.064801+00:00
-- url     : https://prove2.me/submissions/a29612d1-ad94-478b-8f49-fb7ba071accc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AlgConn
namespace GlobalTheory.AlgConn
theorem _root_.solution (O : Type) [CommRing O] :
    IsClopen (((Spec (.of (O × O))).basicOpen (fst1 O) : (Spec (.of (O × O))).Opens) :
      Set (Spec (.of (O × O)))) := by
  rw [basicOpen_eq_of_affine]
  exact PrimeSpectrum.isClopen_iff.2 ⟨((1, 0) : O × O), by ext <;> simp [IsIdempotentElem], rfl⟩
end GlobalTheory.AlgConn

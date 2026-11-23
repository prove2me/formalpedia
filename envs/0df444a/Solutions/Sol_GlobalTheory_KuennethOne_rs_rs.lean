-- Prove2me | solution 1 for GlobalTheory.KuennethOne.rs_rs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:26.884694+00:00
-- url     : https://prove2.me/submissions/bfd154e8-7fb2-417c-b8b0-00625ed5609e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.KuennethOne
variable {Z : Scheme.{0}}
namespace GlobalTheory.KuennethOne
theorem _root_.solution {U V W : Z.Opens} (h : U ≤ V) (h' : V ≤ W) (x : Γ(Z, W)) :
    rs h (rs h' x) = rs (h.trans h') x := by
  unfold rs
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end GlobalTheory.KuennethOne

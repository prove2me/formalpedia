-- Prove2me | solution 1 for GlobalTheory.KuennethOne.rs_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:26.953887+00:00
-- url     : https://prove2.me/submissions/ccfa2f68-a99d-4ec2-9e23-feb57604cbab

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
theorem _root_.solution {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) : rs h x = x := by
  unfold rs
  have : (homOfLE h).op = 𝟙 (Opposite.op U) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl
end GlobalTheory.KuennethOne

-- Prove2me | solution 1 for GlobalTheory.KuennethOne.rs_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:28.046572+00:00
-- url     : https://prove2.me/submissions/245ebd14-4f18-4b8c-b6ff-c438065d9521

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
theorem _root_.solution {T : Scheme.{0}} (f : T ⟶ Z) {U : Z.Opens} {N M : T.Opens} (h : M ≤ N)
    (e : N ≤ f ⁻¹ᵁ U) (x : Γ(Z, U)) :
    rs h ((f.appLE U N e).hom x) = (f.appLE U M (h.trans e)).hom x := by
  unfold rs
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
end GlobalTheory.KuennethOne

-- Prove2me | solution 1 for GlobalTheory.KuennethOne.appLE_rs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:27.928926+00:00
-- url     : https://prove2.me/submissions/650becb8-7e2e-4a65-aeb3-16de8ce746f2

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
theorem _root_.solution {T : Scheme.{0}} (f : T ⟶ Z) {U V : Z.Opens} (h : U ≤ V) {N : T.Opens}
    (e : N ≤ f ⁻¹ᵁ U) (x : Γ(Z, V)) :
    (f.appLE U N e).hom (rs h x) = (f.appLE V N (e.trans (f.preimage_mono h))).hom x := by
  unfold rs
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
end GlobalTheory.KuennethOne

-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.res_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:56.424264+00:00
-- url     : https://prove2.me/submissions/ec86b947-fdd1-46e3-bdff-d4cca2943fc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_GroupHomPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
variable {X X' Y Y' : Scheme.{u}}
namespace GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
theorem _root_.solution {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  ext
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom _ = _
  rw [← Functor.map_comp]; rfl
end GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback

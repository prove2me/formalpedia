-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.isoUnit_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:40:21.727799+00:00
-- url     : https://prove2.me/submissions/84a28934-7e23-4c8b-9824-5cd9aa1422e3

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
variable {K : Type u} [Fintype K]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
theorem _root_.solution {L M : LB X} {u : LB.Iso L M} (hu : u.IsGen) (j j' : M.ι) (i i' : L.ι)
    (f : Y ⟶ X) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ (M.U j ⊓ L.U i)) (h' : W ≤ f ⁻¹ᵁ (M.U j' ⊓ L.U i'))
    (hM : W ≤ f ⁻¹ᵁ (M.U j ⊓ M.U j')) (hL : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U i')) :
    pr f h (isoUnit u j i) =
      pr f hM (M.g j j') * (pr f hL (L.g i i'))⁻¹ * pr f h' (isoUnit u j' i') := by
  have h0 : res (inf_le_left : (M.U j ⊓ L.U i) ⊓ (M.U j' ⊓ L.U i') ≤ _) (isoUnit u j i) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (M.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
        (L.g i i'))⁻¹ * res inf_le_right (isoUnit u j' i') := hu (j, i) (j', i')
  have hh : W ≤ f ⁻¹ᵁ ((M.U j ⊓ L.U i) ⊓ (M.U j' ⊓ L.U i')) := le_inf h h'
  have := congrArg (pr f hh) h0
  simpa only [map_mul, map_inv, pr_res] using this
end GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback

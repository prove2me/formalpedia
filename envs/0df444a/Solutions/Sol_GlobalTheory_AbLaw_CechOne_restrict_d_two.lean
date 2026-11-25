-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.restrict_d_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:58:28.601666+00:00
-- url     : https://prove2.me/submissions/e01756b3-b7af-4eba-9ff3-538e511d8168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_d_two_apply_triple
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
variable {κ : Type} (D : κ → X.Opens)
variable [LinearOrder κ]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M)
variable {D f M}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution (x : GlobalTheory.Cube.Term (secCube f M D) 2) {i j k : κ} (h : i < j) (h' : j < k)
    (hc : ({i, j, k} : Finset κ).card = 2 + 1) {W : X.Opens}
    (hi : W ≤ D i) (hj : W ≤ D j) (hk : W ≤ D k) :
    restrict M (by simp [hi, hj, hk]) (comp M D f (GlobalTheory.Cube.d _ 2 x) {i, j, k} hc) =
      restrict M (le_pair D hj hk) (comp M D f x {j, k} (Finset.card_pair h'.ne)) -
        restrict M (le_pair D hi hk) (comp M D f x {i, k} (Finset.card_pair (h.trans h').ne)) +
        restrict M (le_pair D hi hj) (comp M D f x {i, j} (Finset.card_pair h.ne)) := by
  have e : comp M D f (GlobalTheory.Cube.d _ 2 x) {i, j, k} hc =
      restrict M (iInf_le_iInf_of_subset D (by simp)) (comp M D f x {j, k} (Finset.card_pair h'.ne)) -
      restrict M (iInf_le_iInf_of_subset D (by simp))
        (comp M D f x {i, k} (Finset.card_pair (h.trans h').ne)) +
      restrict M (iInf_le_iInf_of_subset D (by simp [Finset.insert_subset_iff]))
        (comp M D f x {i, j} (Finset.card_pair h.ne)) :=
    d_two_apply_triple _ x h h' hc
  rw [e, map_add, map_sub, restrict_restrict, restrict_restrict, restrict_restrict]
end GlobalTheory.AbLaw.CechOne

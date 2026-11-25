-- Prove2me | solution 1 for GlobalTheory.exists_isClosed_image_of_isClosed_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:50.055611+00:00
-- url     : https://prove2.me/submissions/1599932c-d0f6-46d6-8634-0a1ad0cd496c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Theorems.Thm_GlobalTheory_RationalPoint_range_left_subset_iff
import Theorems.Thm_GlobalTheory_RationalPoint_separatelyContinuousMul
import Theorems.Thm_GlobalTheory_RationalPoint_continuousInv
import Theorems.Thm_GlobalTheory_RationalPoint_pt_mem_image_iff
import Theorems.Thm_GlobalTheory_RationalPoint_isConstructible_image_of_isClosed
import Theorems.Thm_GlobalTheory_isClosed_subgroup_of_eq_preimage_isConstructible
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
open GlobalTheory
open RationalPoint
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G B : Over (Sp k)) [GrpObj G] [GrpObj B] (q : G ⟶ B), IsMonHom q → LocallyOfFiniteType G.hom → QuasiCompact G.hom → LocallyOfFiniteType B.hom → QuasiCompact B.hom → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → ∃ Z' : Set B.left, IsClosed Z' ∧ ∀ y : (𝟙_ (Over (Sp k)) ⟶ B), (∃ x ∈ C, x ≫ q = y) ↔ Set.range y.left ⊆ Z' := by
  intro k _ _ G B _ _ q _ _ _ _ _ C Z hZ hC
  letI := zariski B
  haveI := separatelyContinuousMul B
  haveI := continuousInv B
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ B) :=
    MonoidHom.mk' (fun x => x ≫ q) fun x y => MonObj.mul_comp x y q
  have hcl : IsClosed (C.map φ : Set (𝟙_ (Over (Sp k)) ⟶ B)) := by
    refine isClosed_subgroup_of_eq_preimage_isConstructible _ (f := pt) continuous_induced_dom
      (isConstructible_image_of_isClosed q hZ) ?_
    ext y
    rw [Set.mem_preimage, pt_mem_image_iff q hZ]
    simp only [← range_left_subset_iff, ← hC]
    rfl
  obtain ⟨Z', hZ', h⟩ := isClosed_induced_iff.1 hcl
  refine ⟨Z', hZ', fun y => ?_⟩
  rw [range_left_subset_iff, ← Set.mem_preimage, h]
  rfl
end GlobalTheory

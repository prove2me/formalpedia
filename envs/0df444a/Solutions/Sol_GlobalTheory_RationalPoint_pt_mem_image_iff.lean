-- Prove2me | solution 1 for GlobalTheory.RationalPoint.pt_mem_image_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:07:12.650645+00:00
-- url     : https://prove2.me/submissions/fcc36c32-0cd6-4b38-bd72-61ab02c2c71b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Theorems.Thm_GlobalTheory_RationalPoint_isClosed_pt
import Theorems.Thm_GlobalTheory_RationalPoint_pt_injective
import Theorems.Thm_GlobalTheory_RationalPoint_exists_pt_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
open GlobalTheory
open GlobalTheory.RationalPoint
variable {k : Type} [Field k]
variable [IsAlgClosed k]
namespace GlobalTheory.RationalPoint
theorem _root_.solution {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) {Z : Set X.left} (hZ : IsClosed Z)
    (y : 𝟙_ (Over (Sp k)) ⟶ Y) :
    pt y ∈ f.left '' Z ↔ ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z ∧ x ≫ f = y := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := exists_pt_mem (Z := Z ∩ f.left ⁻¹' {pt y})
      (hZ.inter ((isClosed_pt y).preimage f.left.continuous)) ⟨z, hz, hzy⟩
    exact ⟨x, hx, pt_injective hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨pt x, hx, rfl⟩
end GlobalTheory.RationalPoint

-- Prove2me | solution 1 for GlobalTheory.flat_of_formallyUnramified_grpEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:47.54912+00:00
-- url     : https://prove2.me/submissions/8e685307-f2a1-4cdf-83b0-08c0ae5fec63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_of_closedPoints
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_stalkMap_of_fixed
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


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
open GlobalTheory
open UnramifiedEndFlat
namespace GlobalTheory
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k))
    [GrpObj G] (φ : G ⟶ G) (hG : LocallyOfFiniteType G.hom) (hφ : IsMonHom φ)
    (hu : FormallyUnramified φ.left) : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let o : G.left := η[G].left (IsLocalRing.closedPoint k)
  have ho : IsClosed {o} := (pointEquivClosedPoint G.hom ⟨η[G].left, η[G].w⟩).2
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint k))
  have h0 := flat_stalkMap_of_fixed φ.left G.hom φ.w o ho hfo
  let α := GrpObj.mulRight (A := G) x'
  let β := GrpObj.mulRight (A := G) (x' ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp [α, β, comp_lift_assoc]
  have hα : η[G] ≫ α.hom = x' := by
    simpa [α, comp_lift_assoc] using lift_comp_one_left (𝟙 (𝟙_ (Over (Sp k)))) x'
  have hα' : α.hom.left o = x :=
    (congr(($hα).left (IsLocalRing.closedPoint k))).trans (pointOfClosedPoint_apply G.hom x hx _)
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap o).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp h0
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left o)) (α.hom.left.stalkMap o)).mp h1
end GlobalTheory

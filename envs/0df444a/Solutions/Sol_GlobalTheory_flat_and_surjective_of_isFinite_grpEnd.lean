-- Prove2me | solution 1 for GlobalTheory.flat_and_surjective_of_isFinite_grpEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:39:06.520838+00:00
-- url     : https://prove2.me/submissions/3da1c1bb-718a-459b-8436-898f2e3dc065

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Theorems.Thm_GlobalTheory_FiniteEndFlat_apply_genericPoint
import Theorems.Thm_GlobalTheory_FiniteEndFlat_exists_open_flat
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_of_closedPoints


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open UnramifiedEndFlat FiniteEndFlat
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [IsAlgClosed K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom] (φ : G ⟶ G) [IsMonHom φ] [IsFinite φ.left] :
    Flat φ.left ∧ Surjective φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ := apply_genericPoint φ.left hfo
  refine ⟨?_, ⟨fun y => ?_⟩⟩
  · obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
    refine flat_of_closedPoints _ fun x hx => ?_
    let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
    let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
    let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
    let β := GrpObj.mulRight (A := G) ((y'⁻¹ * x') ≫ φ)
    have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
      simp only [α, β]
      generalize y'⁻¹ * x' = z
      simp [comp_lift_assoc]
    have hα : y' ≫ α.hom = x' := by
      have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
        simp [α, comp_lift_assoc, Hom.mul_def]
      rw [this, mul_inv_cancel_left]
    have hα' : α.hom.left y = x := by
      have h := congr(($hα).left (IsLocalRing.closedPoint K))
      rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
        ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
      exact h
    have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
    have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
      rw [Scheme.Hom.stalkMap_comp]
      exact (Flat.stalkMap β.hom.left _).comp (H y hy)
    rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
    rw [← hα']
    exact (RingHom.Flat.respectsIso.cancel_right_isIso
      (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1
  · exact (genericPoint_specializes y).mem_closed φ.left.isClosedMap.isClosed_range ⟨_, hξ⟩
end GlobalTheory

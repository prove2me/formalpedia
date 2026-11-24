-- Prove2me | solution 1 for GlobalTheory.TorusExtBaseChange.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:19.986309+00:00
-- url     : https://prove2.me/submissions/598db589-84a0-4bb8-9a8e-c42ed93891d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Theorems.Thm_GlobalTheory_TorusExtBaseChange_isPullback_pullback_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusExtBaseChange
namespace GlobalTheory.TorusExtBaseChange
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    {T' G' B' : Over S'} [GrpObj T'] [GrpObj G'] [GrpObj B']
    (eT : T' ≅ (Over.pullback f).obj T) (eG : G' ≅ (Over.pullback f).obj G)
    (eB : B' ≅ (Over.pullback f).obj B) [IsMonHom eT.hom] [IsMonHom eG.hom] [IsMonHom eB.hom]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] (hf : Flat q.left) (hs : Surjective q.left)
    (ha : IsAffineHom q.left) (hk : IsPullback i (toUnit _) q η[B]) :
    ∃ (q' : G' ⟶ B') (i' : T' ⟶ G'), IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧
      IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' η[B'] ∧
      q'.left ≫ eB.hom.left ≫ pullback.fst B.hom f = (eG.hom.left ≫ pullback.fst G.hom f) ≫ q.left ∧
      i'.left ≫ eG.hom.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst T.hom f) ≫ i.left := by
  have pq := isPullback_pullback_map f q
  have pi := isPullback_pullback_map f i
  have iG : IsIso eG.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eG.hom))
  have iB : IsIso eB.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eB.inv))
  have hf' : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hf
  have hs' : Surjective ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hs
  have ha' : IsAffineHom ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq ha
  refine ⟨eG.hom ≫ (Over.pullback f).map q ≫ eB.inv, eT.hom ≫ (Over.pullback f).map i ≫ eG.inv,
    inferInstance, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · refine (hk.map (Over.pullback f)).of_iso eT.symm eG.symm
      (Functor.Monoidal.εIso (Over.pullback f)).symm eB.symm ?_ (toUnit_unique _ _) ?_ ?_
    · simp
    · simp
    · have : η[(Over.pullback f).obj B] ≫ eB.inv = η[B'] := IsMonHom.one_hom _
      rw [← this, Functor.obj.η_def]
      simp
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eB.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pq.w]
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eG.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pi.w]
end GlobalTheory.TorusExtBaseChange

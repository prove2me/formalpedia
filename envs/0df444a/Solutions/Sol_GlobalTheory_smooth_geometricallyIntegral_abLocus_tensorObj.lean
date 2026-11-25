-- Prove2me | solution 1 for GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:41.948345+00:00
-- url     : https://prove2.me/submissions/421c5c3f-6774-4f03-b787-98c95a95b4a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGeometricallyIntegralAbLocusTensorObj
import Theorems.Thm_GlobalTheory_geometricallyConnected_of_geometricallyIntegral
import Theorems.Thm_GlobalTheory_geometricallyIntegral_tensorObj_hom
import Theorems.Thm_GlobalTheory_smooth_tensorObj_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (X : Scheme.{0}) (P Q : Over X), Smooth P.hom → Smooth Q.hom → GeometricallyIntegral P.hom → GeometricallyIntegral Q.hom → Smooth (P ⊗ Q).hom ∧ GeometricallyIntegral (P ⊗ Q).hom ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus P ∩ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus Q ⊆ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus (P ⊗ Q) := by
  intro X P Q hPs hQs hPi hQi
  haveI := _root_.GlobalTheory.geometricallyConnected_of_geometricallyIntegral P.hom
  haveI := _root_.GlobalTheory.geometricallyConnected_of_geometricallyIntegral Q.hom
  refine ⟨_root_.GlobalTheory.smooth_tensorObj_hom P Q, _root_.GlobalTheory.geometricallyIntegral_tensorObj_hom P Q, ?_⟩
  intro s hs'
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus, Set.mem_inter_iff, Set.mem_setOf_eq] at hs' ⊢
  obtain ⟨hP, hQ⟩ := hs'
  intro K _ _ t hs
  haveI : IsProper ((Over.pullback t).obj P).hom := hP K t hs
  haveI : IsProper ((Over.pullback t).obj Q).hom := hQ K t hs
  haveI : IsIso (CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q).left :=
    Functor.map_isIso (Over.forget (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K))
      (CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q)
  have h : IsProper ((CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q).left ≫
      ((Over.pullback t).obj P ⊗ (Over.pullback t).obj Q).hom) := by
    rw [Over.tensorObj_hom]; infer_instance
  rw [Over.w] at h
  exact h
end _root_.GlobalTheory
end GlobalTheory

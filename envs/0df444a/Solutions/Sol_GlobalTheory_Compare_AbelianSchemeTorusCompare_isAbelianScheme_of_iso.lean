-- Prove2me | solution 1 for GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:52.81677+00:00
-- url     : https://prove2.me/submissions/ad3f1cb0-dfd1-4d9b-a95f-299740d1d6fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianModels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianSchemeTorusCompare

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
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Compare GlobalTheory.Compare.AbelianSchemeTorusCompare
open GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels
namespace GlobalTheory.Compare.AbelianSchemeTorusCompare
theorem _root_.solution {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    (e : A ≅ B) (he : IsMonHom e.hom) (hB : IsAbelianScheme B) : IsAbelianScheme A := by
  have hw : A.hom = e.hom.left ≫ B.hom := (Over.w e.hom).symm
  have hiso : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom e.hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]
    have hbc : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{0})
        @GeometricallyConnected := inferInstance
    have hri : MorphismProperty.RespectsIso (C := Scheme.{0}) @GeometricallyConnected :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).2 this
end GlobalTheory.Compare.AbelianSchemeTorusCompare

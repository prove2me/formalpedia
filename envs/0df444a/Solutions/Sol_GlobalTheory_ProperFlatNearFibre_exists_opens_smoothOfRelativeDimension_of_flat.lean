-- Prove2me | solution 1 for GlobalTheory.ProperFlatNearFibre.exists_opens_smoothOfRelativeDimension_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:58:01.141574+00:00
-- url     : https://prove2.me/submissions/3d2a6177-bdd1-46ce-b710-00e75c980c44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsOpensSmoothOfRelativeDimensionOfFlat
import Theorems.Thm_GlobalTheory_VeryDenseFibres_exists_opens_smoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_VeryDenseFibres_mem_smoothLocus_of_smooth_fiber
import Theorems.Thm_GlobalTheory_VeryDenseFibres_smooth_fiber_of_smooth_fiber
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.restrictPoints_val
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.ProperFlatNearFibre
namespace GlobalTheory.ProperFlatNearFibre
theorem _root_.solution {R : CommRingCat.{0}} {Z T : Scheme.{0}}
    (s : Z ⟶ Spec R) [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have hz : z ∈ s.smoothLocus := by
    refine GlobalTheory.VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_
    rw [hw]
    have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
    exact GlobalTheory.VeryDenseFibres.smooth_fiber_of_smooth_fiber s t w
      (inferInstanceAs (Smooth (pullback.snd (pullback.snd s t) (T.fromSpecResidueField w))))
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (s.smoothLocus.ι ≫ s) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨W, hW, hW'⟩ := GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
    (s.smoothLocus.ι ≫ s) t g (by simpa using h2) ⟨z, hz⟩ w hw
  let j := W.ι ≫ s.smoothLocus.ι
  refine ⟨j.opensRange, ⟨⟨⟨z, hz⟩, hW⟩, rfl⟩, ?_⟩
  have e : j.opensRange.ι ≫ s = j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  have h3 : SmoothOfRelativeDimension (0 + g)
      (j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s)) := inferInstance
  rw [e]
  simpa using h3
end GlobalTheory.ProperFlatNearFibre

-- Prove2me | solution 1 for GlobalTheory.SmoothNearFibre.exists_opens_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:58:26.382127+00:00
-- url     : https://prove2.me/submissions/8bbee025-f775-4a11-b7c5-575321e94a5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothOfRelDimOfIsUnitProperFlat
import Theorems.Thm_GlobalTheory_VeryDenseFibres_exists_opens_smoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_VeryDenseFibres_mem_smoothLocus_of_smooth_fiber
import Theorems.Thm_GlobalTheory_VeryDenseFibres_smooth_fiber_of_smooth_fiber
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.SmoothNearFibre
open GlobalTheory.VeryDenseFibres
private lemma smoothOfRelativeDimension_pullback_snd_restrict {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (W : Z.Opens)
    (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd s t)) :
    SmoothOfRelativeDimension g (pullback.snd (W.ι ≫ s) t) := by
  rw [← pullbackRightPullbackFstIso_inv_snd_snd s t W.ι,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension g) h _
private lemma smoothOfRelativeDimension_opensRange_ι_comp' {U Z S : Scheme.{0}} (i : U ⟶ Z) [IsOpenImmersion i] (s : Z ⟶ S)
    (g : ℕ) (h : SmoothOfRelativeDimension g (i ≫ s)) :
    SmoothOfRelativeDimension g (i.opensRange.ι ≫ s) := by
  rw [← i.isoOpensRange_inv_comp, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact h
end GlobalTheory.SmoothNearFibre
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.SmoothNearFibre
open GlobalTheory.VeryDenseFibres
namespace GlobalTheory.SmoothNearFibre
theorem _root_.solution {R : CommRingCat.{0}} {Z T : Scheme.{0}} (s : Z ⟶ Spec R)
    [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
  have hF : Smooth ((pullback.snd s t).fiberToSpecResidueField w) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have hF' : Smooth (s.fiberToSpecResidueField (s z)) := by
    rw [hw]
    exact smooth_fiber_of_smooth_fiber s t w hF
  have hz : z ∈ s.smoothLocus := mem_smoothLocus_of_smooth_fiber s z hF'
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext a
    simp
  have h' : SmoothOfRelativeDimension g (pullback.snd (s.smoothLocus.ι ≫ s) t) :=
    smoothOfRelativeDimension_pullback_snd_restrict s t _ g h
  obtain ⟨V, hV, hVg⟩ :=
    exists_opens_smoothOfRelativeDimension (s.smoothLocus.ι ≫ s) t g h' ⟨z, hz⟩ w (by simpa using hw)
  refine ⟨(V.ι ≫ s.smoothLocus.ι).opensRange, ⟨⟨⟨z, hz⟩, hV⟩, by simp⟩, ?_⟩
  apply smoothOfRelativeDimension_opensRange_ι_comp'
  simpa using hVg
end GlobalTheory.SmoothNearFibre

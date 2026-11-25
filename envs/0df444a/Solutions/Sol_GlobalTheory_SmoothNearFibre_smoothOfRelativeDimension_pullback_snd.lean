-- Prove2me | solution 1 for GlobalTheory.SmoothNearFibre.smoothOfRelativeDimension_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:39.047655+00:00
-- url     : https://prove2.me/submissions/b8989224-2414-47da-9a4e-fccee25b7a69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothOfRelDimOfIsUnitProperFlat
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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.SmoothNearFibre
open GlobalTheory.VeryDenseFibres
namespace GlobalTheory.SmoothNearFibre
theorem _root_.solution {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (g : ℕ)
    (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  have hb := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
  have key : ∀ p : ↥(pullback s t), ∃ U : (pullback s t).Opens,
      p ∈ U ∧ SmoothOfRelativeDimension g (U.ι ≫ pullback.snd s t) := by
    intro p
    have hc : s (pullback.fst s t p) = t (pullback.snd s t p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨W, hzW, hW⟩ := h _ _ hc
    let e := pullbackRightPullbackFstIso s t W.ι
    let j := e.inv ≫ pullback.snd W.ι (pullback.fst s t)
    have hj : j ≫ pullback.snd s t = pullback.snd (W.ι ≫ s) t := by
      simp [j, e]
    refine ⟨j.opensRange, ?_, ?_⟩
    · obtain ⟨q, -, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := W.ι) (g := pullback.fst s t) ⟨_, hzW⟩ p (by simp)
      refine ⟨e.hom q, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      simpa [j] using hq2
    · rw [← j.isoOpensRange_inv_comp, Category.assoc, hj,
        MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
      exact MorphismProperty.pullback_snd _ _ hW
  choose U hU hP using key
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) U ?_ hP
  rw [eq_top_iff]
  intro p _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hU p⟩
end GlobalTheory.SmoothNearFibre

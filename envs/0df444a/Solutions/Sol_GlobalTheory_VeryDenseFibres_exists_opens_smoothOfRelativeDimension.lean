-- Prove2me | solution 1 for GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:35:52.397563+00:00
-- url     : https://prove2.me/submissions/e74be554-af05-4409-9b32-e5c044662e90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_dim_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_dim
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
open GlobalTheory GlobalTheory.VeryDenseFibres
namespace GlobalTheory.VeryDenseFibres
theorem _root_.solution {X T S : Scheme.{0}} (f : X ⟶ S) [Smooth f]
    (t : T ⟶ S) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd f t)) (x : X) (y : T)
    (hxy : f x = t y) : ∃ W : X.Opens, x ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ f) := by
  obtain ⟨n, W, hW, hd⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim f x
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  have h1 : SmoothOfRelativeDimension n (pullback.snd (W.ι ≫ f) t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ hd
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (W.ι ≫ f) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (W.ι ≫ f) t)
    ⟨x, hW⟩ y hxy
  have e : n = g := by simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  exact ⟨W, hW, e ▸ hd⟩
end GlobalTheory.VeryDenseFibres

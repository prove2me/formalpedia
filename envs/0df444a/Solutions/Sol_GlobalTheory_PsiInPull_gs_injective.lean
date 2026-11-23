-- Prove2me | solution 1 for GlobalTheory.PsiInPull.gs_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:05.095393+00:00
-- url     : https://prove2.me/submissions/3dd635af-1bfc-49e2-9246-10cc455221cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiInPull
namespace GlobalTheory.PsiInPull
theorem _root_.solution {Y Z : Scheme.{0}} [IsReduced Y] (f : Z ⟶ Y) (z : Z)
    (hz : ∀ U : Y.Opens, U ≠ ⊥ → f z ∈ U) (U : Y.Opens) (hU : f z ∈ U) {a b : Γ(Y, U)}
    (h : gs f z U a = gs f z U b) : a = b := by
  rw [gs_eq f z U hU, gs_eq f z U hU, ← sub_eq_zero, ← map_sub, ← map_sub] at h
  by_contra hne
  have h1 : f z ∈ Y.basicOpen (a - b) := hz _ (by
    rw [Ne, basicOpen_eq_bot_iff]; exact sub_ne_zero.2 hne)
  have h2 : z ∈ Z.basicOpen ((f.app U).hom (a - b)) := by
    rw [← Scheme.preimage_basicOpen]; exact h1
  have h3 := (Z.mem_basicOpen _ z hU).1 h2
  rw [h] at h3
  exact not_isUnit_zero h3
end GlobalTheory.PsiInPull

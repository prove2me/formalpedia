-- Prove2me | solution 1 for GlobalTheory.LBPush.gm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:58:43.698932+00:00
-- url     : https://prove2.me/submissions/a556ab7c-50ad-4ee7-a8c3-2e6c8bb92426

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCechDataPullbackOfLineBundleOnOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.LBPush
namespace GlobalTheory.LBPush
theorem _root_.solution {X Z : Scheme.{0}} (κ : Z ⟶ X) [IsOpenImmersion κ] (z : Z) {U : X.Opens} (h : κ z ∈ U)
    {a : Γ(X, U)ˣ} (e : gm κ z U a = 1) : gm (𝟙 X) (κ z) U a = 1 := by
  have hU : (𝟙 X) (κ z) ∈ U := h
  unfold gm pullU at e ⊢
  rw [dif_pos h] at e
  rw [dif_pos hU]
  have e' := congrArg Units.val e
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1
  refine ((Scheme.Hom.germ_stalkMap_apply κ U z h (a : Γ(X, U))).trans ?_).trans (map_one _).symm
  exact e'
end GlobalTheory.LBPush

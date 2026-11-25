-- Prove2me | solution 1 for GlobalTheory.CocycleGlue.exists_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:00.629078+00:00
-- url     : https://prove2.me/submissions/decc9622-516e-4f9c-8dbf-7d2d157a8770

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GlueSchemesOverOpensAlongCocycle
import Theorems.Thm_GlobalTheory_CoverGlue_exists_hom


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
open GlobalTheory GlobalTheory.CocycleGlue
namespace GlobalTheory.CocycleGlue
theorem _root_.solution (D : Scheme.GlueData.{0}) {S : Scheme.{0}} (p : ∀ i, D.U i ⟶ S)
    (h : ∀ i j, D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j) :
    ∃ F : D.glued ⟶ S, ∀ i, D.ι i ≫ F = p i := by
  exact GlobalTheory.CoverGlue.exists_hom (ψ := D.ι) (fun i => inferInstance)
    (fun x => by
      obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
      exact ⟨i, y, hy⟩)
    p (B := fun i j => D.V (i, j)) (a := fun i j => D.f i j) (b := fun i j => D.t i j ≫ D.f j i)
    (fun i j => IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)) h
end GlobalTheory.CocycleGlue

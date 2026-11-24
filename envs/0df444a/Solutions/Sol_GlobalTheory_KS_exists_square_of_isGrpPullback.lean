-- Prove2me | solution 1 for GlobalTheory.KS.exists_square_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:32:27.844869+00:00
-- url     : https://prove2.me/submissions/369b24c0-031d-49dc-8c1a-42ba8e4a42cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSquareOfIsGrpPullback

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S)
    [GrpObj G] (f : S' ⟶ S) (m : G'.left ⟶ G.left) (h : IsGrpPullback G' G f m) :
    ∃ m₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst G' G' * snd G' G').left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (G' ⊗ G').hom ≫ f := by
  have hw : m ≫ G.hom = G'.hom ≫ f := h.1.w
  let a : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((fst G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  let b : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((snd G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  refine ⟨(lift a b).left, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact congrArg Over.Hom.left (lift_fst a b)
  · exact congrArg Over.Hom.left (lift_snd a b)
  · rw [← h.2 (G' ⊗ G') (fst G' G') (snd G' G') a b rfl rfl]
    have : lift a b ≫ (fst G G * snd G G) = a * b := by
      rw [MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left this
  · exact Over.w (lift a b)
end GlobalTheory.KS

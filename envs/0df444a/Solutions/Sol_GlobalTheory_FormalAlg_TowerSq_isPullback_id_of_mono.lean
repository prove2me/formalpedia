-- Prove2me | solution 1 for GlobalTheory.FormalAlg.TowerSq.isPullback_id_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:41.256933+00:00
-- url     : https://prove2.me/submissions/0b70c538-b4a0-416e-a1bc-ade9ade3e95b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TowerSquares

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FormalAlg GlobalTheory.FormalAlg.TowerSq
namespace GlobalTheory.FormalAlg.TowerSq
theorem _root_.solution {C : Type*} [Category C] {X Y Z : C} (h : X ⟶ Y) (f : Y ⟶ Z) [Mono f] :
    IsPullback h (𝟙 X) f (h ≫ f) := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk h (𝟙 X) (by simp)) (PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => ?_)
    (fun s m _ h2 => ?_))
  · rw [← cancel_mono f, Category.assoc]
    exact s.condition.symm
  · exact Category.comp_id _
  · simpa using h2
end GlobalTheory.FormalAlg.TowerSq

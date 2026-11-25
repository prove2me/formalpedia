-- Prove2me | solution 1 for GlobalTheory.T.isPullback_thick_tower_squares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:05.619117+00:00
-- url     : https://prove2.me/submissions/5f6805c1-741e-41d9-a697-33e90a78c712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TowerSquares
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TowerSquaresStatement
import Theorems.Thm_GlobalTheory_FormalAlg_towerSquares


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsPullback (β e) (Y e).hom ((Y (e + 1)).hom ≫ thick R I (e + 1)) (thick R I e)) ∧ ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ e, IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) := by
  first | exact @GlobalTheory.FormalAlg.towerSquares | exact GlobalTheory.FormalAlg.towerSquares | (intros; apply GlobalTheory.FormalAlg.towerSquares <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:29.590542+00:00
-- url     : https://prove2.me/submissions/9ef8b0f9-a328-437c-a39f-2adc384feabe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalLiftOfChartLocalLiftsSquareZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalLiftOfChartLocalLiftsSquareZeroStatement
import Theorems.Thm_GlobalTheory_SecGlue_exists_lift_of_chart_lifts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  first | exact @GlobalTheory.SecGlue.exists_lift_of_chart_lifts | exact GlobalTheory.SecGlue.exists_lift_of_chart_lifts | (intros; apply GlobalTheory.SecGlue.exists_lift_of_chart_lifts <;> assumption)
end _root_.GlobalTheory.T

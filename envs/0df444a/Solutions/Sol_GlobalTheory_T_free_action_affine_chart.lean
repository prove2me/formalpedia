-- Prove2me | solution 1 for GlobalTheory.T.free_action_affine_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:42.372938+00:00
-- url     : https://prove2.me/submissions/45d71d9d-0e00-4762-a440-8ac83e58242d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChartStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_hasAffineChart_of_stable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → IsFreeAction G X → ∀ (V : X.left.Opens) (W : S.Opens), IsAffineOpen V → IsAffineOpen W → V ≤ X.hom ⁻¹ᵁ W → (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V → HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable | exact GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable <;> assumption)
end _root_.GlobalTheory.T

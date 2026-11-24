-- Prove2me | solution 1 for GlobalTheory.T.invariant_open_chart_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:06:52.463793+00:00
-- url     : https://prove2.me/submissions/094657e8-2392-4882-a309-43fd488172aa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_InvariantOpenChartPreimage
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_InvariantOpenChartPreimageStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_exists_opens_image_preimage


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
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ (V' : X.Opens), V' ≤ V → a ⁻¹ᵁ V' = b ⁻¹ᵁ V' → ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | exact GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage <;> assumption)
end _root_.GlobalTheory.T

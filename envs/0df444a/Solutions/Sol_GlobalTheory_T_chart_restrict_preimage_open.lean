-- Prove2me | solution 1 for GlobalTheory.T.chart_restrict_preimage_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:39.923101+00:00
-- url     : https://prove2.me/submissions/af52306e-bdc2-4c95-8d37-f4b14a652303

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpen
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpenStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_isChart_restrict_quotient_open


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
theorem _root_.solution : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ D : Y.Opens, ∃ (hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V) (q' : (V.ι ''ᵁ (q ⁻¹ᵁ D)).toScheme ⟶ D.toScheme), IsChart a b (V.ι ''ᵁ (q ⁻¹ᵁ D)) q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open | exact GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open <;> assumption)
end _root_.GlobalTheory.T

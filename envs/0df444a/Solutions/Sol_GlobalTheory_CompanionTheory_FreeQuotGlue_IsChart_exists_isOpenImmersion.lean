-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:49:17.351743+00:00
-- url     : https://prove2.me/submissions/c4171f49-57b9-4c68-9a1c-58683744f6b9

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_InvariantOpenChartPreimageStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_GlueQuotientChartsCoverStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedChartsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_QuotientOfAffineChartCover
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_exists_iso_of_effectiveEpi
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_comp_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_effectiveEpi
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_stable
import Theorems.Thm_GlobalTheory_T_chart_restrict_preimage_open
import Theorems.Thm_GlobalTheory_T_invariant_open_chart_preimage


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
namespace IsChart
theorem _root_.solution {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {V V' : X.Opens}
    {q : V.toScheme ⟶ Y} {q' : V'.toScheme ⟶ Y'} (h : IsChart a b V q) (h' : IsChart a b V' q')
    (hle : V' ≤ V) : ∃ k : Y' ⟶ Y, IsOpenImmersion k ∧ q' ≫ k = X.homOfLE hle ≫ q := by
  obtain ⟨D, rfl⟩ := GlobalTheory.T.invariant_open_chart_preimage h V' hle h'.stable
  obtain ⟨hle₂, q'', hc, hq⟩ := GlobalTheory.T.chart_restrict_preimage_open h D
  have := h'.effectiveEpi
  have := hc.effectiveEpi
  obtain ⟨e, he⟩ := exists_iso_of_effectiveEpi q' q'' fun Z g₁ g₂ ↦ by
    rw [h'.comp_eq_iff, hc.comp_eq_iff]
  refine ⟨e.hom ≫ D.ι, inferInstance, ?_⟩
  rw [reassoc_of% he, hq]
end IsChart
end GlobalTheory.CompanionTheory.FreeQuotGlue

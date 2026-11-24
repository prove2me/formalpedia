-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:49:18.203118+00:00
-- url     : https://prove2.me/submissions/4aab3783-181f-48ce-b27b-51befaef5d32

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_InvariantOpenChartPreimageStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_GlueQuotientChartsCoverStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedChartsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_QuotientOfAffineChartCover
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_stable
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_hasAffineChart_iff
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
theorem _root_.solution {P X : Scheme.{0}} {a b : P ⟶ X} {U V : X.Opens}
    (hU : HasAffineChart a b U) (hV : HasAffineChart a b V) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    ∃ W, HasAffineChart a b W ∧ x ∈ W ∧ W ≤ U ∧ W ≤ V := by
  obtain ⟨Y, q, hY, hq⟩ := (hasAffineChart_iff a b U).1 hU
  obtain ⟨D, hD⟩ := GlobalTheory.T.invariant_open_chart_preimage hq (U ⊓ V) inf_le_left (by
    have h1 := hq.stable
    have h2 := hV.1
    ext p
    have h1' := SetLike.ext_iff.1 h1 p
    have h2' := SetLike.ext_iff.1 h2 p
    exact and_congr h1' h2')
  have hx : x ∈ U.ι ''ᵁ (q ⁻¹ᵁ D) := hD ▸ ⟨hxU, hxV⟩
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨D', hD', hm, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := q u) (U := D) hu
  obtain ⟨hW, q', hc, hq'⟩ := GlobalTheory.T.chart_restrict_preimage_open hq D'
  have hle' : U.ι ''ᵁ (q ⁻¹ᵁ D') ≤ U ⊓ V := by
    rw [← hD]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hle hv, rfl⟩
  have : IsAffine D'.toScheme := hD'
  exact ⟨_, (hasAffineChart_iff a b _).2 ⟨_, q', this, hc⟩, ⟨u, hm, rfl⟩, hW, hle'.trans inf_le_right⟩
end GlobalTheory.CompanionTheory.FreeQuotGlue

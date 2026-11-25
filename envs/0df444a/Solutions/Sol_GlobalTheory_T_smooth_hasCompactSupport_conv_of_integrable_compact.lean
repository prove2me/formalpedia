-- Prove2me | solution 1 for GlobalTheory.T.smooth_hasCompactSupport_conv_of_integrable_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:19.141601+00:00
-- url     : https://prove2.me/submissions/5ec812de-378b-4cd6-a5d9-d5671a0aebaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvSmoothCompactSupport
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvSmoothCompactSupportStatement
import Theorems.Thm_GlobalTheory_ConvSmooth_conv_smooth_compactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Set G, IsCompact K → ∀ κ a : G → ℂ, h.IsSmoothFun κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → h.IsSmoothFun (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) ∧ HasCompactSupport (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) := by
  first | exact @GlobalTheory.ConvSmooth.conv_smooth_compactSupport | exact GlobalTheory.ConvSmooth.conv_smooth_compactSupport | (intros; apply GlobalTheory.ConvSmooth.conv_smooth_compactSupport <;> assumption)
end _root_.GlobalTheory.T

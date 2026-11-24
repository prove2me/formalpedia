-- Prove2me | solution 1 for GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:19.176679+00:00
-- url     : https://prove2.me/submissions/902242c3-40d1-4bc6-8a99-b3d367a63402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKindStatement
import Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ T : Set L, Submodule.span ℝ T = ⊤ → ∀ φ : G → ℂ, Sm (expMap j s) φ ↔ ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => expMap j s (t i • Y i)).prod) := by
  first | exact @GlobalTheory.SmoothForms.SecondKind.main | exact GlobalTheory.SmoothForms.SecondKind.main | (intros; apply GlobalTheory.SmoothForms.SecondKind.main <;> assumption)
end _root_.GlobalTheory.T

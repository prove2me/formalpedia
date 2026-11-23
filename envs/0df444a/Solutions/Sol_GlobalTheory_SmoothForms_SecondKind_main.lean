-- Prove2me | solution 1 for GlobalTheory.SmoothForms.SecondKind.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:30.623588+00:00
-- url     : https://prove2.me/submissions/6e42f50b-caff-481b-aba6-dd68827e8e12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind
import Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_sm_iff

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
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
open NumberField Matrix
open scoped ContDiff Topology
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
namespace GlobalTheory.SmoothForms.SecondKind
namespace _root_.GlobalTheory.SmoothForms.SecondKind
theorem _root_.solution : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
    [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), _root_.GlobalTheory.SmoothForms.IsLieData σ j s →
    _root_.GlobalTheory.SmoothForms.HasLog σ j →
    ∀ T : Set L, Submodule.span ℝ T = ⊤ → ∀ φ : G → ℂ, _root_.GlobalTheory.SmoothForms.Sm (_root_.GlobalTheory.SmoothForms.expMap j s) φ ↔
      ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        φ (g * (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod) := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl T hT φ
  exact _root_.GlobalTheory.SmoothForms.SecondKind.sm_iff H hl T hT φ
end _root_.GlobalTheory.SmoothForms.SecondKind
end GlobalTheory.SmoothForms.SecondKind

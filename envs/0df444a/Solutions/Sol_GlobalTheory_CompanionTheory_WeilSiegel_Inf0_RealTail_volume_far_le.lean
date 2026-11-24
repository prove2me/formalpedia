-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.volume_far_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:57.010315+00:00
-- url     : https://prove2.me/submissions/a2748689-4da5-4ed9-bbde-84d0451f8628

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
theorem _root_.solution {a : ℕ} {Q : (P → ι → ℝ) → (P → ℝ)} {C : ℝ≥0}
    (hbox : ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U)
    (Y : Set (P → ι → ℝ)) {U : Set (P → ℝ)} (hU : MeasurableSet U) (j : ℕ) :
    (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ Y) ∩ boxR (fun _ => (2 : ℝ) ^ j)) ≤
      ((C : ℝ≥0∞) * volume U) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (a * Fintype.card P)) := by
  have hsub : (Q ⁻¹' U ∩ Y) ∩ boxR (fun _ => (2 : ℝ) ^ j) ⊆
      Q ⁻¹' U ∩ boxR (fun _ => (2 : ℝ) ^ j) := fun x hx => ⟨hx.1.1, hx.2⟩
  have hprod : ∏ _w : P, ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ j) ^ (a * Fintype.card P) := by
    rw [Finset.prod_const, ← pow_mul, Finset.card_univ]
  calc (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ Y) ∩ boxR (fun _ => (2 : ℝ) ^ j))
      ≤ volume (Q ⁻¹' U ∩ boxR (fun _ => (2 : ℝ) ^ j)) := measure_mono hsub
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ _w : P, ((2 : ℝ) ^ j) ^ a) * volume U :=
        hbox _ (fun _ => by positivity) U hU
    _ = _ := by rw [hprod]; ring
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail

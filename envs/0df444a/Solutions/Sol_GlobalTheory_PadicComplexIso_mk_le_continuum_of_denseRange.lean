-- Prove2me | solution 1 for GlobalTheory.PadicComplexIso.mk_le_continuum_of_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:36:11.733263+00:00
-- url     : https://prove2.me/submissions/21744013-a34e-4631-9146-35e12e6d4a0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MkLeContinuumOfDenseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open Cardinal
open GlobalTheory GlobalTheory.PadicComplexIso
namespace GlobalTheory.PadicComplexIso
theorem _root_.solution {X Y : Type} [MetricSpace Y] (f : X → Y)
    (hf : DenseRange f) (hX : #X ≤ 𝔠) : #Y ≤ 𝔠 := by
  have hex : ∀ (y : Y) (n : ℕ), ∃ x, dist (f x) y < 1 / ((n : ℝ) + 1) := by
    intro y n
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 hf y (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨x, by rw [dist_comm]; exact hx⟩
  choose g hg using hex
  have hlim : ∀ y, Filter.Tendsto (fun n => f (g y n)) Filter.atTop (nhds y) := by
    intro y
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hg y n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinj : Function.Injective g := by
    intro y y' h
    have h2 := hlim y'
    rw [← h] at h2
    exact tendsto_nhds_unique (hlim y) h2
  calc #Y ≤ #(ℕ → X) := Cardinal.mk_le_of_injective hinj
    _ = #X ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]
    _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right hX
    _ = 𝔠 := Cardinal.continuum_power_aleph0
end GlobalTheory.PadicComplexIso

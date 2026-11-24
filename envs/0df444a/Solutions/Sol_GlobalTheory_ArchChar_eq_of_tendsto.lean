-- Prove2me | solution 1 for GlobalTheory.ArchChar.eq_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:36.686572+00:00
-- url     : https://prove2.me/submissions/659a19d6-b0e4-4138-827c-b2537d3374a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ArchChar
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchChar
theorem _root_.solution (ψ : (ι → ℂˣ) →* ℂˣ) (hψ : Continuous ψ) {X X' : ℕ → ι → ℂˣ} {w w' : ι → ℂˣ}
    (h : ∀ m, ψ (X m) = ψ (X' m))
    (hX : ∀ i, Tendsto (fun m => (X m i : ℂ)) atTop (𝓝 (w i : ℂ)))
    (hX' : ∀ i, Tendsto (fun m => (X' m i : ℂ)) atTop (𝓝 (w' i : ℂ))) : ψ w = ψ w' := by
  have conv : ∀ {Y : ℕ → ι → ℂˣ} {v : ι → ℂˣ},
      (∀ i, Tendsto (fun m => (Y m i : ℂ)) atTop (𝓝 (v i : ℂ))) → Tendsto Y atTop (𝓝 v) := by
    intro Y v hY
    rw [tendsto_pi_nhds]
    intro i
    exact Units.isEmbedding_val₀.isInducing.tendsto_nhds_iff.2 (hY i)
  have h1 := (hψ.tendsto w).comp (conv hX)
  have h2 := (hψ.tendsto w').comp (conv hX')
  have h3 : (ψ ∘ X) = (ψ ∘ X') := funext h
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2
end GlobalTheory.ArchChar

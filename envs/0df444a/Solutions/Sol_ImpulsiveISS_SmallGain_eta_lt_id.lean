-- Prove2me | solution 1 for ImpulsiveISS.SmallGain.eta_lt_id
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:59:59.339649+00:00
-- url     : https://prove2.me/submissions/db6708a9-06b5-466c-b3e0-ce800d7f1ad5

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System
import Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
open scoped NNReal
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

open ImpulsiveISS.SmallGain in
theorem solution {n : ℕ} (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0)
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0) (hσ : IsOmegaPath (ImpulsiveISS.SmallGain.gainOp χ) σ τ) :
    ∀ r : ℝ≥0, 0 < r → etaGain σ τ χ r < r := by
  intro r hr
  obtain ⟨-, hK, hInv, -, -, hΩ⟩ := hσ
  have hO := hΩ r hr
  unfold etaGain
  rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr hr.ne')]
  intro i _
  rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr hr.ne')]
  intro j _
  have h1 : ImpulsiveISS.SmallGain.gainOp χ (σ r) i < σ r i := hO i
  have h2 : χ i j (σ r j) < σ r i := by
    refine lt_of_le_of_lt ?_ h1
    unfold ImpulsiveISS.SmallGain.gainOp
    exact Finset.le_sup (f := fun j => χ i j (σ r j)) (Finset.mem_univ j)
  have hmono : StrictMono (fun r => σ r i) := (hK i).1.2.1
  have hL : τ i (σ r i) = r := (hInv i).1 r
  have hR : σ (τ i (χ i j (σ r j))) i = χ i j (σ r j) := (hInv i).2 _
  have : σ (τ i (χ i j (σ r j))) i < σ r i := by rw [hR]; exact h2
  exact hmono.lt_iff_lt.mp this

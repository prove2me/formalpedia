-- Prove2me | solution 1 for ImpulseGames.Verification.verification_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:07:08.722984+00:00
-- url     : https://prove2.me/submissions/37656e0e-46a9-47b8-b727-e1c23e4528e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
import Definitions.Def_ImpulseGames_Verification_QVI
import Theorems.Thm_ImpulseGames_Verification_step1_deviation_bound
import Theorems.Thm_ImpulseGames_Verification_step2_equilibrium_payoff
import Theorems.Thm_ImpulseGames_Verification_step1_deviation_bound_player_two
import Theorems.Thm_ImpulseGames_Verification_step2_equilibrium_payoff_player_two

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification

theorem solution {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)
    (hV : VerificationHypotheses G V δ) (x : State d) (hx : x ∈ G.S)
    (hΦ : InPhi P 𝔽 W G x (starProfile G V δ)) :
    IsNash P 𝔽 W G x (starProfile G V δ) ∧
    ∀ Y : ℕ → ℝ≥0 → Ω → State d, IsAdmissible P 𝔽 W G x (starProfile G V δ) Y →
      ∀ i, V i x = payoff P G x (starProfile G V δ) Y i := by
  have hEq : ∀ Y : ℕ → ℝ≥0 → Ω → State d, IsAdmissible P 𝔽 W G x (starProfile G V δ) Y →
      ∀ i, V i x = payoff P G x (starProfile G V δ) Y i := by
    intro Y hY i
    cases i
    · exact step2_equilibrium_payoff P 𝔽 W hW G hG V δ hV x hx Y hY
    · exact step2_equilibrium_payoff_player_two P 𝔽 W hW G hG V δ hV x hx Y hY
  refine ⟨⟨hΦ, ?_⟩, hEq⟩
  intro i Ci ξi Y Y' hY hY'
  rw [← hEq Y' hY' i]
  cases i
  · exact step1_deviation_bound P 𝔽 W hW G hG V δ hV x hx Ci ξi Y hY
  · exact step1_deviation_bound_player_two P 𝔽 W hW G hG V δ hV x hx Ci ξi Y hY

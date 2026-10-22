-- Prove2me | solution 1 for ImpulseNMFG.Verification.theorem_2_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:04:50.732359+00:00
-- url     : https://prove2.me/submissions/4b2dc213-e15d-49c5-baa8-e0f98d0abd9d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
import Definitions.Def_ImpulseNMFG_Verification_QVI
import Theorems.Thm_ImpulseNMFG_Verification_step_1
import Theorems.Thm_ImpulseNMFG_Verification_step_2
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State IsBrownianBasis)
open ImpulseNMFG.Verification

theorem solution {N d M : ℕ} [NeZero N] {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin M → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game N d M) (hG : G.Standing)
    (V : Fin N → State d → ℝ) (ξ : (i : Fin N) → State d → G.Imp i)
    (h210 : ∀ i, IsUniqueMinimizer G V ξ i)
    (hi : ∀ i, SolvesQVI G V ξ i)
    (hii : ∀ i, Regular G V ξ i)
    (hiii : ∀ i, BoundaryRegular G V ξ i)
    (x : State d) (hx : x ∈ G.S)
    (hocc : ∀ i, BoundaryNegligible P 𝔽 W G V ξ x i)
    (hadm : InPhi P 𝔽 W G x (starProfile G V ξ)) :
    IsNash P 𝔽 W G x (starProfile G V ξ) ∧
    ∀ (i : Fin N) (Y : ℕ → ℝ≥0 → Ω → State d),
      IsAdmissible P 𝔽 W G x (starProfile G V ξ) Y →
      V i x = cost P G x (starProfile G V ξ) Y i := by
  have h2 := step_2 P 𝔽 W hW G hG V ξ h210 hi hii hiii x hx hocc hadm
  have h1 := step_1 P 𝔽 W hW G hG V ξ h210 hi hii hiii x hx hocc
  refine ⟨⟨hadm, ?_⟩, h2⟩
  intro i A ξ' Y Y' hY hY'
  rw [← h2 i Y' hY']
  exact h1 i A ξ' Y hY

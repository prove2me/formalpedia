-- Prove2me | solution 1 for LinearChoresCLS.completed_market_word
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:00:45.176889+00:00
-- url     : https://prove2.me/submissions/0eefef23-b30a-4cdc-b05e-cc44b426ae8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch
import Theorems.Thm_LinearChoresCLS_completedRatMarket_spec
import Theorems.Thm_LinearChoresCLS_completedRatMarket_word

open NetworkEquilibriumCLS.LinearNash
open LinearChoresCLS

theorem solution :
    ∃ f : List Bool → List Bool, PolyTime f ∧
      ∀ {n : ℕ}, 0 < n → ∀ (P : Quadratic n) (ε : ℚ), 0 < ε →
        let L := chainLength P ε
        let F := completedMarket P ε
        ∃ (a m : ℕ) (e : Agent n L ≃ Fin a) (d : Chore n L ≃ Fin m) (G : RatChoresMarket a m),
          (∀ j : Fin (n+1), (d (Sum.inl j)).val = j.val) ∧
          (∀ i j, (G.disutil (e i) (d j) : ℝ) = F.disutil i j) ∧
          (∀ i, (G.earn (e i) : ℝ) = F.earn i) ∧
          (∀ j, (G.supply (d j) : ℝ) = F.supply j) ∧
          encChores G = f (encQuadratic P ++ encRat ε) := by
  obtain ⟨f, hf, hcode⟩ := completedRatMarket_word
  refine ⟨f, hf, ?_⟩
  intro n hn P ε hε
  dsimp only
  refine ⟨n + 1 + auxAgentCount n (chainLength P ε),
    n + 1 + auxChoreCount n (chainLength P ε),
    agentFinEquiv n (chainLength P ε), choreFinEquiv n (chainLength P ε),
    completedRatMarket P ε, ?_⟩
  obtain ⟨hpos, hdis, hearn, hsupply⟩ := completedRatMarket_spec P ε
  exact ⟨hpos, hdis, hearn, hsupply, hcode hn P ε hε⟩

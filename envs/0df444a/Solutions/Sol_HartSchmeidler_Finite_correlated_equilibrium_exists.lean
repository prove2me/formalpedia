-- Prove2me | solution 1 for HartSchmeidler.Finite.correlated_equilibrium_exists
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:35:13.865041+00:00
-- url     : https://prove2.me/submissions/9d064f2b-1636-4b63-8638-e7156837d981

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HartSchmeidler_Finite_Game
import Theorems.Thm_HartSchmeidler_Finite_minimax_nonneg_criterion
import Theorems.Thm_HartSchmeidler_Finite_aux_game_correspondence
import Theorems.Thm_HartSchmeidler_Finite_eq2_exists_player_vector
import Theorems.Thm_HartSchmeidler_Finite_product_strategy_payoff_zero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


open HartSchmeidler.Finite Finset

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)] (h : ι → (∀ i, S i) → ℝ) :
    ∃ p : (∀ i, S i) → ℝ, IsCorrelatedEq h p :=
  by
  classical
  by_cases hι : IsEmpty ι
  · refine ⟨fun _ => 1, ⟨fun _ => zero_le_one, ?_⟩, fun i => (hι.false i).elim⟩
    simp [Fintype.card_pi, Finset.univ_eq_empty]
  · have : Nonempty ι := not_isEmpty_iff.1 hι
    have : Nonempty (Deviation S) :=
      ⟨⟨Classical.arbitrary ι, (Classical.arbitrary _, Classical.arbitrary _)⟩⟩
    have : Nonempty (∀ i, S i) := ⟨fun i => Classical.arbitrary _⟩
    obtain ⟨p, hp, hpy⟩ := HartSchmeidler.Finite.minimax_nonneg_criterion
      (fun (s : ∀ i, S i) (c : Deviation S) => auxPayoff h s c) (by
        intro y hy
        choose x hx hxbal using fun i =>
          HartSchmeidler.Finite.eq2_exists_player_vector h i (fun r t => y ⟨i, (r, t)⟩)
            (fun r t => hy.1 _)
        obtain ⟨hlot, hzero⟩ :=
          HartSchmeidler.Finite.product_strategy_payoff_zero h y hy x hx hxbal
        exact ⟨_, hlot, hzero.symm.le⟩)
    exact ⟨p, (HartSchmeidler.Finite.aux_game_correspondence h p).2 ⟨hp, hpy⟩⟩

#print axioms solution

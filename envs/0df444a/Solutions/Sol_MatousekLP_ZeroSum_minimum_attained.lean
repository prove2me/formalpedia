-- Prove2me | solution 1 for MatousekLP.ZeroSum.minimum_attained
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:48:12.805203+00:00
-- url     : https://prove2.me/submissions/0804a57e-e1a5-4f3d-a32a-84c5654e6ebb

import Definitions.Def_MatousekLP_ZeroSum_Game
import Mathlib

open Matrix MatousekLP.ZeroSum

namespace ZSAux

variable {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)

lemma continuous_payoff_right (x : Fin m → ℝ) : Continuous (fun y => payoff M x y) := by
  unfold payoff; fun_prop

lemma continuous_payoff_left (y : Fin n → ℝ) : Continuous (fun x => payoff M x y) := by
  unfold payoff; fun_prop

lemma beta_le (x : Fin m → ℝ) {y : Fin n → ℝ} (hy : y ∈ stdSimplex ℝ (Fin n)) :
    beta M x ≤ payoff M x y :=
  csInf_le ((isCompact_stdSimplex ℝ (Fin n)).image (continuous_payoff_right M x)).bddBelow
    ⟨y, hy, rfl⟩

lemma le_alpha (y : Fin n → ℝ) {x : Fin m → ℝ} (hx : x ∈ stdSimplex ℝ (Fin m)) :
    payoff M x y ≤ alpha M y :=
  le_csSup ((isCompact_stdSimplex ℝ (Fin m)).image (continuous_payoff_left M y)).bddAbove
    ⟨x, hx, rfl⟩

lemma beta_isLeast (hn : 1 ≤ n) (x : Fin m → ℝ) :
    IsLeast ((fun y => payoff M x y) '' stdSimplex ℝ (Fin n)) (beta M x) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hK := (isCompact_stdSimplex ℝ (Fin n)).image (continuous_payoff_right M x)
  have hne : ((fun y => payoff M x y) '' stdSimplex ℝ (Fin n)).Nonempty :=
    ⟨_, ⟨Pi.single ⟨0, hn⟩ 1, single_mem_stdSimplex ℝ _, rfl⟩⟩
  exact ⟨hK.sInf_mem hne, fun _ ⟨y, hy, h⟩ => h ▸ beta_le M x hy⟩

lemma alpha_isGreatest (hm : 1 ≤ m) (y : Fin n → ℝ) :
    IsGreatest ((fun x => payoff M x y) '' stdSimplex ℝ (Fin m)) (alpha M y) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hK := (isCompact_stdSimplex ℝ (Fin m)).image (continuous_payoff_left M y)
  have hne : ((fun x => payoff M x y) '' stdSimplex ℝ (Fin m)).Nonempty :=
    ⟨_, ⟨Pi.single ⟨0, hm⟩ 1, single_mem_stdSimplex ℝ _, rfl⟩⟩
  exact ⟨hK.sSup_mem hne, fun _ ⟨x, hx, h⟩ => h ▸ le_alpha M y hx⟩

end ZSAux

open ZSAux in
theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x ∈ stdSimplex ℝ (Fin m),
      IsLeast ((fun y => payoff M x y) '' stdSimplex ℝ (Fin n)) (beta M x)) ∧
    (∀ y ∈ stdSimplex ℝ (Fin n),
      IsGreatest ((fun x => payoff M x y) '' stdSimplex ℝ (Fin m)) (alpha M y)) :=
  ⟨fun x _ => beta_isLeast M hn x, fun y _ => alpha_isGreatest M hm y⟩

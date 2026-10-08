-- Prove2me | solution 1 for MatousekLP.ZeroSum.nash_worstCaseOptimal
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:48:37.739989+00:00
-- url     : https://prove2.me/submissions/e86563f2-11f7-4f9e-9eb1-e5b335a4e897

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
theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) (xt : Fin m → ℝ) (yt : Fin n → ℝ)
    (h : IsMixedNash M xt yt) :
    IsWorstCaseOptimalAlice M xt ∧ IsWorstCaseOptimalBob M yt := by
  obtain ⟨⟨hxt, hA⟩, ⟨hyt, hB⟩⟩ := h
  -- the equilibrium payoff equals beta at xt and alpha at yt
  have hbeta : beta M xt = payoff M xt yt := by
    refine le_antisymm (beta_le M xt hyt) ?_
    exact le_csInf ⟨_, ⟨yt, hyt, rfl⟩⟩ (by rintro _ ⟨y', hy', rfl⟩; exact hB y' hy')
  have halpha : alpha M yt = payoff M xt yt := by
    refine le_antisymm ?_ (le_alpha M yt hxt)
    exact csSup_le ⟨_, ⟨xt, hxt, rfl⟩⟩ (by rintro _ ⟨x', hx', rfl⟩; exact hA x' hx')
  refine ⟨⟨hxt, fun x hx => ?_⟩, ⟨hyt, fun y hy => ?_⟩⟩
  · calc beta M x ≤ payoff M x yt := beta_le M x hyt
      _ ≤ payoff M xt yt := hA x hx
      _ = beta M xt := hbeta.symm
  · calc alpha M yt = payoff M xt yt := halpha
      _ ≤ payoff M xt y := hB y hy
      _ ≤ alpha M y := le_alpha M y hxt

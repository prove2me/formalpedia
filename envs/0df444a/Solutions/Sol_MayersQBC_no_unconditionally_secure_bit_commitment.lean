-- Prove2me | solution 1 for MayersQBC.no_unconditionally_secure_bit_commitment
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:04:03.632894+00:00
-- url     : https://prove2.me/submissions/d0280ec4-2c0b-4f01-98cb-70af9263e429

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_MayersQBC_expectedFidelity
import Definitions.Def_MayersQBC_cheatProb
import Theorems.Thm_MayersQBC_cheatProb_ge_expectedFidelity
open QAlgorithms Filter Topology

open MayersQBC in
theorem solution
    (Γ A B : ℕ → Type) [∀ n, Fintype (Γ n)] [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    [∀ n, Fintype (B n)] [∀ n, DecidableEq (B n)]
    (p q : ∀ n, Γ n → ℝ) (hp : ∀ n, (∀ γ, 0 ≤ p n γ) ∧ ∑ γ, p n γ = 1)
    (ψ0 ψ1 : ∀ n, Γ n → EuclideanSpace ℂ (A n × B n))
    (h0 : ∀ n γ, IsState (ψ0 n γ)) (h1 : ∀ n γ, IsState (ψ1 n γ))
    (acc : ∀ n, Γ n → Matrix (A n × B n) (A n × B n) ℂ) (hacc : ∀ n γ, IsEffect (acc n γ))
    (hcorrect : ∀ n γ, q n γ ≠ 0 → effectProb (acc n γ) (pureDensity (ψ1 n γ)) = 1)
    (hconceal : Tendsto (fun n => expectedFidelity (p n) (q n) (ψ0 n) (ψ1 n)) atTop (𝓝 1)) :
    ∃ U : ∀ n, Γ n → Matrix (A n) (A n) ℂ, (∀ n γ, U n γ ∈ Matrix.unitaryGroup (A n) ℂ) ∧
      (∀ n, expectedFidelity (p n) (q n) (ψ0 n) (ψ1 n) ≤ cheatProb (p n) (acc n) (U n) (ψ0 n)) ∧
      Tendsto (fun n => cheatProb (p n) (acc n) (U n) (ψ0 n)) atTop (𝓝 1) := by
  -- for every security parameter, the two-sided bound `E_γ F'(γ) ≤ P^cheat_n ≤ 1`
  have key := fun n => cheatProb_ge_expectedFidelity (p n) (q n) (hp n) (ψ0 n) (ψ1 n) (h0 n)
    (h1 n) (acc n) (hacc n) (hcorrect n)
  choose U hU hlo hhi using key
  refine ⟨U, hU, hlo, ?_⟩
  -- squeeze: `E_γ F'_n(γ) → 1` and `P^cheat_n ≤ 1`
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hconceal tendsto_const_nhds hlo hhi

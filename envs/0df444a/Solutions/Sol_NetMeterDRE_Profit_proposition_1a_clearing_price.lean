-- Prove2me | solution 1 for NetMeterDRE.Profit.proposition_1a_clearing_price
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:02:25.414828+00:00
-- url     : https://prove2.me/submissions/55292c22-afaa-4ec7-be24-8877111ee2f8

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE

set_option autoImplicit false
open NetMeterDRE.Profit

theorem solution (N : ℕ) (c : ℝ) (hN : 2 < N) (hc : 0 < c) :
    (∀ x p : ℝ, IsClearing (fun _ : Fin N => symSupply N c) x p ↔ p = alpha N c * x) ∧
    ∀ pw : ℝ → ℝ, (∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x)) →
      ∀ x₀ : ℝ, deriv pw x₀ = alpha N c := by
  have hN' : (2 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (N : ℝ) - 2 ≠ 0 := by linarith
  have h3 : (N : ℝ) ≠ 0 := by linarith
  have hc' : c ≠ 0 := hc.ne'
  have hcl : ∀ x p : ℝ, IsClearing (fun _ : Fin N => symSupply N c) x p ↔ p = alpha N c * x := by
    intro x p
    rw [IsClearing]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, symSupply, alpha]
    constructor
    · intro h
      rw [← h]; field_simp
    · intro h
      rw [h]; field_simp
  refine ⟨hcl, ?_⟩
  intro pw hpw x₀
  have : pw = fun x => alpha N c * x := funext fun x => (hcl x (pw x)).1 (hpw x)
  rw [this]
  simp

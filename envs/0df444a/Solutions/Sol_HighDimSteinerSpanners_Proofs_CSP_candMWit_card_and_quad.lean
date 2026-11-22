-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.candMWit_card_and_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:11.433048+00:00
-- url     : https://prove2.me/submissions/78f2d283-bc82-4fd7-845e-1b091dde93b1

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_card_le
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_quad

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} (C₁ r_star m : ℕ)
    (hC₁ : 3 ≤ C₁) (hr : 1000 * C₁ < r_star)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (hd_xa : dHam x a ≤ C₁ * r_star) (hd_xb : dHam x b ≤ C₁ * r_star) :
    let M := candMFresh a b m z_prev x
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) ∧
    ∀ w ∈ candMWit C₁ r_star a b m z_prev x,
      (∀ uv ∈ candA2 C₁ a b x M w, uv.1 ≠ uv.2) ∧
      40 * ((M.card : ℤ) ^ 2 - 2 * ((candA2 C₁ a b x M w).card : ℤ)) ≤
        23 * (r_star : ℤ) * (M.card : ℤ) := by
  exact ⟨candMWit_card_le C₁ r_star m hC₁ hr a b z_prev x hd_xa hd_xb,
    candMWit_quad C₁ r_star m a b z_prev x⟩
end HighDimSteinerSpanners.Proofs.CSP

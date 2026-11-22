-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.choose_two_le_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:22.066263+00:00
-- url     : https://prove2.me/submissions/d6a99b0c-54e8-46de-8b89-e4a2db25d509

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_twice_choose_two

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N : ℕ} : ∀ s : ℕ, s ≤ N → s.choose 2 ≤ s * (N - 1) := by
  classical
  intro s hs
  rcases Nat.eq_zero_or_pos s with rfl | hs_pos
  · simp
  · have h1 : s.choose 2 ≤ 2 * s.choose 2 := Nat.le_mul_of_pos_left _ (by omega)
    have h2 := twice_choose_two s
    have h3 : s * (s - 1) ≤ s * (N - 1) := Nat.mul_le_mul_left s (by omega)
    omega
end HighDimSteinerSpanners.Proofs.CSP

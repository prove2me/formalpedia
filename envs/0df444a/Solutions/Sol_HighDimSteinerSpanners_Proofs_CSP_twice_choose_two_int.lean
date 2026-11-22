-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.twice_choose_two_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:21.716065+00:00
-- url     : https://prove2.me/submissions/73b7d95f-44bd-4338-82d7-d848761f7abe

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
theorem _root_.solution : ∀ m : ℕ, 2 * (m.choose 2 : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
  classical
  intro m
  cases m with
  | zero => norm_num
  | succ k =>
    have hnat := twice_choose_two (k + 1)
    have hcast : (2 : ℤ) * ((k + 1).choose 2 : ℤ) = ((k + 1 : ℕ) : ℤ) * (k : ℤ) := by
      exact_mod_cast hnat
    push_cast at hcast ⊢
    linarith only [hcast]
end HighDimSteinerSpanners.Proofs.CSP

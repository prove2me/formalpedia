-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.twice_choose_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:34.378574+00:00
-- url     : https://prove2.me/submissions/724ab20a-7131-44b4-90fe-5074354a87ce

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ m : ℕ, 2 * m.choose 2 = m * (m - 1) := by
  classical
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ k =>
      have hc : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have ih' : 2 * (k + 1).choose 2 = (k + 1) * k := ih
      have hsub : k + 2 - 1 = k + 1 := rfl
      rw [hc, hsub]
      linarith only [ih']
end HighDimSteinerSpanners.Proofs.CSP

-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.dyadic_linear_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:22.06781+00:00
-- url     : https://prove2.me/submissions/dbcdf526-1a01-48df-aa76-09c5ae413e92

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
theorem _root_.solution : ∀ m : ℕ, 20 ≤ m → 20000 * (m + 2) ≤ 2 ^ m := by
  classical
  intro m hm
  refine Nat.le_induction ?_ ?_ m hm
  · norm_num
  · intro k hk ih
    calc
      20000 * (k + 1 + 2) ≤ 2 * (20000 * (k + 2)) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by ring
end HighDimSteinerSpanners.Proofs.CSP

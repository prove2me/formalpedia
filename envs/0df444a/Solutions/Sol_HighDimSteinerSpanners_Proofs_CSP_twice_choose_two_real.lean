-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.twice_choose_two_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:58.268052+00:00
-- url     : https://prove2.me/submissions/c7ca91a9-03a3-4283-aa69-f675cdb0dda8

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_twice_choose_two_int

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ m : ℕ, 2 * (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
  classical
  intro m
  exact_mod_cast twice_choose_two_int m
end HighDimSteinerSpanners.Proofs.CSP

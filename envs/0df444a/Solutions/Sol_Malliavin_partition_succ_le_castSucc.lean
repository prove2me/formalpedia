-- Prove2me | solution 1 for Malliavin.partition_succ_le_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:59.513485+00:00
-- url     : https://prove2.me/submissions/6c853472-fcd0-484e-8df4-f52c20f4353f

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}
omit [MeasureSpace Ω]
namespace Malliavin
theorem _root_.solution {n : ℕ} (P : Partition n) {i j : Fin n} (h : i < j) :
    P.t i.succ ≤ P.t j.castSucc := by
  have hval : ((i.succ : Fin (n + 1)) : ℕ) ≤ ((j.castSucc : Fin (n + 1)) : ℕ) :=
    Nat.succ_le_of_lt h
  exact P.mono.monotone (Fin.le_iff_val_le_val.mpr hval)
end Malliavin

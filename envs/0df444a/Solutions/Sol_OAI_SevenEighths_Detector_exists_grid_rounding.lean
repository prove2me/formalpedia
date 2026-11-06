-- Prove2me | solution 1 for OAI.SevenEighths.Detector.exists_grid_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:44.183525+00:00
-- url     : https://prove2.me/submissions/dd8bf6e4-6c56-44cb-9e06-c3b260c0ede1

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Detector
namespace OAI.SevenEighths.Detector
theorem _root_.solution {base x e : ℝ} (he : 0 < e) (hx : base ≤ x) :
    ∃ k : ℕ, base + e * k ≤ x ∧ x < base + e * k + e := by
  let k := ⌊(x - base) / e⌋₊
  have hnonneg : 0 ≤ (x - base) / e := div_nonneg (sub_nonneg.mpr hx) he.le
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((x - base) / e)
  have hlo' := (le_div_iff₀ he).mp hlo
  have hhi' := (div_lt_iff₀ he).mp hhi
  refine ⟨k, ?_, ?_⟩ <;> dsimp [k] <;> nlinarith
end OAI.SevenEighths.Detector

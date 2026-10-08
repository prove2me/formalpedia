-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedFiniteForward_endpoint_scalar_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:39:20.523429+00:00
-- url     : https://prove2.me/submissions/984a1b9b-dbd5-4bce-aab6-2d286828a01a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B015

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_slice_mul_count_le_work
    (A Cslice : ℕ) (constants : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : Cslice + 1 ≤ A) (hx : 0 ≤ x)
    (hcount : (count : ℝ) ≤ x) :
    (preparedFiniteForwardParameter A constants n x + Cslice) ^ Cslice * count ≤
      preparedFiniteForwardWork A constants n x := by
  let b := preparedFiniteForwardParameter A constants n x
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A constants n hx
  have hxb : x ≤ b := le_preparedFiniteForwardParameter A constants n hx
  have hCA : (Cslice : ℝ) ≤ A := Nat.cast_le.mpr (by omega)
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbase : 1 ≤ b + A := by linarith
  have hpow : (b + Cslice) ^ Cslice ≤ (b + A) ^ Cslice :=
    pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg Cslice))
      (add_le_add (le_refl b) hCA) Cslice
  have hcount' : (count : ℝ) ≤ b + A :=
    (hcount.trans hxb).trans (le_add_of_nonneg_right (Nat.cast_nonneg A))
  rw [preparedFiniteForwardWork_eq]
  change (b + Cslice) ^ Cslice * count ≤ (b + A) ^ A
  calc
    _ ≤ (b + A) ^ Cslice * (b + A) :=
      mul_le_mul hpow hcount' (Nat.cast_nonneg count)
        (pow_nonneg (le_trans zero_le_one hbase) Cslice)
    _ = (b + A) ^ (Cslice + 1) := (pow_succ _ _).symm
    _ ≤ (b + A) ^ A := pow_le_pow_right₀ hbase hC

theorem preparedFiniteForward_endpoint_scalar_bounds
    (A Cslice : ℕ) (constants : ℕ → ℕ) (n count : ℕ)
    {x gainLog stageLog : ℝ}
    (hA : 2 ≤ A) (hCslice : 1 ≤ Cslice) (hC : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hgain : 0 ≤ gainLog) (hstage : 0 ≤ stageLog)
    (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A constants n x
    let p := preparedFiniteForwardWork A constants n x
    let u := preparedFiniteForwardModelPrecision A constants n x gainLog stageLog
    let cost := b + 1
    let slice := (b + Cslice) ^ Cslice
    0 ≤ p ∧ 0 ≤ u ∧ 0 ≤ cost ∧ 0 ≤ slice ∧ cost ≤ slice ∧
      slice * count ≤ p ∧ (∀ chartCost : ℝ, chartCost ≤ x → chartCost ≤ slice) ∧
      2 * cost + 6 ≤ u := by
  intro b p u cost slice
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A constants n hx
  have hp : 0 ≤ p := preparedFiniteForwardWork_nonneg A constants n hx
  have hprefix : 0 ≤ preparedFiniteForwardPrefixLog A constants n x :=
    (preparedFiniteForward_prefix_bounds A constants n hx).2.1
  have hueq : u = preparedFiniteForwardPrefixLog A constants n x + gainLog +
      p + stageLog + 6 := rfl
  have hu : 0 ≤ u := by linarith
  have hCsliceReal : (1 : ℝ) ≤ Cslice := by exact_mod_cast hCslice
  have hbase : 1 ≤ b + Cslice := by linarith
  have hcost : 0 ≤ cost := by dsimp [cost]; linarith
  have hslice : 0 ≤ slice := pow_nonneg (le_trans zero_le_one hbase) _
  have hcostSlice : cost ≤ slice := by
    have hpower : b + Cslice ≤ (b + Cslice) ^ Cslice := by
      simpa only [pow_one] using pow_le_pow_right₀ hbase hCslice
    dsimp only [cost, slice]
    linarith
  have hsliceCount : slice * count ≤ p :=
    preparedFiniteForward_slice_mul_count_le_work A Cslice constants n count hA hC hx hcount
  have hchart : ∀ chartCost : ℝ, chartCost ≤ x → chartCost ≤ slice := by
    intro chartCost hchartCost
    have hxb : x ≤ b := le_preparedFiniteForwardParameter A constants n hx
    have hbcost : b ≤ cost := by dsimp [cost]; linarith
    exact hchartCost.trans (hxb.trans (hbcost.trans hcostSlice))
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbaseA : 1 ≤ b + A := by linarith
  have hsquare : (b + 2) ^ 2 ≤ p := by
    rw [show p = (b + A) ^ A from preparedFiniteForwardWork_eq A constants n x]
    exact (pow_le_pow_left₀ (by linarith) (by linarith : b + 2 ≤ b + A) 2).trans
      (pow_le_pow_right₀ hbaseA hA)
  have hcostWork : 2 * cost ≤ p := by
    dsimp only [cost]
    nlinarith [sq_nonneg b]
  refine ⟨hp, hu, hcost, hslice, hcostSlice, hsliceCount, hchart, ?_⟩
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedFiniteForward_endpoint_scalar_bounds := @OAI.Erdos3.VectorPolynomial.preparedFiniteForward_endpoint_scalar_bounds

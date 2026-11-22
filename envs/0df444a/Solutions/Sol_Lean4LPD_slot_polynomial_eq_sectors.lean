-- Prove2me | solution 1 for Lean4LPD.slot_polynomial_eq_sectors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:21.925734+00:00
-- url     : https://prove2.me/submissions/ecd4357e-03dc-4055-9c81-41d64501eb2c

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) {X R : ℝ} (hX : 0 < X) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) =
      X ^ m / (Nat.factorial m : ℝ) *
        ∑ D ∈ range m, ((m - 1).choose D : ℝ) *
          ((Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ)) * (R / X) ^ D := by
  rw [← Finset.sum_range_reflect
    (fun k => X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hD' : D < m := Finset.mem_range.mp hD
  have hk : m - 1 - D + 1 = m - D := by omega
  have hsub : m - (m - D) = D := by omega
  rw [hk, hsub, Nat.choose_symm (by omega)]
  have hp : X ^ m = X ^ (m - D) * X ^ D := by
    rw [← pow_add, Nat.sub_add_cancel hD'.le]
  rw [div_pow, hp]
  field_simp
end Lean4LPD

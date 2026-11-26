-- Prove2me | solution 1 for Kyprianou.Ch04.finiteAffineGridIntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:45:03.238787+00:00
-- url     : https://prove2.me/submissions/8fc19879-41f9-4d0c-b046-7da6f23f167f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_uniformGridDriftIntegralLimitV1
import Theorems.Thm_Kyprianou_Ch04_uniformGridSingleAtomLimitV1
import Theorems.Thm_Kyprianou_Ch04_uniformGridRightClosedCellExistsV1
import Theorems.Thm_Kyprianou_Ch04_finiteJumpGridSumDecompositionV1
open MeasureTheory Filter Set Topology
open scoped NNReal Classical
set_option autoImplicit false

/-- The uniform-grid integral of bounded strict-left weights against a finite affine path. -/
theorem solution (T : NNReal) (S : Finset NNReal) (j H Y : NNReal → ℝ) (b C : ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then j r else 0)
    (hH : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r)))
    (hb : ∀ r, |H r| ≤ C) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      let u := T * (i : NNReal) / (n : NNReal)
      let v := T * ((i+1 : ℕ) : NNReal) / (n : NNReal)
      H u * (Y v - Y u)) atTop
      (𝓝 (b * (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal) +
        ∑ r ∈ S, j r * H r)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  let u (n i : ℕ) := T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
  let A (n : ℕ) := ∑ i ∈ Finset.range (n+1),
    H (u n i) * ((u n (i+1) : ℝ) - (u n i : ℝ))
  let J (r : NNReal) (n : ℕ) := ∑ i ∈ Finset.range (n+1),
    if u n i < r ∧ r ≤ u n (i+1) then H (u n i) else 0
  have hA : Tendsto A atTop (𝓝 (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal)) :=
    Kyprianou.Ch04.uniformGridDriftIntegralLimitV1 T H C hb hH
  have hJ (r : NNReal) (hr : r ∈ S) : Tendsto (J r) atTop (𝓝 (H r)) := by
    choose k hk hc using fun n => Kyprianou.Ch04.uniformGridRightClosedCellExistsV1
      T r (hS r hr).1 (hS r hr).2 n
    exact Kyprianou.Ch04.uniformGridSingleAtomLimitV1 T r H k hk hc (hH r (hS r hr).1)
  have h := (hA.const_mul b).add
    (tendsto_finsetSum S (fun r hr => (hJ r hr).const_mul (j r)))
  have he (n : ℕ) : (∑ i ∈ Finset.range (n+1),
      H (u n i) * (Y (u n (i+1)) - Y (u n i))) =
      b * A n + ∑ r ∈ S, j r * J r n := by
    let V := fun t : ℝ => b*t + ∑ r ∈ S, if (r : ℝ) ≤ t then j r else 0
    have hu (i : ℕ) (hi : i ≤ n+1) : u n i ≤ T := by
      dsimp [u]
      rw [div_le_iff₀ (by positivity)]
      gcongr
    have hm (i : ℕ) : u n i ≤ u n (i+1) := by dsimp [u]; gcongr <;> omega
    have hv (t : NNReal) (ht : t ≤ T) : Y t = V t := by
      rw [hY t ht]
      simp [V,NNReal.coe_le_coe]
    have hEq := Kyprianou.Ch04.finiteJumpGridSumDecompositionV1 S (n+1)
      (fun i => (u n i : ℝ)) (fun i => (u n (i+1) : ℝ))
      (fun i => H (u n i)) (fun r => (r : ℝ)) j b V (fun _ => rfl)
      (fun i _ => by exact_mod_cast hm i)
    have hterm : (∑ i ∈ Finset.range (n+1),
        H (u n i) * (Y (u n (i+1)) - Y (u n i))) =
        ∑ i ∈ Finset.range (n+1), H (u n i) * (V (u n (i+1)) - V (u n i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [hv _ (hu _ (by omega)), hv _ (hu _ (by omega))]
    rw [hterm]
    simpa [A,J,NNReal.coe_lt_coe,NNReal.coe_le_coe] using hEq
  simpa only [← he,u] using h

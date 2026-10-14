-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualMean_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T14:08:41.953745+00:00
-- url     : https://prove2.me/submissions/78e08c9b-184c-4684-b085-20c942420e27

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

namespace OAI

open scoped BigOperators

namespace PiExponent

open Filter Topology

theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

theorem mem_strictWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by
  classical
  simp only [strictWeightedSimplex, Finset.mem_filter, mem_realWeightedSimplex hw,
    and_iff_right_iff_imp]
  exact fun h => h.le

end PiExponent

end OAI

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

theorem row_mem_iff {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (b : Fin (m + 1) → ℕ) :
    b ∈ PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (b 0 : ℝ) + (∑ i, w i * (b i.succ : ℝ)) / θ < H := by
  have hp : ∀ i, 0 < rowWeights v0 θ w i := by
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  rw [PiExponent.mem_strictWeightedSimplex hp, Fin.sum_univ_succ]
  simp only [rowWeights, Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
    Finset.sum_div]

theorem row_weight_lt {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (ρ : Row K v0 θ w H) :
    v0 * (ρ.2.1 0 : ℝ) + (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ < H :=
  (row_mem_iff hv0 hθ hw ρ.2.1).mp ρ.2.2

end PiExponent.InterpolationMatrix

end OAI

namespace OAI

namespace PiExponent

open scoped BigOperators

namespace MatrixArithmetic

theorem actual_row_card_pos {m K : ℕ} {v0 θ H : ℝ} {q : Fin m → ℕ}
    (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    0 < Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨0, hK⟩, ⟨fun _ => 0, ?_⟩⟩⟩
  apply (InterpolationMatrix.row_mem_iff hv0 hθ hw _).mpr
  simpa using hH

theorem ceil_log_weight_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  exact lt_of_lt_of_le (Real.log_pos hqR) (Nat.le_ceil _)

theorem row_weighted_cost_le {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i)
    (ρ : PiExponent.InterpolationMatrix.Row K v0 θ w H) :
    (∑ i, (ρ.2.1 i.succ : ℝ) * w i) ≤ H * θ := by
  have hb := PiExponent.InterpolationMatrix.row_weight_lt hv0 hθ hw ρ
  have h0 : 0 ≤ v0 * (ρ.2.1 0 : ℝ) := mul_nonneg hv0.le (Nat.cast_nonneg _)
  have hh : (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ ≤ H := by linarith
  have hm := (div_le_iff₀ hθ).mp hh
  simpa only [mul_comm] using hm

theorem meanRowWeight_nonneg {m : ℕ} (K : ℕ) (v0 θ : ℝ) (q : Fin m → ℕ)
    {H : ℝ} (hH : 0 ≤ H) : 0 ≤ meanRowWeight K v0 θ q H := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro ρ hρ
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact mul_nonneg (Nat.cast_nonneg _) hH

theorem meanRowWeight_le_theta {m K : ℕ} {v0 θ H : ℝ} (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hH : 0 < H) : meanRowWeight K v0 θ q H ≤ θ := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) := by
    exact_mod_cast actual_row_card_pos hK hv0 hθ hH hw
  apply (div_le_iff₀ (mul_pos hM hH)).mpr
  calc
    rowWeightedSum K v0 θ q H ≤
        ∑ _ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H, H * θ :=
      Finset.sum_le_sum (fun ρ hρ => row_weighted_cost_le hv0 hθ hw ρ)
    _ = θ * ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end MatrixArithmetic

end PiExponent

end OAI

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

theorem finiteDenominators_two_le {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

end PiExponent.DeterminantContradiction

end OAI

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter
open scoped Topology

theorem solution {nu : ℝ} (d : FixedData nu) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : ℝ) := by
  exact ⟨MatrixArithmetic.meanRowWeight_nonneg _ _ _ _ hH.le,
    MatrixArithmetic.meanRowWeight_le_theta (finiteDenominators d)
      (finiteDenominators_two_le d) (Nat.zero_lt_of_lt d.K_pos)
      d.v0_pos d.base.theta_pos hH⟩

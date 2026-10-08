-- Prove2me | solution 1 for Gomory69.Asymptotic.sub_mem_basisCone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:56:34.922822+00:00
-- url     : https://prove2.me/submissions/9f417156-edcc-403a-92b8-0c934c62d617

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram



namespace Gomory69.Asymptotic

open Matrix

theorem euclNorm_smul' {m : ℕ} (s : ℝ) (v : Fin m → ℝ) : euclNorm (s • v) = |s| * euclNorm v := by
  unfold euclNorm
  have : ∑ k, (s • v) k ^ 2 = s ^ 2 * ∑ k, v k ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; simp [mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

theorem euclNorm_pos' {m : ℕ} (v : Fin m → ℝ) (hv : v ≠ 0) : 0 < euclNorm v := by
  unfold euclNorm
  apply Real.sqrt_pos.2
  by_contra h
  apply hv
  have h0 : ∑ k, v k ^ 2 = 0 := le_antisymm (not_lt.1 h) (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  funext k
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (v k))).1 h0 k (Finset.mem_univ k)
  simpa using this

theorem basisCone_closed {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) : IsClosed (basisCone B) := by
  have : basisCone B = ⋂ k, {y : Fin m → ℝ | 0 ≤ ((realMatrix B)⁻¹ *ᵥ y) k} := by
    ext y; simp [basisCone]
  rw [this]
  apply isClosed_iInter
  intro k
  apply isClosed_le continuous_const
  have : Continuous (fun y : Fin m → ℝ => (realMatrix B)⁻¹ *ᵥ y) := by
    exact (Matrix.mulVecLin (realMatrix B)⁻¹).continuous_of_finiteDimensional
  exact (continuous_apply k).comp this

theorem sub_mem_core {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0)
    (d : ℝ) (y v : Fin m → ℝ) (hy : y ∈ deepCone B d) (hv : euclNorm v ≤ d) :
    y - v ∈ basisCone B := by
  by_contra hnot
  have hK := basisCone_closed B
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hnot (by simpa using hy.1)
  have hg : Continuous (fun s : ℝ => y - s • v) := by fun_prop
  let S : Set ℝ := {s | s ∈ Set.Icc (0:ℝ) 1 ∧ y - s • v ∈ basisCone B}
  have hSc : IsClosed S := by
    have : S = Set.Icc (0:ℝ) 1 ∩ (fun s : ℝ => y - s • v) ⁻¹' basisCone B := rfl
    rw [this]; exact isClosed_Icc.inter (hK.preimage hg)
  have hS0 : (0:ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, by simpa using hy.1⟩
  have hSb : BddAbove S := ⟨1, fun s hs => hs.1.2⟩
  have hmem : sSup S ∈ S := hSc.csSup_mem ⟨0, hS0⟩ hSb
  set s0 := sSup S with hs0
  have hs0le : ∀ s ∈ S, s ≤ s0 := fun s hs => le_csSup hSb hs
  have hs1 : s0 < 1 := by
    rcases lt_or_eq_of_le hmem.1.2 with h | h
    · exact h
    · exfalso; apply hnot; have := hmem.2; rw [h] at this; simpa using this
  have hz : y - s0 • v ∈ frontier (basisCone B) := by
    rw [frontier, hK.closure_eq]
    refine ⟨hmem.2, ?_⟩
    intro hint
    have hnhds : basisCone B ∈ nhds (y - s0 • v) := mem_interior_iff_mem_nhds.1 hint
    have := hg.continuousAt (x := s0) |>.preimage_mem_nhds hnhds
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 this
    have hs' : min (s0 + ε / 2) 1 ∈ S := by
      refine ⟨⟨le_min (by linarith [hmem.1.1]) zero_le_one, min_le_right _ _⟩, ?_⟩
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have : s0 < min (s0 + ε / 2) 1 := lt_min (by linarith) hs1
      rw [abs_of_pos (by linarith)]
      linarith [min_le_left (s0 + ε / 2) 1]
    have := hs0le _ hs'
    have : s0 < min (s0 + ε / 2) 1 := lt_min (by linarith) hs1
    linarith
  have hd := hy.2 _ hz
  have : y - (y - s0 • v) = s0 • v := by abel
  rw [this, euclNorm_smul', abs_of_nonneg hmem.1.1] at hd
  have hp := euclNorm_pos' v hv0
  nlinarith

end Gomory69.Asymptotic

open Gomory69.Asymptotic


theorem solution {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0)
    (d : ℝ) (y v : Fin m → ℝ) (hy : y ∈ deepCone B d) (hv : euclNorm v ≤ d) :
    y - v ∈ basisCone B := by
  exact sub_mem_core B hdet d y v hy hv

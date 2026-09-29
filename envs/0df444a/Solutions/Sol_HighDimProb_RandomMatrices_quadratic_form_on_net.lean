-- Prove2me | solution 1 for HighDimProb.RandomMatrices.quadratic_form_on_net
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:00:02.750735+00:00
-- url     : https://prove2.me/submissions/1b7cac7e-267f-4bb7-bf43-33234a55f00c

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm

namespace HighDimProb.RandomMatrices

/-- `⟨A u, v⟩ ≤ ‖A‖ ‖u‖ ‖v‖`. -/
theorem aux_qfn_inner_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (Matrix.toEuclideanLin A u) v ≤ matrixOpNorm A * ‖u‖ * ‖v‖ := by
  have h1 := real_inner_le_norm (Matrix.toEuclideanLin A u) v
  have h2 : ‖Matrix.toEuclideanLin A u‖ ≤ matrixOpNorm A * ‖u‖ := by
    have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)).le_opNorm u
    simpa [matrixOpNorm] using this
  calc inner ℝ (Matrix.toEuclideanLin A u) v ≤ ‖Matrix.toEuclideanLin A u‖ * ‖v‖ := h1
    _ ≤ matrixOpNorm A * ‖u‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

end HighDimProb.RandomMatrices

open HighDimProb.RandomMatrices

theorem solution {m n : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (N : Set (EuclideanSpace ℝ (Fin n)))
    (hN : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) N ε)
    (M : Set (EuclideanSpace ℝ (Fin m)))
    (hM : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) M ε) :
    sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M)
        ≤ matrixOpNorm A ∧
    matrixOpNorm A ≤ (1 / (1 - 2 * ε)) *
        sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M) := by
  set S := sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M) with hS
  -- unit vectors exist
  have exn : ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 :=
    ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  have exm : ∃ y : EuclideanSpace ℝ (Fin m), ‖y‖ = 1 :=
    ⟨EuclideanSpace.single ⟨0, hm⟩ 1, by simp⟩
  have hNn : N.Nonempty := by
    obtain ⟨x, hx⟩ := exn
    obtain ⟨y, hy, -⟩ := hN.2 x (by simpa using hx)
    exact ⟨y, hy⟩
  have hMn : M.Nonempty := by
    obtain ⟨x, hx⟩ := exm
    obtain ⟨y, hy, -⟩ := hM.2 x (by simpa using hx)
    exact ⟨y, hy⟩
  have hne : (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M).Nonempty :=
    hNn.image2 hMn
  have hub : ∀ z ∈ Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M,
      z ≤ matrixOpNorm A := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hx1 : ‖x‖ = 1 := by simpa using hN.1 hx
    have hy1 : ‖y‖ = 1 := by simpa using hM.1 hy
    have := aux_qfn_inner_le A x y
    rw [hx1, hy1] at this
    simpa using this
  have hbdd : BddAbove (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M) :=
    ⟨matrixOpNorm A, hub⟩
  refine ⟨csSup_le hne hub, ?_⟩
  -- key estimate
  have key : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → ∀ y : EuclideanSpace ℝ (Fin m),
      ‖y‖ = 1 → inner ℝ (Matrix.toEuclideanLin A x) y ≤ S + 2 * ε * matrixOpNorm A := by
    intro x hx y hy
    obtain ⟨x0, hx0, hdx⟩ := hN.2 x (by simpa using hx)
    obtain ⟨y0, hy0, hdy⟩ := hM.2 y (by simpa using hy)
    have hx0n : ‖x0‖ = 1 := by simpa using hN.1 hx0
    rw [dist_eq_norm] at hdx hdy
    have hdecomp : inner ℝ (Matrix.toEuclideanLin A x) y =
        inner ℝ (Matrix.toEuclideanLin A (x - x0)) y +
        inner ℝ (Matrix.toEuclideanLin A x0) (y - y0) +
        inner ℝ (Matrix.toEuclideanLin A x0) y0 := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 := aux_qfn_inner_le A (x - x0) y
    have h2 := aux_qfn_inner_le A x0 (y - y0)
    have h3 : inner ℝ (Matrix.toEuclideanLin A x0) y0 ≤ S :=
      le_csSup hbdd ⟨x0, hx0, y0, hy0, rfl⟩
    rw [hy] at h1
    rw [hx0n] at h2
    have hA : 0 ≤ matrixOpNorm A := norm_nonneg _
    have e1 : matrixOpNorm A * ‖x - x0‖ * 1 ≤ matrixOpNorm A * ε * 1 := by
      gcongr
    have e2 : matrixOpNorm A * 1 * ‖y - y0‖ ≤ matrixOpNorm A * 1 * ε := by
      gcongr
    rw [hdecomp]
    nlinarith
  have key2 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      ‖Matrix.toEuclideanLin A x‖ ≤ S + 2 * ε * matrixOpNorm A := by
    intro x hx
    by_cases h0 : Matrix.toEuclideanLin A x = 0
    · obtain ⟨y, hy⟩ := exm
      have := key x hx y hy
      rw [h0, inner_zero_left] at this
      rw [h0, norm_zero]
      exact this
    · have hpos : 0 < ‖Matrix.toEuclideanLin A x‖ := norm_pos_iff.mpr h0
      have hy : ‖(‖Matrix.toEuclideanLin A x‖⁻¹) • Matrix.toEuclideanLin A x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      have := key x hx _ hy
      rw [inner_smul_right, real_inner_self_eq_norm_sq] at this
      have e : ‖Matrix.toEuclideanLin A x‖⁻¹ * ‖Matrix.toEuclideanLin A x‖ ^ 2 =
          ‖Matrix.toEuclideanLin A x‖ := by
        field_simp
      rw [e] at this
      exact this
  have hC : 0 ≤ S + 2 * ε * matrixOpNorm A := by
    obtain ⟨x, hx⟩ := exn
    exact le_trans (norm_nonneg _) (key2 x hx)
  have hle : matrixOpNorm A ≤ S + 2 * ε * matrixOpNorm A := by
    unfold matrixOpNorm
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
    intro x hx
    simpa using key2 x hx
  have hpos : 0 < 1 - 2 * ε := by linarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  nlinarith

-- Prove2me | solution 1 for ModernConvex.PathFollowing.close_duality_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:31:09.811881+00:00
-- url     : https://prove2.me/submissions/93f49d8b-245d-4762-b10a-f0243b569739

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder
open ModernConvex.PathFollowing
theorem g69a2_sqrt_facts {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ) (hX : X.PosDef) :
    CFC.sqrt X * CFC.sqrt X = X ∧ (CFC.sqrt X)ᵀ = CFC.sqrt X ∧
      CFC.sqrt X * X⁻¹ * CFC.sqrt X = 1 := by
  have h0 : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ X := hX.posSemidef.nonneg
  have h1 : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X h0
  have hR : (CFC.sqrt X).PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  have h2 : (CFC.sqrt X)ᵀ = CFC.sqrt X := by
    have := hR.1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨h1, h2, ?_⟩
  set R := CFC.sqrt X
  have hdet : R.det ≠ 0 := by
    intro h
    have := hX.det_pos
    rw [← h1, det_mul, h, zero_mul] at this
    exact lt_irrefl _ this
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hXi : X⁻¹ = R⁻¹ * R⁻¹ := by rw [← h1, Matrix.mul_inv_rev]
  rw [hXi, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hu]

theorem g69a2_frob_sq {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : Mᵀ = M) :
    frobNorm M ^ 2 = (M * M).trace := by
  unfold frobNorm
  refine (Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).trans ?_
  conv_rhs => rw [show M * M = M * Mᵀ by rw [hM]]
  simp [trace, mul_apply, sq]

theorem g69a2_dist_sq {k : ℕ} (t : ℝ) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : X.PosDef) (hS : S.IsHermitian) :
    (X * (t • S - X⁻¹) * X * (t • S - X⁻¹)).trace = centralPathDist t X S ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := g69a2_sqrt_facts X hX
  set R := CFC.sqrt X
  set A := t • S - X⁻¹ with hA
  have hAT : Aᵀ = A := by
    have hS' : Sᵀ = S := by
      have := hS; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    have hXi : (X⁻¹)ᵀ = X⁻¹ := by
      rw [transpose_nonsing_inv]
      have := hX.1; rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
      rw [this]
    rw [hA, transpose_sub, transpose_smul, hS', hXi]
  have hM : t • (R * S * R) - 1 = R * A * R := by
    rw [hA, Matrix.mul_sub, Matrix.sub_mul, ← h3, Matrix.mul_smul, Matrix.smul_mul]
  have hMT : (R * A * R)ᵀ = R * A * R := by
    rw [transpose_mul, transpose_mul, h2, hAT, Matrix.mul_assoc]
  rw [show centralPathDist t X S = frobNorm (R * A * R) by unfold centralPathDist; rw [hM]]
  rw [g69a2_frob_sq _ hMT]
  symm
  calc (R * A * R * (R * A * R)).trace = (R * (A * (R * R) * A * R)).trace := by
        simp only [Matrix.mul_assoc]
    _ = ((A * (R * R) * A * R) * R).trace := trace_mul_comm _ _
    _ = ((A * X * A) * X).trace := by
        rw [Matrix.mul_assoc (A * (R * R) * A) R R, h1]
    _ = (X * (A * X * A)).trace := trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem g69a2_trace_le_of_frob {k : ℕ} (hk : 0 < k) (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : frobNorm M ≤ 1) : M.trace ≤ k := by
  have hnn : 0 ≤ ∑ i, ∑ j, M i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hS : ∑ i, ∑ j, M i j ^ 2 ≤ 1 := by
    have h := Real.sq_sqrt hnn
    unfold frobNorm at hM
    have h0 := Real.sqrt_nonneg (∑ i, ∑ j, M i j ^ 2)
    nlinarith
  have hd : ∑ i, M i i ^ 2 ≤ ∑ i, ∑ j, M i j ^ 2 :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => M i j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin k => (1:ℝ)) (fun i => M i i)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  have htr : M.trace = ∑ i, M i i := rfl
  rw [htr]
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have : (∑ i, M i i) ^ 2 ≤ (k:ℝ) := by nlinarith
  nlinarith


/-- Ben-Tal–Nemirovski, Proposition 6.4.2, pp. 395–396, in the SDP case `K = Sᵏ₊` (verified on
p. 396, `θ(K) = k`): if `(X, S)` is a pair of strictly feasible solutions of `(P)`, `(D)` and
`t > 0` with `dist((X, S), Z∗(t)) = ‖tX^{1/2}SX^{1/2} − I‖₂ ≤ 1` (Close), then
`DualityGap(X, S) = Tr(XS) ≤ 2k/t` (6.4.12). -/
theorem solution {k : ℕ} (hk : 0 < k) (P : SDPPair k) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : P.StrictlyPrimalFeasible X) (hS : P.StrictlyDualFeasible S) (t : ℝ) (ht : 0 < t)
    (hclose : centralPathDist t X S ≤ 1) :
    P.dualityGap X S = (X * S).trace ∧ (X * S).trace ≤ 2 * (k : ℝ) / t := by
  constructor
  · have h0 := hS.1.2 _ hX.1
    unfold SDPPair.dualityGap
    simp only [Matrix.add_mul, Matrix.mul_sub, trace_add, trace_sub] at h0
    rw [trace_mul_comm P.C X, trace_mul_comm P.C P.B]
    linarith
  · obtain ⟨h1, h2, h3⟩ := g69a2_sqrt_facts X hX.2
    have hN := g69a2_trace_le_of_frob hk _ hclose
    rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at hN
    have e : (CFC.sqrt X * S * CFC.sqrt X).trace = (X * S).trace := by
      rw [trace_mul_comm, ← Matrix.mul_assoc, h1]
    rw [e] at hN
    rw [le_div_iff₀ ht]
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith


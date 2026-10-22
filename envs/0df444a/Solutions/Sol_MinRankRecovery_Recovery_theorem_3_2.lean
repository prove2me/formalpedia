-- Prove2me | solution 1 for MinRankRecovery.Recovery.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:42:17.46825+00:00
-- url     : https://prove2.me/submissions/c3f5b41a-623b-4f03-aa82-faaf4510acee

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst
set_option autoImplicit false
open HighDimStat.MatrixRank MinRankRecovery.Recovery Matrix

lemma mrr_upper_bound {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Matrix (Fin m) (Fin n) ℝ, measNorm Xs X ≤ C * frobeniusNorm X := by
  refine ⟨Real.sqrt (∑ i, ∑ a, ∑ b, (Xs i a b) ^ 2), Real.sqrt_nonneg _, fun X => ?_⟩
  unfold measNorm frobeniusNorm
  rw [← Real.sqrt_mul (show (0 : ℝ) ≤ ∑ i, ∑ a, ∑ b, (Xs i a b) ^ 2 from
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => sq_nonneg _))))]
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  unfold observationOp traceInner
  -- Cauchy–Schwarz over the pair index
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun ab => Xs i ab.1 ab.2) (fun ab => X ab.1 ab.2)
  simp only [Fintype.sum_prod_type] at this
  simpa [sq] using this

lemma mrr_rank_sub {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℝ) : (X - Y).rank ≤ X.rank + Y.rank := by
  unfold Matrix.rank
  have : LinearMap.range (X - Y).mulVecLin ≤
      LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine Submodule.mem_sup.2 ⟨X.mulVecLin v, ⟨v, rfl⟩, -(Y.mulVecLin v), ⟨-v, ?_⟩, ?_⟩
    · simp [Matrix.mulVec_neg]
    · simp [Matrix.sub_mulVec]; abel
  calc _ ≤ Module.finrank ℝ ↥(LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin) :=
        Submodule.finrank_mono this
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

theorem solution {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hδ : ripConst Xs (2 * r) < 1) (X0 : Matrix (Fin m) (Fin n) ℝ) (hX0 : X0.rank ≤ r) :
    ∀ X : Matrix (Fin m) (Fin n) ℝ, X.rank ≤ r →
      observationOp Xs X = observationOp Xs X0 → X = X0 := by
  intro X hX hobs
  obtain ⟨C, hC0, hC⟩ := mrr_upper_bound Xs
  set S : Set ℝ := {δ : ℝ | 0 ≤ δ ∧ ∀ X : Matrix (Fin m) (Fin n) ℝ, X.rank ≤ 2 * r →
    (1 - δ) * frobeniusNorm X ≤ measNorm Xs X ∧ measNorm Xs X ≤ (1 + δ) * frobeniusNorm X} with hS
  have hfrob0 : ∀ Y : Matrix (Fin m) (Fin n) ℝ, 0 ≤ frobeniusNorm Y := fun Y => Real.sqrt_nonneg _
  have hmeas0 : ∀ Y : Matrix (Fin m) (Fin n) ℝ, 0 ≤ measNorm Xs Y := fun Y => Real.sqrt_nonneg _
  have hne : S.Nonempty := by
    refine ⟨max 1 C, le_trans zero_le_one (le_max_left _ _), fun Y _ => ⟨?_, ?_⟩⟩
    · have : (1 - max 1 C) ≤ 0 := by linarith [le_max_left 1 C]
      nlinarith [hfrob0 Y, hmeas0 Y]
    · have h1 := hC Y
      have h2 : C ≤ 1 + max 1 C := by linarith [le_max_right 1 C, le_max_left 1 C]
      nlinarith [hfrob0 Y]
  obtain ⟨δ, hδS, hδlt⟩ := exists_lt_of_csInf_lt hne hδ
  set Z := X - X0 with hZ
  have hrank : Z.rank ≤ 2 * r := by
    rw [hZ]
    have := mrr_rank_sub X X0
    omega
  have hZobs : ∀ i, observationOp Xs Z i = 0 := by
    intro i
    have := congrFun hobs i
    unfold observationOp traceInner at this ⊢
    simp only [hZ, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
    linarith
  have hmeasZ : measNorm Xs Z = 0 := by
    unfold measNorm
    simp [hZobs]
  have h1 := (hδS.2 Z hrank).1
  rw [hmeasZ] at h1
  have hpos : 0 < 1 - δ := by linarith
  have hfZ : frobeniusNorm Z = 0 := by
    have := hfrob0 Z
    nlinarith
  unfold frobeniusNorm at hfZ
  rw [Real.sqrt_eq_zero'] at hfZ
  have hfZ : ∑ i, ∑ j, Z i j ^ 2 = 0 :=
    le_antisymm hfZ (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have hall : ∀ i j, Z i j = 0 := by
    intro i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (Z i j)))).1 hfZ i (Finset.mem_univ i)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (Z i j))).1 h2 j (Finset.mem_univ j)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h3
  ext i j
  have := hall i j
  simp only [hZ, Matrix.sub_apply] at this
  linarith

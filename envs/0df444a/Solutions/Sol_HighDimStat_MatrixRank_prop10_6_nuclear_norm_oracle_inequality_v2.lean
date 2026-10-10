-- Prove2me | solution 1 for HighDimStat.MatrixRank.prop10_6_nuclear_norm_oracle_inequality_v2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-09T22:58:26.507788+00:00
-- url     : https://prove2.me/submissions/daa8717d-f0ed-45b2-893b-4f75d5ca6419

/-
SPDX-License-Identifier: Apache-2.0
Complete proof of the corrected nuclear-norm oracle inequality, with constants
72, 16 and 256 and the exact canonical rank condition. All custom proof bodies
are included below. Spectral and polar arguments are reconstructed from Mathlib.
See the accompanying reconstruction scope for conceptual attribution.
-/
import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

/- Complete module: NuclearOracleScalar -/
section

namespace HighDimStat.MatrixRank

lemma nuclear_oracle_scalar_finish
    (κ lam tau T tail B C N curvature psi r : ℝ)
    (hκ : 0 < κ) (hlam : 0 < lam) (htau : 0 ≤ tau)
    (htail : 0 ≤ tail) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hcurv : 0 ≤ curvature)
    (hpsi : psi ^ 2 = 2 * r) (hcompat : B ≤ psi * T)
    (hnuc : N ≤ B + C)
    (hlower : κ / 2 * T ^ 2 - tau * N ^ 2 ≤ curvature)
    (hupper : curvature ≤ 3 * lam / 2 * B - lam / 2 * C + 2 * lam * tail)
    (hbudget : 64 * tau * r ≤ κ / 4) :
    T ^ 2 ≤ 72 * (lam ^ 2 / κ ^ 2) * r +
      1 / κ * (16 * lam * tail + 256 * tau * tail ^ 2) := by
  have hcone : C ≤ 3 * B + 4 * tail := by nlinarith
  have hnorm : N ≤ 4 * B + 4 * tail := by linarith
  have hsquare : N ^ 2 ≤ 32 * B ^ 2 + 32 * tail ^ 2 := by
    nlinarith [sq_nonneg (B - tail)]
  have hpsiT : 0 ≤ psi * T := le_trans hB hcompat
  have hBsq : B ^ 2 ≤ 2 * r * T ^ 2 := by
    nlinarith [mul_self_le_mul_self hB hcompat]
  have htol : tau * N ^ 2 ≤ κ / 4 * T ^ 2 + 32 * tau * tail ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hsquare htau
    have hb := mul_le_mul_of_nonneg_left hBsq (show 0 ≤ 32 * tau by positivity)
    have hc := mul_le_mul_of_nonneg_right hbudget (sq_nonneg T)
    nlinarith
  have hmain : κ / 4 * T ^ 2 ≤ 3 * lam / 2 * B + 2 * lam * tail +
      32 * tau * tail ^ 2 := by nlinarith
  have hlin := mul_le_mul_of_nonneg_left hcompat
    (show 0 ≤ 3 * κ * lam / 2 by positivity)
  have hyoung : κ * (3 * lam / 2 * B) ≤ κ ^ 2 / 8 * T ^ 2 + 9 * lam ^ 2 * r := by
    nlinarith [sq_nonneg (κ * T - 6 * lam * psi)]
  have hm := mul_le_mul_of_nonneg_left hmain hκ.le
  have hfinal : κ ^ 2 * T ^ 2 ≤ 72 * lam ^ 2 * r +
      κ * (16 * lam * tail + 256 * tau * tail ^ 2) := by nlinarith
  have hrhs : (72 * (lam ^ 2 / κ ^ 2) * r +
      1 / κ * (16 * lam * tail + 256 * tau * tail ^ 2)) * κ ^ 2 =
      72 * lam ^ 2 * r + κ * (16 * lam * tail + 256 * tau * tail ^ 2) := by
    field_simp
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hκ)).mp
  rw [hrhs]
  nlinarith

end HighDimStat.MatrixRank

end

/- Complete module: NuclearLeastSquaresCore -/
section

namespace HighDimStat.MatrixRank

lemma nuclearNorm_nonneg {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    0 ≤ nuclearNorm A := by
  unfold nuclearNorm singularValues
  exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

lemma tailSingularSum_nonneg {d1 d2 : ℕ}
    (A : Matrix (Fin d1) (Fin d2) ℝ) (r : ℕ) : 0 ≤ tailSingularSum A r := by
  unfold tailSingularSum singularValues
  exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

lemma traceInner_sub_right {d1 d2 : ℕ} (A B C : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A (B - C) = traceInner A B - traceInner A C := by
  simp [traceInner, mul_sub, Finset.sum_sub_distrib]

lemma least_squares_basic_inequality {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (S H : Matrix (Fin d1) (Fin d2) ℝ) (lam : ℝ)
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) S + w i) lam H) :
    (∑ i, (observationOp Xs (H - S) i) ^ 2) / (2 * (n : ℝ)) ≤
      (1 / (n : ℝ)) * (∑ i, w i * observationOp Xs (H - S) i) +
        lam * (nuclearNorm S - nuclearNorm H) := by
  have hobs (i : Fin n) : observationOp Xs (H - S) i =
      traceInner (Xs i) H - traceInner (Xs i) S := traceInner_sub_right _ _ _
  have hexpand : (∑ i, (traceInner (Xs i) S + w i - observationOp Xs H i) ^ 2) =
      (∑ i, (w i) ^ 2) + (∑ i, (observationOp Xs (H - S) i) ^ 2) -
        2 * (∑ i, w i * observationOp Xs (H - S) i) := by
    calc
      _ = ∑ i, ((w i) ^ 2 + (observationOp Xs (H - S) i) ^ 2 -
          2 * (w i * observationOp Xs (H - S) i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hobs]
        unfold observationOp
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hs := hsol S
  simp only [observationOp, add_sub_cancel_left] at hs
  change (1 / (2 * (n : ℝ))) *
      (∑ i, (traceInner (Xs i) S + w i - observationOp Xs H i) ^ 2) +
      lam * nuclearNorm H ≤ (1 / (2 * (n : ℝ))) * (∑ i, (w i) ^ 2) +
      lam * nuclearNorm S at hs
  rw [hexpand] at hs
  have hc : (1 / (2 * (n : ℝ))) * 2 = 1 / (n : ℝ) := by
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · field_simp
  rw [← hc]
  rw [div_eq_mul_inv]
  simp only [one_div] at hs ⊢
  nlinarith

lemma zero_samples_oracle_bound {d1 d2 : ℕ}
    (Xs : Fin 0 → Matrix (Fin d1) (Fin d2) ℝ)
    (S H : Matrix (Fin d1) (Fin d2) ℝ) (κ c0 lam : ℝ) (r : ℕ)
    (hκ : 0 < κ) (hlam : 0 ≤ lam) (hRSC : RSCNuclear Xs κ c0) :
    (frobeniusNorm (H - S)) ^ 2 ≤ 72 * (lam ^ 2 / κ ^ 2) * r +
      1 / κ * (16 * lam * tailSingularSum S r +
        256 * c0 * ((d1 : ℝ) + d2) / (0 : ℝ) * (tailSingularSum S r) ^ 2) := by
  have hh := hRSC (H - S)
  simp only [Nat.cast_zero, mul_zero, div_zero, zero_mul, sub_zero] at hh
  have hz : (frobeniusNorm (H - S)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (frobeniusNorm (H - S))]
  rw [hz]
  simp only [div_zero, zero_mul, add_zero]
  have ht := tailSingularSum_nonneg S r
  positivity

end HighDimStat.MatrixRank

end

/- Complete module: MatrixNormBounds -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

def vecNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

lemma vecNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ vecNorm v := Real.sqrt_nonneg _

lemma vecNorm_sq {n : ℕ} (v : Fin n → ℝ) : vecNorm v ^ 2 = ∑ j, v j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma vecNorm_div {n : ℕ} (v : Fin n → ℝ) (c : ℝ) :
    vecNorm (fun j => v j / c) = vecNorm v / |c| := by
  simp only [vecNorm, div_pow, ← Finset.sum_div]
  rw [Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    Real.sqrt_sq_eq_abs]

lemma unit_mulVec_norm_le_frobenius {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : ∑ j, v j ^ 2 = 1) :
    vecNorm (A.mulVec v) ≤ frobeniusNorm A := by
  apply Real.sqrt_le_sqrt
  calc
    ∑ i, (A.mulVec v i) ^ 2 ≤
        ∑ i, (∑ j, A i j ^ 2) * (∑ j, v j ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) v
    _ = ∑ i, ∑ j, A i j ^ 2 := by simp [hv]

lemma native_opNorm_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    BddAbove (Set.range (fun v : {v : Fin n → ℝ // ∑ j, v j ^ 2 = 1} =>
      vecNorm (A.mulVec v.1))) := by
  refine ⟨frobeniusNorm A, ?_⟩
  rintro _ ⟨v,rfl⟩
  exact unit_mulVec_norm_le_frobenius A v v.property

lemma unit_mulVec_norm_le_opNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : ∑ j, v j ^ 2 = 1) :
    vecNorm (A.mulVec v) ≤ opNorm A :=
  le_ciSup (native_opNorm_bdd A) ⟨v,hv⟩

lemma native_opNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ opNorm A := by
  classical
  let V := {v : Fin n → ℝ // ∑ j, v j ^ 2 = 1}
  by_cases hv : Nonempty V
  · obtain ⟨v⟩ := hv
    exact (vecNorm_nonneg _).trans (unit_mulVec_norm_le_opNorm A v v.property)
  · have : IsEmpty V := not_nonempty_iff.mp hv
    change 0 ≤ ⨆ v : V, vecNorm (A.mulVec v.1)
    simp

lemma mulVec_norm_le_opNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) : vecNorm (A.mulVec v) ≤ opNorm A * vecNorm v := by
  classical
  by_cases hz : vecNorm v = 0
  · have hs : ∑ j, v j ^ 2 = 0 := by rw [← vecNorm_sq, hz]; norm_num
    have hv : ∀ j, v j = 0 := by
      intro j
      have hj : v j ^ 2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sq_nonneg (v k))).mp hs j (Finset.mem_univ j)
      exact sq_eq_zero_iff.mp hj
    simp [vecNorm, Matrix.mulVec, dotProduct, hv]
  · have hp : 0 < vecNorm v := lt_of_le_of_ne (vecNorm_nonneg v) (Ne.symm hz)
    let w : Fin n → ℝ := fun j => v j / vecNorm v
    have hw : ∑ j, w j ^ 2 = 1 := by
      simp only [w, div_pow, ← Finset.sum_div, ← vecNorm_sq]
      exact div_self (pow_ne_zero 2 hz)
    have he : A.mulVec w = fun i => A.mulVec v i / vecNorm v := by
      funext i
      simp [w, Matrix.mulVec, dotProduct, mul_div_assoc, Finset.sum_div]
    have hb := unit_mulVec_norm_le_opNorm A w hw
    rw [he, vecNorm_div, abs_of_pos hp] at hb
    exact (div_le_iff₀ hp).mp hb

lemma native_opNorm_le_of_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ v, vecNorm (A.mulVec v) ≤ C * vecNorm v) :
    opNorm A ≤ C := by
  classical
  let V := {v : Fin n → ℝ // ∑ j, v j ^ 2 = 1}
  by_cases hv : Nonempty V
  · let := hv
    apply ciSup_le
    intro v
    have hh := hb v.1
    simpa only [vecNorm, v.property, Real.sqrt_one, mul_one] using hh
  · have : IsEmpty V := not_nonempty_iff.mp hv
    change (⨆ v : V, vecNorm (A.mulVec v.1)) ≤ C
    simpa using hC

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: MatrixSpectral -/
section

noncomputable section
open Matrix

namespace HighDimStat.MatrixRank.Proof

variable {m n : ℕ}

def gramEigenvalues (A : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ :=
  (Matrix.posSemidef_conjTranspose_mul_self A).1.eigenvalues

lemma gramEigenvalues_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    0 ≤ gramEigenvalues A j :=
  (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg j

lemma nuclearNorm_eq_sum_sqrt (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A = ∑ j, Real.sqrt (gramEigenvalues A j) := by
  let h := (Matrix.posSemidef_conjTranspose_mul_self A).1
  let f : Fin (Fintype.card (Fin n)) → ℝ := fun j => Real.sqrt (h.eigenvalues₀ j)
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  exact ((finCongr (Fintype.card_fin n)).symm.sum_comp f).trans
    (e.symm.sum_comp f).symm

lemma spectral_data (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      Aᵀ * A = U * Matrix.diagonal (gramEigenvalues A) * Uᵀ := by
  let h := (Matrix.posSemidef_conjTranspose_mul_self A).1
  refine ⟨h.eigenvectorUnitary, ?_, ?_, ?_⟩
  · simpa [Unitary.coe_star, Matrix.star_eq_conjTranspose]
      using Unitary.coe_star_mul_self h.eigenvectorUnitary
  · simpa [Unitary.coe_star, Matrix.star_eq_conjTranspose]
      using Unitary.coe_mul_star_self h.eigenvectorUnitary
  · simpa [Unitary.conjStarAlgAut_apply, gramEigenvalues, h, Matrix.star_eq_conjTranspose]
      using h.spectral_theorem

end HighDimStat.MatrixRank.Proof


end
end

/- Complete module: OrderedSingularBasis -/
section

noncomputable section
open Matrix

namespace HighDimStat.MatrixRank.Proof

lemma ordered_singular_basis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      (A * U)ᵀ * (A * U) =
        Matrix.diagonal (fun j => singularValues A j ^ 2) := by
  classical
  obtain ⟨V, hV, hV', hspec⟩ := spectral_data A
  let e₀ : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let e : Fin n ≃ Fin n := (finCongr (Fintype.card_fin n)).symm.trans e₀
  have he (j : Fin n) : gramEigenvalues A (e j) = singularValues A j ^ 2 := by
    have hn := gramEigenvalues_nonneg A (e j)
    simp only [gramEigenvalues, Matrix.IsHermitian.eigenvalues, e,
      Equiv.trans_apply] at hn ⊢
    simpa [singularValues, e₀] using (Real.sq_sqrt hn).symm
  have hgram : (A * V)ᵀ * (A * V) = Matrix.diagonal (gramEigenvalues A) := by
    calc
      (A * V)ᵀ * (A * V) = Vᵀ * (Aᵀ * A) * V := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Vᵀ * (V * Matrix.diagonal (gramEigenvalues A) * Vᵀ) * V := by rw [hspec]
      _ = Matrix.diagonal (gramEigenvalues A) := by
        simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]
        rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  refine ⟨V.submatrix id e, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_submatrix]
    change Vᵀ.submatrix e (Equiv.refl _) * V.submatrix (Equiv.refl _) e = 1
    rw [Matrix.submatrix_mul_equiv, hV, Matrix.submatrix_one_equiv]
  · rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hV']
    rfl
  · have hav : A * V.submatrix id e = (A * V).submatrix id e := by
      exact Matrix.submatrix_mul_equiv A V id (Equiv.refl _) e
    rw [hav, Matrix.transpose_submatrix]
    change (A * V)ᵀ.submatrix e (Equiv.refl _) *
      (A * V).submatrix (Equiv.refl _) e = _
    rw [Matrix.submatrix_mul_equiv, hgram, Matrix.submatrix_diagonal_equiv]
    congr 1
    exact funext he

end HighDimStat.MatrixRank.Proof


end
end

/- Complete module: MatrixTraceDuality -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma traceInner_eq_trace {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A B = Matrix.trace (Aᵀ * B) := by
  simp only [traceInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

lemma traceInner_mul_orthogonal {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) :
    traceInner (A * U) (B * U) = traceInner A B := by
  rw [traceInner_eq_trace, traceInner_eq_trace, Matrix.transpose_mul]
  calc
    Matrix.trace (Uᵀ * Aᵀ * (B * U)) = Matrix.trace (Uᵀ * (Aᵀ * B) * U) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (U * Uᵀ * (Aᵀ * B)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Aᵀ * B) := by rw [hU, Matrix.one_mul]

lemma orthogonal_column_sq {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (j : Fin n) : ∑ i, U i j ^ 2 = 1 := by
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j j) hU
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, ← sq] using hh

lemma singularValues_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    0 ≤ singularValues A j := Real.sqrt_nonneg _

lemma singular_basis_column_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ)
    (hg : (A * U)ᵀ * (A * U) = Matrix.diagonal (fun j => singularValues A j ^ 2))
    (j : Fin n) : vecNorm (fun i => (A * U) i j) = singularValues A j := by
  have hh : (∑ i, (A * U) i j * (A * U) i j) = singularValues A j ^ 2 := by
    change ((A * U)ᵀ * (A * U)) j j = _
    rw [hg, Matrix.diagonal_apply_eq]
  simp only [← sq] at hh
  change Real.sqrt (∑ i, (A * U) i j ^ 2) = _
  rw [hh, Real.sqrt_sq (singularValues_nonneg A j)]

lemma traceInner_le_opNorm_mul_nuclearNorm {m n : ℕ}
    (B A : Matrix (Fin m) (Fin n) ℝ) : traceInner B A ≤ opNorm B * nuclearNorm A := by
  obtain ⟨U,hU,hU',hg⟩ := ordered_singular_basis A
  have hcol (j : Fin n) : (∑ i, (B * U) i j * (A * U) i j) ≤
      opNorm B * singularValues A j := by
    have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => (B * U) i j) (fun i => (A * U) i j)
    change (∑ i, (B * U) i j * (A * U) i j) ≤
      vecNorm (fun i => (B * U) i j) * vecNorm (fun i => (A * U) i j) at hc
    rw [singular_basis_column_norm A U hg j] at hc
    have hb : vecNorm (fun i => (B * U) i j) ≤ opNorm B :=
      unit_mulVec_norm_le_opNorm B (fun i => U i j) (orthogonal_column_sq U hU j)
    exact hc.trans (mul_le_mul_of_nonneg_right hb (singularValues_nonneg A j))
  calc
    traceInner B A = traceInner (B * U) (A * U) := (traceInner_mul_orthogonal B A U hU').symm
    _ = ∑ j, ∑ i, (B * U) i j * (A * U) i j := Finset.sum_comm
    _ ≤ ∑ j, opNorm B * singularValues A j := Finset.sum_le_sum (fun j _ => hcol j)
    _ = opNorm B * nuclearNorm A := (Finset.mul_sum _ _ _).symm

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: NuclearNoiseBound -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma traceInner_smul_left {m n : ℕ} (c : ℝ)
    (A B : Matrix (Fin m) (Fin n) ℝ) : traceInner (c • A) B = c * traceInner A B := by
  simp only [traceInner, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma traceInner_sum_left {m n : ℕ} {ι : Type*}
    (s : Finset ι) (A : ι → Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner (∑ i ∈ s, A i) B = ∑ i ∈ s, traceInner (A i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceInner]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simp only [traceInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib] at ih ⊢
      rw [ih]

lemma observation_noise_trace {m d n : ℕ}
    (Xs : Fin n → Matrix (Fin m) (Fin d) ℝ) (w : Fin n → ℝ)
    (D : Matrix (Fin m) (Fin d) ℝ) :
    traceInner ((1 / (n : ℝ)) • observationOpAdjoint Xs w) D =
      (1 / (n : ℝ)) * (∑ i, w i * observationOp Xs D i) := by
  rw [traceInner_smul_left]
  unfold observationOpAdjoint
  rw [traceInner_sum_left]
  simp only [traceInner_smul_left, observationOp]

lemma noise_bound_on_good_event {m d n : ℕ}
    (Xs : Fin n → Matrix (Fin m) (Fin d) ℝ) (w : Fin n → ℝ)
    (D : Matrix (Fin m) (Fin d) ℝ) (lam : ℝ)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lam / 2) :
    (1 / (n : ℝ)) * (∑ i, w i * observationOp Xs D i) ≤ lam / 2 * nuclearNorm D := by
  rw [← observation_noise_trace]
  exact (traceInner_le_opNorm_mul_nuclearNorm _ D).trans
    (mul_le_mul_of_nonneg_right hG (nuclearNorm_nonneg D))

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: NuclearSpectralFormula -/
section

noncomputable section
open Matrix

namespace HighDimStat.MatrixRank.Proof

lemma nuclearNorm_of_gram_diagonalization {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hU : Uᵀ * U = 1)
    (hgram : Aᵀ * A = U * Matrix.diagonal v * Uᵀ) :
    nuclearNorm A = ∑ j, Real.sqrt (v j) := by
  have hc : (Aᵀ * A).charpoly = (Matrix.diagonal v).charpoly := by
    rw [hgram, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hd : (Matrix.diagonal v).charpoly.roots = Multiset.map v Finset.univ.val := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have he := (Matrix.posSemidef_conjTranspose_mul_self A).1.roots_charpoly_eq_eigenvalues
  have ht : Multiset.map (gramEigenvalues A) Finset.univ.val =
      Multiset.map v Finset.univ.val := by
    have he' : (Aᵀ * A).charpoly.roots = Multiset.map (gramEigenvalues A) Finset.univ.val := by
      simpa only [gramEigenvalues, RCLike.ofReal_real_eq_id, id_eq, Function.comp_def,
        Matrix.conjTranspose_eq_transpose_of_trivial] using he
    rw [hc, hd] at he'
    exact he'.symm
  have hs := congrArg (fun s : Multiset ℝ => (s.map Real.sqrt).sum) ht
  rw [nuclearNorm_eq_sum_sqrt]
  simpa only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum] using hs

end HighDimStat.MatrixRank.Proof


end
end

/- Complete module: SpectralMask -/
section

noncomputable section
open Matrix

namespace HighDimStat.MatrixRank.Proof

def spectralMask {n : ℕ} (s : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun j => if j ∈ s then 1 else 0)

lemma spectralMask_transpose {n : ℕ} (s : Finset (Fin n)) :
    (spectralMask s)ᵀ = spectralMask s := Matrix.diagonal_transpose _

lemma spectralMask_sq {n : ℕ} (s : Finset (Fin n)) :
    spectralMask s * spectralMask s = spectralMask s := by
  rw [spectralMask, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs <;> norm_num

lemma nuclearNorm_spectral_mask {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1)
    (hg : (A * U)ᵀ * (A * U) = Matrix.diagonal (fun j => singularValues A j ^ 2))
    (s : Finset (Fin n)) :
    nuclearNorm (A * U * spectralMask s * Uᵀ) = ∑ j ∈ s, singularValues A j := by
  have hgram : (A * U * spectralMask s * Uᵀ)ᵀ *
      (A * U * spectralMask s * Uᵀ) =
      U * Matrix.diagonal (fun j => if j ∈ s then singularValues A j ^ 2 else 0) * Uᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, spectralMask_transpose]
    calc
      U * (spectralMask s * (Uᵀ * Aᵀ)) * (A * U * spectralMask s * Uᵀ) =
        U * (spectralMask s * ((A * U)ᵀ * (A * U)) * spectralMask s) * Uᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hg]
        congr 2
        simp only [spectralMask, Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        split_ifs <;> simp
  rw [nuclearNorm_of_gram_diagonalization _ U _ hU hgram]
  have hn (j : Fin n) : 0 ≤ singularValues A j := Real.sqrt_nonneg _
  simp_rw [apply_ite Real.sqrt, Real.sqrt_zero, Real.sqrt_sq (hn _)]
  simp

end HighDimStat.MatrixRank.Proof


end
end

/- Complete module: GramProjection -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma gram_zero_column {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (hg : Bᵀ * B = diagonal v) (j : Fin n) (hj : v j = 0) :
    ∀ i, B i j = 0 := by
  have hs : ∑ i, (B i j)^2 = 0 := by
    have h := congrArg (fun M => M j j) hg
    simpa [Matrix.mul_apply, pow_two, hj] using h
  intro i
  have hz : (B i j)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (B k j))).mp hs i (Finset.mem_univ _)
  nlinarith [sq_nonneg (B i j)]

def gramProjection {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (s : Finset (Fin n)) : Matrix (Fin m) (Fin m) ℝ :=
  B * diagonal (fun j => if j ∈ s then (v j)⁻¹ else 0) * Bᵀ

lemma gramProjection_transpose {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (s : Finset (Fin n)) :
    (gramProjection B v s)ᵀ = gramProjection B v s := by
  simp [gramProjection, Matrix.transpose_mul, Matrix.mul_assoc]

lemma gramProjection_mul {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (hg : Bᵀ * B = diagonal v) (s : Finset (Fin n)) :
    gramProjection B v s * B = B * spectralMask s := by
  unfold gramProjection
  rw [Matrix.mul_assoc, hg, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.mul_diagonal, spectralMask, ite_mul, zero_mul]
  by_cases hs : j ∈ s
  · by_cases hv : v j = 0
    · simp [hs, hv, gram_zero_column B v hg j hv i]
    · simp [hs, hv]
  · simp [hs]

lemma gramProjection_sq {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (hg : Bᵀ * B = diagonal v) (s : Finset (Fin n)) :
    gramProjection B v s * gramProjection B v s = gramProjection B v s := by
  conv_lhs => rhs; unfold gramProjection
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, gramProjection_mul B v hg s]
  unfold gramProjection
  rw [Matrix.mul_assoc B, spectralMask, Matrix.diagonal_mul_diagonal]
  congr 2
  congr 1
  funext j
  split_ifs <;> simp

lemma gramProjection_rank {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (s : Finset (Fin n)) :
    (gramProjection B v s).rank ≤ s.card := by
  classical
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  by_contra h
  simp [h] at hj

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: SpectralTruncation -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma spectralMask_compl {n : ℕ} (s : Finset (Fin n)) :
    spectralMask sᶜ = 1 - spectralMask s := by
  classical
  rw [spectralMask, spectralMask, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext j
  by_cases h : j ∈ s <;> simp [h]

lemma spectralMask_rank {n : ℕ} (s : Finset (Fin n)) :
    (spectralMask s).rank = s.card := by
  classical
  rw [spectralMask, Matrix.rank_diagonal, Fintype.card_subtype]
  congr 1
  ext j
  simp

lemma singular_truncation_projections {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ) :
    ∃ (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ),
      Pᵀ = P ∧ P * P = P ∧ Qᵀ = Q ∧ Q * Q = Q ∧
      P.rank ≤ r ∧ Q.rank ≤ r ∧ P * A = A * Q ∧
      nuclearNorm (A - P * A) = tailSingularSum A r := by
  classical
  obtain ⟨U,hU,hU',hg⟩ := ordered_singular_basis A
  let s : Finset (Fin n) := Finset.univ.filter (fun j => j.val < r)
  let P := gramProjection (A * U) (fun j => singularValues A j ^ 2) s
  let Q := U * spectralMask s * Uᵀ
  have hcard : s.card ≤ r := by
    rw [← Finset.card_range r]
    apply Finset.card_le_card_of_injOn Fin.val
    · intro j hj
      change j ∈ s at hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro a _ b _ h
      exact Fin.ext h
  have hPA : P * A = A * Q := by
    have hh := gramProjection_mul (A * U) (fun j => singularValues A j ^ 2) hg s
    have hh' := congrArg (fun M => M * Uᵀ) hh
    simpa only [← Matrix.mul_assoc, Matrix.mul_assoc U Uᵀ, hU', Matrix.mul_one,
      P, Q, Matrix.mul_assoc] using hh'
  refine ⟨P,Q,gramProjection_transpose _ _ _,gramProjection_sq _ _ hg _,?_,?_,?_,?_,hPA,?_⟩
  · simp only [Q, Matrix.transpose_mul, Matrix.transpose_transpose, spectralMask_transpose,
      Matrix.mul_assoc]
  · change (U * spectralMask s * Uᵀ) * (U * spectralMask s * Uᵀ) = _
    calc
      _ = U * (spectralMask s * (Uᵀ * U) * spectralMask s) * Uᵀ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, spectralMask_sq]
  · exact (gramProjection_rank _ _ _).trans hcard
  · exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans (by rw [spectralMask_rank]; exact hcard))
  · have he : A - P * A = A * U * spectralMask sᶜ * Uᵀ := by
      rw [hPA, spectralMask_compl]
      simp only [Q, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc,
        hU', Matrix.mul_one]
    rw [he, nuclearNorm_spectral_mask A U hU hg]
    unfold tailSingularSum
    congr 1
    ext j
    simp [s, not_lt]

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: MatrixFrobenius -/
section

noncomputable section
open Matrix

namespace HighDimStat.MatrixRank.Proof

lemma frobeniusNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (A i j))

lemma frobeniusNorm_sq_eq_trace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = Matrix.trace (Aᵀ * A) := by
  rw [frobeniusNorm_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, ← sq]
  exact Finset.sum_comm

lemma sum_gramEigenvalues {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∑ j, gramEigenvalues A j = frobeniusNorm A ^ 2 := by
  rw [frobeniusNorm_sq_eq_trace]
  simpa [gramEigenvalues] using
    (Matrix.posSemidef_conjTranspose_mul_self A).1.trace_eq_sum_eigenvalues.symm

lemma frobeniusNorm_sq_mul_orthogonal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U * Uᵀ = 1) : frobeniusNorm (A * U) ^ 2 = frobeniusNorm A ^ 2 := by
  rw [frobeniusNorm_sq_eq_trace, frobeniusNorm_sq_eq_trace, Matrix.transpose_mul]
  calc
    Matrix.trace (Uᵀ * Aᵀ * (A * U)) = Matrix.trace (Uᵀ * (Aᵀ * A) * U) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (U * Uᵀ * (Aᵀ * A)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Aᵀ * A) := by rw [hU, Matrix.one_mul]

lemma frobeniusNorm_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm Aᵀ = frobeniusNorm A := by
  unfold frobeniusNorm
  congr 1
  exact Finset.sum_comm

end HighDimStat.MatrixRank.Proof


end
end

/- Complete module: NuclearRankFrobenius -/
section

noncomputable section
open Matrix

namespace HighDimStat.MatrixRank.Proof

lemma nuclearNorm_sq_le_rank_mul_frobeniusNorm_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A ^ 2 ≤ (A.rank : ℝ) * frobeniusNorm A ^ 2 := by
  classical
  let s := Finset.univ.filter (fun j : Fin n => gramEigenvalues A j ≠ 0)
  have hz (j : Fin n) (hj : j ∉ s) : gramEigenvalues A j = 0 := by
    simpa [s] using hj
  have hsum : ∑ j ∈ s, Real.sqrt (gramEigenvalues A j) = nuclearNorm A := by
    rw [nuclearNorm_eq_sum_sqrt]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simp [hz j hj]
  have hsq : ∑ j ∈ s, (Real.sqrt (gramEigenvalues A j)) ^ 2 = frobeniusNorm A ^ 2 := by
    simp_rw [Real.sq_sqrt (gramEigenvalues_nonneg A _)]
    rw [← sum_gramEigenvalues]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    exact hz j hj
  have hr : A.rank = s.card := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self A).1.rank_eq_card_non_zero_eigs
    rw [Matrix.rank_conjTranspose_mul_self] at h
    simpa [s, gramEigenvalues, Fintype.card_subtype] using h
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ))
    (fun j => Real.sqrt (gramEigenvalues A j))
  simpa [hsum, hsq, hr] using hc

end HighDimStat.MatrixRank.Proof


end
end

/- Complete module: TangentGeometry -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma matrix_rank_add_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  have h := Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)
  exact h.trans (Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))

lemma frobenius_sq_sub {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (A-B)^2 = frobeniusNorm A^2 + frobeniusNorm B^2 -
      2 * Matrix.trace (Aᵀ * B) := by
  simp only [frobeniusNorm_sq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.sub_apply]
  rw [Finset.sum_comm (f := fun j i => A i j * B i j)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  congr 1
  funext i
  congr 1
  funext j
  ring

lemma projection_complement_sq {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P*P=P) : (1-P)*(1-P)=1-P := by
  noncomm_ring [hP]

lemma tangent_frobenius_sq_le {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hPt : Pᵀ=P) (hP : P*P=P) (hQt : Qᵀ=Q) (hQ : Q*Q=Q) :
    frobeniusNorm (D - (1-P)*D*(1-Q))^2 ≤ frobeniusNorm D^2 := by
  let E := (1-P)*D*(1-Q)
  have hp : (1-P)ᵀ=1-P := by simp [hPt]
  have hq : (1-Q)ᵀ=1-Q := by simp [hQt]
  have hs : Matrix.trace (Eᵀ*E) = Matrix.trace (Dᵀ*E) := by
    change Matrix.trace (((1-P)*D*(1-Q))ᵀ*((1-P)*D*(1-Q))) = _
    simp only [Matrix.transpose_mul, hp, hq]
    calc
      _ = Matrix.trace ((1-Q) * (Dᵀ*((1-P)*(1-P))*D) * (1-Q)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((1-Q)*(1-Q)) * (Dᵀ*((1-P)*(1-P))*D)) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace ((1-Q) * (Dᵀ*(1-P)*D)) := by
        rw [projection_complement_sq P hP, projection_complement_sq Q hQ]
      _ = _ := by
        rw [Matrix.trace_mul_comm]
        simp only [E, Matrix.mul_assoc]
  have ht : Matrix.trace (Dᵀ*E) = frobeniusNorm E^2 := by
    rw [frobeniusNorm_sq_eq_trace, hs]
  change frobeniusNorm (D-E)^2 ≤ _
  rw [frobenius_sq_sub, ht]
  nlinarith [sq_nonneg (frobeniusNorm E)]

lemma tangent_rank_le {m n r : ℕ} (D : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.rank ≤ r) (hQ : Q.rank ≤ r) :
    (D - (1-P)*D*(1-Q)).rank ≤ 2*r := by
  have he : D-(1-P)*D*(1-Q) = P*D + ((1-P)*D)*Q := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [he]
  exact (matrix_rank_add_le _ _).trans
    ((add_le_add ((Matrix.rank_mul_le_left _ _).trans hP)
      ((Matrix.rank_mul_le_right _ _).trans hQ)).trans_eq (by omega))

lemma tangent_nuclear_bound {m n r : ℕ} (D : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hPt : Pᵀ=P) (hP : P*P=P) (hQt : Qᵀ=Q) (hQ : Q*Q=Q)
    (hPr : P.rank ≤ r) (hQr : Q.rank ≤ r) :
    nuclearNorm (D-(1-P)*D*(1-Q)) ≤ Real.sqrt (2*(r:ℝ)) * frobeniusNorm D := by
  let T := D-(1-P)*D*(1-Q)
  have hr : (T.rank : ℝ) ≤ 2*(r:ℝ) := by
    exact_mod_cast tangent_rank_le D P Q hPr hQr
  have hf := tangent_frobenius_sq_le D P Q hPt hP hQt hQ
  have hb := nuclearNorm_sq_le_rank_mul_frobeniusNorm_sq T
  have hm := mul_le_mul_of_nonneg_right hr (sq_nonneg (frobeniusNorm T))
  have hm' := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2*(r:ℝ) by positivity)
  have hs : Real.sqrt (2*(r:ℝ))^2 = 2*(r:ℝ) := Real.sq_sqrt (by positivity)
  have hn : 0 ≤ Real.sqrt (2*(r:ℝ)) * frobeniusNorm D := by
    unfold frobeniusNorm
    positivity
  change nuclearNorm T ≤ _
  nlinarith [sq_nonneg (nuclearNorm T)]

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: MatrixVectorGeometry -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma vecNorm_mulVec_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) : vecNorm (A.mulVec v) ^ 2 = v ⬝ᵥ ((Aᵀ * A).mulVec v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  rw [vecNorm_sq]
  simp only [dotProduct, pow_two]

lemma vecNorm_orthogonal_mulVec {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (v : Fin n → ℝ) : vecNorm (U.mulVec v) = vecNorm v := by
  have hh := vecNorm_mulVec_sq U v
  rw [hU, Matrix.one_mulVec] at hh
  have hs : vecNorm (U.mulVec v) ^ 2 = vecNorm v ^ 2 := by
    rw [vecNorm_sq v]
    simpa only [dotProduct, ← sq] using hh
  nlinarith [vecNorm_nonneg (U.mulVec v), vecNorm_nonneg v]

lemma opNorm_le_one_of_gram_diagonal {m n : ℕ}
    (Z : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ) (hU : U * Uᵀ = 1) (hp : ∀ j, p j ≤ 1)
    (hg : Zᵀ * Z = U * Matrix.diagonal p * Uᵀ) : opNorm Z ≤ 1 := by
  apply native_opNorm_le_of_bound Z 1 (by norm_num)
  intro v
  let w := Uᵀ.mulVec v
  have he : vecNorm (Z.mulVec v) ^ 2 = ∑ j, p j * w j ^ 2 := by
    rw [vecNorm_mulVec_sq, hg]
    simp only [← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro j _
    change w j * (p j * w j) = p j * w j ^ 2
    ring
  have hb : (∑ j, p j * w j ^ 2) ≤ ∑ j, w j ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hp j) (sq_nonneg (w j))
  have hw : vecNorm w = vecNorm v :=
    vecNorm_orthogonal_mulVec Uᵀ (by simpa only [Matrix.transpose_transpose] using hU) v
  rw [← vecNorm_sq, hw] at hb
  nlinarith [vecNorm_nonneg (Z.mulVec v), vecNorm_nonneg v]

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: NuclearPolarCertificate -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma nuclear_polar_certificate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (Z : Matrix (Fin m) (Fin n) ℝ)
      (L : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin n) (Fin n) ℝ),
      Z = L * A ∧ Z = A * R ∧ opNorm Z ≤ 1 ∧ traceInner Z A = nuclearNorm A := by
  classical
  obtain ⟨U,hU,hU',hg⟩ := ordered_singular_basis A
  let s := singularValues A
  let V := A * U
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun j => (s j)⁻¹)
  let E : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun j => (s j)⁻¹ ^ 3)
  let p : Fin n → ℝ := fun j => if s j = 0 then 0 else 1
  let Z := V * D * Uᵀ
  let L := V * E * Vᵀ
  let R := U * D * Uᵀ
  have hD : Dᵀ = D := by simp [D]
  have hd2 : D * Matrix.diagonal (fun j => s j ^ 2) * D = Matrix.diagonal p := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    dsimp [p]
    by_cases hz : s j = 0
    · simp [hz]
    · simp [hz]
      field_simp
  have hd3 : E * Matrix.diagonal (fun j => s j ^ 2) = D := by
    simp only [E, D, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases hz : s j = 0
    · simp [hz]
    · field_simp
  have hA : A = V * Uᵀ := by
    dsimp [V]
    rw [Matrix.mul_assoc, hU', Matrix.mul_one]
  have hgram : Zᵀ * Z = U * Matrix.diagonal p * Uᵀ := by
    change (V * D * Uᵀ)ᵀ * (V * D * Uᵀ) = _
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hD]
    calc
      U * (D * Vᵀ) * (V * D * Uᵀ) = U * (D * (Vᵀ * V) * D) * Uᵀ := by
        simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal p * Uᵀ := by rw [hg, hd2]
  have hleft : L * A = Z := by
    change V * E * Vᵀ * A = V * D * Uᵀ
    calc
      V * E * Vᵀ * A = V * E * Vᵀ * (V * Uᵀ) := congrArg (fun B => V * E * Vᵀ * B) hA
      _ = V * (E * (Vᵀ * V)) * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = V * D * Uᵀ := by rw [hg, hd3]
  have hright : A * R = Z := by simp only [R, Z, V, Matrix.mul_assoc]
  have hop : opNorm Z ≤ 1 :=
    opNorm_le_one_of_gram_diagonal Z U p hU' (fun j => by dsimp [p]; split <;> norm_num) hgram
  have hZU : Z * U = V * D := by
    dsimp [Z]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  have hcolumn (j : Fin n) : ∑ i, V i j ^ 2 = s j ^ 2 := by
    have hh : (∑ i, V i j * V i j) = s j ^ 2 := by
      change (Vᵀ * V) j j = _
      rw [hg, Matrix.diagonal_apply_eq]
    simpa only [← sq] using hh
  have htrace : traceInner Z A = nuclearNorm A := by
    calc
      traceInner Z A = traceInner (Z * U) (A * U) := (traceInner_mul_orthogonal Z A U hU').symm
      _ = traceInner (V * D) V := by rw [hZU]
      _ = ∑ j, (s j)⁻¹ * (∑ i, V i j ^ 2) := by
        unfold traceInner
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [D, Matrix.mul_diagonal]
        ring
      _ = ∑ j, s j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcolumn]
        by_cases hz : s j = 0
        · simp [hz]
        · field_simp
      _ = nuclearNorm A := rfl
  exact ⟨Z,L,R,hleft.symm,hright.symm,hop,htrace⟩

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: NuclearNormGeometry -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma traceInner_add_left {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    traceInner (A + B) C = traceInner A C + traceInner B C := by
  simp [traceInner, add_mul, Finset.sum_add_distrib]

lemma traceInner_add_right {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A (B + C) = traceInner A B + traceInner A C := by
  simp [traceInner, mul_add, Finset.sum_add_distrib]

lemma nuclearNorm_triangle {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  obtain ⟨Z, L, R, _hl, _hr, hop, ht⟩ := nuclear_polar_certificate (A + B)
  rw [← ht, traceInner_add_right]
  have ha := (traceInner_le_opNorm_mul_nuclearNorm Z A).trans
    (mul_le_mul_of_nonneg_right hop (nuclearNorm_nonneg A))
  have hb := (traceInner_le_opNorm_mul_nuclearNorm Z B).trans
    (mul_le_mul_of_nonneg_right hop (nuclearNorm_nonneg B))
  simpa only [one_mul] using add_le_add ha hb

lemma nuclearNorm_neg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm (-A) = nuclearNorm A := by
  obtain ⟨U,hU,_hU',hg⟩ := spectral_data A
  have hn : (-A)ᵀ * (-A) = U * Matrix.diagonal (gramEigenvalues A) * Uᵀ := by
    simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using hg
  rw [nuclearNorm_of_gram_diagonalization (-A) U (gramEigenvalues A) hU hn,
    nuclearNorm_of_gram_diagonalization A U (gramEigenvalues A) hU hg]

lemma nuclearNorm_sub_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm (A - B) ≤ nuclearNorm A + nuclearNorm B := by
  simpa only [sub_eq_add_neg, nuclearNorm_neg] using nuclearNorm_triangle A (-B)

lemma nuclearNorm_reverse_triangle {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A - nuclearNorm B ≤ nuclearNorm (A + B) := by
  have hh := nuclearNorm_triangle (A + B) (-B)
  rw [add_neg_cancel_right, nuclearNorm_neg] at hh
  linarith

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: NuclearBlockAdditivity -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma projection_vec_norm_split {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hs : Qᵀ = Q) (hi : Q * Q = Q) (v : Fin n → ℝ) :
    vecNorm (Q.mulVec v) ^ 2 + vecNorm ((1 - Q).mulVec v) ^ 2 = vecNorm v ^ 2 := by
  have hc : (1 - Q)ᵀ * (1 - Q) = 1 - Q := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, hs,
      sub_mul, mul_sub, one_mul, mul_one, hi, sub_self, sub_zero]
  rw [vecNorm_mulVec_sq, vecNorm_mulVec_sq, hs, hi, hc]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, vecNorm_sq]
  simp only [dotProduct, pow_two]
  ring

lemma left_supported_cross_zero {m n : ℕ}
    (P : Matrix (Fin m) (Fin m) ℝ) (A B : Matrix (Fin m) (Fin n) ℝ)
    (hP : Pᵀ = P) (ha : P * A = A) (hb : P * B = 0) : Aᵀ * B = 0 := by
  have hat : Aᵀ * P = Aᵀ := by
    simpa only [Matrix.transpose_mul, hP] using congrArg Matrix.transpose ha
  rw [← hat, Matrix.mul_assoc, hb, Matrix.mul_zero]

lemma supported_contractions_add {m n : ℕ}
    (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (Z W : Matrix (Fin m) (Fin n) ℝ)
    (hPs : Pᵀ = P) (hQs : Qᵀ = Q) (hQi : Q * Q = Q)
    (hPZ : P * Z = Z) (hPW : P * W = 0)
    (hZQ : Z * Q = Z) (hWQ : W * Q = 0)
    (hZ : opNorm Z ≤ 1) (hW : opNorm W ≤ 1) : opNorm (Z + W) ≤ 1 := by
  have hzw := left_supported_cross_zero P Z W hPs hPZ hPW
  have hwz : Wᵀ * Z = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hzw
  have hg : (Z + W)ᵀ * (Z + W) = Zᵀ * Z + Wᵀ * W := by
    simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, hzw, hwz, add_zero, zero_add]
  have hWc : W * (1 - Q) = W := by rw [Matrix.mul_sub, Matrix.mul_one, hWQ, sub_zero]
  apply native_opNorm_le_of_bound (Z + W) 1 (by norm_num)
  intro v
  have hz := (mulVec_norm_le_opNorm Z (Q.mulVec v)).trans
    (mul_le_mul_of_nonneg_right hZ (vecNorm_nonneg _))
  have hw := (mulVec_norm_le_opNorm W ((1 - Q).mulVec v)).trans
    (mul_le_mul_of_nonneg_right hW (vecNorm_nonneg _))
  rw [Matrix.mulVec_mulVec, hZQ, one_mul] at hz
  rw [Matrix.mulVec_mulVec, hWc, one_mul] at hw
  have hsplit : vecNorm ((Z + W).mulVec v) ^ 2 =
      vecNorm (Z.mulVec v) ^ 2 + vecNorm (W.mulVec v) ^ 2 := by
    rw [vecNorm_mulVec_sq, hg, Matrix.add_mulVec, dotProduct_add,
      ← vecNorm_mulVec_sq, ← vecNorm_mulVec_sq]
  have hp := projection_vec_norm_split Q hQs hQi v
  have hzsq := mul_self_le_mul_self (vecNorm_nonneg _) hz
  have hwsq := mul_self_le_mul_self (vecNorm_nonneg _) hw
  nlinarith [vecNorm_nonneg ((Z + W).mulVec v), vecNorm_nonneg v]

lemma traceInner_symm {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A B = traceInner B A := by simp only [traceInner, mul_comm]

lemma nuclearNorm_orthogonal_blocks {m n : ℕ}
    (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (A B : Matrix (Fin m) (Fin n) ℝ)
    (hPs : Pᵀ = P) (hQs : Qᵀ = Q) (hQi : Q * Q = Q)
    (hPA : P * A = A) (hAQ : A * Q = A)
    (hPB : P * B = 0) (hBQ : B * Q = 0) :
    nuclearNorm (A + B) = nuclearNorm A + nuclearNorm B := by
  obtain ⟨Z,L,R,hZL,hZR,hZ,htZ⟩ := nuclear_polar_certificate A
  obtain ⟨W,L',R',hWL,hWR,hW,htW⟩ := nuclear_polar_certificate B
  have hPZ : P * Z = Z := by simp only [hZR, ← Matrix.mul_assoc, hPA]
  have hZQ : Z * Q = Z := by simp only [hZL, Matrix.mul_assoc, hAQ]
  have hPW : P * W = 0 := by simp only [hWR, ← Matrix.mul_assoc, hPB, Matrix.zero_mul]
  have hWQ : W * Q = 0 := by simp only [hWL, Matrix.mul_assoc, hBQ, Matrix.mul_zero]
  have hop := supported_contractions_add P Q Z W hPs hQs hQi hPZ hPW hZQ hWQ hZ hW
  have hzb : traceInner Z B = 0 := by
    rw [traceInner_eq_trace, left_supported_cross_zero P Z B hPs hPZ hPB, Matrix.trace_zero]
  have hwa : traceInner W A = 0 := by
    rw [traceInner_symm, traceInner_eq_trace,
      left_supported_cross_zero P A W hPs hPA hPW, Matrix.trace_zero]
  have ht : traceInner (Z + W) (A + B) = nuclearNorm A + nuclearNorm B := by
    rw [traceInner_add_left, traceInner_add_right, traceInner_add_right,
      htZ, htW, hzb, hwa, add_zero, zero_add]
  apply le_antisymm (nuclearNorm_triangle A B)
  rw [← ht]
  exact (traceInner_le_opNorm_mul_nuclearNorm (Z + W) (A + B)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hop (nuclearNorm_nonneg (A + B)))

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: NuclearDecomposition -/
section

noncomputable section
open Matrix
namespace HighDimStat.MatrixRank.Proof

lemma nuclear_decomposition {m n : ℕ} (A D : Matrix (Fin m) (Fin n) ℝ) (r : ℕ) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      nuclearNorm D ≤ B+C ∧
      B ≤ Real.sqrt (2*(r:ℝ)) * frobeniusNorm D ∧
      nuclearNorm A - nuclearNorm (A+D) ≤ B-C+2*tailSingularSum A r := by
  obtain ⟨P,Q,hPt,hP,hQt,hQ,hPr,hQr,hPA,htail⟩ := singular_truncation_projections A r
  let E := (1-P)*D*(1-Q)
  let T := D-E
  let A0 := P*A
  let A1 := A-A0
  have hPA0 : P*A0=A0 := by dsimp [A0]; rw [← Matrix.mul_assoc, hP]
  have hA0Q : A0*Q=A0 := by
    dsimp [A0]
    rw [hPA, Matrix.mul_assoc, hQ]
  have hPE : P*E=0 := by
    dsimp [E]
    have hc : P*(1-P)=0 := by rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.zero_mul, Matrix.zero_mul]
  have hEQ : E*Q=0 := by
    dsimp [E]
    have hc : (1-Q)*Q=0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQ, sub_self]
    rw [Matrix.mul_assoc, hc, Matrix.mul_zero]
  have hblock := nuclearNorm_orthogonal_blocks P Q A0 E hPt hQt hQ hPA0 hA0Q hPE hEQ
  have he : A+D = (A0+E)+(A1+T) := by dsimp [A1,T]; abel
  have ht : nuclearNorm A1 = tailSingularSum A r := htail
  have hlow := nuclearNorm_reverse_triangle (A0+E) (A1+T)
  rw [← he, hblock] at hlow
  have hpert := nuclearNorm_triangle A1 T
  have ha := nuclearNorm_triangle A0 A1
  have haa : A0+A1=A := by dsimp [A1]; abel
  rw [haa, ht] at ha
  rw [ht] at hpert
  refine ⟨nuclearNorm T,nuclearNorm E,nuclearNorm_nonneg _,nuclearNorm_nonneg _,?_,?_,?_⟩
  · have hd := nuclearNorm_triangle T E
    have hde : T+E=D := sub_add_cancel _ _
    rwa [hde] at hd
  · exact tangent_nuclear_bound D P Q hPt hP hQt hQ hPr hQr
  · linarith

end HighDimStat.MatrixRank.Proof

end
end

/- Complete module: NuclearOracleRoot -/
section


namespace HighDimStat.MatrixRank

/-- Proposition 10.6 (p. 319), **with corrected constants and rank condition**: suppose the
observation operator `Xn` satisfies the restricted strong convexity condition (10.17) with
curvature `κ > 0` and tolerance constant `c0 ≥ 0`. Then, conditioned on the good event
`G(λn) = {|||(1/n)Σwᵢ Xᵢ|||₂ ≤ λn/2}`, any optimal solution `Θ̂` of nuclear-norm-regularized
least squares (10.16) satisfies, for any target rank `r ∈ {1,...,d'}` with
`256 c0 (d1+d2) r ≤ κ n`,
`|||Θ̂ - Θ*|||_F² ≤ 72 (λn²/κ²) r + (1/κ){16 λn Σ_{j>r} σⱼ(Θ*) + 256 c0 (d1+d2)/n (Σ_{j>r} σⱼ(Θ*))²}`.

Correction to the printed source. The printed bound
`(9/2)(λn²/κ²) r + (1/κ){2λn·tail + 32 c0(d1+d2)/n · tail²}` under the printed rank condition
`r ≤ κn/(128 c0(d1+d2))` is false: a non-degenerate instance (`d1 = d2 = 101`, `r = 1`,
`κ = 1`, `λn = 1/100`, rank condition met with equality, RSC verified for every matrix, a
KKT-certified global minimizer) has `|||Θ̂ - Θ*|||_F² = 5.24 > 4.08`. The proposition is the
instantiation of Theorem 9.19 with `Ψ²(M̄) = 2r`, `τn² = c0(d1+d2)/n`,
`Φ(Θ*_{M⊥}) = Σ_{j>r}σⱼ(Θ*)`; the printed constants are not even those of the printed
Theorem 9.19 (which would give `18, 8, 128`), and the printed Theorem 9.19 itself is false
with a positive tolerance (see `cor9_20_special_case_v2`). Running the book's proof of
Theorem 9.19 with the tolerance term accounted for — `Φ(Δ)² ≤ 32Ψ²‖Δ‖² + 32Φ(θ*_{M⊥})²` leaves
curvature `κ/2 − 32τn²Ψ² ≥ κ/4` once `τn²Ψ² ≤ κ/128` (here: `256 c0(d1+d2) r ≤ κn`), and then
`F(Δ) ≥ (κ/4)‖Δ‖² − (3/2)λnΨ‖Δ‖ − 2λnΦ(θ*_{M⊥}) − 32τn²Φ(θ*_{M⊥})² > 0` for
`‖Δ‖² > 36λn²Ψ²/κ² + (16/κ)(λnΦ(θ*_{M⊥}) + 16τn²Φ(θ*_{M⊥})²)` — gives exactly the bound
stated here. The rank condition is written multiplicatively so that `c0 = 0` (no tolerance)
imposes no restriction, as in the source. -/
theorem prop10_6_nuclear_norm_oracle_inequality_v2 {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ c0 lamN : ℝ) (r : ℕ)
    (hκ : 0 < κ) (hc0 : 0 ≤ c0) (hlam : 0 < lamN)
    (hRSC : RSCNuclear Xs κ c0)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN / 2)
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar + w i) lamN Θhat)
    (hr1 : 1 ≤ r) (hr2 : r ≤ min d1 d2)
    (hr3 : 256 * c0 * ((d1 : ℝ) + d2) * r ≤ κ * n) :
    (frobeniusNorm (Θhat - Θstar)) ^ 2 ≤
      72 * (lamN ^ 2 / κ ^ 2) * r +
        1 / κ * (16 * lamN * tailSingularSum Θstar r +
          256 * c0 * ((d1 : ℝ) + d2) / n * (tailSingularSum Θstar r) ^ 2) := by
  have hd1 : 1 ≤ d1 := hr1.trans (hr2.trans (Nat.min_le_left _ _))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    simpa only [Nat.cast_zero] using
      zero_samples_oracle_bound Xs Θstar Θhat κ c0 lamN r hκ hlam.le hRSC
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    let D := Θhat - Θstar
    let tau := c0 * ((d1 : ℝ) + d2) / (n : ℝ)
    let curvature := (∑ i, (observationOp Xs D i) ^ 2) / (2 * (n : ℝ))
    obtain ⟨B,C,hB,hC,hN,hcompat,hdiff⟩ := Proof.nuclear_decomposition Θstar D r
    have he : Θstar + D = Θhat := by dsimp [D]; abel
    rw [he] at hdiff
    have hbasic := least_squares_basic_inequality Xs w Θstar Θhat lamN hsol
    change curvature ≤ (1 / (n : ℝ)) * (∑ i, w i * observationOp Xs D i) +
      lamN * (nuclearNorm Θstar - nuclearNorm Θhat) at hbasic
    have hnoise := Proof.noise_bound_on_good_event Xs w D lamN hG
    have hN' := mul_le_mul_of_nonneg_left hN (show 0 ≤ lamN / 2 by positivity)
    have hdiff' := mul_le_mul_of_nonneg_left hdiff hlam.le
    have hupper : curvature ≤ 3 * lamN / 2 * B - lamN / 2 * C +
        2 * lamN * tailSingularSum Θstar r := by nlinarith
    have hlower := hRSC D
    change κ / 2 * frobeniusNorm D ^ 2 - tau * nuclearNorm D ^ 2 ≤ curvature at hlower
    have htau : 0 ≤ tau := by
      have hd1R : (0 : ℝ) ≤ d1 := le_trans (by norm_num : (0 : ℝ) ≤ 1)
        (by exact_mod_cast hd1)
      exact div_nonneg (mul_nonneg hc0 (add_nonneg hd1R (Nat.cast_nonneg d2))) hnR.le
    have hcurv : 0 ≤ curvature := by
      dsimp [curvature]
      exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    have hrdiv : (256 * c0 * ((d1 : ℝ) + d2) * (r : ℝ)) / (n : ℝ) ≤ κ :=
      (div_le_iff₀ hnR).mpr hr3
    have hbudget : 64 * tau * (r : ℝ) ≤ κ / 4 := by
      dsimp [tau]
      simp only [div_eq_mul_inv] at hrdiv ⊢
      nlinarith
    have hanswer := nuclear_oracle_scalar_finish κ lamN tau (frobeniusNorm D)
      (tailSingularSum Θstar r) B C (nuclearNorm D) curvature (Real.sqrt (2 * (r : ℝ)))
      (r : ℝ) hκ hlam htau (tailSingularSum_nonneg Θstar r) hB hC
      (nuclearNorm_nonneg D) hcurv (Real.sq_sqrt (by positivity))
      hcompat hN hlower hupper hbudget
    dsimp only [D,tau] at hanswer
    simpa only [mul_div_assoc, mul_assoc] using hanswer

end HighDimStat.MatrixRank



end

open HighDimStat.MatrixRank

theorem solution {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ c0 lamN : ℝ) (r : ℕ)
    (hκ : 0 < κ) (hc0 : 0 ≤ c0) (hlam : 0 < lamN)
    (hRSC : RSCNuclear Xs κ c0)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN / 2)
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar + w i) lamN Θhat)
    (hr1 : 1 ≤ r) (hr2 : r ≤ min d1 d2)
    (hr3 : 256 * c0 * ((d1 : ℝ) + d2) * r ≤ κ * n) :
    (frobeniusNorm (Θhat - Θstar)) ^ 2 ≤
      72 * (lamN ^ 2 / κ ^ 2) * r +
        1 / κ * (16 * lamN * tailSingularSum Θstar r +
          256 * c0 * ((d1 : ℝ) + d2) / n * (tailSingularSum Θstar r) ^ 2) := by
  exact @HighDimStat.MatrixRank.prop10_6_nuclear_norm_oracle_inequality_v2
    d1 d2 n Xs w Θstar Θhat κ c0 lamN r hκ hc0 hlam hRSC hG hsol hr1 hr2 hr3

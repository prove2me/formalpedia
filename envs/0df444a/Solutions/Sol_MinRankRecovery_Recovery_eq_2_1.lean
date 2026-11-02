-- Prove2me | solution 1 for MinRankRecovery.Recovery.eq_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:34:28.899415+00:00
-- url     : https://prove2.me/submissions/72dd777f-7682-4bdf-b282-d844f32a4f97

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

open HighDimStat.MatrixRank Matrix
open scoped BigOperators

namespace SolEq21

lemma mulVec_sq_le_frob_sq {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : ∑ j, (v j) ^ 2 = 1) :
    ∑ i, (X.mulVec v i) ^ 2 ≤ ∑ i, ∑ j, (X i j) ^ 2 := by
  refine Finset.sum_le_sum fun i _ => ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j) v
  rw [hv, mul_one] at hcs
  simpa [Matrix.mulVec, dotProduct] using hcs

lemma opNorm_bddAbove {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    BddAbove (Set.range (fun v : {v : Fin n → ℝ // ∑ j, (v j) ^ 2 = 1} =>
      Real.sqrt (∑ i, (X.mulVec v.1 i) ^ 2))) := by
  refine ⟨frobeniusNorm X, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact Real.sqrt_le_sqrt (mulVec_sq_le_frob_sq X v.1 v.2)

lemma opNorm_nonneg {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ opNorm X := by
  unfold opNorm
  by_cases hne : Nonempty {v : Fin n → ℝ // ∑ j, (v j) ^ 2 = 1}
  · obtain ⟨v₀⟩ := hne
    exact le_trans (Real.sqrt_nonneg _)
      (le_ciSup (opNorm_bddAbove X) v₀)
  · have : IsEmpty {v : Fin n → ℝ // ∑ j, (v j) ^ 2 = 1} := not_nonempty_iff.mp hne
    simp

lemma opNorm_le_frobeniusNorm {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    opNorm X ≤ frobeniusNorm X := by
  unfold opNorm
  by_cases hne : Nonempty {v : Fin n → ℝ // ∑ j, (v j) ^ 2 = 1}
  · have := hne
    refine ciSup_le fun v => ?_
    exact Real.sqrt_le_sqrt (mulVec_sq_le_frob_sq X v.1 v.2)
  · have : IsEmpty {v : Fin n → ℝ // ∑ j, (v j) ^ 2 = 1} := not_nonempty_iff.mp hne
    simp [frobeniusNorm, Real.sqrt_nonneg]

noncomputable def eigPerm (n : ℕ) : Fin n ≃ Fin n :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm.trans
    (finCongr (Fintype.card_fin n))

lemma singularValues_eigPerm {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    singularValues X (eigPerm n i) =
      Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues i) := by
  simp [singularValues, eigPerm, Matrix.IsHermitian.eigenvalues]

lemma trace_conjTranspose_mul_self_eq_sum_sq {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    (Xᴴ * X).trace = ∑ i, ∑ j, (X i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial, ← sq]
  exact Finset.sum_comm

lemma sum_singularValues_sq {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    ∑ j, (singularValues X j) ^ 2 = ∑ i, ∑ j, (X i j) ^ 2 := by
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self X
  have hHerm := hPSD.1
  rw [← (eigPerm n).sum_comp (fun j => (singularValues X j) ^ 2)]
  have h1 : ∑ i : Fin n, (singularValues X (eigPerm n i)) ^ 2 =
      ∑ i : Fin n, hHerm.eigenvalues i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [singularValues_eigPerm, Real.sq_sqrt (hPSD.eigenvalues_nonneg i)]
  have h_tr : (Xᴴ * X).trace = ∑ i : Fin n, hHerm.eigenvalues i := by
    simpa using hHerm.trace_eq_sum_eigenvalues
  rw [h1, ← h_tr, trace_conjTranspose_mul_self_eq_sum_sq]

lemma frobeniusNorm_eq_sqrt_sum_singularValues_sq {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm X = Real.sqrt (∑ j, (singularValues X j) ^ 2) := by
  rw [frobeniusNorm, sum_singularValues_sq]

lemma singularValues_nonneg {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    0 ≤ singularValues X j :=
  Real.sqrt_nonneg _

lemma frobeniusNorm_le_nuclearNorm {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm X ≤ nuclearNorm X := by
  rw [frobeniusNorm_eq_sqrt_sum_singularValues_sq, nuclearNorm]
  have h_nonneg : 0 ≤ ∑ j, singularValues X j :=
    Finset.sum_nonneg fun j _ => singularValues_nonneg X j
  rw [← Real.sqrt_sq h_nonneg]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => singularValues_nonneg X j

lemma mulVec_eigenvector_norm_sq {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    ∑ k, (X.mulVec ((Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvectorBasis i).ofLp k) ^ 2 =
      (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues i := by
  let hHerm := (Matrix.posSemidef_conjTranspose_mul_self X).1
  let u : Fin n → ℝ := (hHerm.eigenvectorBasis i).ofLp
  have hu_unit : dotProduct u u = 1 := by
    have hnorm : inner ℝ (hHerm.eigenvectorBasis i) (hHerm.eigenvectorBasis i) = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hHerm.eigenvectorBasis.orthonormal.1 i, mul_one]
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hnorm
    exact hnorm
  have h1 : ∑ k, (X.mulVec u k) ^ 2 = dotProduct (X.mulVec u) (X.mulVec u) := by
    simp [dotProduct, sq]
  have h2 : dotProduct (X.mulVec u) (X.mulVec u) = dotProduct u ((Xᴴ * X).mulVec u) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
      star_trivial, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have h3 : (Xᴴ * X).mulVec u = hHerm.eigenvalues i • u :=
    hHerm.mulVec_eigenvectorBasis i
  rw [h1, h2, h3, dotProduct_smul, hu_unit, smul_eq_mul, mul_one]

lemma singularValues_le_opNorm {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    singularValues X j ≤ opNorm X := by
  let i := (eigPerm n).symm j
  have hj : j = eigPerm n i := ((eigPerm n).apply_symm_apply j).symm
  rw [hj, singularValues_eigPerm]
  let hHerm := (Matrix.posSemidef_conjTranspose_mul_self X).1
  let u : Fin n → ℝ := (hHerm.eigenvectorBasis i).ofLp
  have hu_sq : ∑ k, (u k) ^ 2 = 1 := by
    have hnorm : inner ℝ (hHerm.eigenvectorBasis i) (hHerm.eigenvectorBasis i) = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hHerm.eigenvectorBasis.orthonormal.1 i, mul_one]
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hnorm
    simpa [dotProduct, sq, u] using hnorm
  rw [← mulVec_eigenvector_norm_sq X i]
  exact le_ciSup (opNorm_bddAbove X) ⟨u, hu_sq⟩

lemma card_support_singularValues_le_rank {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    (Finset.univ.filter (fun j : Fin n => singularValues X j ≠ 0)).card ≤ X.rank := by
  let hPSD := Matrix.posSemidef_conjTranspose_mul_self X
  let hHerm := hPSD.1
  have h_rank : (Xᴴ * X).rank = X.rank := Matrix.rank_conjTranspose_mul_self X
  rw [← h_rank, hHerm.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have h_bij : (Finset.univ.filter (fun j : Fin n => singularValues X j ≠ 0)).card =
      (Finset.univ.filter (fun i : Fin n => hHerm.eigenvalues i ≠ 0)).card := by
    refine Finset.card_bij (fun j _ => (eigPerm n).symm j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro h0
      apply hj
      have hj' : j = eigPerm n ((eigPerm n).symm j) := ((eigPerm n).apply_symm_apply j).symm
      rw [hj', singularValues_eigPerm, h0, Real.sqrt_zero]
    · intro j₁ _ j₂ _ h
      exact (eigPerm n).symm.injective h
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨eigPerm n i, ?_, (eigPerm n).symm_apply_apply i⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, singularValues_eigPerm]
      exact (Real.sqrt_ne_zero (hPSD.eigenvalues_nonneg i)).mpr hi
  exact le_of_eq h_bij

end SolEq21

open SolEq21

theorem solution {m n : ℕ} (r : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) (hX : X.rank ≤ r) :
    opNorm X ≤ frobeniusNorm X ∧ frobeniusNorm X ≤ nuclearNorm X ∧
      nuclearNorm X ≤ Real.sqrt r * frobeniusNorm X ∧
      Real.sqrt r * frobeniusNorm X ≤ r * opNorm X := by
  refine ⟨opNorm_le_frobeniusNorm X, frobeniusNorm_le_nuclearNorm X, ?_, ?_⟩
  · let S := Finset.univ.filter (fun j : Fin n => singularValues X j ≠ 0)
    have hS_card : (S.card : ℝ) ≤ r := by
      exact_mod_cast (card_support_singularValues_le_rank X).trans hX
    have h_nuc_S : nuclearNorm X = ∑ j ∈ S, 1 * singularValues X j := by
      rw [nuclearNorm]
      symm
      simpa using (Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
        exact hj))
    have h_frob_S : ∑ j : Fin n, (singularValues X j) ^ 2 = ∑ j ∈ S, (singularValues X j) ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ S) fun j _ hj => ?_
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
      rw [hj, sq, mul_zero]
    have h_cs : (nuclearNorm X) ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, (singularValues X j) ^ 2 := by
      rw [h_nuc_S]
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (singularValues X)
      simpa using h1
    have h_le : (nuclearNorm X) ^ 2 ≤ (Real.sqrt r * frobeniusNorm X) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r), frobeniusNorm_eq_sqrt_sum_singularValues_sq,
        Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _), h_frob_S]
      exact h_cs.trans (mul_le_mul_of_nonneg_right hS_card (Finset.sum_nonneg fun j _ => sq_nonneg _))
    have h_nonneg : 0 ≤ Real.sqrt r * frobeniusNorm X :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [abs_le_of_sq_le_sq' h_le h_nonneg]
  · let S := Finset.univ.filter (fun j : Fin n => singularValues X j ≠ 0)
    have hS_card : (S.card : ℝ) ≤ r := by
      exact_mod_cast (card_support_singularValues_le_rank X).trans hX
    have h_frob_S : ∑ j : Fin n, (singularValues X j) ^ 2 = ∑ j ∈ S, (singularValues X j) ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ S) fun j _ hj => ?_
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
      rw [hj, sq, mul_zero]
    have h_frob_le : ∑ j : Fin n, (singularValues X j) ^ 2 ≤ (r : ℝ) * (opNorm X) ^ 2 := by
      rw [h_frob_S]
      have h1 : ∑ j ∈ S, (singularValues X j) ^ 2 ≤ ∑ _j ∈ S, (opNorm X) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact pow_le_pow_left₀ (singularValues_nonneg X j) (singularValues_le_opNorm X j) 2
      have h2 : ∑ _j ∈ S, (opNorm X) ^ 2 = (S.card : ℝ) * (opNorm X) ^ 2 := by
        simp
      exact (h1.trans_eq h2).trans (mul_le_mul_of_nonneg_right hS_card (sq_nonneg _))
    have h_sqrt : frobeniusNorm X ≤ Real.sqrt r * opNorm X := by
      rw [frobeniusNorm_eq_sqrt_sum_singularValues_sq,
        ← Real.sqrt_sq (opNorm_nonneg X), ← Real.sqrt_mul (Nat.cast_nonneg r)]
      exact Real.sqrt_le_sqrt h_frob_le
    calc Real.sqrt r * frobeniusNorm X
      _ ≤ Real.sqrt r * (Real.sqrt r * opNorm X) :=
          mul_le_mul_of_nonneg_left h_sqrt (Real.sqrt_nonneg _)
      _ = (Real.sqrt r * Real.sqrt r) * opNorm X := by ring
      _ = r * opNorm X := by rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]

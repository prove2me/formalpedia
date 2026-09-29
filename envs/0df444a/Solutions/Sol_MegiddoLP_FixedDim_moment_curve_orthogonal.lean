-- Prove2me | solution 1 for MegiddoLP.FixedDim.moment_curve_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:07:16.43449+00:00
-- url     : https://prove2.me/submissions/4114cfa7-bcea-477e-b034-c67dce635094

import Mathlib

open Polynomial Matrix

theorem solution (n d : ℕ) (a : Fin n → Fin d → ℝ) (ha : ∀ i, a i ≠ 0) :
    {ε : ℝ | ∃ i, a i ⬝ᵥ (fun j : Fin d => ε ^ (j : ℕ)) = 0}.Finite ∧
    {ε : ℝ | ∃ i, a i ⬝ᵥ (fun j : Fin d => ε ^ (j : ℕ)) = 0}.ncard ≤ n * (d - 1) ∧
    ∃ M : Matrix (Fin d) (Fin d) ℝ, IsUnit M.det ∧
      ∀ i j, (M.transpose.mulVec (a i)) j ≠ 0 := by
  classical
  set P : Fin n → ℝ[X] := fun i => ∑ j : Fin d, C (a i j) * X ^ (j : ℕ) with hPdef
  have heval : ∀ (i : Fin n) (ε : ℝ),
      (P i).eval ε = a i ⬝ᵥ (fun j : Fin d => ε ^ (j : ℕ)) := by
    intro i ε
    rw [hPdef]
    simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, dotProduct]
  have hcoeff : ∀ (i : Fin n) (j0 : Fin d), (P i).coeff (j0 : ℕ) = a i j0 := by
    intro i j0
    rw [hPdef]
    simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single_of_mem j0 (Finset.mem_univ j0)]
    · simp
    · intro b _ hb
      have : ((j0 : ℕ) = (b : ℕ)) = False := by
        simp only [eq_iff_iff, iff_false]
        intro h
        exact hb (Fin.val_injective h).symm
      simp [this]
  have hPne : ∀ i, P i ≠ 0 := by
    intro i hzero
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp (ha i)
    have := hcoeff i j0
    rw [hzero] at this
    simp only [coeff_zero] at this
    exact hj0 this.symm
  have hdeg : ∀ i, (P i).natDegree ≤ d - 1 := by
    intro i
    rw [hPdef]
    refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X_pow]
    have := j.isLt
    omega
  set badF : Finset ℝ := Finset.univ.biUnion (fun i => (P i).roots.toFinset) with hbadF
  have hsetEq : {ε : ℝ | ∃ i, a i ⬝ᵥ (fun j : Fin d => ε ^ (j : ℕ)) = 0} = ↑badF := by
    ext ε
    simp only [Set.mem_setOf_eq, hbadF, Finset.coe_biUnion, Finset.coe_univ, Set.mem_iUnion,
      Set.mem_iUnion₂, Finset.mem_coe, Multiset.mem_toFinset]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Set.mem_univ i, (mem_roots (hPne i)).mpr (by rw [IsRoot, heval i ε]; exact hi)⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨i, by rw [← heval i ε]; exact (mem_roots (hPne i)).mp hi⟩
  have hcard : badF.card ≤ n * (d - 1) := by
    refine le_trans (Finset.card_biUnion_le) ?_
    calc ∑ i : Fin n, ((P i).roots.toFinset).card
        ≤ ∑ _i : Fin n, (d - 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact le_trans (Multiset.toFinset_card_le _) (le_trans (card_roots' (P i)) (hdeg i))
      _ = n * (d - 1) := by simp [Finset.sum_const, mul_comm]
  refine ⟨by rw [hsetEq]; exact badF.finite_toSet, ?_, ?_⟩
  · have hn : (↑badF : Set ℝ).ncard = badF.card := by
      rw [Set.ncard_def, Set.encard_coe_eq_coe_finsetCard]
      simp
    rw [hsetEq, hn]
    exact hcard
  · -- pick `d` distinct reals outside `badF`
    obtain ⟨T, hTsub, hTcard⟩ :=
      (Set.Finite.infinite_compl badF.finite_toSet).exists_subset_card_eq d
    set ε : Fin d → ℝ := fun k => ((T.equivFin.symm (finCongr hTcard.symm k) : ℝ)) with hεdef
    have hεmem : ∀ k, ε k ∉ badF := by
      intro k
      have h1 : (ε k) ∈ (↑T : Set ℝ) := (T.equivFin.symm (finCongr hTcard.symm k)).2
      have := hTsub h1
      simpa using this
    have hεinj : Function.Injective ε := by
      intro k l hkl
      have h1 : T.equivFin.symm (finCongr hTcard.symm k)
          = T.equivFin.symm (finCongr hTcard.symm l) := Subtype.ext hkl
      have h2 := T.equivFin.symm.injective h1
      exact (finCongr hTcard.symm).injective h2
    refine ⟨(Matrix.vandermonde ε)ᵀ, ?_, ?_⟩
    · rw [Matrix.det_transpose]
      refine isUnit_iff_ne_zero.mpr ?_
      intro hzero
      obtain ⟨i, j, hij, hne⟩ := Matrix.det_vandermonde_eq_zero_iff.mp hzero
      exact hne (hεinj hij)
    · intro i j
      rw [Matrix.transpose_transpose]
      have hval : (Matrix.vandermonde ε *ᵥ a i) j = (P i).eval (ε j) := by
        rw [heval i (ε j)]
        simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [hval]
      intro hzero
      have : ε j ∈ badF := by
        rw [hbadF]
        refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
        rw [Multiset.mem_toFinset]
        exact (mem_roots (hPne i)).mpr hzero
      exact hεmem j this

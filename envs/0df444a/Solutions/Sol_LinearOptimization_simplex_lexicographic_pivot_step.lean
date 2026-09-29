-- Prove2me | solution 1 for LinearOptimization.simplex_lexicographic_pivot_step
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T03:36:28.140893+00:00
-- url     : https://prove2.me/submissions/c945a3e6-51a4-4716-8ebf-25b3511ff249

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Matrix

private lemma lexLt_smul_pos {k : ℕ} {u v : Fin k → ℝ} {a : ℝ}
    (ha : 0 < a) (h : LinearOptimization.LexLt u v) :
    LinearOptimization.LexLt (a • u) (a • v) := by
  rcases h with ⟨i, hi, hpre⟩
  refine ⟨i, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_pos ha (sub_pos.mpr hi)]
  · intro q hq
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hpre q hq]

private lemma lexPos_smul_pos {k : ℕ} {u : Fin k → ℝ} {a : ℝ}
    (ha : 0 < a) (h : LinearOptimization.LexPos u) :
    LinearOptimization.LexPos (a • u) := by
  unfold LinearOptimization.LexPos at h ⊢
  simpa using lexLt_smul_pos ha h

private lemma lexPos_sub_of_lt {k : ℕ} {u v : Fin k → ℝ}
    (h : LinearOptimization.LexLt u v) :
    LinearOptimization.LexPos (v - u) := by
  rcases h with ⟨i, hi, hpre⟩
  refine ⟨i, ?_, ?_⟩
  · simp only [Pi.zero_apply, Pi.sub_apply]
    linarith
  · intro q hq
    simp only [Pi.zero_apply, Pi.sub_apply, hpre q hq, sub_self]

private lemma lexPos_add {k : ℕ} {u v : Fin k → ℝ}
    (hu : LinearOptimization.LexPos u) (hv : LinearOptimization.LexPos v) :
    LinearOptimization.LexPos (u + v) := by
  rcases hu with ⟨i, hi, hprei⟩
  rcases hv with ⟨j, hj, hprej⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · refine ⟨i, ?_, ?_⟩
    · have hvzero : v i = 0 := (hprej i hij).symm
      simpa [hvzero] using hi
    · intro q hqi
      have huzero : u q = 0 := (hprei q hqi).symm
      have hvzero : v q = 0 := (hprej q (lt_trans hqi hij)).symm
      simp [huzero, hvzero]
  · subst j
    refine ⟨i, ?_, ?_⟩
    · simp only [Pi.zero_apply] at hi hj
      simp only [Pi.zero_apply, Pi.add_apply]
      linarith
    · intro q hqi
      have huzero : u q = 0 := (hprei q hqi).symm
      have hvzero : v q = 0 := (hprej q hqi).symm
      simp [huzero, hvzero]
  · refine ⟨j, ?_, ?_⟩
    · have huzero : u j = 0 := (hprei j hij).symm
      simpa [huzero] using hj
    · intro q hqj
      have huzero : u q = 0 := (hprei q (lt_trans hqj hij)).symm
      have hvzero : v q = 0 := (hprej q hqj).symm
      simp [huzero, hvzero]

private lemma lexPos_add_nonneg_smul {k : ℕ} {u v : Fin k → ℝ} {a : ℝ}
    (hu : LinearOptimization.LexPos u) (hv : LinearOptimization.LexPos v)
    (ha : 0 ≤ a) : LinearOptimization.LexPos (u + a • v) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hu
  · exact lexPos_add hu (lexPos_smul_pos ha hv)

private lemma lexLt_add_of_pos {k : ℕ} (u : Fin k → ℝ) {v : Fin k → ℝ}
    (hv : LinearOptimization.LexPos v) :
    LinearOptimization.LexLt u (u + v) := by
  rcases hv with ⟨i, hi, hpre⟩
  refine ⟨i, ?_, ?_⟩
  · simp only [Pi.zero_apply] at hi
    simp only [Pi.add_apply]
    linarith
  · intro q hq
    have hvzero : v q = 0 := (hpre q hq).symm
    simp [hvzero]

private lemma inv_mulVec_basis_col {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n)
    [Invertible (LinearOptimization.basisMatrix A B)] (i : Fin m) :
    (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r (B i)) =
      Pi.single i 1 := by
  funext k
  have h : (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r (B i)) k =
      ((LinearOptimization.basisMatrix A B)⁻¹ *
        LinearOptimization.basisMatrix A B) k i := by
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct,
      LinearOptimization.basisMatrix]
  rw [h, Matrix.inv_mul_of_invertible]
  simp [Matrix.one_apply, Pi.single_apply]

private lemma replaced_sum_apply {m : ℕ} (g u : Fin m → ℝ) (ℓ i : Fin m) :
    (∑ k : Fin m, g k • (if k = ℓ then u else Pi.single k 1)) i =
      g ℓ * u i + if i = ℓ then 0 else g i := by
  classical
  by_cases hi : i = ℓ
  · subst i
    rw [Finset.sum_apply, Finset.sum_eq_single ℓ]
    · simp
    · intro k _ hk
      simp [hk, Ne.symm hk]
    · simp
  · rw [Finset.sum_apply, ← Finset.sum_erase_add Finset.univ
      (fun k => (g k • (if k = ℓ then u else Pi.single k 1)) i)
      (Finset.mem_univ ℓ)]
    have hi_mem : i ∈ Finset.univ.erase ℓ := by simp [hi]
    rw [Finset.sum_eq_single i]
    · simp [hi]
      ring
    · intro k hk hki
      have hkℓ : k ≠ ℓ := (Finset.mem_erase.mp hk).1
      simp [hkℓ, hki, Ne.symm hki]
    · intro hnot
      exact (hnot hi_mem).elim

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B B' : Fin m ↪ Fin n) (x x' : Fin n → ℝ)
    (hstate : LinearOptimization.IsSimplexState A b B x)
    (hpos : ∀ i, LinearOptimization.LexPos (LinearOptimization.tableauRow A b B i))
    (hpivot : LinearOptimization.IsLexicographicPivot A b c B x B' x') :
    (∀ i, LinearOptimization.LexPos (LinearOptimization.tableauRow A b B' i)) ∧
      LinearOptimization.LexLt (LinearOptimization.tableauZerothRow A b c B)
        (LinearOptimization.tableauZerothRow A b c B') := by
  classical
  rcases hpivot with ⟨j, ℓ, hpivot, hlex⟩
  rcases hpivot with ⟨hj, hcj, hℓ, hB'ne, hB'ℓ, hx'⟩
  have hB := hstate.1
  have hcols : LinearIndependent ℝ (LinearOptimization.basisMatrix A B).col := by
    exact hB
  letI : Invertible (LinearOptimization.basisMatrix A B) :=
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcols).invertible
  have hu_ne : LinearOptimization.pivotColumn A B j ℓ ≠ 0 := ne_of_gt hℓ
  have hnewcol : ∀ i : Fin m,
      (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r (B' i)) =
        if i = ℓ then LinearOptimization.pivotColumn A B j else Pi.single i 1 := by
    intro i
    by_cases hi : i = ℓ
    · subst i
      simp [hB'ℓ, LinearOptimization.pivotColumn]
    · rw [hB'ne i hi, inv_mulVec_basis_col]
      simp [hi]
  have hB' : LinearOptimization.IsStdBasis A B' := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    have htrans := congrArg
      ((LinearOptimization.basisMatrix A B)⁻¹.mulVec) hg
    have htrans' : ∑ k : Fin m,
        g k • ((LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r (B' k))) = 0 := by
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_zero] at htrans
      exact htrans
    have hell := congrFun htrans' ℓ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hell
    simp_rw [hnewcol] at hell
    have hell' : g ℓ * LinearOptimization.pivotColumn A B j ℓ = 0 := by
      calc
        _ = ∑ k : Fin m,
            g k * (if k = ℓ then LinearOptimization.pivotColumn A B j
              else Pi.single k 1) ℓ := by
              symm
              rw [Finset.sum_eq_single ℓ]
              · simp
              · intro k _ hk
                simp [hk, Ne.symm hk]
              · simp
        _ = 0 := hell
    have hgell : g ℓ = 0 := (mul_eq_zero.mp hell').resolve_right hu_ne
    by_cases hi : i = ℓ
    · simpa [hi] using hgell
    · have hirow := congrFun htrans' i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hirow
      simp_rw [hnewcol] at hirow
      calc
        g i = ∑ k : Fin m,
            g k * (if k = ℓ then LinearOptimization.pivotColumn A B j
              else Pi.single k 1) i := by
              symm
              rw [Finset.sum_eq_single i]
              · simp [hi]
              · intro k _ hki
                by_cases hkℓ : k = ℓ
                · subst k
                  simp [hgell]
                · simp [hkℓ, Ne.symm hki]
              · simp
        _ = 0 := hirow
  have hcols' : LinearIndependent ℝ (LinearOptimization.basisMatrix A B').col := by
    exact hB'
  letI : Invertible (LinearOptimization.basisMatrix A B') :=
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcols').invertible
  let oldSol : (Fin m → ℝ) → (Fin m → ℝ) := fun z =>
    (LinearOptimization.basisMatrix A B)⁻¹.mulVec z
  let newSol : (Fin m → ℝ) → (Fin m → ℝ) := fun z =>
    (LinearOptimization.basisMatrix A B')⁻¹.mulVec z
  have hnew_solve (z : Fin m → ℝ) :
      (LinearOptimization.basisMatrix A B').mulVec (newSol z) = z := by
    dsimp [newSol]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
    simp
  have hrel (z : Fin m → ℝ) :
      ∑ k : Fin m, (newSol z k) •
        (if k = ℓ then LinearOptimization.pivotColumn A B j else Pi.single k 1) =
      oldSol z := by
    calc
      _ = (LinearOptimization.basisMatrix A B)⁻¹.mulVec
          ((LinearOptimization.basisMatrix A B').mulVec (newSol z)) := by
        funext r
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [← hnewcol k]
        simp [Matrix.mulVec, dotProduct, LinearOptimization.basisMatrix]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = oldSol z := by rw [hnew_solve]
  have hnewSol_ell (z : Fin m → ℝ) :
      newSol z ℓ = oldSol z ℓ / LinearOptimization.pivotColumn A B j ℓ := by
    have hz := congrFun (hrel z) ℓ
    rw [replaced_sum_apply] at hz
    simp at hz
    apply (eq_div_iff hu_ne).2
    linarith
  have hnewSol_ne (z : Fin m → ℝ) (i : Fin m) (hi : i ≠ ℓ) :
      newSol z i = oldSol z i - LinearOptimization.pivotColumn A B j i *
        (oldSol z ℓ / LinearOptimization.pivotColumn A B j ℓ) := by
    have hz := congrFun (hrel z) i
    rw [replaced_sum_apply] at hz
    simp [hi] at hz
    rw [hnewSol_ell z] at hz
    linarith
  have hrow_old (i : Fin m) :
      LinearOptimization.tableauRow A b B i =
        Fin.cons (oldSol b i) (fun q => oldSol (fun r => A r q) i) := by
    funext q
    refine Fin.cases ?_ (fun q => ?_) q
    · rfl
    · simp [LinearOptimization.tableauRow, oldSol, Matrix.mul_apply,
        Matrix.mulVec, dotProduct]
  have hrow_new (i : Fin m) :
      LinearOptimization.tableauRow A b B' i =
        Fin.cons (newSol b i) (fun q => newSol (fun r => A r q) i) := by
    funext q
    refine Fin.cases ?_ (fun q => ?_) q
    · rfl
    · simp [LinearOptimization.tableauRow, newSol, Matrix.mul_apply,
        Matrix.mulVec, dotProduct]
  have hrow_ell :
      LinearOptimization.tableauRow A b B' ℓ =
        (LinearOptimization.pivotColumn A B j ℓ)⁻¹ •
          LinearOptimization.tableauRow A b B ℓ := by
    rw [hrow_old ℓ, hrow_new ℓ]
    funext q
    refine Fin.cases ?_ (fun q => ?_) q
    · simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, hnewSol_ell]
      field_simp
    · simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, hnewSol_ell]
      field_simp
  have hrow_ne (i : Fin m) (hi : i ≠ ℓ) :
      LinearOptimization.tableauRow A b B' i =
        LinearOptimization.tableauRow A b B i -
          (LinearOptimization.pivotColumn A B j i /
            LinearOptimization.pivotColumn A B j ℓ) •
              LinearOptimization.tableauRow A b B ℓ := by
    rw [hrow_old i, hrow_old ℓ, hrow_new i]
    funext q
    refine Fin.cases ?_ (fun q => ?_) q
    · simp only [Fin.cons_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hnewSol_ne b i hi]
      field_simp
    · simp only [Fin.cons_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hnewSol_ne (fun r => A r q) i hi]
      field_simp
  let costB : Fin m → ℝ := fun i => c (B i)
  let phiOld : (Fin m → ℝ) → ℝ := fun z => costB ⬝ᵥ oldSol z
  let phiNew : (Fin m → ℝ) → ℝ := fun z => (fun i => c (B' i)) ⬝ᵥ newSol z
  let qcoeff : Fin m → ℝ := fun k => costB ⬝ᵥ
    (if k = ℓ then LinearOptimization.pivotColumn A B j else Pi.single k 1)
  have hcoeff (k : Fin m) :
      c (B' k) = qcoeff k +
        if k = ℓ then LinearOptimization.reducedCost A c B j else 0 := by
    by_cases hk : k = ℓ
    · subst k
      simp [qcoeff, costB, hB'ℓ, LinearOptimization.reducedCost,
        LinearOptimization.pivotColumn]
    · simp [qcoeff, costB, hk, hB'ne k hk, dotProduct_single]
  have hqsum (z : Fin m → ℝ) :
      (∑ k : Fin m, newSol z k * qcoeff k) = phiOld z := by
    have hz := congrArg (fun v => costB ⬝ᵥ v) (hrel z)
    calc
      _ = costB ⬝ᵥ (∑ k : Fin m, newSol z k •
          (if k = ℓ then LinearOptimization.pivotColumn A B j else Pi.single k 1)) := by
        rw [dotProduct_sum]
        simp_rw [dotProduct_smul]
        rfl
      _ = costB ⬝ᵥ oldSol z := hz
      _ = phiOld z := rfl
  have hphi (z : Fin m → ℝ) :
      phiNew z = phiOld z + LinearOptimization.reducedCost A c B j *
        (oldSol z ℓ / LinearOptimization.pivotColumn A B j ℓ) := by
    dsimp [phiNew]
    simp only [dotProduct]
    conv_lhs =>
      enter [2, k]
      rw [hcoeff k]
    simp only [add_mul]
    rw [Finset.sum_add_distrib]
    have hdelta : (∑ k : Fin m,
        (if k = ℓ then LinearOptimization.reducedCost A c B j else 0) * newSol z k) =
        LinearOptimization.reducedCost A c B j * newSol z ℓ := by
      rw [Finset.sum_eq_single ℓ]
      · simp
      · intro k _ hk
        simp [hk]
      · simp
    have hqsum' : (∑ k : Fin m, qcoeff k * newSol z k) = phiOld z := by
      simpa [mul_comm] using hqsum z
    rw [hdelta, hqsum', hnewSol_ell]
  have hzeroRow :
      LinearOptimization.tableauZerothRow A b c B' =
        LinearOptimization.tableauZerothRow A b c B -
          (LinearOptimization.reducedCost A c B j /
            LinearOptimization.pivotColumn A B j ℓ) •
              LinearOptimization.tableauRow A b B ℓ := by
    rw [hrow_old ℓ]
    funext t
    refine Fin.cases ?_ (fun q => ?_) t
    · simp only [LinearOptimization.tableauZerothRow, Fin.cons_zero,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      change -phiNew b = -phiOld b -
        (LinearOptimization.reducedCost A c B j /
          LinearOptimization.pivotColumn A B j ℓ) * oldSol b ℓ
      rw [hphi]
      ring
    · simp only [LinearOptimization.tableauZerothRow, Fin.cons_succ,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      change c q - phiNew (fun r => A r q) =
        (c q - phiOld (fun r => A r q)) -
          (LinearOptimization.reducedCost A c B j /
            LinearOptimization.pivotColumn A B j ℓ) * oldSol (fun r => A r q) ℓ
      rw [hphi]
      ring
  constructor
  · intro i
    by_cases hi : i = ℓ
    · subst i
      rw [hrow_ell]
      exact lexPos_smul_pos (inv_pos.mpr hℓ) (hpos ℓ)
    · rw [hrow_ne i hi]
      by_cases hui : 0 < LinearOptimization.pivotColumn A B j i
      · have hs := lexLt_smul_pos hui (hlex i hui hi)
        have hs' : LinearOptimization.LexLt
            ((LinearOptimization.pivotColumn A B j i /
              LinearOptimization.pivotColumn A B j ℓ) •
                LinearOptimization.tableauRow A b B ℓ)
            (LinearOptimization.tableauRow A b B i) := by
          simpa [smul_smul, div_eq_mul_inv, (ne_of_gt hui)] using hs
        exact lexPos_sub_of_lt hs'
      · have hui_nonpos : LinearOptimization.pivotColumn A B j i ≤ 0 := le_of_not_gt hui
        have hcoef : 0 ≤ -(LinearOptimization.pivotColumn A B j i /
            LinearOptimization.pivotColumn A B j ℓ) := by
          exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hui_nonpos (le_of_lt hℓ))
        have heq : LinearOptimization.tableauRow A b B i -
              (LinearOptimization.pivotColumn A B j i /
                LinearOptimization.pivotColumn A B j ℓ) •
                  LinearOptimization.tableauRow A b B ℓ =
            LinearOptimization.tableauRow A b B i +
              (-(LinearOptimization.pivotColumn A B j i /
                LinearOptimization.pivotColumn A B j ℓ)) •
                  LinearOptimization.tableauRow A b B ℓ := by
          module
        rw [heq]
        exact lexPos_add_nonneg_smul (hpos i) (hpos ℓ) hcoef
  · rw [hzeroRow]
    let alpha : ℝ := -(LinearOptimization.reducedCost A c B j /
      LinearOptimization.pivotColumn A B j ℓ)
    have halpha : 0 < alpha := by
      dsimp [alpha]
      exact neg_pos.mpr (div_neg_of_neg_of_pos hcj hℓ)
    have heq : LinearOptimization.tableauZerothRow A b c B -
          (LinearOptimization.reducedCost A c B j /
            LinearOptimization.pivotColumn A B j ℓ) •
              LinearOptimization.tableauRow A b B ℓ =
        LinearOptimization.tableauZerothRow A b c B +
          alpha • LinearOptimization.tableauRow A b B ℓ := by
      dsimp [alpha]
      module
    rw [heq]
    exact lexLt_add_of_pos _ (lexPos_smul_pos halpha (hpos ℓ))

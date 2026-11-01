-- Prove2me | solution 1 for KeatingSnaith.cue_even_moment_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T12:43:57.113054+00:00
-- url     : https://prove2.me/submissions/a89d915b-221e-4a11-8bf1-d2f0771be363

import Mathlib
import Definitions.Def_keating_snaith_cue

set_option autoImplicit false

namespace KS7ff

open Matrix

section DJ

variable {K : Type*} [Field K]

/-- interior index of `Fin (m+2)` -/
def fI (m : ℕ) (i : Fin m) : Fin (m + 2) := i.succ.castSucc

/-- the two ends -/
def gE (m : ℕ) : Fin 2 → Fin (m + 2) := ![0, Fin.last (m + 1)]

noncomputable def schurEntry {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) K)
    (r c : Fin (m + 2)) : K :=
  M r c - ∑ i, ∑ j, M r (fI m i) * (M.submatrix (fI m) (fI m))⁻¹ i j * M (fI m j) c

lemma schur_apply_eq {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) K) {ι : Type*}
    (rr cc : ι → Fin (m + 2)) (x y : ι) :
    ((Matrix.of fun (x : ι) (y : ι) => M (rr x) (cc y)) -
        (Matrix.of fun (x : ι) (j : Fin m) => M (rr x) (fI m j)) *
          (M.submatrix (fI m) (fI m))⁻¹ * (Matrix.of fun (i : Fin m) (y : ι) => M (fI m i) (cc y))) x y
      = schurEntry M (rr x) (cc y) := by
  simp only [schurEntry, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma det_bordered {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) K)
    (hA : (M.submatrix (fI m) (fI m)).det ≠ 0) (r c : Fin (m + 2)) :
    (Matrix.of fun x y : Fin m ⊕ Unit =>
        M (Sum.elim (fI m) (fun _ => r) x) (Sum.elim (fI m) (fun _ => c) y)).det
      = (M.submatrix (fI m) (fI m)).det * schurEntry M r c := by
  have : Invertible (M.submatrix (fI m) (fI m)) :=
    invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hA)
  have hblk : (Matrix.of fun x y : Fin m ⊕ Unit =>
        M (Sum.elim (fI m) (fun _ => r) x) (Sum.elim (fI m) (fun _ => c) y))
      = fromBlocks (M.submatrix (fI m) (fI m)) (Matrix.of fun i (_ : Unit) => M (fI m i) c)
          (Matrix.of fun (_ : Unit) j => M r (fI m j)) (Matrix.of fun (_ : Unit) (_ : Unit) => M r c) := by
    ext (x | x) (y | y) <;> rfl
  rw [hblk, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 1
  rw [det_unique]
  exact schur_apply_eq M (fun _ => r) (fun _ => c) default default

lemma det_full {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) K)
    (hA : (M.submatrix (fI m) (fI m)).det ≠ 0) :
    (Matrix.of fun x y : Fin m ⊕ Fin 2 =>
        M (Sum.elim (fI m) (gE m) x) (Sum.elim (fI m) (gE m) y)).det
      = (M.submatrix (fI m) (fI m)).det *
          (schurEntry M 0 0 * schurEntry M (Fin.last _) (Fin.last _)
            - schurEntry M 0 (Fin.last _) * schurEntry M (Fin.last _) 0) := by
  have : Invertible (M.submatrix (fI m) (fI m)) :=
    invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hA)
  have hblk : (Matrix.of fun x y : Fin m ⊕ Fin 2 =>
        M (Sum.elim (fI m) (gE m) x) (Sum.elim (fI m) (gE m) y))
      = fromBlocks (M.submatrix (fI m) (fI m)) (Matrix.of fun i (y : Fin 2) => M (fI m i) (gE m y))
          (Matrix.of fun (x : Fin 2) j => M (gE m x) (fI m j))
          (Matrix.of fun (x : Fin 2) (y : Fin 2) => M (gE m x) (gE m y)) := by
    ext (x | x) (y | y) <;> rfl
  rw [hblk, det_fromBlocks₁₁, det_fin_two, invOf_eq_nonsing_inv]
  congr 1
  simp only [schur_apply_eq M (gE m) (gE m)]
  rfl

/-- `det (X.submatrix e₁ e₂) = sign · det X` -/
lemma det_submatrix_two {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) K) (e₁ e₂ : ι ≃ Fin n) :
    (X.submatrix e₁ e₂).det = (Equiv.Perm.sign (e₂.symm.trans e₁) : K) * X.det := by
  have h : X.submatrix e₁ e₂ = (X.submatrix (e₂.symm.trans e₁) id).submatrix e₂ e₂ := by
    ext x y; simp
  rw [h, det_submatrix_equiv_self, det_permute]

lemma fI_inj (m : ℕ) : Function.Injective (fI m) := by
  intro a b h
  simpa [fI] using h

noncomputable def E0 (m : ℕ) : Fin m ⊕ Fin 2 ≃ Fin (m + 2) :=
  Equiv.ofBijective (Sum.elim (fI m) (gE m)) <| by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp⟩
    rintro (a | a) (b | b) h
    · simp [fI_inj m h]
    all_goals
      first
      | (fin_cases a <;> fin_cases b <;> simp_all [fI, gE, Fin.ext_iff] <;> omega)
      | (fin_cases a <;> simp_all [fI, gE, Fin.ext_iff] <;> omega)
      | (fin_cases b <;> simp_all [fI, gE, Fin.ext_iff] <;> omega)

noncomputable def E1 (m : ℕ) : Fin m ⊕ Unit ≃ Fin (m + 1) :=
  Equiv.ofBijective (Sum.elim Fin.succ (fun _ => 0)) <| by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp⟩
    rintro (a | a) (b | b) h
    · simpa using h
    · exact absurd h (Fin.succ_ne_zero a)
    · exact absurd h.symm (Fin.succ_ne_zero b)
    · rfl

noncomputable def E2 (m : ℕ) : Fin m ⊕ Unit ≃ Fin (m + 1) :=
  Equiv.ofBijective (Sum.elim Fin.castSucc (fun _ => Fin.last m)) <| by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp⟩
    rintro (a | a) (b | b) h
    · simpa using h
    · exact absurd h (Fin.castSucc_ne_last a)
    · exact absurd h.symm (Fin.castSucc_ne_last b)
    · rfl

/-- Desnanot–Jacobi (Dodgson condensation), for a matrix whose interior minor is nonzero. -/
theorem desnanot_jacobi {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) K)
    (hA : (M.submatrix (fI m) (fI m)).det ≠ 0) :
    M.det * (M.submatrix (fI m) (fI m)).det
      = (M.submatrix Fin.castSucc Fin.castSucc).det * (M.submatrix Fin.succ Fin.succ).det
        - (M.submatrix Fin.castSucc Fin.succ).det * (M.submatrix Fin.succ Fin.castSucc).det := by
  have h0 : M.det = (Matrix.of fun x y : Fin m ⊕ Fin 2 =>
        M (Sum.elim (fI m) (gE m) x) (Sum.elim (fI m) (gE m) y)).det := by
    rw [← det_submatrix_equiv_self (E0 m) M]; rfl
  have h1 : (M.submatrix Fin.castSucc Fin.castSucc).det = (Matrix.of fun x y : Fin m ⊕ Unit =>
        M (Sum.elim (fI m) (fun _ => 0) x) (Sum.elim (fI m) (fun _ => 0) y)).det := by
    rw [← det_submatrix_equiv_self (E1 m)]
    congr 1; ext (x | x) (y | y) <;> simp [E1, fI]
  have h2 : (M.submatrix Fin.succ Fin.succ).det = (Matrix.of fun x y : Fin m ⊕ Unit =>
        M (Sum.elim (fI m) (fun _ => Fin.last _) x) (Sum.elim (fI m) (fun _ => Fin.last _) y)).det := by
    rw [← det_submatrix_equiv_self (E2 m)]
    congr 1; ext (x | x) (y | y) <;> simp [E2, fI]
  have h3 : (Matrix.of fun x y : Fin m ⊕ Unit =>
        M (Sum.elim (fI m) (fun _ => 0) x) (Sum.elim (fI m) (fun _ => Fin.last _) y)).det
      = (Equiv.Perm.sign ((E2 m).symm.trans (E1 m)) : K) * (M.submatrix Fin.castSucc Fin.succ).det := by
    rw [← det_submatrix_two]
    congr 1; ext (x | x) (y | y) <;> simp [E1, E2, fI]
  have h4 : (Matrix.of fun x y : Fin m ⊕ Unit =>
        M (Sum.elim (fI m) (fun _ => Fin.last _) x) (Sum.elim (fI m) (fun _ => 0) y)).det
      = (Equiv.Perm.sign ((E1 m).symm.trans (E2 m)) : K) * (M.submatrix Fin.succ Fin.castSucc).det := by
    rw [← det_submatrix_two]
    congr 1; ext (x | x) (y | y) <;> simp [E1, E2, fI]
  have hs : (Equiv.Perm.sign ((E1 m).symm.trans (E2 m)) : K)
      = (Equiv.Perm.sign ((E2 m).symm.trans (E1 m)) : K) := by
    rw [← Equiv.Perm.sign_symm]; rfl
  have hss : (Equiv.Perm.sign ((E2 m).symm.trans (E1 m)) : K)
      * (Equiv.Perm.sign ((E2 m).symm.trans (E1 m)) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  have b00 := det_bordered M hA 0 0
  have bll := det_bordered M hA (Fin.last _) (Fin.last _)
  have b0l := det_bordered M hA 0 (Fin.last _)
  have bl0 := det_bordered M hA (Fin.last _) 0
  have hf := det_full M hA
  rw [hs] at h4
  set s := (Equiv.Perm.sign ((E2 m).symm.trans (E1 m)) : K)
  have e3 : (M.submatrix Fin.castSucc Fin.succ).det * (M.submatrix Fin.succ Fin.castSucc).det
      = (s * (M.submatrix Fin.castSucc Fin.succ).det) * (s * (M.submatrix Fin.succ Fin.castSucc).det) := by
    linear_combination (-(M.submatrix Fin.castSucc Fin.succ).det * (M.submatrix Fin.succ Fin.castSucc).det) * hss
  rw [e3, ← h3, ← h4, h0, h1, h2, b00, bll, b0l, bl0, hf]
  ring

end DJ

section Toep

/-- the binomial Toeplitz matrix `[C(n, a+i-j)]` -/
noncomputable def bT (n a N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => if (j : ℕ) ≤ a + i then (Nat.choose n (a + i - j) : ℝ) else 0

/-- MacMahon's product -/
noncomputable def FF (N a b : ℕ) : ℝ :=
  ∏ j ∈ Finset.range N, ((Nat.factorial j : ℝ) * (Nat.factorial (a + b + j) : ℝ) /
    ((Nat.factorial (a + j) : ℝ) * (Nat.factorial (b + j) : ℝ)))

lemma FF_pos (N a b : ℕ) : 0 < FF N a b := by
  unfold FF
  apply Finset.prod_pos
  intro j _
  positivity

lemma bT_cc (n a m : ℕ) : (bT n a (m + 1)).submatrix Fin.castSucc Fin.castSucc = bT n a m := by
  ext i j; simp [bT]

lemma bT_ss (n a m : ℕ) : (bT n a (m + 1)).submatrix Fin.succ Fin.succ = bT n a m := by
  ext i j
  simp only [bT, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ]
  split_ifs with h1 h2 h2 <;> first | rfl | omega | (congr 2; omega)

lemma bT_int (n a m : ℕ) : (bT n a (m + 2)).submatrix (fI m) (fI m) = bT n a m := by
  ext i j
  simp only [bT, fI, Matrix.submatrix_apply, Matrix.of_apply, Fin.coe_castSucc, Fin.val_succ]
  split_ifs with h1 h2 h2 <;> first | rfl | omega | (congr 2; omega)

lemma bT_cs (n a m : ℕ) : (bT n (a + 1) (m + 1)).submatrix Fin.castSucc Fin.succ = bT n a m := by
  ext i j
  simp only [bT, Matrix.submatrix_apply, Matrix.of_apply, Fin.coe_castSucc, Fin.val_succ]
  split_ifs with h1 h2 h2 <;> first | rfl | omega | (congr 2; omega)

lemma bT_sc (n a m : ℕ) : (bT n a (m + 1)).submatrix Fin.succ Fin.castSucc = bT n (a + 1) m := by
  ext i j
  simp only [bT, Matrix.submatrix_apply, Matrix.of_apply, Fin.coe_castSucc, Fin.val_succ]
  split_ifs with h1 h2 h2 <;> first | rfl | omega | (congr 2; omega)

lemma det_bT_zero_left (b N : ℕ) : (bT (0 + b) 0 N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [bT]
  · intro i j hij
    have : (i : ℕ) < j := hij
    simp only [bT, Matrix.of_apply]
    rw [if_neg (by omega)]

lemma det_bT_zero_right (a N : ℕ) : (bT (a + 0) a N).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [bT]
  · intro i j hij
    have : (j : ℕ) < i := hij
    simp only [bT, Matrix.of_apply]
    split_ifs with h
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    · rfl

lemma FF_zero_left (N b : ℕ) : FF N 0 b = 1 := by
  unfold FF
  apply Finset.prod_eq_one
  intro j _
  rw [show 0 + b + j = b + j by omega, show 0 + j = j by omega]
  have h1 : (0 : ℝ) < (Nat.factorial j : ℝ) := by positivity
  have h2 : (0 : ℝ) < (Nat.factorial (b + j) : ℝ) := by positivity
  field_simp

lemma FF_zero_right (N a : ℕ) : FF N a 0 = 1 := by
  unfold FF
  apply Finset.prod_eq_one
  intro j _
  rw [show a + 0 + j = a + j by omega, show 0 + j = j by omega]
  have h1 : (0 : ℝ) < (Nat.factorial j : ℝ) := by positivity
  have h2 : (0 : ℝ) < (Nat.factorial (a + j) : ℝ) := by positivity
  field_simp

lemma det_bT_one (a b : ℕ) : (bT (a + b) a 1).det = FF 1 a b := by
  rw [Matrix.det_unique]
  simp only [bT, Matrix.of_apply, FF, Finset.prod_range_one]
  simp only [Fin.default_eq_zero, Fin.val_zero, Nat.zero_le, if_true, add_zero, Nat.sub_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul]
  rw [Nat.cast_choose ℝ (by omega : a ≤ a + b), show a + b - a = b by omega]

/-- one-step ratio of `FF` -/
lemma FF_succ (N a b : ℕ) : FF (N + 1) a b = FF N a b *
    ((Nat.factorial N : ℝ) * (Nat.factorial (a + b + N) : ℝ) /
      ((Nat.factorial (a + N) : ℝ) * (Nat.factorial (b + N) : ℝ))) := by
  unfold FF; rw [Finset.prod_range_succ]

lemma fact_succ' (x : ℕ) : (Nat.factorial (x + 1) : ℝ) = (x + 1 : ℝ) * (Nat.factorial x : ℝ) := by
  rw [Nat.factorial_succ]; push_cast; ring

/-- the telescoping product identity behind Dodgson's step -/
lemma FF_key (a b M : ℕ) :
    FF M a (b + 2) * FF M (a + 2) b * (((a : ℝ) + 1 + M) * ((b : ℝ) + 1 + M))
      = FF M (a + 1) (b + 1) ^ 2 * (((a : ℝ) + 1) * ((b : ℝ) + 1)) := by
  induction M with
  | zero => simp [FF]
  | succ M ih =>
    rw [FF_succ, FF_succ, FF_succ]
    rw [show a + (b + 2) + M = a + b + 2 + M by omega, show a + 2 + b + M = a + b + 2 + M by omega,
      show a + 1 + (b + 1) + M = a + b + 2 + M by omega]
    rw [show a + 2 + M = (a + M + 1) + 1 by omega, show b + 2 + M = (b + M + 1) + 1 by omega,
      show a + 1 + M = (a + M) + 1 by omega, show b + 1 + M = (b + M) + 1 by omega]
    rw [fact_succ' (a + M + 1), fact_succ' (b + M + 1), fact_succ' (a + M), fact_succ' (b + M)]
    have hA : (Nat.factorial (a + M) : ℝ) ≠ 0 := by positivity
    have hB : (Nat.factorial (b + M) : ℝ) ≠ 0 := by positivity
    have h1 : (a : ℝ) + M + 1 ≠ 0 := by positivity
    have h2 : (b : ℝ) + M + 1 ≠ 0 := by positivity
    have h3 : (a : ℝ) + M + 1 + 1 ≠ 0 := by positivity
    have h4 : (b : ℝ) + M + 1 + 1 ≠ 0 := by positivity
    push_cast
    linear_combination (norm := (field_simp; ring))
      ((Nat.factorial M : ℝ) * (Nat.factorial (a + b + 2 + M) : ℝ)) ^ 2 /
        ((Nat.factorial (a + M) : ℝ) ^ 2 * (Nat.factorial (b + M) : ℝ) ^ 2 *
          ((a : ℝ) + M + 1) ^ 2 * ((b : ℝ) + M + 1) ^ 2) * ih

lemma FF_dodgson (a b m : ℕ) :
    FF (m + 2) (a + 1) (b + 1) * FF m (a + 1) (b + 1)
      = FF (m + 1) (a + 1) (b + 1) ^ 2 - FF (m + 1) a (b + 2) * FF (m + 1) (a + 2) b := by
  have hk := FF_key a b (m + 1)
  have hP := FF_succ m (a + 1) (b + 1)
  have h2 := FF_succ (m + 1) (a + 1) (b + 1)
  have hD : ((a : ℝ) + 1 + ((m + 1 : ℕ) : ℝ)) * ((b : ℝ) + 1 + ((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hXY : FF (m + 1) a (b + 2) * FF (m + 1) (a + 2) b
      = FF (m + 1) (a + 1) (b + 1) ^ 2 * (((a : ℝ) + 1) * ((b : ℝ) + 1)) /
        (((a : ℝ) + 1 + ((m + 1 : ℕ) : ℝ)) * ((b : ℝ) + 1 + ((m + 1 : ℕ) : ℝ))) := by
    rw [eq_div_iff hD, hk]
  rw [hXY, h2, hP]
  rw [show a + 1 + (b + 1) + (m + 1) = (a + b + 2 + m) + 1 by omega,
    show a + 1 + (b + 1) + m = a + b + 2 + m by omega,
    show a + 1 + (m + 1) = (a + 1 + m) + 1 by omega, show b + 1 + (m + 1) = (b + 1 + m) + 1 by omega,
    fact_succ' (a + b + 2 + m), fact_succ' m, fact_succ' (a + 1 + m), fact_succ' (b + 1 + m)]
  have hA : (Nat.factorial (a + 1 + m) : ℝ) ≠ 0 := by positivity
  have hB : (Nat.factorial (b + 1 + m) : ℝ) ≠ 0 := by positivity
  have hM : (Nat.factorial m : ℝ) ≠ 0 := by positivity
  have h5 : (a : ℝ) + 1 + m + 1 ≠ 0 := by positivity
  have h6 : (b : ℝ) + 1 + m + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem toep_det (N : ℕ) : ∀ a b : ℕ, (bT (a + b) a N).det = FF N a b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a b
  rcases a with _ | a
  · rw [det_bT_zero_left, FF_zero_left]
  rcases b with _ | b
  · rw [det_bT_zero_right, FF_zero_right]
  match N, ih with
  | 0, _ => simp [FF]
  | 1, _ => exact det_bT_one _ _
  | m + 2, ih =>
    have hint := ih m (by omega) (a + 1) (b + 1)
    have h1 := ih (m + 1) (by omega) (a + 1) (b + 1)
    have hX : (bT (a + 1 + (b + 1)) a (m + 1)).det = FF (m + 1) a (b + 2) := by
      rw [show a + 1 + (b + 1) = a + (b + 2) by omega]; exact ih (m + 1) (by omega) a (b + 2)
    have hY : (bT (a + 1 + (b + 1)) (a + 1 + 1) (m + 1)).det = FF (m + 1) (a + 2) b := by
      rw [show a + 1 + (b + 1) = (a + 2) + b by omega]; exact ih (m + 1) (by omega) (a + 2) b
    have hA : ((bT (a + 1 + (b + 1)) (a + 1) (m + 2)).submatrix (fI m) (fI m)).det ≠ 0 := by
      rw [bT_int, hint]; exact (FF_pos _ _ _).ne'
    have hdj := desnanot_jacobi (bT (a + 1 + (b + 1)) (a + 1) (m + 2)) hA
    rw [bT_int, bT_cc, bT_ss, bT_cs, bT_sc, hint, h1, hX, hY, ← sq, ← FF_dodgson] at hdj
    exact mul_right_cancel₀ (FF_pos m (a + 1) (b + 1)).ne' hdj

theorem toep_det_kk (N k : ℕ) : (bT (2 * k) k N).det
    = ∏ j ∈ Finset.range N, (Nat.factorial j : ℝ) * (Nat.factorial (2 * k + j) : ℝ) /
        (Nat.factorial (j + k) : ℝ) ^ 2 := by
  rw [show 2 * k = k + k by ring, toep_det]
  unfold FF
  apply Finset.prod_congr rfl
  intro j _
  rw [show k + j = j + k by ring, sq]

end Toep

section Heine

open MeasureTheory Finset KeatingSnaith
open scoped Real ComplexConjugate

/-- the Andreief basis functions `(-e^{it})^i (1-e^{it})^k` -/
noncomputable def fb (k i : ℕ) (t : ℝ) : ℂ :=
  (-Complex.exp (t * Complex.I)) ^ i * (1 - Complex.exp (t * Complex.I)) ^ k

lemma integral_exp_pow (p q : ℕ) :
    ∫ t in Set.Ioc 0 (2 * π), Complex.exp (t * Complex.I) ^ p * Complex.exp (-(t * Complex.I)) ^ q
      = if p = q then (2 * π : ℂ) else 0 := by
  have h : ∀ t : ℝ, Complex.exp (t * Complex.I) ^ p * Complex.exp (-(t * Complex.I)) ^ q
      = Complex.exp (((p : ℂ) - q) * Complex.I * t) := by
    intro t
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; ring
  simp_rw [h]
  rw [← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hpq
  · subst hpq; simp
  · have hc : ((p : ℂ) - q) * Complex.I ≠ 0 := by
      apply mul_ne_zero _ Complex.I_ne_zero
      rw [sub_ne_zero]; exact_mod_cast hpq
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (((p : ℂ) - q) * Complex.I * ↑(2 * π)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I ((p : ℤ) - q)
      rw [← this]; congr 1; push_cast; ring
    rw [h1]; simp

lemma fb_mul_conj (k a b : ℕ) (t : ℝ) :
    fb k a t * conj (fb k b t) = ∑ r ∈ Finset.range (2 * k + 1),
      ((-1 : ℂ) ^ (a + b + k + r) * (Nat.choose (2 * k) r : ℂ)) *
        (Complex.exp (t * Complex.I) ^ (a + r) * Complex.exp (-(t * Complex.I)) ^ (b + k)) := by
  set e := Complex.exp (t * Complex.I) with he
  set w := Complex.exp (-(t * Complex.I)) with hw
  have hew : e * w = 1 := by rw [he, hw, ← Complex.exp_add]; simp
  have hc : conj e = w := by
    rw [he, hw, ← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  have h1w : 1 - w = -(1 - e) * w := by linear_combination (-1 : ℂ) * hew
  have hbin : (1 - e) ^ (2 * k) = ∑ r ∈ Finset.range (2 * k + 1),
      (-1 : ℂ) ^ r * (Nat.choose (2 * k) r : ℂ) * e ^ r := by
    rw [show (1 : ℂ) - e = -e + 1 by ring, add_pow]
    apply Finset.sum_congr rfl
    intro r _
    rw [neg_pow]; ring
  have key : fb k a t * conj (fb k b t)
      = (-1 : ℂ) ^ (a + b + k) * e ^ a * w ^ (b + k) * (1 - e) ^ (2 * k) := by
    unfold fb
    rw [← he]
    simp only [map_mul, map_pow, map_neg, map_sub, map_one, hc]
    rw [h1w, neg_pow e, neg_pow w, mul_pow, neg_pow (1 - e)]
    ring
  rw [key, hbin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma gram_entry (k a b : ℕ) :
    ∫ t in Set.Ioc 0 (2 * π), fb k a t * conj (fb k b t)
      = (2 * π : ℂ) * (if a ≤ k + b then (Nat.choose (2 * k) (k + b - a) : ℂ) else 0) := by
  simp_rw [fb_mul_conj]
  rw [integral_finset_sum]
  swap
  · intro r _
    exact Continuous.integrableOn_Ioc (by fun_prop)
  simp_rw [integral_const_mul, integral_exp_pow]
  split_ifs with hab
  · rw [Finset.sum_eq_single (k + b - a)]
    · rw [if_pos (by omega), show a + b + k + (k + b - a) = 2 * (b + k) by omega, pow_mul]
      simp; ring
    · intro r _ hr
      rw [if_neg (by omega), mul_zero]
    · intro hr
      simp only [Finset.mem_range, not_lt] at hr
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · rw [mul_zero]
    apply Finset.sum_eq_zero
    intro r _
    rw [if_neg (by omega), mul_zero]

lemma andreief_sum {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) :
    ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, G (σ j) (τ j)
      = (Nat.factorial N : ℂ) * G.det := by
  have inner : ∀ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, G (σ j) (τ j) = G.det := by
    intro σ
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rw [← Equiv.sum_comp (Equiv.mulRight σ)]
    apply Finset.sum_congr rfl
    intro ρ _
    simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, Matrix.transpose_apply]
    have hp : ∏ j, G (σ j) ((ρ * σ) j) = ∏ i, G i (ρ i) := by
      rw [← Equiv.prod_comp σ (fun i => G i (ρ i))]
      rfl
    rw [hp]
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    linear_combination ((Equiv.Perm.sign ρ : ℤ) : ℂ) * (∏ i, G i (ρ i)) * hs
  simp_rw [inner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- the Andreief matrix -/
noncomputable def Vm (k N : ℕ) (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => fb k i (θ j)

lemma det_Vm (k N : ℕ) (θ : Fin N → ℝ) :
    (Vm k N θ).det = (∏ i, ∏ j ∈ Finset.Ioi i,
        (Complex.exp (θ i * Complex.I) - Complex.exp (θ j * Complex.I))) *
      ∏ j, (1 - Complex.exp (θ j * Complex.I)) ^ k := by
  have h : Vm k N θ = (Matrix.vandermonde fun j => -Complex.exp (θ j * Complex.I))ᵀ *
      Matrix.diagonal (fun j => (1 - Complex.exp (θ j * Complex.I)) ^ k) := by
    ext i j
    simp [Vm, fb, Matrix.mul_diagonal, Matrix.vandermonde_apply]
  rw [h, Matrix.det_mul, Matrix.det_transpose, Matrix.det_vandermonde, Matrix.det_diagonal]
  congr 1
  apply Finset.prod_congr rfl; intro i _
  apply Finset.prod_congr rfl; intro j _
  ring

lemma prod_filter_lt {N : ℕ} (g : Fin N → Fin N → ℝ) :
    ∏ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), g p.1 p.2
      = ∏ i, ∏ j ∈ Finset.Ioi i, g i j := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro i _
  rw [← Finset.prod_filter]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext j; simp

lemma density_eq (k N : ℕ) (θ : Fin N → ℝ) :
    cueDensity N θ * ‖charPoly N θ‖ ^ (2 * k) = ‖(Vm k N θ).det‖ ^ 2 := by
  rw [det_Vm, norm_mul, mul_pow]
  have hc : cueDensity N θ = ∏ i, ∏ j ∈ Finset.Ioi i,
      ‖Complex.exp (θ i * Complex.I) - Complex.exp (θ j * Complex.I)‖ ^ 2 :=
    prod_filter_lt (fun i j => ‖Complex.exp (θ i * Complex.I) - Complex.exp (θ j * Complex.I)‖ ^ 2)
  rw [hc]
  unfold charPoly
  congr 1
  · rw [norm_prod, ← Finset.prod_pow]
    apply Finset.prod_congr rfl; intro i _
    rw [norm_prod, ← Finset.prod_pow]
  · rw [norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow]
    apply Finset.prod_congr rfl; intro j _
    rw [norm_pow, ← pow_mul, mul_comm k 2]

lemma vol_phaseBox (N : ℕ) : (volume : Measure (Fin N → ℝ)).restrict (phaseBox N)
    = Measure.pi (fun _ : Fin N => (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π))) := by
  rw [phaseBox, MeasureTheory.volume_pi, Measure.restrict_pi_pi]

lemma integral_density (k N : ℕ) :
    ((∫ θ in phaseBox N, cueDensity N θ * ‖charPoly N θ‖ ^ (2 * k) : ℝ) : ℂ)
      = (Nat.factorial N : ℂ) * (2 * π : ℂ) ^ N * (((bT (2 * k) k N).det : ℝ) : ℂ) := by
  simp_rw [density_eq]
  rw [← integral_complex_ofReal, vol_phaseBox]
  have hpt : ∀ θ : Fin N → ℝ, (((‖(Vm k N θ).det‖ ^ 2 : ℝ)) : ℂ)
      = ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
          ∏ j, (fb k (σ j) (θ j) * conj (fb k (τ j) (θ j))) := by
    intro θ
    push_cast
    rw [← Complex.mul_conj', (starRingEnd ℂ).map_det, Matrix.det_apply', Matrix.det_apply',
      Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro σ _
    apply Finset.sum_congr rfl; intro τ _
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Vm, Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  simp_rw [hpt]
  have hint : ∀ σ τ : Equiv.Perm (Fin N), Integrable (fun θ : Fin N → ℝ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        ∏ j, (fb k (σ j) (θ j) * conj (fb k (τ j) (θ j))))
      (Measure.pi (fun _ : Fin N => (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π)))) := by
    intro σ τ
    apply Integrable.const_mul
    apply Integrable.fintype_prod (f := fun j t => fb k (σ j) t * conj (fb k (τ j) t))
    intro j
    exact Continuous.integrableOn_Ioc (by unfold fb; fun_prop)
  rw [integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => hint σ τ))]
  simp_rw [integral_finset_sum _ (fun τ _ => hint _ τ)]
  simp_rw [integral_const_mul]
  have hprod : ∀ σ τ : Equiv.Perm (Fin N),
      ∫ θ : Fin N → ℝ, ∏ j, (fb k (σ j) (θ j) * conj (fb k (τ j) (θ j)))
        ∂(Measure.pi (fun _ : Fin N => (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π))))
      = ∏ j, (Matrix.of fun a b : Fin N => ∫ t in Set.Ioc 0 (2 * π), fb k a t * conj (fb k b t))
          (σ j) (τ j) := by
    intro σ τ
    rw [integral_fintype_prod_eq_prod (f := fun j t => fb k (σ j) t * conj (fb k (τ j) t))]
    rfl
  simp_rw [hprod]
  rw [andreief_sum]
  have hG : (Matrix.of fun a b : Fin N => ∫ t in Set.Ioc 0 (2 * π), fb k a t * conj (fb k b t))
      = (2 * π : ℂ) • ((bT (2 * k) k N).map (fun x : ℝ => (x : ℂ)))ᵀ := by
    ext a b
    simp only [Matrix.of_apply, gram_entry, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.map_apply, bT, smul_eq_mul]
    congr 1
    split_ifs <;> simp
  rw [hG, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  have hmap : ((bT (2 * k) k N).map (fun x : ℝ => (x : ℂ))).det = (((bT (2 * k) k N).det : ℝ) : ℂ) := by
    exact (Complex.ofRealHom.map_det (bT (2 * k) k N)).symm
  rw [hmap]; ring

theorem cue_even_moment_main (N k : ℕ) :
    cueAverage N (fun θ => ‖charPoly N θ‖ ^ (2 * k))
      = ∏ j ∈ Finset.range N,
          (Nat.factorial j : ℝ) * (Nat.factorial (2 * k + j) : ℝ) /
            (Nat.factorial (j + k) : ℝ) ^ 2 := by
  rw [← toep_det_kk]
  unfold cueAverage
  simp only [smul_eq_mul]
  have h := integral_density k N
  have h2 : (∫ θ in phaseBox N, cueDensity N θ * ‖charPoly N θ‖ ^ (2 * k))
      = (Nat.factorial N : ℝ) * (2 * π) ^ N * (bT (2 * k) k N).det := by
    exact_mod_cast h
  rw [h2]
  have hpos : (0 : ℝ) < (Nat.factorial N : ℝ) * (2 * π) ^ N := by positivity
  field_simp

end Heine

section Asym

open Finset Filter Topology

lemma asc (c n : ℕ) : ((c + n).factorial : ℝ) = (c.factorial : ℝ) * ∏ j ∈ range n, ((c : ℝ) + 1 + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [← add_assoc, fact_succ', ih, prod_range_succ]; push_cast; ring

lemma closed_form (N k : ℕ) :
    ∏ j ∈ range N, (Nat.factorial j : ℝ) * (Nat.factorial (2 * k + j) : ℝ) /
        (Nat.factorial (j + k) : ℝ) ^ 2
      = ∏ i ∈ range k, ((Nat.factorial i : ℝ) / (Nat.factorial (i + k) : ℝ) *
          ∏ j ∈ range k, ((i : ℝ) + N + 1 + j)) := by
  have h1 : ∀ j : ℕ, (Nat.factorial j : ℝ) * (Nat.factorial (2 * k + j) : ℝ) /
      (Nat.factorial (j + k) : ℝ) ^ 2 = ∏ i ∈ range k, (((j : ℝ) + k + 1 + i) / ((j : ℝ) + 1 + i)) := by
    intro j
    rw [show 2 * k + j = (j + k) + k by ring, asc (j + k) k, asc j k, prod_div_distrib]
    have hp : ∏ i ∈ range k, ((j : ℝ) + 1 + i) ≠ 0 :=
      prod_ne_zero_iff.mpr (fun i _ => by positivity)
    have hj : (Nat.factorial j : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [prod_congr rfl (fun j _ => h1 j), Finset.prod_comm]
  apply prod_congr rfl
  intro i _
  rw [prod_div_distrib]
  have F1 : (Nat.factorial (i + k + N) : ℝ) = (Nat.factorial (i + k) : ℝ) *
      ∏ j ∈ range N, ((j : ℝ) + k + 1 + i) := by
    rw [asc (i + k) N]; congr 1; apply prod_congr rfl; intro j _; push_cast; ring
  have F2 : (Nat.factorial (i + N) : ℝ) = (Nat.factorial i : ℝ) *
      ∏ j ∈ range N, ((j : ℝ) + 1 + i) := by
    rw [asc i N]; congr 1; apply prod_congr rfl; intro j _; ring
  have F3 : (Nat.factorial (i + N + k) : ℝ) = (Nat.factorial (i + N) : ℝ) *
      ∏ j ∈ range k, ((i : ℝ) + N + 1 + j) := by
    rw [asc (i + N) k]; congr 1; apply prod_congr rfl; intro j _; push_cast; ring
  rw [show i + N + k = i + k + N by ring] at F3
  have hB : ∏ j ∈ range N, ((j : ℝ) + 1 + i) ≠ 0 := prod_ne_zero_iff.mpr (fun j _ => by positivity)
  have hk : (Nat.factorial (i + k) : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hB, div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hk]
  linear_combination F3 - F1 + (∏ j ∈ range k, ((i : ℝ) + N + 1 + j)) * F2

theorem asym (k : ℕ) :
    Tendsto (fun N : ℕ => (∏ j ∈ range N, (Nat.factorial j : ℝ) * (Nat.factorial (2 * k + j) : ℝ) /
        (Nat.factorial (j + k) : ℝ) ^ 2) / (N : ℝ) ^ (k ^ 2))
      atTop (𝓝 (∏ j ∈ range k, (Nat.factorial j : ℝ) / (Nat.factorial (k + j) : ℝ))) := by
  have hev : ∀ᶠ N : ℕ in atTop,
      ∏ i ∈ range k, ((Nat.factorial i : ℝ) / (Nat.factorial (i + k) : ℝ) *
          ∏ j ∈ range k, (1 + ((i : ℝ) + 1 + j) / N))
        = (∏ j ∈ range N, (Nat.factorial j : ℝ) * (Nat.factorial (2 * k + j) : ℝ) /
            (Nat.factorial (j + k) : ℝ) ^ 2) / (N : ℝ) ^ (k ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [closed_form, show (N : ℝ) ^ (k ^ 2) = ∏ i ∈ range k, ∏ j ∈ range k, (N : ℝ) by
      simp [prod_const, card_range, ← pow_mul, sq]]
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro i _
    rw [mul_div_assoc, ← prod_div_distrib]
    congr 1
    apply prod_congr rfl
    intro j _
    field_simp
    ring
  refine Tendsto.congr' hev ?_
  have hL : ∏ j ∈ range k, (Nat.factorial j : ℝ) / (Nat.factorial (k + j) : ℝ)
      = ∏ i ∈ range k, ((Nat.factorial i : ℝ) / (Nat.factorial (i + k) : ℝ) *
          ∏ j ∈ range k, ((1 : ℝ) + 0)) := by
    apply prod_congr rfl; intro i _; simp [add_comm]
  rw [hL]
  apply tendsto_finset_prod
  intro i _
  apply Tendsto.const_mul
  apply tendsto_finset_prod
  intro j _
  exact tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)

end Asym

end KS7ff

open KeatingSnaith Finset MeasureTheory Filter Topology Real in
theorem solution (k : ℕ) :
    Tendsto (fun N : ℕ => cueAverage N (fun θ => ‖charPoly N θ‖ ^ (2 * k)) / (N : ℝ) ^ (k ^ 2))
      atTop (𝓝 (∏ j ∈ Finset.range k,
        (Nat.factorial j : ℝ) / (Nat.factorial (k + j) : ℝ))) := by
  have h : (fun N : ℕ => cueAverage N (fun θ => ‖charPoly N θ‖ ^ (2 * k)) / (N : ℝ) ^ (k ^ 2))
      = fun N : ℕ => (∏ j ∈ Finset.range N, (Nat.factorial j : ℝ) * (Nat.factorial (2 * k + j) : ℝ) /
          (Nat.factorial (j + k) : ℝ) ^ 2) / (N : ℝ) ^ (k ^ 2) := by
    funext N
    rw [KS7ff.cue_even_moment_main]
  rw [h]
  exact KS7ff.asym k

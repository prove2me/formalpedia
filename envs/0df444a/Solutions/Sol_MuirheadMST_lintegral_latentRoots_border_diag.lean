-- Prove2me | solution 1 for MuirheadMST.lintegral_latentRoots_border_diag
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:24:38.807486+00:00
-- url     : https://prove2.me/submissions/0535892c-9880-49a2-8310-d1728e591812

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory Polynomial

/-!
Secular-equation change of variables (Anderson). For `μ₀ > ⋯ > μ_{m-1}`, the latent roots `l` of the
arrow matrix `[[c, bᵀ], [b, diag μ]]` are the roots of the secular polynomial
`(X - c) ∏ (X - μ_i) - ∑ b_i² ∏_{k≠i} (X - μ_k)`; they interlace `μ`, and `(b_i², c)` is recovered from `l`
by `qOf`, `cOf`. On each sign orthant of `b` the inverse map `l ↦ (c, σ_i √(qOf μ l i))` is a
diffeomorphism from the interlacing region, with Jacobian `2^{-m} V(l) ∏ |μ_i - l_j|^{-1/2}`.
-/

namespace MuirheadMST


/-- The latent roots of a symmetric array are its sorted eigenvalues; the characteristic polynomial
factors over them. -/
lemma latentRoots_spec {n : ℕ} (A : Fin n → Fin n → ℝ) (hA : (Matrix.of A).IsHermitian) :
    Antitone (latentRoots A) ∧ (Matrix.of A).charpoly = ∏ j, (X - C (latentRoots A j)) := by
  unfold latentRoots
  rw [dif_pos hA]
  refine ⟨fun i j hij => hA.eigenvalues₀_antitone (by simpa using hij), ?_⟩
  rw [hA.charpoly_eq]
  simp only [Matrix.IsHermitian.eigenvalues, RCLike.ofReal_real_eq_id, id]
  exact ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm.prod_comp
    (fun k => X - C (hA.eigenvalues₀ k))).trans
    ((finCongr (Fintype.card_fin n).symm).prod_comp (fun k => X - C (hA.eigenvalues₀ k))).symm

/-- A symmetric array whose characteristic polynomial is `∏ (X - l j)` with `l` antitone has latent
roots `l`. -/
lemma latentRoots_eq_of_charpoly {n : ℕ} (A : Fin n → Fin n → ℝ) (hA : (Matrix.of A).IsHermitian)
    (l : Fin n → ℝ) (hl : Antitone l) (hc : (Matrix.of A).charpoly = ∏ j, (X - C (l j))) :
    latentRoots A = l := by
  obtain ⟨h1, h2⟩ := latentRoots_spec A hA
  have hr := congrArg Polynomial.roots (h2.symm.trans hc)
  have key : ∀ f : Fin n → ℝ, Antitone f →
      ((∏ j, (X - C (f j))).roots).sort (· ≥ ·) = List.ofFn f := by
    intro f hf
    have : (∏ j, (X - C (f j)) : ℝ[X]) = ((Finset.univ.val.map f).map fun a => X - C a).prod := by
      simp [Multiset.map_map, Finset.prod_eq_multiset_prod, Function.comp_def]
    rw [this, roots_multiset_prod_X_sub_C, Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hf.sortedGE_ofFn
  have := (key _ h1).symm.trans ((congrArg _ hr).trans (key _ hl))
  exact List.ofFn_injective this



/-- The arrow array `[[y₀, y₁ … y_m], [y_{i+1}, diag μ]]`. -/
def arrowMat {m : ℕ} (μ : Fin m → ℝ) (y : Fin (m + 1) → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  Fin.cons y (fun i => Fin.cons (y i.succ) (diagArray μ i))

/-- The secular polynomial `(X - c) ∏ (X - μ_i) - ∑ q_i ∏_{k ≠ i} (X - μ_k)`. -/
noncomputable def secPoly {m : ℕ} (μ : Fin m → ℝ) (q : Fin m → ℝ) (c : ℝ) : ℝ[X] :=
  (X - C c) * ∏ i, (X - C (μ i)) - ∑ i, C (q i) * ∏ k ∈ Finset.univ.erase i, (X - C (μ k))

lemma arrowMat_isHermitian {m : ℕ} (μ : Fin m → ℝ) (y : Fin (m + 1) → ℝ) :
    (Matrix.of (arrowMat μ y)).IsHermitian := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [arrowMat, diagArray, eq_comm]; split_ifs <;> simp_all

lemma prod_succAbove_eq_prod_erase {n : ℕ} (f : Fin (n + 1) → ℝ[X]) (i : Fin (n + 1)) :
    ∏ r, f (i.succAbove r) = ∏ k ∈ Finset.univ.erase i, f k := by
  rw [← Finset.prod_image (fun a _ b _ h => Fin.succAbove_right_injective h)]
  congr 1
  ext k
  simp [eq_comm (b := k), Fin.exists_succAbove_eq_iff]

lemma arrow_minor_det {n : ℕ} (μ : Fin (n + 1) → ℝ) (y : Fin (n + 2) → ℝ) (i : Fin (n + 1)) :
    ((Matrix.charmatrix (Matrix.of (arrowMat μ y))).submatrix Fin.succ i.succ.succAbove).det =
      (-1) ^ (i : ℕ) * (-C (y i.succ)) * ∏ k ∈ Finset.univ.erase i, (X - C (μ k)) := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single i]
  · congr 1
    · simp [Matrix.charmatrix_apply, arrowMat, Fin.succAbove_of_castSucc_lt, Fin.castSucc_zero]
    · have : ((Matrix.charmatrix (Matrix.of (arrowMat μ y))).submatrix Fin.succ i.succ.succAbove).submatrix
          i.succAbove Fin.succ = Matrix.diagonal (fun r => X - C (μ (i.succAbove r))) := by
        refine Matrix.ext fun r s => ?_
        simp [Matrix.charmatrix_apply, arrowMat, diagArray, Matrix.diagonal, Fin.succ_succAbove_succ]
        split_ifs <;> simp_all
      rw [this, Matrix.det_diagonal]
      exact prod_succAbove_eq_prod_erase (fun k => X - C (μ k)) i
  · intro a _ hai
    obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hai.symm
    rw [Matrix.det_eq_zero_of_row_eq_zero r, mul_zero]
    intro s
    simp [Matrix.charmatrix_apply, arrowMat, diagArray, Matrix.diagonal, Fin.succ_succAbove_succ, hr,
      Fin.ne_succAbove i s]
  · simp

/-- Characteristic polynomial of the arrow array: the secular polynomial with `q_i = y_{i+1}²`. -/
lemma charpoly_arrowMat {m : ℕ} (μ : Fin m → ℝ) (y : Fin (m + 1) → ℝ) :
    (Matrix.of (arrowMat μ y)).charpoly = secPoly μ (fun i => y i.succ ^ 2) (y 0) := by
  cases m with
  | zero =>
    simp [Matrix.charpoly, Matrix.det_unique, secPoly, Matrix.charmatrix_apply, arrowMat]
  | succ n =>
    rw [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, secPoly, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    · have : (Matrix.charmatrix (Matrix.of (arrowMat μ y))).submatrix Fin.succ (Fin.succAbove 0) =
          Matrix.diagonal (fun r => X - C (μ r)) := by
        refine Matrix.ext fun r s => ?_
        simp [Matrix.charmatrix_apply, arrowMat, diagArray, Matrix.diagonal]
        split_ifs <;> simp_all
      rw [this, Matrix.det_diagonal]
      simp [Matrix.charmatrix_apply, arrowMat]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [arrow_minor_det]
      have h1 : ((-1 : ℝ[X]) ^ (i : ℕ)) * ((-1) ^ (i : ℕ)) = 1 := by rw [← mul_pow]; simp
      simp only [Fin.val_succ, map_pow]
      have h0 : Matrix.charmatrix (Matrix.of (arrowMat μ y)) 0 i.succ = -C (y i.succ) := by
        simp [Matrix.charmatrix_apply, arrowMat, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero i).symm]
      rw [h0]
      linear_combination (-(C (y i.succ)) ^ 2 * ∏ k ∈ Finset.univ.erase i, (X - C (μ k))) * h1



/-- `∏_{k ≠ i} (μ_i - μ_k)`. -/
noncomputable def dOf {m : ℕ} (μ : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∏ k ∈ Finset.univ.erase i, (μ i - μ k)

/-- The border entry `c` recovered from the roots: `c = ∑ l_j - ∑ μ_i`. -/
noncomputable def cOf {m : ℕ} (μ : Fin m → ℝ) (l : Fin (m + 1) → ℝ) : ℝ :=
  ∑ j, l j - ∑ i, μ i

/-- The squared border entries recovered from the roots: `q_i = -∏_j (μ_i - l_j) / ∏_{k≠i} (μ_i - μ_k)`. -/
noncomputable def qOf {m : ℕ} (μ : Fin m → ℝ) (l : Fin (m + 1) → ℝ) (i : Fin m) : ℝ :=
  -(∏ j, (μ i - l j)) / dOf μ i

lemma dOf_ne_zero {m : ℕ} {μ : Fin m → ℝ} (hμ : Function.Injective μ) (i : Fin m) : dOf μ i ≠ 0 := by
  rw [dOf, Finset.prod_ne_zero_iff]
  intro k hk
  exact sub_ne_zero.2 (hμ.ne (Finset.ne_of_mem_erase hk).symm)

lemma eval_secPoly {m : ℕ} (μ : Fin m → ℝ) (hμ : Function.Injective μ) (q : Fin m → ℝ) (c : ℝ)
    (i : Fin m) : (secPoly μ q c).eval (μ i) = -(q i * dOf μ i) := by
  have h0 : ∏ k, (μ i - μ k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  simp only [secPoly, eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finsetSum, h0, mul_zero,
    zero_sub, neg_inj]
  rw [Finset.sum_eq_single i, dOf]
  · intro k _ hki
    rw [Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hki.symm, Finset.mem_univ _⟩) (sub_self _),
      mul_zero]
  · simp

/-- Coefficients of `∏_{j < n+1} (X - v_j)` from degree `n` up. -/
lemma coeff_prod_X_sub_C_of_le {n : ℕ} (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : n ≤ k) :
    (∏ j, (X - C (v j))).coeff k = if k = n then -∑ j, v j else if k = n + 1 then 1 else 0 := by
  have hdeg : (∏ j, (X - C (v j))).natDegree = n + 1 := by
    rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C (v j))]
    simp
  rcases hk.eq_or_lt with rfl | hk
  · simpa using prod_X_sub_C_coeff_card_pred Finset.univ v (by simp)
  rw [if_neg hk.ne']
  rcases (Nat.succ_le_of_lt hk).eq_or_lt with rfl | hk'
  · rw [if_pos rfl]
    have := (monic_prod_X_sub_C v Finset.univ).coeff_natDegree
    rwa [hdeg] at this
  · rw [if_neg hk'.ne', coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk')]

/-- With `(q, c) = (qOf μ l, cOf μ l)` the secular polynomial is `∏ (X - l_j)`. -/
lemma secPoly_qOf_cOf {m : ℕ} (μ : Fin m → ℝ) (hμ : Function.Injective μ) (l : Fin (m + 1) → ℝ) :
    secPoly μ (qOf μ l) (cOf μ l) = ∏ j, (X - C (l j)) := by
  set P : ℝ[X] := ∏ j, (X - C (l j))
  have hQ : (X - C (cOf μ l)) * ∏ i, (X - C (μ i)) =
      ∏ j, (X - C ((Fin.cons (cOf μ l) μ : Fin (m + 1) → ℝ) j)) := by
    rw [Fin.prod_univ_succ]; simp
  have hsum : ∑ j, (Fin.cons (cOf μ l) μ : Fin (m + 1) → ℝ) j = ∑ j, l j := by
    rw [Fin.sum_univ_succ]; simp [cOf]
  rw [← sub_eq_zero]
  by_contra hne
  have hlt : (secPoly μ (qOf μ l) (cOf μ l) - P).degree < m := by
    rw [degree_lt_iff_coeff_zero]
    intro k hk
    simp only [secPoly, hQ, coeff_sub, finsetSum_coeff, coeff_C_mul]
    have hz : ∑ x, qOf μ l x * (∏ x ∈ Finset.univ.erase x, (X - C (μ x))).coeff k = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C (μ j))]
      simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, Finset.mem_univ,
        Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]
      have := i.pos
      omega
    rw [coeff_prod_X_sub_C_of_le _ k hk, coeff_prod_X_sub_C_of_le _ k hk, hsum, hz]
    split_ifs <;> ring
  refine hne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hμ (fun i => ?_) ?_)
  · rw [eval_sub, eval_secPoly μ hμ, qOf, div_mul_cancel₀ _ (dOf_ne_zero hμ i)]
    simp [P, eval_prod]
  · simpa using (natDegree_lt_iff_degree_lt hne).2 hlt

lemma secPoly_inj {m : ℕ} {μ : Fin m → ℝ} (hμ : Function.Injective μ) {q q' : Fin m → ℝ}
    {c c' : ℝ} (h : secPoly μ q c = secPoly μ q' c') : q = q' ∧ c = c' := by
  have hq : q = q' := by
    funext i
    have := congrArg (eval (μ i)) h
    rw [eval_secPoly μ hμ, eval_secPoly μ hμ, neg_inj] at this
    exact mul_right_cancel₀ (dOf_ne_zero hμ i) this
  subst hq
  refine ⟨rfl, ?_⟩
  have h1 := sub_left_injective h
  have hne : (∏ i, (X - C (μ i)) : ℝ[X]) ≠ 0 := (monic_prod_X_sub_C μ _).ne_zero
  have h2 := mul_right_cancel₀ hne h1
  simpa using h2



/-- A product of nonzero reals has sign `(-1)^(number of negative factors)`. -/
lemma neg_one_pow_card_mul_prod_pos {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ j ∈ s, f j ≠ 0) : 0 < (-1) ^ (s.filter (fun j => f j < 0)).card * ∏ j ∈ s, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfa := hf a (Finset.mem_insert_self a s)
    rw [Finset.filter_insert, Finset.prod_insert ha]
    split_ifs with hneg
    · rw [Finset.card_insert_of_notMem (by simp [ha]), pow_succ]
      nlinarith
    · have : 0 < f a := lt_of_le_of_ne (not_lt.1 hneg) (Ne.symm hfa)
      nlinarith

lemma mod_two_eq_of_neg_one_pow {a b : ℕ} {x : ℝ} (ha : 0 < (-1) ^ a * x) (hb : 0 < (-1) ^ b * x) :
    a % 2 = b % 2 := by
  rw [neg_one_pow_eq_pow_mod_two] at ha
  rw [neg_one_pow_eq_pow_mod_two (n := b)] at hb
  have h1 := Nat.mod_lt a two_pos
  have h2 := Nat.mod_lt b two_pos
  interval_cases (a % 2) <;> interval_cases (b % 2) <;> simp at ha hb ⊢ <;> linarith

/-- Discrete core of interlacing: a monotone count with the parity of `i + 1`, bounded by `m + 1`,
is exactly `i + 1`. -/
lemma parity_count (m : ℕ) (N : ℕ → ℕ) (hmono : ∀ i, i + 1 < m → N i ≤ N (i + 1))
    (hpar : ∀ i < m, N i % 2 = (i + 1) % 2) (hle : ∀ i < m, N i ≤ m + 1) :
    ∀ i < m, N i = i + 1 := by
  have lower : ∀ i < m, i + 1 ≤ N i := by
    intro i
    induction i with
    | zero => intro h; have := hpar 0 h; omega
    | succ i ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hmono i h
      have h3 := hpar (i + 1) h
      omega
  have upper : ∀ k i, i + k + 1 = m → N i ≤ i + 1 := by
    intro k
    induction k with
    | zero => intro i h; have := hpar i (by omega); have := hle i (by omega); omega
    | succ k ih =>
      intro i h
      have h1 := ih (i + 1) (by omega)
      have h2 := hmono i (by omega)
      have h3 := hpar i (by omega)
      omega
  intro i hi
  exact le_antisymm (upper (m - 1 - i) i (by omega)) (lower i hi)

/-- The open interlacing region `l₀ > μ₀ > l₁ > ⋯ > μ_{m-1} > l_m`. -/
def interlaceSet {m : ℕ} (μ : Fin m → ℝ) : Set (Fin (m + 1) → ℝ) :=
  {l | ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i}

lemma strictAnti_of_mem_interlaceSet {m : ℕ} {μ : Fin m → ℝ} {l : Fin (m + 1) → ℝ}
    (hl : l ∈ interlaceSet μ) : StrictAnti l :=
  Fin.strictAnti_iff_succ_lt.2 fun i => (hl i).2.trans (hl i).1

/-- On the interlacing region, `l_j > μ_i` exactly for `j ≤ i`. -/
lemma lt_iff_of_mem_interlaceSet {m : ℕ} {μ : Fin m → ℝ} {l : Fin (m + 1) → ℝ}
    (hl : l ∈ interlaceSet μ) (i : Fin m) (j : Fin (m + 1)) :
    (μ i < l j ↔ j ≤ i.castSucc) ∧ (j ≤ i.castSucc ∨ l j < μ i) := by
  have ha := (strictAnti_of_mem_interlaceSet hl).antitone
  by_cases hj : j ≤ i.castSucc
  · exact ⟨⟨fun _ => hj, fun _ => (hl i).1.trans_le (ha hj)⟩, Or.inl hj⟩
  · have h2 : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.1 (not_le.1 hj)
    have : l j < μ i := (ha h2).trans_lt (hl i).2
    exact ⟨⟨fun h => absurd h (not_lt.2 this.le), fun h => absurd h hj⟩, Or.inr this⟩

lemma card_filter_lt_of_mem_interlaceSet {m : ℕ} {μ : Fin m → ℝ} {l : Fin (m + 1) → ℝ}
    (hl : l ∈ interlaceSet μ) (i : Fin m) :
    (Finset.univ.filter fun j => μ i - l j < 0).card = i + 1 := by
  have : (Finset.univ.filter fun j => μ i - l j < 0) = Finset.Iic i.castSucc := by
    ext j; simp [sub_neg, (lt_iff_of_mem_interlaceSet hl i j).1]
  rw [this, Fin.card_Iic]; simp

lemma card_filter_dOf {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ) (i : Fin m) :
    ((Finset.univ.erase i).filter fun k => μ i - μ k < 0).card = i := by
  have : ((Finset.univ.erase i).filter fun k => μ i - μ k < 0) = Finset.Iio i := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, sub_neg, Finset.mem_Iio]
    exact ⟨fun h => lt_of_not_ge fun hik => absurd h.2 (not_lt.2 (hμ.antitone hik)),
      fun h => ⟨⟨h.ne, trivial⟩, hμ h⟩⟩
  rw [this, Fin.card_Iio]

lemma dOf_sign {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ) (i : Fin m) :
    0 < (-1) ^ (i : ℕ) * dOf μ i := by
  have := neg_one_pow_card_mul_prod_pos (Finset.univ.erase i) (fun k => μ i - μ k)
    (fun k hk => sub_ne_zero.2 (hμ.injective.ne (Finset.ne_of_mem_erase hk).symm))
  rwa [card_filter_dOf hμ] at this

lemma qOf_pos {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ) {l : Fin (m + 1) → ℝ}
    (hl : l ∈ interlaceSet μ) (i : Fin m) : 0 < qOf μ l i := by
  have hP := neg_one_pow_card_mul_prod_pos Finset.univ (fun j => μ i - l j) (fun j _ => by
    rcases (lt_iff_of_mem_interlaceSet hl i j).2 with h | h
    · exact sub_ne_zero.2 ((lt_iff_of_mem_interlaceSet hl i j).1.2 h).ne
    · exact sub_ne_zero.2 h.ne')
  rw [card_filter_lt_of_mem_interlaceSet hl i] at hP
  have hd := dOf_sign hμ i
  rw [qOf]
  rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;>
    simp only [pow_succ, h] at hP hd <;> simp at hP hd
  · exact div_pos (by linarith) hd
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)

/-- Forward direction: on the interlacing region, the arrow array with `y_{i+1}² = qOf μ l i` and
`y₀ = cOf μ l` has latent roots `l`. -/
lemma latentRoots_arrowMat_of_mem {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ)
    {l : Fin (m + 1) → ℝ} (hl : l ∈ interlaceSet μ) (y : Fin (m + 1) → ℝ)
    (hq : ∀ i, y i.succ ^ 2 = qOf μ l i) (hc : y 0 = cOf μ l) :
    latentRoots (arrowMat μ y) = l := by
  apply latentRoots_eq_of_charpoly _ (arrowMat_isHermitian μ y) l
    (strictAnti_of_mem_interlaceSet hl).antitone
  rw [charpoly_arrowMat, ← secPoly_qOf_cOf μ hμ.injective l, hc]
  congr 1
  funext i
  exact hq i

/-- Backward direction: if every border entry `y_{i+1}` is nonzero, the latent roots of the arrow
array interlace `μ` and recover `(y_{i+1}², y₀)` through `qOf`, `cOf`. -/
lemma arrowMat_spec {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ) (y : Fin (m + 1) → ℝ)
    (hy : ∀ i : Fin m, y i.succ ≠ 0) :
    latentRoots (arrowMat μ y) ∈ interlaceSet μ ∧
      qOf μ (latentRoots (arrowMat μ y)) = (fun i => y i.succ ^ 2) ∧
      cOf μ (latentRoots (arrowMat μ y)) = y 0 := by
  set l := latentRoots (arrowMat μ y)
  obtain ⟨hanti, hchar⟩ := latentRoots_spec _ (arrowMat_isHermitian μ y)
  rw [charpoly_arrowMat] at hchar
  have hqc := secPoly_inj hμ.injective (hchar.trans (secPoly_qOf_cOf μ hμ.injective l).symm)
  refine ⟨?_, hqc.1.symm, hqc.2.symm⟩
  have hP : ∀ i, ∏ j, (μ i - l j) = -(y i.succ ^ 2 * dOf μ i) := by
    intro i
    have := congrArg (eval (μ i)) hchar
    rw [eval_secPoly μ hμ.injective] at this
    rw [this]
    simp [eval_prod, l]
  have hne : ∀ i j, μ i - l j ≠ 0 := by
    intro i j h
    have h0 : ∏ j, (μ i - l j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h
    rw [hP] at h0
    have := dOf_ne_zero hμ.injective i
    have := hy i
    simp_all
  have hsign1 : ∀ i : Fin m, 0 < (-1) ^ ((i : ℕ) + 1) * ∏ j, (μ i - l j) := by
    intro i
    rw [hP]
    have e : (-1 : ℝ) ^ ((i : ℕ) + 1) * -(y i.succ ^ 2 * dOf μ i) =
        y i.succ ^ 2 * ((-1) ^ (i : ℕ) * dOf μ i) := by ring
    rw [e]
    exact mul_pos (by have := hy i; positivity) (dOf_sign hμ i)
  have hsign2 : ∀ i, 0 < (-1) ^ ((Finset.univ.filter fun j => μ i - l j < 0).card) *
      ∏ j, (μ i - l j) := fun i => neg_one_pow_card_mul_prod_pos _ _ (fun j _ => hne i j)
  let N : ℕ → ℕ := fun i =>
    if h : i < m then (Finset.univ.filter fun j => μ ⟨i, h⟩ - l j < 0).card else 0
  have hN := parity_count m N
    (fun i hi => by
      simp only [N, dif_pos hi, dif_pos (show i < m by omega)]
      refine Finset.card_le_card fun j => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
      intro h
      exact lt_of_le_of_lt (hμ.antitone (show (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩ by
        simp [Fin.le_def])) h)
    (fun i hi => by
      simp only [N, dif_pos hi]
      exact mod_two_eq_of_neg_one_pow (hsign2 ⟨i, hi⟩) (hsign1 ⟨i, hi⟩))
    (fun i hi => by
      simp only [N, dif_pos hi]
      exact (Finset.card_filter_le _ _).trans (by simp))
  intro i
  have hc : (Finset.univ.filter fun j => μ i - l j < 0).card = i + 1 := by
    simpa [N, i.isLt] using hN i i.isLt
  simp only [sub_neg] at hc
  constructor
  · by_contra h
    push Not at h
    have hsub : (Finset.univ.filter fun j => μ i < l j) ⊆ Finset.Iio i.castSucc := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio] at hj ⊢
      by_contra hji
      push Not at hji
      linarith [hanti hji]
    have := Finset.card_le_card hsub
    rw [hc, Fin.card_Iio, Fin.val_castSucc] at this
    omega
  · by_contra h
    push Not at h
    have hsub : Finset.Iic i.succ ⊆ (Finset.univ.filter fun j => μ i < l j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic] at hj ⊢
      have h1 := hanti hj
      have h2 := hne i j
      have : μ i - l j ≤ 0 := by linarith
      exact sub_neg.1 (lt_of_le_of_ne this h2)
    have := Finset.card_le_card hsub
    rw [hc, Fin.card_Iic, Fin.val_succ] at this
    omega



/-- `(cOf μ l, qOf μ l)` as one vector, `c` in slot `0`. -/
noncomputable def phiMap {m : ℕ} (μ : Fin m → ℝ) (l : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cons (cOf μ l) (qOf μ l)

/-- Jacobian matrix of `phiMap μ` at `l`: a row of ones, then `∏_{j' ≠ j} (μ_i - l_{j'}) / d_i`. -/
noncomputable def phiJac {m : ℕ} (μ : Fin m → ℝ) (l : Fin (m + 1) → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun r j => (Fin.cons (1 : ℝ)
    (fun i => (∏ j' ∈ Finset.univ.erase j, (μ i - l j')) / dOf μ i) : Fin (m + 1) → ℝ) r

lemma hasFDerivAt_phiMap {m : ℕ} (μ : Fin m → ℝ) (l : Fin (m + 1) → ℝ) :
    HasFDerivAt (phiMap μ) (LinearMap.toContinuousLinearMap (Matrix.toLin' (phiJac μ l))) l := by
  rw [hasFDerivAt_pi']
  intro r
  refine Fin.cases ?_ (fun i => ?_) r
  · simp only [phiMap, Fin.cons_zero, cOf]
    have h : HasFDerivAt (fun l : Fin (m + 1) → ℝ => ∑ j, l j)
        (∑ j, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) j) l :=
      HasFDerivAt.fun_sum (fun j _ => hasFDerivAt_apply j l)
    refine (h.sub_const _).congr_fderiv ?_
    ext v
    simp [phiJac, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · simp only [phiMap, Fin.cons_succ, qOf]
    have h : HasFDerivAt (fun l : Fin (m + 1) → ℝ => ∏ j, (μ i - l j))
        (∑ j, (∏ j' ∈ Finset.univ.erase j, (μ i - l j')) •
          -ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) j) l :=
      HasFDerivAt.finsetProd (fun j _ => (hasFDerivAt_apply j l).const_sub (μ i))
    have e : (fun l : Fin (m + 1) → ℝ => -(∏ j, (μ i - l j)) / dOf μ i) =
        fun l => (∏ j, (μ i - l j)) * (-(dOf μ i)⁻¹) := by funext; ring
    rw [e]
    refine (h.mul_const _).congr_fderiv ?_
    ext v
    simp [phiJac, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma abs_vandermondeProd {n : ℕ} (v : Fin n → ℝ) :
    |vandermondeProd v| = ∏ i, ∏ k, if i < k then |v i - v k| else 1 := by
  rw [vandermondeProd, Finset.abs_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.abs_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma abs_det_vandermonde {n : ℕ} (v : Fin n → ℝ) :
    |(Matrix.vandermonde v).det| = |vandermondeProd v| := by
  rw [Matrix.det_vandermonde, abs_vandermondeProd, Finset.abs_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.abs_prod, ← Finset.prod_filter]
  have : Finset.univ.filter (fun k => i < k) = Finset.Ioi i := by ext k; simp
  rw [this]
  exact Finset.prod_congr rfl fun k _ => abs_sub_comm _ _

lemma prod_prod_erase_abs {n : ℕ} (v : Fin n → ℝ) :
    ∏ i, ∏ k ∈ Finset.univ.erase i, |v i - v k| = |vandermondeProd v| ^ 2 := by
  have h1 : ∀ i, ∏ k ∈ Finset.univ.erase i, |v i - v k| =
      ∏ k, ((if i < k then |v i - v k| else 1) * (if k < i then |v i - v k| else 1)) := by
    intro i
    rw [← Finset.filter_ne', Finset.prod_filter]
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp
    · simp [h, h.ne, not_lt.2 h.le]
  simp_rw [h1, Finset.prod_mul_distrib, abs_vandermondeProd, sq]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
  rw [abs_sub_comm]

/-- Evaluation map in coefficient coordinates: leading coefficient, then values at `μ_i` over `d_i`. -/
noncomputable def evalMat {m : ℕ} (μ : Fin m → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun r k => (Fin.cons (if k = Fin.last m then (1 : ℝ) else 0)
    (fun i => μ i ^ (k : ℕ) / dOf μ i) : Fin (m + 1) → ℝ) r

/-- Coefficients of the polynomials `∏_{j' ≠ j} (X - l_{j'})`, one per column. -/
noncomputable def coeffMat {m : ℕ} (l : Fin (m + 1) → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun k j => (∏ j' ∈ Finset.univ.erase j, (X - C (l j'))).coeff k

lemma natDegree_prod_erase {n : ℕ} (l : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    (∏ j' ∈ Finset.univ.erase j, (X - C (l j'))).natDegree = n := by
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C (l j))]
  simp

lemma sum_coeff_mul_pow {n : ℕ} (l : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (x : ℝ) :
    ∑ k : Fin (n + 1), (∏ j' ∈ Finset.univ.erase j, (X - C (l j'))).coeff k * x ^ (k : ℕ) =
      ∏ j' ∈ Finset.univ.erase j, (x - l j') := by
  have h := Fin.sum_univ_eq_sum_range
    (fun k => (∏ j' ∈ Finset.univ.erase j, (X - C (l j'))).coeff k * x ^ k) (n + 1)
  try simp only at h
  rw [h, ← eval_eq_sum_range' (by rw [natDegree_prod_erase]; omega)]
  simp [eval_prod]

lemma phiJac_eq_mul {m : ℕ} (μ : Fin m → ℝ) (l : Fin (m + 1) → ℝ) :
    phiJac μ l = evalMat μ * coeffMat l := by
  ext r j
  refine Fin.cases ?_ (fun i => ?_) r
  · simp only [phiJac, evalMat, coeffMat, Matrix.mul_apply, Matrix.of_apply, Fin.cons_zero, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := (monic_prod_X_sub_C l (Finset.univ.erase j)).coeff_natDegree
    rw [natDegree_prod_erase] at this
    simpa using this.symm
  · simp only [phiJac, evalMat, coeffMat, Matrix.mul_apply, Matrix.of_apply, Fin.cons_succ]
    rw [← sum_coeff_mul_pow, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring

lemma det_evalMat {m : ℕ} (μ : Fin m → ℝ) :
    (evalMat μ).det = (-1) ^ m * (∏ i, (dOf μ i)⁻¹) * (Matrix.vandermonde μ).det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last m)]
  · have : (evalMat μ).submatrix Fin.succ (Fin.last m).succAbove =
        Matrix.of fun i k => (dOf μ i)⁻¹ * Matrix.vandermonde μ i k := by
      ext i k
      simp [evalMat, Matrix.vandermonde, div_eq_mul_inv, mul_comm]
    rw [this, Matrix.det_mul_column]
    simp [evalMat, mul_assoc]
  · intro k _ hk
    simp [evalMat, hk]
  · simp

lemma det_coeffMat_mul {m : ℕ} (l : Fin (m + 1) → ℝ) :
    (Matrix.vandermonde l).det * (coeffMat l).det = ∏ j, ∏ j' ∈ Finset.univ.erase j, (l j - l j') := by
  rw [← Matrix.det_mul]
  have : Matrix.vandermonde l * coeffMat l =
      Matrix.diagonal fun j => ∏ j' ∈ Finset.univ.erase j, (l j - l j') := by
    refine Matrix.ext fun a j => ?_
    rw [Matrix.mul_apply]
    simp only [Matrix.vandermonde_apply, coeffMat, Matrix.of_apply]
    rw [Finset.sum_congr rfl (fun k _ => mul_comm _ _), sum_coeff_mul_pow]
    by_cases h : a = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)
  rw [this, Matrix.det_diagonal]

lemma abs_det_phiJac {m : ℕ} {μ : Fin m → ℝ} (hμ : Function.Injective μ) {l : Fin (m + 1) → ℝ}
    (hl : Function.Injective l) :
    |(phiJac μ l).det| = |vandermondeProd l| / |vandermondeProd μ| := by
  have hVμ : |vandermondeProd μ| ≠ 0 := by
    rw [← abs_det_vandermonde]; exact abs_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hμ)
  have hVl : |vandermondeProd l| ≠ 0 := by
    rw [← abs_det_vandermonde]; exact abs_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hl)
  have hd : ∏ i, |dOf μ i| = |vandermondeProd μ| ^ 2 := by
    rw [← prod_prod_erase_abs]
    simp [dOf, Finset.abs_prod]
  have hC : |(coeffMat l).det| = |vandermondeProd l| := by
    have h := congrArg abs (det_coeffMat_mul l)
    rw [abs_mul, abs_det_vandermonde, Finset.abs_prod] at h
    simp_rw [Finset.abs_prod] at h
    rw [prod_prod_erase_abs, sq] at h
    exact mul_left_cancel₀ hVl h
  rw [phiJac_eq_mul, Matrix.det_mul, abs_mul, hC, det_evalMat, abs_mul, abs_mul,
    abs_det_vandermonde, Finset.abs_prod]
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_inv]
  rw [Finset.prod_inv_distrib, hd]
  field_simp



/-- The sign `±1` attached to a Boolean. -/
def sgn {m : ℕ} (σ : Fin m → Bool) (i : Fin m) : ℝ := if σ i then -1 else 1

lemma sgn_mul_self {m : ℕ} (σ : Fin m → Bool) (i : Fin m) : sgn σ i * sgn σ i = 1 := by
  unfold sgn; split_ifs <;> norm_num

/-- `y ↦ (y₀, σ_i √y_{i+1})`. -/
noncomputable def sqrtMap {m : ℕ} (σ : Fin m → Bool) (y : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cons (y 0) (fun i => sgn σ i * √(y i.succ))

/-- The border `(c, b)` with `b_i = σ_i √(q_i)`, as a function of the roots `l`. -/
noncomputable def psiMap {m : ℕ} (μ : Fin m → ℝ) (σ : Fin m → Bool) (l : Fin (m + 1) → ℝ) :
    Fin (m + 1) → ℝ :=
  sqrtMap σ (phiMap μ l)

noncomputable def sqrtDiag {m : ℕ} (σ : Fin m → Bool) (y : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cons 1 (fun i => sgn σ i * (1 / (2 * √(y i.succ))))

lemma hasFDerivAt_sqrtMap {m : ℕ} (σ : Fin m → Bool) (y : Fin (m + 1) → ℝ)
    (hy : ∀ i, 0 < y (Fin.succ i)) :
    HasFDerivAt (sqrtMap σ)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal (sqrtDiag σ y)))) y := by
  rw [hasFDerivAt_pi']
  intro r
  refine Fin.cases ?_ (fun i => ?_) r
  · simp only [sqrtMap, Fin.cons_zero]
    refine (hasFDerivAt_apply 0 y).congr_fderiv ?_
    ext v
    simp [sqrtDiag, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  · simp only [sqrtMap, Fin.cons_succ]
    refine (((hasFDerivAt_apply i.succ y).sqrt (hy i).ne').const_mul (sgn σ i)).congr_fderiv ?_
    ext v
    simp [sqrtDiag, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    ring

lemma hasFDerivAt_psiMap {m : ℕ} (μ : Fin m → ℝ) (σ : Fin m → Bool) {l : Fin (m + 1) → ℝ}
    (hq : ∀ i, 0 < qOf μ l i) :
    HasFDerivAt (psiMap μ σ) (LinearMap.toContinuousLinearMap
      (Matrix.toLin' (Matrix.diagonal (sqrtDiag σ (phiMap μ l)) * phiJac μ l))) l := by
  have h := (hasFDerivAt_sqrtMap σ (phiMap μ l) (by simpa [phiMap] using hq)).comp l
    (hasFDerivAt_phiMap μ l)
  refine h.congr_fderiv ?_
  ext v
  simp [Matrix.toLin'_mul]

lemma abs_det_psiJac {m : ℕ} {μ : Fin m → ℝ} (hμ : Function.Injective μ) (σ : Fin m → Bool)
    {l : Fin (m + 1) → ℝ} (hl : Function.Injective l) (hq : ∀ i, 0 < qOf μ l i) :
    |(Matrix.diagonal (sqrtDiag σ (phiMap μ l)) * phiJac μ l).det| =
      (∏ i, 1 / (2 * √(qOf μ l i))) * (|vandermondeProd l| / |vandermondeProd μ|) := by
  rw [Matrix.det_mul, abs_mul, abs_det_phiJac hμ hl, Matrix.det_diagonal, Fin.prod_univ_succ,
    abs_mul, Finset.abs_prod]
  congr 1
  simp only [sqrtDiag, phiMap, Fin.cons_zero, Fin.cons_succ, abs_one, one_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := Real.sqrt_pos.2 (hq i)
  unfold sgn; split_ifs <;> simp [abs_mul, abs_of_pos h]

lemma vandermondeProd_pos {n : ℕ} {l : Fin n → ℝ} (hl : StrictAnti l) : 0 < vandermondeProd l := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  split_ifs with h
  · exact sub_pos.2 (hl h)
  · exact one_pos

/-- The density identity on the interlacing region: Jacobian of `psiMap` equals
`2^{-m} V(l) ∏ |μ_i - l_j|^{-1/2}`. -/
lemma psiJac_density {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ) {l : Fin (m + 1) → ℝ}
    (hl : l ∈ interlaceSet μ) :
    (∏ i, 1 / (2 * √(qOf μ l i))) * (|vandermondeProd l| / |vandermondeProd μ|) =
      (2 ^ m)⁻¹ * (vandermondeProd l *
        ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2)) := by
  have hVμ : 0 < |vandermondeProd μ| := abs_pos.2 (vandermondeProd_pos hμ).ne'
  rw [abs_of_pos (vandermondeProd_pos (strictAnti_of_mem_interlaceSet hl))]
  set a : Fin m → ℝ := fun i => ∏ j, |μ i - l j|
  have hd0 : ∀ i, 0 < |dOf μ i| := fun i => abs_pos.2 (dOf_ne_zero hμ.injective i)
  have ha0 : ∀ i, 0 < a i := fun i => by
    have := qOf_pos hμ hl i
    rw [qOf] at this
    refine Finset.prod_pos fun j _ => abs_pos.2 fun h => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ j) h] at this
    simp at this
  have hq : ∀ i, qOf μ l i = a i / |dOf μ i| := fun i => by
    rw [← abs_of_pos (qOf_pos hμ hl i), qOf, abs_div, abs_neg, Finset.abs_prod]
  have hrp : ∀ i, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2) = (√(a i))⁻¹ := fun i => by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (ha0 i).le, ← Real.finsetProd_rpow _ _
      (fun j _ => abs_nonneg _)]
    norm_num
  have hdprod : ∏ i, √|dOf μ i| = |vandermondeProd μ| := by
    rw [← Real.sqrt_prod _ (fun i _ => abs_nonneg _)]
    rw [show ∏ i, |dOf μ i| = |vandermondeProd μ| ^ 2 by
      rw [← prod_prod_erase_abs]; simp [dOf, Finset.abs_prod]]
    exact Real.sqrt_sq (abs_nonneg _)
  simp_rw [hrp, hq, Real.sqrt_div' _ (abs_nonneg _)]
  have hsa : ∀ i, 0 < √(a i) := fun i => Real.sqrt_pos.2 (ha0 i)
  have e : ∀ i, 1 / (2 * (√(a i) / √|dOf μ i|)) = (2 : ℝ)⁻¹ * (√|dOf μ i| * (√(a i))⁻¹) := by
    intro i
    have := Real.sqrt_pos.2 (hd0 i)
    field_simp [(hsa i).ne']
  simp_rw [e, Finset.prod_mul_distrib, hdprod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  field_simp



/-- The open orthant `{σ_i y_{i+1} > 0}`. -/
def orthant {m : ℕ} (σ : Fin m → Bool) : Set (Fin (m + 1) → ℝ) :=
  {y | ∀ i, 0 < sgn σ i * y i.succ}

lemma measurableSet_orthant {m : ℕ} (σ : Fin m → Bool) : MeasurableSet (orthant σ) := by
  have : orthant σ = ⋂ i, {y : Fin (m + 1) → ℝ | 0 < sgn σ i * y i.succ} := by
    ext y; simp [orthant]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (by fun_prop)

lemma measurableSet_interlaceSet {m : ℕ} (μ : Fin m → ℝ) : MeasurableSet (interlaceSet μ) := by
  have : interlaceSet μ = ⋂ i, ({l : Fin (m + 1) → ℝ | μ i < l i.castSucc} ∩
      {l | l i.succ < μ i}) := by
    ext l; simp [interlaceSet]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)

lemma latentRoots_psiMap {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ) (σ : Fin m → Bool)
    {l : Fin (m + 1) → ℝ} (hl : l ∈ interlaceSet μ) :
    latentRoots (arrowMat μ (psiMap μ σ l)) = l := by
  refine latentRoots_arrowMat_of_mem hμ hl _ (fun i => ?_) (by simp [psiMap, sqrtMap, phiMap])
  simp only [psiMap, sqrtMap, phiMap, Fin.cons_succ, Fin.cons_zero]
  rw [mul_pow, Real.sq_sqrt (qOf_pos hμ hl i).le, show sgn σ i ^ 2 = 1 by
    rw [sq, sgn_mul_self], one_mul]

lemma psiMap_injOn {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ) (σ : Fin m → Bool) :
    Set.InjOn (psiMap μ σ) (interlaceSet μ) := by
  intro l hl l' hl' h
  rw [← latentRoots_psiMap hμ σ hl, ← latentRoots_psiMap hμ σ hl', h]

lemma psiMap_image {m : ℕ} {μ : Fin m → ℝ} (hμ : StrictAnti μ) (σ : Fin m → Bool) :
    psiMap μ σ '' interlaceSet μ = orthant σ := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩ i
    simp only [psiMap, sqrtMap, phiMap, Fin.cons_succ, Fin.cons_zero]
    rw [← mul_assoc, sgn_mul_self, one_mul]
    exact Real.sqrt_pos.2 (qOf_pos hμ hl i)
  · intro hy
    have hy0 : ∀ i : Fin m, y i.succ ≠ 0 := fun i h => by
      have := hy i; rw [h, mul_zero] at this; exact lt_irrefl _ this
    obtain ⟨hU, hq, hc⟩ := arrowMat_spec hμ y hy0
    refine ⟨_, hU, ?_⟩
    ext r
    refine Fin.cases ?_ (fun i => ?_) r
    · simp [psiMap, sqrtMap, phiMap, hc]
    · simp only [psiMap, sqrtMap, phiMap, Fin.cons_succ, hq, Real.sqrt_sq_eq_abs]
      have := hy i
      unfold sgn at this ⊢
      split_ifs at this ⊢
      · rw [abs_of_neg (by linarith)]; ring
      · rw [abs_of_pos (by linarith)]; ring

lemma lintegral_border_eq_arrow (m : ℕ) (μ : Fin m → ℝ) (h : (Fin (m + 1) → ℝ) → ENNReal) :
    ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots
        ((Fin.cons (Fin.cons p.2 p.1 : Fin (m + 1) → ℝ)
          (fun i => (Fin.cons (p.1 i) (diagArray μ i) : Fin (m + 1) → ℝ)) :
            Fin (m + 1) → Fin (m + 1) → ℝ))) =
      ∫⁻ y : Fin (m + 1) → ℝ, h (latentRoots (arrowMat μ y)) := by
  let e : (Fin m → ℝ) × ℝ ≃ᵐ (Fin (m + 1) → ℝ) :=
    MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
  have he : MeasurePreserving e volume volume :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0).symm.comp
      (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
        (ν := (volume : Measure ℝ)))
  rw [← he.lintegral_comp_emb e.measurableEmbedding]
  congr 1
  funext p
  have : e p = Fin.cons p.2 p.1 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']
    rfl
  rw [this]
  rfl

lemma orthant_disjoint {m : ℕ} : Pairwise (Function.onFun Disjoint (orthant (m := m))) := by
  intro σ τ hστ
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    by_contra h; push Not at h; exact hστ (funext h)
  refine Set.disjoint_left.2 fun y hσ hτ => ?_
  have h1 := hσ i
  have h2 := hτ i
  unfold sgn at h1 h2
  cases hs : σ i <;> cases ht : τ i <;> simp_all <;> linarith

lemma ae_iUnion_orthant (m : ℕ) :
    (⋃ σ, orthant (m := m) σ) =ᵐ[volume] (Set.univ : Set (Fin (m + 1) → ℝ)) := by
  rw [ae_eq_univ]
  refine measure_mono_null (t := ⋃ i : Fin m, {y : Fin (m + 1) → ℝ | y i.succ = 0}) ?_
    (measure_iUnion_null fun i => ?_)
  · intro y hy
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra h'
    push Not at h'
    refine hy (fun i => decide (y i.succ < 0)) fun i => ?_
    unfold sgn
    by_cases hi : y i.succ < 0
    · simp [hi]
    · simp [hi]; exact lt_of_le_of_ne (not_lt.1 hi) (h' i).symm
  · rw [volume_pi]
    exact Measure.pi_hyperplane _ _ _

theorem lintegral_latentRoots_border_diag (m : ℕ) (μ : Fin m → ℝ) (hμ : StrictAnti μ)
    (h : (Fin (m + 1) → ℝ) → ENNReal) (hh : Measurable h) :
    ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots
        ((Fin.cons (Fin.cons p.2 p.1 : Fin (m + 1) → ℝ)
          (fun i => (Fin.cons (p.1 i) (diagArray μ i) : Fin (m + 1) → ℝ)) :
            Fin (m + 1) → Fin (m + 1) → ℝ))) =
      ∫⁻ l : Fin (m + 1) → ℝ,
        (if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
          ENNReal.ofReal (vandermondeProd l *
            ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
        else 0) * h l := by
  set ρ : (Fin (m + 1) → ℝ) → ENNReal := fun l => ENNReal.ofReal (vandermondeProd l *
    ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
  rw [lintegral_border_eq_arrow, ← setLIntegral_univ, ← setLIntegral_congr (ae_iUnion_orthant m),
    lintegral_iUnion measurableSet_orthant orthant_disjoint, tsum_fintype]
  have hσ : ∀ σ : Fin m → Bool, ∫⁻ y in orthant σ, h (latentRoots (arrowMat μ y)) =
      ∫⁻ l in interlaceSet μ, (2 ^ m)⁻¹ * (ρ l * h l) := by
    intro σ
    rw [← psiMap_image hμ σ, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (measurableSet_interlaceSet μ)
      (fun l hl => (hasFDerivAt_psiMap μ σ (fun i => qOf_pos hμ hl i)).hasFDerivWithinAt)
      (psiMap_injOn hμ σ)]
    refine setLIntegral_congr_fun (measurableSet_interlaceSet μ) (fun l hl => ?_)
    simp only [latentRoots_psiMap hμ σ hl]
    rw [← mul_assoc]
    congr 1
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
      abs_det_psiJac hμ.injective σ (strictAnti_of_mem_interlaceSet hl).injective
        (fun i => qOf_pos hμ hl i), psiJac_density hμ hl, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  simp_rw [hσ]
  rw [Finset.sum_const, Finset.card_univ, lintegral_const_mul' _ _ (by simp), nsmul_eq_mul,
    ← mul_assoc]
  have hcard : ((Fintype.card (Fin m → Bool) : ℕ) : ENNReal) * (2 ^ m)⁻¹ = 1 := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by simp) (by simp)
  rw [hcard, one_mul, ← lintegral_indicator (measurableSet_interlaceSet μ)]
  congr 1
  funext l
  simp only [Set.indicator, interlaceSet, Set.mem_setOf_eq, ρ]
  split_ifs <;> simp

end MuirheadMST

open MuirheadMST in
theorem solution (m : ℕ) (μ : Fin m → ℝ) (hμ : StrictAnti μ)
    (h : (Fin (m + 1) → ℝ) → ENNReal) (hh : Measurable h) :
    ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots
        ((Fin.cons (Fin.cons p.2 p.1 : Fin (m + 1) → ℝ)
          (fun i => (Fin.cons (p.1 i) (diagArray μ i) : Fin (m + 1) → ℝ)) :
            Fin (m + 1) → Fin (m + 1) → ℝ))) =
      ∫⁻ l : Fin (m + 1) → ℝ,
        (if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
          ENNReal.ofReal (vandermondeProd l *
            ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
        else 0) * h l :=
  MuirheadMST.lintegral_latentRoots_border_diag m μ hμ h hh

-- Prove2me | solution 1 for HarlowTASI.ewr_jlms_imp_duality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:43:04.38282+00:00
-- url     : https://prove2.me/submissions/1f71974e-11e7-4a59-b8fd-83ecece57953

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras
import Theorems.Thm_HarlowTASI_centralizer_blockAlgebraLeft

open Matrix
open scoped Kronecker ComplexOrder

set_option maxHeartbeats 800000

namespace HarlowTASI_JlmsImpDuality

open HarlowTASI

/-! ### Part 1: EReal sum helpers and Klein's inequality (`relativeEntropy ρ σ = 0 ↔ ρ = σ`) -/

lemma ereal_add_ne_bot {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : a + b ≠ ⊥ := by
  induction a using EReal.rec <;> induction b using EReal.rec <;> simp_all [← EReal.coe_add]

lemma ereal_sum_ne_bot {α : Type*} (s : Finset α) (f : α → EReal)
    (hf : ∀ x ∈ s, f x ≠ ⊥) : ∑ x ∈ s, f x ≠ ⊥ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ereal_add_ne_bot (hf a (Finset.mem_insert_self a s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

lemma ereal_sum_eq_top_of_mem {α : Type*} (s : Finset α) (f : α → EReal)
    (hf : ∀ x ∈ s, f x ≠ ⊥) {a : α} (ha : a ∈ s) (htop : f a = ⊤) :
    ∑ x ∈ s, f x = ⊤ := by
  classical
  induction s using Finset.induction with
  | empty => simp at ha
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    rcases Finset.mem_insert.mp ha with rfl | has
    · rw [htop]
      exact EReal.top_add_of_ne_bot
        (ereal_sum_ne_bot s f (fun x hx => hf x (Finset.mem_insert_of_mem hx)))
    · have h_rest : ∑ x ∈ s, f x = ⊤ :=
        ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) has
      rw [h_rest]
      exact EReal.add_top_of_ne_bot (hf b (Finset.mem_insert_self b s))

lemma ereal_coe_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ∑ x ∈ s, ((f x : ℝ) : EReal) = ((∑ x ∈ s, f x : ℝ) : EReal) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

lemma log_add_one_le_and_eq {x : ℝ} (hx : 0 < x) :
    Real.log x + 1 ≤ x ∧ (Real.log x + 1 = x ↔ x = 1) := by
  have hle : Real.log x + 1 ≤ x := by
    have h := Real.add_one_le_exp (Real.log x)
    rwa [Real.exp_log hx] at h
  refine ⟨hle, ⟨fun heq => ?_, fun h1 => by subst h1; simp⟩⟩
  by_contra hne
  have hstrict := Real.log_lt_sub_one_of_pos hx hne
  linarith

lemma onb_sum_inner_sq_left {n : Type} [Fintype n] [DecidableEq n]
    (v : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (x : EuclideanSpace ℂ n) :
    ∑ j : n, ‖inner ℂ x (v j)‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := v.sum_sq_norm_inner_right x
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  rw [norm_inner_symm]

lemma onb_sum_inner_sq_right {n : Type} [Fintype n] [DecidableEq n]
    (u : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (y : EuclideanSpace ℂ n) :
    ∑ i : n, ‖inner ℂ (u i) y‖ ^ 2 = ‖y‖ ^ 2 :=
  u.sum_sq_norm_inner_right y

lemma classicalRelTerm_self (p : ℝ) : classicalRelTerm p p = 0 := by
  unfold classicalRelTerm
  by_cases hp : p = 0
  · simp [hp]
  · simp [hp]

lemma relativeEntropy_self {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : relativeEntropy ρ ρ = 0 := by
  unfold relativeEntropy
  by_cases hH : ρ.IsHermitian
  · rw [dif_pos ⟨hH, hH⟩]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases h1 : hH.eigenvalues i = 0 ∨
        ‖inner ℂ (hH.eigenvectorBasis i) (hH.eigenvectorBasis j)‖ = 0
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases hij : i = j
      · subst hij
        have hpi : hH.eigenvalues i ≠ 0 := (not_or.mp h1).1
        rw [if_neg hpi, sub_self, mul_zero, EReal.coe_zero]
      · exfalso
        apply (not_or.mp h1).2
        rw [norm_eq_zero]
        exact hH.eigenvectorBasis.orthonormal.2 hij
  · have hnot : ¬(ρ.IsHermitian ∧ ρ.IsHermitian) := fun h => hH h.1
    rw [dif_neg hnot]

lemma eq_of_relativeEntropy_eq_zero {n : Type} [Fintype n] [DecidableEq n]
    {ρ σ : Matrix n n ℂ} (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (h0 : relativeEntropy ρ σ = 0) : ρ = σ := by
  have hH : ρ.IsHermitian ∧ σ.IsHermitian := ⟨hρ.1.isHermitian, hσ.1.isHermitian⟩
  unfold relativeEntropy at h0
  rw [dif_pos hH] at h0
  let p := hH.1.eigenvalues
  let q := hH.2.eigenvalues
  let u := hH.1.eigenvectorBasis
  let v := hH.2.eigenvectorBasis
  let w : n → n → ℝ := fun i j => ‖inner ℂ (u i) (v j)‖ ^ 2
  have hp_nonneg : ∀ i, 0 ≤ p i := hρ.1.eigenvalues_nonneg
  have hq_nonneg : ∀ j, 0 ≤ q j := hσ.1.eigenvalues_nonneg
  have hw_nonneg : ∀ i j, 0 ≤ w i j := fun i j => sq_nonneg _
  let T : n → n → EReal := fun i j =>
    if p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0 then (0 : EReal)
    else if q j = 0 then ⊤
    else ((w i j * p i * (Real.log (p i) - Real.log (q j)) : ℝ) : EReal)
  change ∑ i : n, ∑ j : n, T i j = 0 at h0
  have hT_ne_bot : ∀ i j, T i j ≠ ⊥ := by
    intro i j
    change (if p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0 then (0 : EReal)
      else if q j = 0 then ⊤
      else ((w i j * p i * (Real.log (p i) - Real.log (q j)) : ℝ) : EReal)) ≠ ⊥
    split_ifs
    · decide
    · decide
    · exact EReal.coe_ne_bot _
  have h_row_ne_bot : ∀ i, ∑ j : n, T i j ≠ ⊥ :=
    fun i => ereal_sum_ne_bot Finset.univ (fun j => T i j) (fun j _ => hT_ne_bot i j)
  have hq_ne_zero : ∀ i j, ¬(p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0) → q j ≠ 0 := by
    intro i j hij hqj
    have hT_top : T i j = ⊤ := by
      change (if p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0 then (0 : EReal)
        else if q j = 0 then ⊤
        else ((w i j * p i * (Real.log (p i) - Real.log (q j)) : ℝ) : EReal)) = ⊤
      rw [if_neg hij, if_pos hqj]
    have hrow_top : ∑ j' : n, T i j' = ⊤ :=
      ereal_sum_eq_top_of_mem Finset.univ (fun j' => T i j')
        (fun j' _ => hT_ne_bot i j') (Finset.mem_univ j) hT_top
    have hsum_top : ∑ i' : n, ∑ j' : n, T i' j' = ⊤ :=
      ereal_sum_eq_top_of_mem Finset.univ (fun i' => ∑ j' : n, T i' j')
        (fun i' _ => h_row_ne_bot i') (Finset.mem_univ i) hrow_top
    rw [h0] at hsum_top
    exact EReal.zero_ne_top hsum_top
  let t : n → n → ℝ := fun i j =>
    if p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0 then 0
    else w i j * p i * (Real.log (p i) - Real.log (q j))
  have hT_eq_t : ∀ i j, T i j = ((t i j : ℝ) : EReal) := by
    intro i j
    change (if p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0 then (0 : EReal)
      else if q j = 0 then ⊤
      else ((w i j * p i * (Real.log (p i) - Real.log (q j)) : ℝ) : EReal)) =
      (((if p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0 then 0
        else w i j * p i * (Real.log (p i) - Real.log (q j)) : ℝ) : EReal))
    by_cases hij : p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0
    · rw [if_pos hij, if_pos hij, EReal.coe_zero]
    · rw [if_neg hij, if_neg hij, if_neg (hq_ne_zero i j hij)]
  have ht_sum : ∑ i : n, ∑ j : n, t i j = 0 := by
    have h0' : (((∑ i : n, ∑ j : n, t i j : ℝ) : EReal)) = 0 := by
      rw [← ereal_coe_sum]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h0
      rw [← ereal_coe_sum]
      exact Finset.sum_congr rfl fun j _ => (hT_eq_t i j).symm
    exact_mod_cast h0'
  have ht_ge : ∀ i j, w i j * (p i - q j) ≤ t i j := by
    intro i j
    dsimp [t]
    by_cases hij : p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0
    · rw [if_pos hij]
      rcases hij with hpi | hwij
      · rw [hpi, zero_sub, mul_neg, Left.neg_nonpos_iff]
        exact mul_nonneg (hw_nonneg i j) (hq_nonneg j)
      · have hw0 : w i j = 0 := by dsimp [w]; rw [hwij, zero_pow two_ne_zero]
        rw [hw0, zero_mul]
    · rw [if_neg hij]
      have hq_nz := hq_ne_zero i j hij
      have hij' : p i ≠ 0 ∧ ‖inner ℂ (u i) (v j)‖ ≠ 0 := not_or.mp hij
      have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) hij'.1.symm
      have hq_pos : 0 < q j := lt_of_le_of_ne (hq_nonneg j) hq_nz.symm
      have h_div_pos : 0 < q j / p i := div_pos hq_pos hp_pos
      have hlog := (log_add_one_le_and_eq h_div_pos).1
      rw [Real.log_div hq_pos.ne' hp_pos.ne'] at hlog
      have hlog2 : p i - q j ≤ p i * (Real.log (p i) - Real.log (q j)) := by
        have hmul := mul_le_mul_of_nonneg_left hlog hp_pos.le
        have hcancel : p i * (q j / p i) = q j := mul_div_cancel₀ (q j) hp_pos.ne'
        linarith
      have hmul2 := mul_le_mul_of_nonneg_left hlog2 (hw_nonneg i j)
      linarith
  have hw_sum_j : ∀ i, ∑ j : n, w i j = 1 := by
    intro i
    dsimp [w]
    rw [onb_sum_inner_sq_left v (u i), u.orthonormal.1 i, one_pow]
  have hw_sum_i : ∀ j, ∑ i : n, w i j = 1 := by
    intro j
    dsimp [w]
    rw [onb_sum_inner_sq_right u (v j), v.orthonormal.1 j, one_pow]
  have hp_sum : ∑ i : n, p i = 1 := by
    have htr := hH.1.trace_eq_sum_eigenvalues
    rw [hρ.2] at htr
    have hre := congr_arg Complex.re htr
    simpa [p, Complex.re_sum] using hre.symm
  have hq_sum : ∑ j : n, q j = 1 := by
    have htr := hH.2.trace_eq_sum_eigenvalues
    rw [hσ.2] at htr
    have hre := congr_arg Complex.re htr
    simpa [q, Complex.re_sum] using hre.symm
  have h_lower_sum : ∑ i : n, ∑ j : n, w i j * (p i - q j) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [Finset.sum_comm (f := fun i j => w i j * q j)]
    simp_rw [← Finset.sum_mul, hw_sum_j, hw_sum_i, one_mul, hp_sum, hq_sum, sub_self]
  have ht_eq : ∀ i j, t i j = w i j * (p i - q j) := by
    have h_row_le : ∀ i, ∑ j : n, w i j * (p i - q j) ≤ ∑ j : n, t i j :=
      fun i => Finset.sum_le_sum (fun j _ => ht_ge i j)
    have h_row_eq : ∀ i ∈ (Finset.univ : Finset n),
        ∑ j : n, w i j * (p i - q j) = ∑ j : n, t i j :=
      (Finset.sum_eq_sum_iff_of_le (fun i _ => h_row_le i)).mp (h_lower_sum.trans ht_sum.symm)
    intro i j
    have h_col_eq : ∀ j' ∈ (Finset.univ : Finset n),
        w i j' * (p i - q j') = t i j' :=
      (Finset.sum_eq_sum_iff_of_le (fun j' _ => ht_ge i j')).mp (h_row_eq i (Finset.mem_univ i))
    exact (h_col_eq j (Finset.mem_univ j)).symm
  have hpq_eq : ∀ i j, ‖inner ℂ (u i) (v j)‖ ≠ 0 → p i = q j := by
    intro i j h_inner
    have hw_pos : 0 < w i j := sq_pos_of_ne_zero h_inner
    have h_eq := ht_eq i j
    dsimp [t] at h_eq
    by_cases hpi : p i = 0
    · rw [if_pos (Or.inl hpi), hpi, zero_sub, mul_neg] at h_eq
      have hqj : q j = 0 := by nlinarith
      rw [hpi, hqj]
    · have hij : ¬(p i = 0 ∨ ‖inner ℂ (u i) (v j)‖ = 0) := not_or.mpr ⟨hpi, h_inner⟩
      rw [if_neg hij] at h_eq
      have hq_nz := hq_ne_zero i j hij
      have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)
      have hq_pos : 0 < q j := lt_of_le_of_ne (hq_nonneg j) (Ne.symm hq_nz)
      have h_div_pos : 0 < q j / p i := div_pos hq_pos hp_pos
      have h_log_eq : Real.log (q j / p i) + 1 = q j / p i := by
        rw [Real.log_div hq_pos.ne' hp_pos.ne']
        have h_cancel : p i * (Real.log (p i) - Real.log (q j)) = p i - q j := by nlinarith
        have h_cancel_div : p i * (Real.log (p i) - Real.log (q j)) / p i = (p i - q j) / p i :=
          congr_arg (· / p i) h_cancel
        have h_div : (p i - q j) / p i = 1 - q j / p i := by
          rw [sub_div, div_self hp_pos.ne']
        have h_div2 : p i * (Real.log (p i) - Real.log (q j)) / p i =
            Real.log (p i) - Real.log (q j) := mul_div_cancel_left₀ _ hp_pos.ne'
        linarith
      have h1 := (log_add_one_le_and_eq h_div_pos).2.mp h_log_eq
      exact ((div_eq_one_iff_eq hp_pos.ne').mp h1).symm
  let U1 : Matrix n n ℂ := hH.1.eigenvectorUnitary
  let U2 : Matrix n n ℂ := hH.2.eigenvectorUnitary
  have hU1_mem := hH.1.eigenvectorUnitary.2
  have hU2_mem := hH.2.eigenvectorUnitary.2
  have hU1_mul : U1 * U1ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU1_mem
  have hU2_mul : U2 * U2ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU2_mem
  have h_comm : U2ᴴ * U1 * diagonal (fun i => (p i : ℂ)) =
      diagonal (fun j => (q j : ℂ)) * (U2ᴴ * U1) := by
    ext j i
    rw [mul_diagonal, diagonal_mul]
    by_cases h_zero : (U2ᴴ * U1) j i = 0
    · rw [h_zero, zero_mul, mul_zero]
    · have h_entry : (U2ᴴ * U1) j i = inner ℂ (v j) (u i) := by
        rw [mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
        refine Finset.sum_congr rfl fun x _ => ?_
        dsimp [U1, U2, u, v, Matrix.IsHermitian.eigenvectorUnitary_apply]
        ring
      have h_norm_ne : ‖inner ℂ (u i) (v j)‖ ≠ 0 := by
        rw [norm_inner_symm, norm_ne_zero_iff, ← h_entry]
        exact h_zero
      rw [hpq_eq i j h_norm_ne]
      ring
  have hρ_spec : ρ = U1 * diagonal (fun i => (p i : ℂ)) * U1ᴴ := by
    conv_lhs => rw [hH.1.spectral_theorem]
    rfl
  have hσ_spec : σ = U2 * diagonal (fun j => (q j : ℂ)) * U2ᴴ := by
    conv_lhs => rw [hH.2.spectral_theorem]
    rfl
  calc ρ = 1 * (U1 * diagonal (fun i => (p i : ℂ)) * U1ᴴ) := by rw [← hρ_spec, Matrix.one_mul]
    _ = (U2 * U2ᴴ) * (U1 * diagonal (fun i => (p i : ℂ)) * U1ᴴ) := by rw [hU2_mul]
    _ = U2 * (U2ᴴ * U1 * diagonal (fun i => (p i : ℂ))) * U1ᴴ := by simp only [Matrix.mul_assoc]
    _ = U2 * (diagonal (fun j => (q j : ℂ)) * (U2ᴴ * U1)) * U1ᴴ := by rw [h_comm]
    _ = (U2 * diagonal (fun j => (q j : ℂ)) * U2ᴴ) * (U1 * U1ᴴ) := by simp only [Matrix.mul_assoc]
    _ = σ := by rw [hU1_mul, Matrix.mul_one, ← hσ_spec]

/-! ### Part 2: Partial traces and vanishing algebraic relative entropy -/

lemma psd_traceRight {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    {M : Matrix (A × B) (A × B) ℂ} (hM : M.PosSemidef) : (traceRight M).PosSemidef := by
  have : traceRight M = ∑ k, M.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
    ext i j; simp [traceRight, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun k _ => hM.submatrix _

lemma psd_traceLeft {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    {M : Matrix (A × B) (A × B) ℂ} (hM : M.PosSemidef) : (traceLeft M).PosSemidef := by
  have : traceLeft M = ∑ k, M.submatrix (fun i => (k, i)) (fun i => (k, i)) := by
    ext i j; simp [traceLeft, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun k _ => hM.submatrix _

lemma tr_traceRight {A B : Type} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ) :
    (traceRight M).trace = M.trace := by
  simp [traceRight, Matrix.trace, Fintype.sum_prod_type]

lemma tr_traceLeft {A B : Type} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ) :
    (traceLeft M).trace = M.trace := by
  simp [traceLeft, Matrix.trace, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma isDensityMatrix_conj_isometry {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (V : Matrix A B ℂ) (hV : IsIsometry V)
    {ρ : Matrix B B ℂ} (hρ : IsDensityMatrix ρ) : IsDensityMatrix (V * ρ * Vᴴ) := by
  refine ⟨hρ.1.mul_mul_conjTranspose_same V, ?_⟩
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul, hρ.2]

lemma isDensityMatrix_traceRight {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    {M : Matrix (A × B) (A × B) ℂ} (hM : IsDensityMatrix M) : IsDensityMatrix (traceRight M) :=
  ⟨psd_traceRight hM.1, by rw [tr_traceRight, hM.2]⟩

lemma isDensityMatrix_traceLeft {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    {M : Matrix (A × B) (A × B) ℂ} (hM : IsDensityMatrix M) : IsDensityMatrix (traceLeft M) :=
  ⟨psd_traceLeft hM.1, by rw [tr_traceLeft, hM.2]⟩

lemma algebraicRelEntropyRight_eq_zero_of_traceLeft_eq {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    {ρ σ : Matrix C C ℂ}
    (h_eq : ∀ a : Fin N, traceLeft (diagBlock U ρ a) = traceLeft (diagBlock U σ a)) :
    algebraicRelEntropyRight U ρ σ = 0 := by
  have hw : ∀ a : Fin N, blockWeight U ρ a = blockWeight U σ a := by
    intro a
    unfold blockWeight
    rw [← tr_traceLeft (diagBlock U ρ a), ← tr_traceLeft (diagBlock U σ a), h_eq a]
  have hs : ∀ a : Fin N, blockStateRight U ρ a = blockStateRight U σ a := by
    intro a
    unfold blockStateRight
    rw [hw a, h_eq a]
  unfold algebraicRelEntropyRight
  have h1 : ∑ a : Fin N, classicalRelTerm (blockWeight U ρ a) (blockWeight U σ a) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hw a, classicalRelTerm_self]
  have h2 : ∑ a : Fin N, ((blockWeight U ρ a : ℝ) : EReal) *
      relativeEntropy (blockStateRight U ρ a) (blockStateRight U σ a) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hs a, relativeEntropy_self, mul_zero]
  rw [h1, h2, add_zero]

lemma algebraicRelEntropyLeft_eq_zero_of_traceRight_eq {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    {ρ σ : Matrix C C ℂ}
    (h_eq : ∀ a : Fin N, traceRight (diagBlock U ρ a) = traceRight (diagBlock U σ a)) :
    algebraicRelEntropyLeft U ρ σ = 0 := by
  have hw : ∀ a : Fin N, blockWeight U ρ a = blockWeight U σ a := by
    intro a
    unfold blockWeight
    rw [← tr_traceRight (diagBlock U ρ a), ← tr_traceRight (diagBlock U σ a), h_eq a]
  have hs : ∀ a : Fin N, blockStateLeft U ρ a = blockStateLeft U σ a := by
    intro a
    unfold blockStateLeft
    rw [hw a, h_eq a]
  unfold algebraicRelEntropyLeft
  have h1 : ∑ a : Fin N, classicalRelTerm (blockWeight U ρ a) (blockWeight U σ a) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hw a, classicalRelTerm_self]
  have h2 : ∑ a : Fin N, ((blockWeight U ρ a : ℝ) : EReal) *
      relativeEntropy (blockStateLeft U ρ a) (blockStateLeft U σ a) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hs a, relativeEntropy_self, mul_zero]
  rw [h1, h2, add_zero]

/-! ### Part 3: General Gram-matrix pseudo-inverse lifting -/

noncomputable def familyGram {N : ℕ} {d1 d2 : Fin N → ℕ} {K L : Type} [Fintype K] [Fintype L]
    (S : ∀ a : Fin N, Fin (d1 a) → Matrix K (Fin (d2 a) × L) ℂ) (a : Fin N) :
    Matrix (Fin (d2 a) × L) (Fin (d2 a) × L) ℂ :=
  if h : 0 < d1 a then (S a ⟨0, h⟩)ᴴ * S a ⟨0, h⟩ else 0

lemma familyGram_posSemidef {N : ℕ} {d1 d2 : Fin N → ℕ} {K L : Type} [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (S : ∀ a : Fin N, Fin (d1 a) → Matrix K (Fin (d2 a) × L) ℂ) (a : Fin N) :
    (familyGram S a).PosSemidef := by
  unfold familyGram
  by_cases h : 0 < d1 a
  · rw [dif_pos h]
    exact posSemidef_conjTranspose_mul_self _
  · rw [dif_neg h]
    exact PosSemidef.zero

noncomputable def familyGramInv {N : ℕ} {d1 d2 : Fin N → ℕ} {K L : Type} [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (S : ∀ a : Fin N, Fin (d1 a) → Matrix K (Fin (d2 a) × L) ℂ) (a : Fin N) :
    Matrix (Fin (d2 a) × L) (Fin (d2 a) × L) ℂ :=
  let hG := (familyGram_posSemidef S a).isHermitian
  let UG : Matrix (Fin (d2 a) × L) (Fin (d2 a) × L) ℂ := hG.eigenvectorUnitary
  UG * diagonal (fun m => (((hG.eigenvalues m)⁻¹ : ℝ) : ℂ)) * UGᴴ

lemma familyGramInv_conjTranspose {N : ℕ} {d1 d2 : Fin N → ℕ} {K L : Type} [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (S : ∀ a : Fin N, Fin (d1 a) → Matrix K (Fin (d2 a) × L) ℂ) (a : Fin N) :
    (familyGramInv S a)ᴴ = familyGramInv S a := by
  dsimp [familyGramInv]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  congr 2
  ext m m'
  rw [conjTranspose_apply]
  by_cases h : m = m'
  · subst h; simp
  · rw [diagonal_apply_ne _ (Ne.symm h), diagonal_apply_ne _ h, star_zero]

lemma mul_familyGramInv_mul_self {N : ℕ} {d1 d2 : Fin N → ℕ} {K L : Type} [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (S : ∀ a : Fin N, Fin (d1 a) → Matrix K (Fin (d2 a) × L) ℂ) (a : Fin N) (i : Fin (d1 a))
    (h_same : (S a i)ᴴ * S a i = familyGram S a) :
    S a i * familyGramInv S a * familyGram S a = S a i := by
  let hG := (familyGram_posSemidef S a).isHermitian
  let UG : Matrix (Fin (d2 a) × L) (Fin (d2 a) × L) ℂ := hG.eigenvectorUnitary
  let ev := hG.eigenvalues
  let u := hG.eigenvectorBasis
  have hUG1 : UGᴴ * UG = 1 := Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
  have hUG2 : UG * UGᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
  have hG_spec : familyGram S a = UG * diagonal (fun m => (ev m : ℂ)) * UGᴴ := by
    conv_lhs => rw [hG.spectral_theorem]
    rfl
  change S a i * (UG * diagonal (fun m => (((ev m)⁻¹ : ℝ) : ℂ)) * UGᴴ) * familyGram S a = S a i
  rw [hG_spec]
  have h_assoc : S a i * (UG * diagonal (fun m => (((ev m)⁻¹ : ℝ) : ℂ)) * UGᴴ) *
      (UG * diagonal (fun m => (ev m : ℂ)) * UGᴴ) =
      (S a i * UG * (diagonal (fun m => (((ev m)⁻¹ : ℝ) : ℂ)) * diagonal (fun m => (ev m : ℂ)))) * UGᴴ := by
    calc S a i * (UG * diagonal (fun m => (((ev m)⁻¹ : ℝ) : ℂ)) * UGᴴ) *
          (UG * diagonal (fun m => (ev m : ℂ)) * UGᴴ)
      _ = S a i * UG * diagonal (fun m => (((ev m)⁻¹ : ℝ) : ℂ)) * (UGᴴ * UG) *
          diagonal (fun m => (ev m : ℂ)) * UGᴴ := by simp only [Matrix.mul_assoc]
      _ = (S a i * UG * (diagonal (fun m => (((ev m)⁻¹ : ℝ) : ℂ)) * diagonal (fun m => (ev m : ℂ)))) * UGᴴ := by
          rw [hUG1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h_assoc, diagonal_mul_diagonal]
  have h_col : S a i * UG * diagonal (fun m => (((ev m)⁻¹ : ℝ) : ℂ) * (ev m : ℂ)) = S a i * UG := by
    ext k m
    rw [mul_diagonal]
    by_cases hm : ev m = 0
    · rw [hm, _root_.inv_zero, Complex.ofReal_zero, zero_mul, mul_zero]
      have h_norm : star (S a i *ᵥ (u m).ofLp) ⬝ᵥ (S a i *ᵥ (u m).ofLp) = 0 := by
        rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h_same,
          hG.mulVec_eigenvectorBasis m]
        change star (u m).ofLp ⬝ᵥ ((ev m : ℂ) • (u m).ofLp) = 0
        rw [hm, Complex.ofReal_zero, zero_smul, dotProduct_zero]
      have h_vec_zero : (S a i *ᵥ (u m).ofLp) k = 0 :=
        congr_fun (dotProduct_star_self_eq_zero.mp h_norm) k
      have h_entry : (S a i * UG) k m = (S a i *ᵥ (u m).ofLp) k := by
        rw [mul_apply, mulVec, dotProduct]
        rfl
      rw [h_entry, h_vec_zero]
    · have h_inv : (((ev m)⁻¹ : ℝ) : ℂ) * (ev m : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hm, Complex.ofReal_one]
      rw [h_inv, mul_one]
  rw [h_col, Matrix.mul_assoc, hUG2, Matrix.mul_one]

noncomputable def familyLift {N : ℕ} {d1 d2 : Fin N → ℕ} {K L : Type} [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (S : ∀ a : Fin N, Fin (d1 a) → Matrix K (Fin (d2 a) × L) ℂ)
    (x : ∀ a : Fin N, Matrix (Fin (d1 a)) (Fin (d1 a)) ℂ) : Matrix K K ℂ :=
  ∑ a : Fin N, ∑ i' : Fin (d1 a), ∑ i : Fin (d1 a),
    x a i' i • (S a i' * familyGramInv S a * (S a i)ᴴ)

lemma familyLift_conjTranspose {N : ℕ} {d1 d2 : Fin N → ℕ} {K L : Type} [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (S : ∀ a : Fin N, Fin (d1 a) → Matrix K (Fin (d2 a) × L) ℂ)
    (x : ∀ a : Fin N, Matrix (Fin (d1 a)) (Fin (d1 a)) ℂ) :
    (familyLift S x)ᴴ = familyLift S (fun a => (x a)ᴴ) := by
  unfold familyLift
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [conjTranspose_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, familyGramInv_conjTranspose, Matrix.mul_assoc]
  rfl

lemma matrix_sum_mul {α K M P : Type*} [Fintype M] (s : Finset α)
    (f : α → Matrix K M ℂ) (B : Matrix M P ℂ) :
    (∑ a ∈ s, f a) * B = ∑ a ∈ s, f a * B := by
  ext k p
  simp only [mul_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma familyLift_mul_slice {N : ℕ} {d1 d2 : Fin N → ℕ} {K L : Type} [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (S : ∀ a : Fin N, Fin (d1 a) → Matrix K (Fin (d2 a) × L) ℂ)
    (h_same : ∀ a (i : Fin (d1 a)), (S a i)ᴴ * S a i = familyGram S a)
    (h_orth : ∀ (a' a : Fin N) (i' : Fin (d1 a')) (i : Fin (d1 a)),
      (⟨a', i'⟩ : Σ a, Fin (d1 a)) ≠ ⟨a, i⟩ → (S a' i')ᴴ * S a i = 0)
    (x : ∀ a : Fin N, Matrix (Fin (d1 a)) (Fin (d1 a)) ℂ)
    (a₀ : Fin N) (i₀ : Fin (d1 a₀)) :
    familyLift S x * S a₀ i₀ = ∑ i' : Fin (d1 a₀), x a₀ i' i₀ • S a₀ i' := by
  unfold familyLift
  rw [matrix_sum_mul, Finset.sum_eq_single a₀]
  · rw [matrix_sum_mul]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [matrix_sum_mul, Finset.sum_eq_single i₀]
    · rw [Matrix.smul_mul, Matrix.mul_assoc, h_same a₀ i₀,
        mul_familyGramInv_mul_self S a₀ i' (h_same a₀ i')]
    · intro i _ hi
      have hne : (⟨a₀, i⟩ : Σ a, Fin (d1 a)) ≠ ⟨a₀, i₀⟩ := fun h => hi (Sigma.mk.inj_iff.mp h).2.eq
      rw [Matrix.smul_mul, Matrix.mul_assoc, h_orth a₀ a₀ i i₀ hne, Matrix.mul_zero, smul_zero]
    · intro h; exact (h (Finset.mem_univ i₀)).elim
  · intro a _ ha
    rw [matrix_sum_mul]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [matrix_sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : (⟨a, i⟩ : Σ a, Fin (d1 a)) ≠ ⟨a₀, i₀⟩ := fun h => ha (congr_arg Sigma.fst h)
    rw [Matrix.smul_mul, Matrix.mul_assoc, h_orth a a₀ i i₀ hne, Matrix.mul_zero, smul_zero]
  · intro h; exact (h (Finset.mem_univ a₀)).elim

/-! ### Part 4: Pure code states, two-vector superpositions, and polarization -/

def vecMatrix {Idx : Type} (φ : Idx → ℂ) : Matrix (Fin 1) Idx ℂ :=
  fun _ p => star (φ p)

def sigmaVec {Idx : Type} [Fintype Idx] (φ : Idx → ℂ) : Matrix Idx Idx ℂ :=
  (vecMatrix φ)ᴴ * vecMatrix φ

lemma sigmaVec_apply {Idx : Type} [Fintype Idx] (φ : Idx → ℂ) (p q : Idx) :
    sigmaVec φ p q = φ p * star (φ q) := by
  simp [sigmaVec, vecMatrix, mul_apply]

lemma sigmaVec_posSemidef {Idx : Type} [Fintype Idx] [DecidableEq Idx] (φ : Idx → ℂ) :
    (sigmaVec φ).PosSemidef :=
  posSemidef_conjTranspose_mul_self (vecMatrix φ)

def codeState {Idx C : Type} [Fintype Idx] [Fintype C]
    (U : Matrix Idx C ℂ) (φ : Idx → ℂ) : Matrix C C ℂ :=
  Uᴴ * sigmaVec φ * U

lemma codeState_posSemidef {Idx C : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [DecidableEq C] (U : Matrix Idx C ℂ) (φ : Idx → ℂ) :
    (codeState U φ).PosSemidef := by
  unfold codeState
  have h := (sigmaVec_posSemidef φ).mul_mul_conjTranspose_same Uᴴ
  simpa [conjTranspose_conjTranspose] using h

lemma codeState_trace {Idx C : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [DecidableEq C] (U : Matrix Idx C ℂ) (hU : IsUnitaryMatrix U) (φ : Idx → ℂ) :
    (codeState U φ).trace = ∑ p : Idx, φ p * star (φ p) := by
  unfold codeState
  rw [Matrix.trace_mul_cycle, hU.2, Matrix.one_mul]
  simp [ Matrix.trace, sigmaVec_apply]

lemma mul_codeState_mul_conjTranspose_U {Idx C : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [DecidableEq C] (U : Matrix Idx C ℂ) (hU : IsUnitaryMatrix U) (φ : Idx → ℂ) :
    U * codeState U φ * Uᴴ = sigmaVec φ := by
  calc U * (Uᴴ * sigmaVec φ * U) * Uᴴ
      = (U * Uᴴ) * sigmaVec φ * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = sigmaVec φ := by rw [hU.2, Matrix.one_mul, Matrix.mul_one]

lemma diagBlock_codeState_apply {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (φ : BlockIndex N dr drb → ℂ)
    (a : Fin N) (ij i'j' : Fin (dr a) × Fin (drb a)) :
    diagBlock U (codeState U φ) a ij i'j' = φ ⟨a, ij⟩ * star (φ ⟨a, i'j'⟩) := by
  unfold diagBlock
  rw [mul_codeState_mul_conjTranspose_U U hU φ, submatrix_apply, sigmaVec_apply]

lemma mul_sigmaVec_mul_conjTranspose_apply {Idx K : Type} [Fintype Idx] [Fintype K]
    (W : Matrix K Idx ℂ) (φ : Idx → ℂ) (k k' : K) :
    (W * sigmaVec φ * Wᴴ) k k' = (W *ᵥ φ) k * star ((W *ᵥ φ) k') := by
  have h1 : W * sigmaVec φ * Wᴴ = (vecMatrix φ * Wᴴ)ᴴ * (vecMatrix φ * Wᴴ) := by
    simp only [sigmaVec, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [h1, mul_apply, Fin.sum_univ_one, conjTranspose_apply]
  have h2 : ∀ x : K, (vecMatrix φ * Wᴴ) 0 x = star ((W *ᵥ φ) x) := by
    intro x
    simp only [mul_apply, vecMatrix, conjTranspose_apply, mulVec, dotProduct, star_sum, star_mul]
  rw [h2 k, h2 k', star_star]

lemma V_mul_codeState_mul_V_conjTranspose {Idx C K : Type} [Fintype Idx] [Fintype C] [Fintype K]
    (U : Matrix Idx C ℂ) (V : Matrix K C ℂ) (φ : Idx → ℂ) :
    V * codeState U φ * Vᴴ = (V * Uᴴ) * sigmaVec φ * (V * Uᴴ)ᴴ := by
  simp only [codeState, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

def basisVec {Idx : Type} [DecidableEq Idx] (p : Idx) (x : Idx) : ℂ :=
  if x = p then 1 else 0

lemma star_basisVec {Idx : Type} [DecidableEq Idx] (p x : Idx) :
    star (basisVec p x) = basisVec p x := by
  unfold basisVec; split_ifs <;> simp

lemma sum_basisVec_mul {Idx : Type} [Fintype Idx] [DecidableEq Idx] (p : Idx) (f : Idx → ℂ) :
    ∑ x : Idx, basisVec p x * f x = f p := by
  simp [basisVec]

lemma sum_mul_basisVec {Idx : Type} [Fintype Idx] [DecidableEq Idx] (p : Idx) (f : Idx → ℂ) :
    ∑ x : Idx, f x * basisVec p x = f p := by
  simp [basisVec]

def linVec {Idx : Type} [DecidableEq Idx] (p q : Idx) (α β : ℂ) (x : Idx) : ℂ :=
  α * basisVec p x + β * basisVec q x

lemma sum_linVec_mul_star {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (p q : Idx) (α β : ℂ) :
    ∑ x : Idx, linVec p q α β x * star (linVec p q α β x) =
      α * star α + α * star β * basisVec q p + β * star α * basisVec p q + β * star β := by
  have h_expand : ∀ x : Idx, linVec p q α β x * star (linVec p q α β x) =
      (α * star α) * basisVec p x + (α * star β) * (basisVec p x * basisVec q x) +
      (β * star α) * (basisVec q x * basisVec p x) + (β * star β) * basisVec q x := by
    intro x
    unfold linVec
    rw [star_add, star_mul, star_mul, star_basisVec, star_basisVec]
    have hp2 : basisVec p x * basisVec p x = basisVec p x := by
      unfold basisVec; split_ifs <;> ring
    have hq2 : basisVec q x * basisVec q x = basisVec q x := by
      unfold basisVec; split_ifs <;> ring
    linear_combination (α * star α) * hp2 + (β * star β) * hq2
  simp_rw [h_expand, Finset.sum_add_distrib, ← Finset.mul_sum, sum_basisVec_mul]
  have hp1 : ∑ x : Idx, basisVec p x = 1 := by simpa using sum_basisVec_mul p (fun _ => 1)
  have hq1 : ∑ x : Idx, basisVec q x = 1 := by simpa using sum_basisVec_mul q (fun _ => 1)
  rw [hp1, hq1, mul_one, mul_one]

lemma mulVec_linVec {Idx K : Type} [Fintype Idx] [DecidableEq Idx]
    (W : Matrix K Idx ℂ) (p q : Idx) (α β : ℂ) (k : K) :
    (W *ᵥ linVec p q α β) k = α * W k p + β * W k q := by
  simp only [mulVec, dotProduct, linVec, mul_add, ← mul_assoc, Finset.sum_add_distrib,
    sum_mul_basisVec]
  ring

noncomputable def s2inv : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma star_s2inv : star s2inv = s2inv := by
  unfold s2inv
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

lemma s2inv_mul_s2inv : s2inv * s2inv = (2 : ℂ)⁻¹ := by
  unfold s2inv
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma isDensityMatrix_codeState_basisVec {Idx C : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [DecidableEq C] (U : Matrix Idx C ℂ) (hU : IsUnitaryMatrix U) (p : Idx) :
    IsDensityMatrix (codeState U (linVec p p 1 0)) := by
  refine ⟨codeState_posSemidef U _, ?_⟩
  rw [codeState_trace U hU, sum_linVec_mul_star]
  simp

lemma isDensityMatrix_codeState_twoVec {Idx C : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [DecidableEq C] (U : Matrix Idx C ℂ) (hU : IsUnitaryMatrix U)
    {p q : Idx} (hpq : p ≠ q) {c : ℂ} (hc : c * star c = 1) :
    IsDensityMatrix (codeState U (linVec p q s2inv (s2inv * c))) := by
  refine ⟨codeState_posSemidef U _, ?_⟩
  rw [codeState_trace U hU, sum_linVec_mul_star]
  have hpq1 : basisVec p q = 0 := if_neg hpq.symm
  have hpq2 : basisVec q p = 0 := if_neg hpq
  rw [hpq1, hpq2, mul_zero, mul_zero, add_zero, add_zero, star_mul, star_s2inv]
  calc s2inv * s2inv + s2inv * c * (star c * s2inv)
      = (s2inv * s2inv) * (1 + c * star c) := by ring
    _ = 1 := by rw [s2inv_mul_s2inv, hc]; norm_num

def F_R {Idx R Rb : Type} [Fintype R] (W : Matrix (R × Rb) Idx ℂ)
    (b b' : Rb) (p q : Idx) : ℂ :=
  ∑ r : R, W (r, b) p * star (W (r, b') q)

def F_Rb {Idx R Rb : Type} [Fintype Rb] (W : Matrix (R × Rb) Idx ℂ)
    (r r' : R) (p q : Idx) : ℂ :=
  ∑ b : Rb, W (r, b) p * star (W (r', b) q)

lemma traceLeft_codeState_linVec {Idx C R Rb : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [Fintype R] [Fintype Rb]
    (U : Matrix Idx C ℂ) (V : Matrix (R × Rb) C ℂ)
    (p q : Idx) (α β : ℂ) (b b' : Rb) :
    traceLeft (V * codeState U (linVec p q α β) * Vᴴ) b b' =
      (α * star α) * F_R (V * Uᴴ) b b' p p +
      (α * star β) * F_R (V * Uᴴ) b b' p q +
      (β * star α) * F_R (V * Uᴴ) b b' q p +
      (β * star β) * F_R (V * Uᴴ) b b' q q := by
  rw [V_mul_codeState_mul_V_conjTranspose]
  unfold traceLeft F_R
  simp_rw [mul_sigmaVec_mul_conjTranspose_apply, mulVec_linVec]
  have h_term : ∀ r : R,
      (α * (V * Uᴴ) (r, b) p + β * (V * Uᴴ) (r, b) q) *
        star (α * (V * Uᴴ) (r, b') p + β * (V * Uᴴ) (r, b') q) =
      (α * star α) * ((V * Uᴴ) (r, b) p * star ((V * Uᴴ) (r, b') p)) +
      (α * star β) * ((V * Uᴴ) (r, b) p * star ((V * Uᴴ) (r, b') q)) +
      (β * star α) * ((V * Uᴴ) (r, b) q * star ((V * Uᴴ) (r, b') p)) +
      (β * star β) * ((V * Uᴴ) (r, b) q * star ((V * Uᴴ) (r, b') q)) := by
    intro r; rw [star_add, star_mul, star_mul]; ring
  simp_rw [h_term, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma traceRight_codeState_linVec {Idx C R Rb : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [Fintype R] [Fintype Rb]
    (U : Matrix Idx C ℂ) (V : Matrix (R × Rb) C ℂ)
    (p q : Idx) (α β : ℂ) (r r' : R) :
    traceRight (V * codeState U (linVec p q α β) * Vᴴ) r r' =
      (α * star α) * F_Rb (V * Uᴴ) r r' p p +
      (α * star β) * F_Rb (V * Uᴴ) r r' p q +
      (β * star α) * F_Rb (V * Uᴴ) r r' q p +
      (β * star β) * F_Rb (V * Uᴴ) r r' q q := by
  rw [V_mul_codeState_mul_V_conjTranspose]
  unfold traceRight F_Rb
  simp_rw [mul_sigmaVec_mul_conjTranspose_apply, mulVec_linVec]
  have h_term : ∀ b : Rb,
      (α * (V * Uᴴ) (r, b) p + β * (V * Uᴴ) (r, b) q) *
        star (α * (V * Uᴴ) (r', b) p + β * (V * Uᴴ) (r', b) q) =
      (α * star α) * ((V * Uᴴ) (r, b) p * star ((V * Uᴴ) (r', b) p)) +
      (α * star β) * ((V * Uᴴ) (r, b) p * star ((V * Uᴴ) (r', b) q)) +
      (β * star α) * ((V * Uᴴ) (r, b) q * star ((V * Uᴴ) (r', b) p)) +
      (β * star β) * ((V * Uᴴ) (r, b) q * star ((V * Uᴴ) (r', b) q)) := by
    intro b; rw [star_add, star_mul, star_mul]; ring
  simp_rw [h_term, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma traceLeft_twoVec_sub {Idx C R Rb : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [Fintype R] [Fintype Rb]
    (U : Matrix Idx C ℂ) (V : Matrix (R × Rb) C ℂ)
    (p q : Idx) (c : ℂ) (b b' : Rb) :
    traceLeft (V * codeState U (linVec p q s2inv (s2inv * c)) * Vᴴ) b b' -
      traceLeft (V * codeState U (linVec p q s2inv (s2inv * (-c))) * Vᴴ) b b' =
      star c * F_R (V * Uᴴ) b b' p q + c * F_R (V * Uᴴ) b b' q p := by
  rw [traceLeft_codeState_linVec, traceLeft_codeState_linVec]
  simp only [star_mul, star_neg, star_s2inv]
  have h_alg :
      (s2inv * s2inv * F_R (V * Uᴴ) b b' p p +
        s2inv * (star c * s2inv) * F_R (V * Uᴴ) b b' p q +
        s2inv * c * s2inv * F_R (V * Uᴴ) b b' q p +
        s2inv * c * (star c * s2inv) * F_R (V * Uᴴ) b b' q q) -
      (s2inv * s2inv * F_R (V * Uᴴ) b b' p p +
        s2inv * (-star c * s2inv) * F_R (V * Uᴴ) b b' p q +
        s2inv * -c * s2inv * F_R (V * Uᴴ) b b' q p +
        s2inv * -c * (-star c * s2inv) * F_R (V * Uᴴ) b b' q q) =
      (2 : ℂ) * (s2inv * s2inv) * (star c * F_R (V * Uᴴ) b b' p q + c * F_R (V * Uᴴ) b b' q p) := by ring
  rw [h_alg, s2inv_mul_s2inv, mul_inv_cancel₀ two_ne_zero, one_mul]

lemma traceRight_twoVec_sub {Idx C R Rb : Type} [Fintype Idx] [DecidableEq Idx]
    [Fintype C] [Fintype R] [Fintype Rb]
    (U : Matrix Idx C ℂ) (V : Matrix (R × Rb) C ℂ)
    (p q : Idx) (c : ℂ) (r r' : R) :
    traceRight (V * codeState U (linVec p q s2inv (s2inv * c)) * Vᴴ) r r' -
      traceRight (V * codeState U (linVec p q s2inv (s2inv * (-c))) * Vᴴ) r r' =
      star c * F_Rb (V * Uᴴ) r r' p q + c * F_Rb (V * Uᴴ) r r' q p := by
  rw [traceRight_codeState_linVec, traceRight_codeState_linVec]
  simp only [star_mul, star_neg, star_s2inv]
  have h_alg :
      (s2inv * s2inv * F_Rb (V * Uᴴ) r r' p p +
        s2inv * (star c * s2inv) * F_Rb (V * Uᴴ) r r' p q +
        s2inv * c * s2inv * F_Rb (V * Uᴴ) r r' q p +
        s2inv * c * (star c * s2inv) * F_Rb (V * Uᴴ) r r' q q) -
      (s2inv * s2inv * F_Rb (V * Uᴴ) r r' p p +
        s2inv * (-star c * s2inv) * F_Rb (V * Uᴴ) r r' p q +
        s2inv * -c * s2inv * F_Rb (V * Uᴴ) r r' q p +
        s2inv * -c * (-star c * s2inv) * F_Rb (V * Uᴴ) r r' q q) =
      (2 : ℂ) * (s2inv * s2inv) * (star c * F_Rb (V * Uᴴ) r r' p q + c * F_Rb (V * Uᴴ) r r' q p) := by ring
  rw [h_alg, s2inv_mul_s2inv, mul_inv_cancel₀ two_ne_zero, one_mul]

lemma eq_zero_of_one_and_I {x y : ℂ}
    (h1 : star (1 : ℂ) * x + (1 : ℂ) * y = 0)
    (hI : star Complex.I * x + Complex.I * y = 0) : x = 0 := by
  have h_star_I : star Complex.I = -Complex.I := by simp
  rw [star_one, one_mul, one_mul] at h1
  rw [h_star_I] at hI
  have h2x : (2 : ℂ) * x = 0 := by
    calc (2 : ℂ) * x
        = (x + y) - (Complex.I * Complex.I) * (x - y) := by
            rw [Complex.I_mul_I]; ring
      _ = (x + y) + Complex.I * (-Complex.I * x + Complex.I * y) := by ring
      _ = 0 := by rw [h1, hI, mul_zero, add_zero]
  exact (mul_eq_zero.mp h2x).resolve_left two_ne_zero

lemma traceLeft_diagBlock_linVec_indep_i {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U)
    (a₀ : Fin N) (i₁ i₂ : Fin (dr a₀)) (j₁ j₂ : Fin (drb a₀)) (α β : ℂ) (a : Fin N) :
    traceLeft (diagBlock U (codeState U (linVec ⟨a₀, (i₁, j₁)⟩ ⟨a₀, (i₁, j₂)⟩ α β)) a) =
    traceLeft (diagBlock U (codeState U (linVec ⟨a₀, (i₂, j₁)⟩ ⟨a₀, (i₂, j₂)⟩ α β)) a) := by
  ext k₁ k₂
  unfold traceLeft
  simp_rw [diagBlock_codeState_apply U hU]
  by_cases ha : a = a₀
  · subst ha
    have h_eval : ∀ (i₀ i : Fin (dr a)) (k : Fin (drb a)),
        linVec (⟨a, (i₀, j₁)⟩ : BlockIndex N dr drb) ⟨a, (i₀, j₂)⟩ α β ⟨a, (i, k)⟩ =
          if i = i₀ then (α * (if k = j₁ then 1 else 0) + β * (if k = j₂ then 1 else 0)) else 0 := by
      intro i₀ i k
      unfold linVec basisVec
      simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and]
      by_cases hi : i = i₀
      · subst hi; simp
      · simp [hi]
    simp_rw [h_eval]
    rw [Finset.sum_eq_single i₁, Finset.sum_eq_single i₂]
    · simp
    · intro i _ hi; simp [hi]
    · intro h; exact (h (Finset.mem_univ i₂)).elim
    · intro i _ hi; simp [hi]
    · intro h; exact (h (Finset.mem_univ i₁)).elim
  · have h_zero : ∀ (i₀ : Fin (dr a₀)) (i : Fin (dr a)) (k : Fin (drb a)),
        linVec (⟨a₀, (i₀, j₁)⟩ : BlockIndex N dr drb) ⟨a₀, (i₀, j₂)⟩ α β ⟨a, (i, k)⟩ = 0 := by
      intro i₀ i k
      unfold linVec basisVec
      have hne1 : (⟨a, (i, k)⟩ : BlockIndex N dr drb) ≠ ⟨a₀, (i₀, j₁)⟩ :=
        fun h => ha (congr_arg Sigma.fst h)
      have hne2 : (⟨a, (i, k)⟩ : BlockIndex N dr drb) ≠ ⟨a₀, (i₀, j₂)⟩ :=
        fun h => ha (congr_arg Sigma.fst h)
      rw [if_neg hne1, if_neg hne2, mul_zero, mul_zero, add_zero]
    simp_rw [h_zero]

lemma traceRight_diagBlock_linVec_indep_j {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U)
    (a₀ : Fin N) (i₁ i₂ : Fin (dr a₀)) (j₁ j₂ : Fin (drb a₀)) (α β : ℂ) (a : Fin N) :
    traceRight (diagBlock U (codeState U (linVec ⟨a₀, (i₁, j₁)⟩ ⟨a₀, (i₂, j₁)⟩ α β)) a) =
    traceRight (diagBlock U (codeState U (linVec ⟨a₀, (i₁, j₂)⟩ ⟨a₀, (i₂, j₂)⟩ α β)) a) := by
  ext k₁ k₂
  unfold traceRight
  simp_rw [diagBlock_codeState_apply U hU]
  by_cases ha : a = a₀
  · subst ha
    have h_eval : ∀ (j₀ : Fin (drb a)) (i : Fin (dr a)) (j : Fin (drb a)),
        linVec (⟨a, (i₁, j₀)⟩ : BlockIndex N dr drb) ⟨a, (i₂, j₀)⟩ α β ⟨a, (i, j)⟩ =
          if j = j₀ then (α * (if i = i₁ then 1 else 0) + β * (if i = i₂ then 1 else 0)) else 0 := by
      intro j₀ i j
      unfold linVec basisVec
      simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and]
      by_cases hj : j = j₀
      · subst hj; simp
      · simp [hj]
    simp_rw [h_eval]
    rw [Finset.sum_eq_single j₁, Finset.sum_eq_single j₂]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact (h (Finset.mem_univ j₂)).elim
    · intro j _ hj; simp [hj]
    · intro h; exact (h (Finset.mem_univ j₁)).elim
  · have h_zero : ∀ (j₀ : Fin (drb a₀)) (i : Fin (dr a)) (j : Fin (drb a)),
        linVec (⟨a₀, (i₁, j₀)⟩ : BlockIndex N dr drb) ⟨a₀, (i₂, j₀)⟩ α β ⟨a, (i, j)⟩ = 0 := by
      intro j₀ i j
      unfold linVec basisVec
      have hne1 : (⟨a, (i, j)⟩ : BlockIndex N dr drb) ≠ ⟨a₀, (i₁, j₀)⟩ :=
        fun h => ha (congr_arg Sigma.fst h)
      have hne2 : (⟨a, (i, j)⟩ : BlockIndex N dr drb) ≠ ⟨a₀, (i₂, j₀)⟩ :=
        fun h => ha (congr_arg Sigma.fst h)
      rw [if_neg hne1, if_neg hne2, mul_zero, mul_zero, add_zero]
    simp_rw [h_zero]

def projLeft {N : ℕ} {dr drb : Fin N → ℕ} (x : BlockIndex N dr drb) : Σ a, Fin (dr a) :=
  ⟨x.1, x.2.1⟩

def projRight {N : ℕ} {dr drb : Fin N → ℕ} (x : BlockIndex N dr drb) : Σ a, Fin (drb a) :=
  ⟨x.1, x.2.2⟩

lemma traceLeft_diagBlock_twoVec_neg_eq {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U)
    {a₁ a₂ : Fin N} {i₁ : Fin (dr a₁)} {i₂ : Fin (dr a₂)}
    (hne : (⟨a₁, i₁⟩ : Σ a, Fin (dr a)) ≠ ⟨a₂, i₂⟩)
    (j₁ : Fin (drb a₁)) (j₂ : Fin (drb a₂)) (c : ℂ) (a : Fin N) :
    traceLeft (diagBlock U (codeState U (linVec ⟨a₁, (i₁, j₁)⟩ ⟨a₂, (i₂, j₂)⟩ s2inv (s2inv * c))) a) =
    traceLeft (diagBlock U (codeState U (linVec ⟨a₁, (i₁, j₁)⟩ ⟨a₂, (i₂, j₂)⟩ s2inv (s2inv * (-c)))) a) := by
  ext k₁ k₂
  unfold traceLeft
  simp_rw [diagBlock_codeState_apply U hU]
  refine Finset.sum_congr rfl fun i _ => ?_
  let p : BlockIndex N dr drb := ⟨a₁, (i₁, j₁)⟩
  let q : BlockIndex N dr drb := ⟨a₂, (i₂, j₂)⟩
  let x₁ : BlockIndex N dr drb := ⟨a, (i, k₁)⟩
  let x₂ : BlockIndex N dr drb := ⟨a, (i, k₂)⟩
  have h_orth1 : basisVec p x₁ * basisVec q x₂ = 0 := by
    unfold basisVec
    by_cases hp : x₁ = p
    · have hq : x₂ ≠ q := fun hq =>
        hne ((congr_arg projLeft hp).symm.trans (congr_arg projLeft hq))
      rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  have h_orth2 : basisVec q x₁ * basisVec p x₂ = 0 := by
    unfold basisVec
    by_cases hq : x₁ = q
    · have hp : x₂ ≠ p := fun hp =>
        hne ((congr_arg projLeft hp).symm.trans (congr_arg projLeft hq))
      rw [if_neg hp, mul_zero]
    · rw [if_neg hq, zero_mul]
  change linVec p q s2inv (s2inv * c) x₁ * star (linVec p q s2inv (s2inv * c) x₂) =
    linVec p q s2inv (s2inv * (-c)) x₁ * star (linVec p q s2inv (s2inv * (-c)) x₂)
  unfold linVec
  simp only [star_add, star_mul, star_neg, star_s2inv, star_basisVec]
  linear_combination (2 * s2inv * s2inv * star c) * h_orth1 + (2 * s2inv * s2inv * c) * h_orth2

lemma traceRight_diagBlock_twoVec_neg_eq {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U)
    {a₁ a₂ : Fin N} {j₁ : Fin (drb a₁)} {j₂ : Fin (drb a₂)}
    (hne : (⟨a₁, j₁⟩ : Σ a, Fin (drb a)) ≠ ⟨a₂, j₂⟩)
    (i₁ : Fin (dr a₁)) (i₂ : Fin (dr a₂)) (c : ℂ) (a : Fin N) :
    traceRight (diagBlock U (codeState U (linVec ⟨a₁, (i₁, j₁)⟩ ⟨a₂, (i₂, j₂)⟩ s2inv (s2inv * c))) a) =
    traceRight (diagBlock U (codeState U (linVec ⟨a₁, (i₁, j₁)⟩ ⟨a₂, (i₂, j₂)⟩ s2inv (s2inv * (-c)))) a) := by
  ext k₁ k₂
  unfold traceRight
  simp_rw [diagBlock_codeState_apply U hU]
  refine Finset.sum_congr rfl fun j _ => ?_
  let p : BlockIndex N dr drb := ⟨a₁, (i₁, j₁)⟩
  let q : BlockIndex N dr drb := ⟨a₂, (i₂, j₂)⟩
  let x₁ : BlockIndex N dr drb := ⟨a, (k₁, j)⟩
  let x₂ : BlockIndex N dr drb := ⟨a, (k₂, j)⟩
  have h_orth1 : basisVec p x₁ * basisVec q x₂ = 0 := by
    unfold basisVec
    by_cases hp : x₁ = p
    · have hq : x₂ ≠ q := fun hq =>
        hne ((congr_arg projRight hp).symm.trans (congr_arg projRight hq))
      rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  have h_orth2 : basisVec q x₁ * basisVec p x₂ = 0 := by
    unfold basisVec
    by_cases hq : x₁ = q
    · have hp : x₂ ≠ p := fun hp =>
        hne ((congr_arg projRight hp).symm.trans (congr_arg projRight hq))
      rw [if_neg hp, mul_zero]
    · rw [if_neg hq, zero_mul]
  change linVec p q s2inv (s2inv * c) x₁ * star (linVec p q s2inv (s2inv * c) x₂) =
    linVec p q s2inv (s2inv * (-c)) x₁ * star (linVec p q s2inv (s2inv * (-c)) x₂)
  unfold linVec
  simp only [star_add, star_mul, star_neg, star_s2inv, star_basisVec]
  linear_combination (2 * s2inv * s2inv * star c) * h_orth1 + (2 * s2inv * s2inv * c) * h_orth2

/-! ### Part 5: Slice Gram identities and operator reconstruction -/

def sliceR {N : ℕ} {dr drb : Fin N → ℕ} {R Rb : Type}
    (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ) (a : Fin N) (i : Fin (dr a)) :
    Matrix R (Fin (drb a) × Rb) ℂ :=
  fun r jb => W (r, jb.2) ⟨a, (i, jb.1)⟩

def sliceRb {N : ℕ} {dr drb : Fin N → ℕ} {R Rb : Type}
    (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ) (a : Fin N) (j : Fin (drb a)) :
    Matrix Rb (Fin (dr a) × R) ℂ :=
  fun b ir => W (ir.2, b) ⟨a, (ir.1, j)⟩

lemma sliceR_gram_apply {N : ℕ} {dr drb : Fin N → ℕ} {R Rb : Type} [Fintype R]
    (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (a' a : Fin N) (i' : Fin (dr a')) (i : Fin (dr a))
    (jb' : Fin (drb a') × Rb) (jb : Fin (drb a) × Rb) :
    ((sliceR W a' i')ᴴ * sliceR W a i) jb' jb =
      F_R W jb.2 jb'.2 ⟨a, (i, jb.1)⟩ ⟨a', (i', jb'.1)⟩ := by
  simp only [mul_apply, conjTranspose_apply, sliceR, F_R]
  refine Finset.sum_congr rfl fun r _ => mul_comm _ _

lemma sliceRb_gram_apply {N : ℕ} {dr drb : Fin N → ℕ} {R Rb : Type} [Fintype Rb]
    (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (a' a : Fin N) (j' : Fin (drb a')) (j : Fin (drb a))
    (ir' : Fin (dr a') × R) (ir : Fin (dr a) × R) :
    ((sliceRb W a' j')ᴴ * sliceRb W a j) ir' ir =
      F_Rb W ir.2 ir'.2 ⟨a, (ir.1, j)⟩ ⟨a', (ir'.1, j')⟩ := by
  simp only [mul_apply, conjTranspose_apply, sliceRb, F_Rb]
  refine Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma norm_sq_unit (c : ℂ) (hc : c = 1 ∨ c = -1 ∨ c = Complex.I ∨ c = -Complex.I) :
    c * star c = 1 := by
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Complex.I_mul_I]

lemma sliceR_orth_of_agree_left {R Rb C : Type} [Fintype R] [Fintype Rb] [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U)
    (V : Matrix (R × Rb) C ℂ)
    (h_agree_left : ∀ ρ₁ ρ₂ : Matrix C C ℂ,
      IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
      (∀ a : Fin N, traceLeft (diagBlock U ρ₁ a) = traceLeft (diagBlock U ρ₂ a)) →
      traceLeft (V * ρ₁ * Vᴴ) = traceLeft (V * ρ₂ * Vᴴ))
    (a' a : Fin N) (i' : Fin (dr a')) (i : Fin (dr a))
    (hne : (⟨a', i'⟩ : Σ a, Fin (dr a)) ≠ ⟨a, i⟩) :
    (sliceR (V * Uᴴ) a' i')ᴴ * sliceR (V * Uᴴ) a i = 0 := by
  ext jb' jb
  rw [sliceR_gram_apply, Matrix.zero_apply]
  let p : BlockIndex N dr drb := ⟨a, (i, jb.1)⟩
  let q : BlockIndex N dr drb := ⟨a', (i', jb'.1)⟩
  have hpq : p ≠ q := fun h => hne.symm (congr_arg projLeft h)
  have hne' : (⟨a, i⟩ : Σ a, Fin (dr a)) ≠ ⟨a', i'⟩ := hne.symm
  have h_pol : ∀ (c : ℂ), c * star c = 1 → (-c) * star (-c) = 1 →
      star c * F_R (V * Uᴴ) jb.2 jb'.2 p q + c * F_R (V * Uᴴ) jb.2 jb'.2 q p = 0 := by
    intro c hc hnc
    have h_eq := h_agree_left
      (codeState U (linVec p q s2inv (s2inv * c)))
      (codeState U (linVec p q s2inv (s2inv * (-c))))
      (isDensityMatrix_codeState_twoVec U hU hpq hc)
      (isDensityMatrix_codeState_twoVec U hU hpq hnc)
      (traceLeft_diagBlock_twoVec_neg_eq U hU hne' jb.1 jb'.1 c)
    have h_sub : traceLeft (V * codeState U (linVec p q s2inv (s2inv * c)) * Vᴴ) jb.2 jb'.2 -
        traceLeft (V * codeState U (linVec p q s2inv (s2inv * (-c))) * Vᴴ) jb.2 jb'.2 = 0 := by
      rw [h_eq, sub_self]
    rw [← traceLeft_twoVec_sub U V p q c jb.2 jb'.2, h_sub]
  exact eq_zero_of_one_and_I
    (h_pol 1 (norm_sq_unit 1 (Or.inl rfl)) (norm_sq_unit (-1) (Or.inr (Or.inl rfl))))
    (h_pol Complex.I (norm_sq_unit Complex.I (Or.inr (Or.inr (Or.inl rfl))))
      (norm_sq_unit (-Complex.I) (Or.inr (Or.inr (Or.inr rfl)))))

lemma sliceR_same_of_agree_left {R Rb C : Type} [Fintype R] [Fintype Rb] [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U)
    (V : Matrix (R × Rb) C ℂ)
    (h_agree_left : ∀ ρ₁ ρ₂ : Matrix C C ℂ,
      IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
      (∀ a : Fin N, traceLeft (diagBlock U ρ₁ a) = traceLeft (diagBlock U ρ₂ a)) →
      traceLeft (V * ρ₁ * Vᴴ) = traceLeft (V * ρ₂ * Vᴴ))
    (a : Fin N) (i : Fin (dr a)) :
    (sliceR (V * Uᴴ) a i)ᴴ * sliceR (V * Uᴴ) a i = familyGram (sliceR (V * Uᴴ)) a := by
  unfold familyGram
  have hi0 : 0 < dr a := i.pos
  rw [dif_pos hi0]
  let i₀ : Fin (dr a) := ⟨0, hi0⟩
  ext jb' jb
  rw [sliceR_gram_apply, sliceR_gram_apply]
  by_cases hj : jb.1 = jb'.1
  · rw [← hj]
    have h_eq := h_agree_left
      (codeState U (linVec ⟨a, (i, jb.1)⟩ ⟨a, (i, jb.1)⟩ 1 0))
      (codeState U (linVec ⟨a, (i₀, jb.1)⟩ ⟨a, (i₀, jb.1)⟩ 1 0))
      (isDensityMatrix_codeState_basisVec U hU _)
      (isDensityMatrix_codeState_basisVec U hU _)
      (traceLeft_diagBlock_linVec_indep_i U hU a i i₀ jb.1 jb.1 1 0)
    have h_entry := congr_fun (congr_fun h_eq jb.2) jb'.2
    simpa [traceLeft_codeState_linVec] using h_entry
  · let p₁ : BlockIndex N dr drb := ⟨a, (i, jb.1)⟩
    let q₁ : BlockIndex N dr drb := ⟨a, (i, jb'.1)⟩
    let p₂ : BlockIndex N dr drb := ⟨a, (i₀, jb.1)⟩
    let q₂ : BlockIndex N dr drb := ⟨a, (i₀, jb'.1)⟩
    have hpq₁ : p₁ ≠ q₁ := fun h => hj (congr_arg Prod.snd (Sigma.mk.inj_iff.mp h).2.eq)
    have hpq₂ : p₂ ≠ q₂ := fun h => hj (congr_arg Prod.snd (Sigma.mk.inj_iff.mp h).2.eq)
    have h_pol : ∀ (c : ℂ), c * star c = 1 → (-c) * star (-c) = 1 →
        star c * (F_R (V * Uᴴ) jb.2 jb'.2 p₁ q₁ - F_R (V * Uᴴ) jb.2 jb'.2 p₂ q₂) +
        c * (F_R (V * Uᴴ) jb.2 jb'.2 q₁ p₁ - F_R (V * Uᴴ) jb.2 jb'.2 q₂ p₂) = 0 := by
      intro c hc hnc
      have h_eq_pos := h_agree_left
        (codeState U (linVec p₁ q₁ s2inv (s2inv * c)))
        (codeState U (linVec p₂ q₂ s2inv (s2inv * c)))
        (isDensityMatrix_codeState_twoVec U hU hpq₁ hc)
        (isDensityMatrix_codeState_twoVec U hU hpq₂ hc)
        (traceLeft_diagBlock_linVec_indep_i U hU a i i₀ jb.1 jb'.1 s2inv (s2inv * c))
      have h_eq_neg := h_agree_left
        (codeState U (linVec p₁ q₁ s2inv (s2inv * (-c))))
        (codeState U (linVec p₂ q₂ s2inv (s2inv * (-c))))
        (isDensityMatrix_codeState_twoVec U hU hpq₁ hnc)
        (isDensityMatrix_codeState_twoVec U hU hpq₂ hnc)
        (traceLeft_diagBlock_linVec_indep_i U hU a i i₀ jb.1 jb'.1 s2inv (s2inv * (-c)))
      have h_sub1 := traceLeft_twoVec_sub U V p₁ q₁ c jb.2 jb'.2
      have h_sub2 := traceLeft_twoVec_sub U V p₂ q₂ c jb.2 jb'.2
      rw [h_eq_pos, h_eq_neg] at h_sub1
      linear_combination -h_sub1 + h_sub2
    have h_zero := eq_zero_of_one_and_I
      (h_pol 1 (norm_sq_unit 1 (Or.inl rfl)) (norm_sq_unit (-1) (Or.inr (Or.inl rfl))))
      (h_pol Complex.I (norm_sq_unit Complex.I (Or.inr (Or.inr (Or.inl rfl))))
        (norm_sq_unit (-Complex.I) (Or.inr (Or.inr (Or.inr rfl)))))
    exact sub_eq_zero.mp h_zero

lemma sliceRb_orth_of_agree_right {R Rb C : Type} [Fintype R] [Fintype Rb] [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U)
    (V : Matrix (R × Rb) C ℂ)
    (h_agree_right : ∀ ρ₁ ρ₂ : Matrix C C ℂ,
      IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
      (∀ a : Fin N, traceRight (diagBlock U ρ₁ a) = traceRight (diagBlock U ρ₂ a)) →
      traceRight (V * ρ₁ * Vᴴ) = traceRight (V * ρ₂ * Vᴴ))
    (a' a : Fin N) (j' : Fin (drb a')) (j : Fin (drb a))
    (hne : (⟨a', j'⟩ : Σ a, Fin (drb a)) ≠ ⟨a, j⟩) :
    (sliceRb (V * Uᴴ) a' j')ᴴ * sliceRb (V * Uᴴ) a j = 0 := by
  ext ir' ir
  rw [sliceRb_gram_apply, Matrix.zero_apply]
  let p : BlockIndex N dr drb := ⟨a, (ir.1, j)⟩
  let q : BlockIndex N dr drb := ⟨a', (ir'.1, j')⟩
  have hpq : p ≠ q := fun h => hne.symm (congr_arg projRight h)
  have hne' : (⟨a, j⟩ : Σ a, Fin (drb a)) ≠ ⟨a', j'⟩ := hne.symm
  have h_pol : ∀ (c : ℂ), c * star c = 1 → (-c) * star (-c) = 1 →
      star c * F_Rb (V * Uᴴ) ir.2 ir'.2 p q + c * F_Rb (V * Uᴴ) ir.2 ir'.2 q p = 0 := by
    intro c hc hnc
    have h_eq := h_agree_right
      (codeState U (linVec p q s2inv (s2inv * c)))
      (codeState U (linVec p q s2inv (s2inv * (-c))))
      (isDensityMatrix_codeState_twoVec U hU hpq hc)
      (isDensityMatrix_codeState_twoVec U hU hpq hnc)
      (traceRight_diagBlock_twoVec_neg_eq U hU hne' ir.1 ir'.1 c)
    have h_sub : traceRight (V * codeState U (linVec p q s2inv (s2inv * c)) * Vᴴ) ir.2 ir'.2 -
        traceRight (V * codeState U (linVec p q s2inv (s2inv * (-c))) * Vᴴ) ir.2 ir'.2 = 0 := by
      rw [h_eq, sub_self]
    rw [← traceRight_twoVec_sub U V p q c ir.2 ir'.2, h_sub]
  exact eq_zero_of_one_and_I
    (h_pol 1 (norm_sq_unit 1 (Or.inl rfl)) (norm_sq_unit (-1) (Or.inr (Or.inl rfl))))
    (h_pol Complex.I (norm_sq_unit Complex.I (Or.inr (Or.inr (Or.inl rfl))))
      (norm_sq_unit (-Complex.I) (Or.inr (Or.inr (Or.inr rfl)))))

lemma sliceRb_same_of_agree_right {R Rb C : Type} [Fintype R] [Fintype Rb] [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U)
    (V : Matrix (R × Rb) C ℂ)
    (h_agree_right : ∀ ρ₁ ρ₂ : Matrix C C ℂ,
      IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
      (∀ a : Fin N, traceRight (diagBlock U ρ₁ a) = traceRight (diagBlock U ρ₂ a)) →
      traceRight (V * ρ₁ * Vᴴ) = traceRight (V * ρ₂ * Vᴴ))
    (a : Fin N) (j : Fin (drb a)) :
    (sliceRb (V * Uᴴ) a j)ᴴ * sliceRb (V * Uᴴ) a j = familyGram (sliceRb (V * Uᴴ)) a := by
  unfold familyGram
  have hj0 : 0 < drb a := j.pos
  rw [dif_pos hj0]
  let j₀ : Fin (drb a) := ⟨0, hj0⟩
  ext ir' ir
  rw [sliceRb_gram_apply, sliceRb_gram_apply]
  by_cases hi : ir.1 = ir'.1
  · rw [← hi]
    have h_eq := h_agree_right
      (codeState U (linVec ⟨a, (ir.1, j)⟩ ⟨a, (ir.1, j)⟩ 1 0))
      (codeState U (linVec ⟨a, (ir.1, j₀)⟩ ⟨a, (ir.1, j₀)⟩ 1 0))
      (isDensityMatrix_codeState_basisVec U hU _)
      (isDensityMatrix_codeState_basisVec U hU _)
      (traceRight_diagBlock_linVec_indep_j U hU a ir.1 ir.1 j j₀ 1 0)
    have h_entry := congr_fun (congr_fun h_eq ir.2) ir'.2
    simpa [traceRight_codeState_linVec] using h_entry
  · let p₁ : BlockIndex N dr drb := ⟨a, (ir.1, j)⟩
    let q₁ : BlockIndex N dr drb := ⟨a, (ir'.1, j)⟩
    let p₂ : BlockIndex N dr drb := ⟨a, (ir.1, j₀)⟩
    let q₂ : BlockIndex N dr drb := ⟨a, (ir'.1, j₀)⟩
    have hpq₁ : p₁ ≠ q₁ := fun h => hi (Sigma.mk.inj_iff.mp (congr_arg projLeft h)).2.eq
    have hpq₂ : p₂ ≠ q₂ := fun h => hi (Sigma.mk.inj_iff.mp (congr_arg projLeft h)).2.eq
    have h_pol : ∀ (c : ℂ), c * star c = 1 → (-c) * star (-c) = 1 →
        star c * (F_Rb (V * Uᴴ) ir.2 ir'.2 p₁ q₁ - F_Rb (V * Uᴴ) ir.2 ir'.2 p₂ q₂) +
        c * (F_Rb (V * Uᴴ) ir.2 ir'.2 q₁ p₁ - F_Rb (V * Uᴴ) ir.2 ir'.2 q₂ p₂) = 0 := by
      intro c hc hnc
      have h_eq_pos := h_agree_right
        (codeState U (linVec p₁ q₁ s2inv (s2inv * c)))
        (codeState U (linVec p₂ q₂ s2inv (s2inv * c)))
        (isDensityMatrix_codeState_twoVec U hU hpq₁ hc)
        (isDensityMatrix_codeState_twoVec U hU hpq₂ hc)
        (traceRight_diagBlock_linVec_indep_j U hU a ir.1 ir'.1 j j₀ s2inv (s2inv * c))
      have h_eq_neg := h_agree_right
        (codeState U (linVec p₁ q₁ s2inv (s2inv * (-c))))
        (codeState U (linVec p₂ q₂ s2inv (s2inv * (-c))))
        (isDensityMatrix_codeState_twoVec U hU hpq₁ hnc)
        (isDensityMatrix_codeState_twoVec U hU hpq₂ hnc)
        (traceRight_diagBlock_linVec_indep_j U hU a ir.1 ir'.1 j j₀ s2inv (s2inv * (-c)))
      have h_sub1 := traceRight_twoVec_sub U V p₁ q₁ c ir.2 ir'.2
      have h_sub2 := traceRight_twoVec_sub U V p₂ q₂ c ir.2 ir'.2
      rw [h_eq_pos, h_eq_neg] at h_sub1
      linear_combination -h_sub1 + h_sub2
    have h_zero := eq_zero_of_one_and_I
      (h_pol 1 (norm_sq_unit 1 (Or.inl rfl)) (norm_sq_unit (-1) (Or.inr (Or.inl rfl))))
      (h_pol Complex.I (norm_sq_unit Complex.I (Or.inr (Or.inr (Or.inl rfl))))
        (norm_sq_unit (-Complex.I) (Or.inr (Or.inr (Or.inr rfl)))))
    exact sub_eq_zero.mp h_zero

lemma familyLift_sliceR_intertwine {N : ℕ} {dr drb : Fin N → ℕ} {R Rb : Type}
    [Fintype R] [DecidableEq R] [Fintype Rb] [DecidableEq Rb]
    (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (h_same : ∀ a (i : Fin (dr a)), (sliceR W a i)ᴴ * sliceR W a i = familyGram (sliceR W) a)
    (h_orth : ∀ (a' a : Fin N) (i' : Fin (dr a')) (i : Fin (dr a)),
      (⟨a', i'⟩ : Σ a, Fin (dr a)) ≠ ⟨a, i⟩ → (sliceR W a' i')ᴴ * sliceR W a i = 0)
    (x : ∀ a : Fin N, Matrix (Fin (dr a)) (Fin (dr a)) ℂ) :
    (familyLift (sliceR W) x ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W = W * blockLeftOp (drb := drb) x := by
  ext ⟨r, b⟩ ⟨a₀, ⟨i₀, j₀⟩⟩
  have h_lhs : ((familyLift (sliceR W) x ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W) (r, b) ⟨a₀, (i₀, j₀)⟩ =
      (familyLift (sliceR W) x * sliceR W a₀ i₀) r (j₀, b) := by
    rw [mul_apply, Fintype.sum_prod_type]
    simp only [kroneckerMap_apply, one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  have h_rhs : (W * blockLeftOp (drb := drb) x) (r, b) ⟨a₀, (i₀, j₀)⟩ =
      ∑ i' : Fin (dr a₀), x a₀ i' i₀ * W (r, b) ⟨a₀, (i', j₀)⟩ := by
    rw [mul_apply, Fintype.sum_sigma, Finset.sum_eq_single a₀]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Finset.sum_eq_single j₀]
      · simp [blockLeftOp, blockDiagonal'_apply_eq, kroneckerMap_apply, mul_comm]
      · intro j' _ hj'
        simp [blockLeftOp, blockDiagonal'_apply_eq, kroneckerMap_apply, one_apply_ne hj']
      · intro h; exact (h (Finset.mem_univ j₀)).elim
    · intro a _ ha
      refine Finset.sum_eq_zero fun ij _ => ?_
      rw [blockLeftOp, blockDiagonal'_apply, dif_neg ha, mul_zero]
    · intro h; exact (h (Finset.mem_univ a₀)).elim
  rw [h_lhs, h_rhs, familyLift_mul_slice (sliceR W) h_same h_orth x a₀ i₀]
  simp [Matrix.sum_apply, sliceR]

lemma familyLift_sliceRb_intertwine {N : ℕ} {dr drb : Fin N → ℕ} {R Rb : Type}
    [Fintype R] [DecidableEq R] [Fintype Rb] [DecidableEq Rb]
    (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (h_same : ∀ a (j : Fin (drb a)), (sliceRb W a j)ᴴ * sliceRb W a j = familyGram (sliceRb W) a)
    (h_orth : ∀ (a' a : Fin N) (j' : Fin (drb a')) (j : Fin (drb a)),
      (⟨a', j'⟩ : Σ a, Fin (drb a)) ≠ ⟨a, j⟩ → (sliceRb W a' j')ᴴ * sliceRb W a j = 0)
    (y : ∀ a : Fin N, Matrix (Fin (drb a)) (Fin (drb a)) ℂ) :
    ((1 : Matrix R R ℂ) ⊗ₖ familyLift (sliceRb W) y) * W = W * blockRightOp (dr := dr) y := by
  ext ⟨r, b⟩ ⟨a₀, ⟨i₀, j₀⟩⟩
  have h_lhs : (((1 : Matrix R R ℂ) ⊗ₖ familyLift (sliceRb W) y) * W) (r, b) ⟨a₀, (i₀, j₀)⟩ =
      (familyLift (sliceRb W) y * sliceRb W a₀ j₀) b (i₀, r) := by
    rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [kroneckerMap_apply, one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  have h_rhs : (W * blockRightOp (dr := dr) y) (r, b) ⟨a₀, (i₀, j₀)⟩ =
      ∑ j' : Fin (drb a₀), y a₀ j' j₀ * W (r, b) ⟨a₀, (i₀, j')⟩ := by
    rw [mul_apply, Fintype.sum_sigma, Finset.sum_eq_single a₀]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single i₀]
      · refine Finset.sum_congr rfl fun j' _ => ?_
        simp [blockRightOp, blockDiagonal'_apply_eq, kroneckerMap_apply, mul_comm]
      · intro i' _ hi'
        refine Finset.sum_eq_zero fun j' _ => ?_
        simp [blockRightOp, blockDiagonal'_apply_eq, kroneckerMap_apply, one_apply_ne hi']
      · intro h; exact (h (Finset.mem_univ i₀)).elim
    · intro a _ ha
      refine Finset.sum_eq_zero fun ij _ => ?_
      rw [blockRightOp, blockDiagonal'_apply, dif_neg ha, mul_zero]
    · intro h; exact (h (Finset.mem_univ a₀)).elim
  rw [h_lhs, h_rhs, familyLift_mul_slice (sliceRb W) h_same h_orth y a₀ j₀]
  simp [Matrix.sum_apply, sliceRb]

lemma blockLeftOp_conjTranspose {N : ℕ} {dr drb : Fin N → ℕ}
    (x : ∀ a : Fin N, Matrix (Fin (dr a)) (Fin (dr a)) ℂ) :
    (blockLeftOp (drb := drb) x)ᴴ = blockLeftOp (drb := drb) (fun a => (x a)ᴴ) := by
  unfold blockLeftOp
  rw [blockDiagonal'_conjTranspose]
  congr 1; funext a
  rw [conjTranspose_kronecker, conjTranspose_one]

lemma blockRightOp_conjTranspose {N : ℕ} {dr drb : Fin N → ℕ}
    (y : ∀ a : Fin N, Matrix (Fin (drb a)) (Fin (drb a)) ℂ) :
    (blockRightOp (dr := dr) y)ᴴ = blockRightOp (dr := dr) (fun a => (y a)ᴴ) := by
  unfold blockRightOp
  rw [blockDiagonal'_conjTranspose]
  congr 1; funext a
  rw [conjTranspose_kronecker, conjTranspose_one]

end HarlowTASI_JlmsImpDuality

open HarlowTASI HarlowTASI_JlmsImpDuality in
theorem solution {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U)
    (h : ∀ ρ σ : Matrix C C ℂ, IsDensityMatrix ρ → IsDensityMatrix σ →
        relativeEntropy (traceRight (V * ρ * Vᴴ)) (traceRight (V * σ * Vᴴ)) =
            algebraicRelEntropyLeft U ρ σ ∧
        relativeEntropy (traceLeft (V * ρ * Vᴴ)) (traceLeft (V * σ * Vᴴ)) =
            algebraicRelEntropyRight U ρ σ) :
    ∀ O ∈ M, ∀ O' ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
        ∃ (OR : Matrix R R ℂ) (ORb : Matrix Rb Rb ℂ),
          (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
          (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORb) * V = V * O' ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * V = V * O'ᴴ := by
  have h_agree_left : ∀ ρ₁ ρ₂ : Matrix C C ℂ,
      IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
      (∀ a : Fin N, traceLeft (diagBlock U ρ₁ a) = traceLeft (diagBlock U ρ₂ a)) →
      traceLeft (V * ρ₁ * Vᴴ) = traceLeft (V * ρ₂ * Vᴴ) := by
    intro ρ₁ ρ₂ hρ₁ hρ₂ h_eq
    have h_rel := (h ρ₁ ρ₂ hρ₁ hρ₂).2
    rw [algebraicRelEntropyRight_eq_zero_of_traceLeft_eq U h_eq] at h_rel
    exact eq_of_relativeEntropy_eq_zero
      (isDensityMatrix_traceLeft (isDensityMatrix_conj_isometry V hV hρ₁))
      (isDensityMatrix_traceLeft (isDensityMatrix_conj_isometry V hV hρ₂))
      h_rel
  have h_agree_right : ∀ ρ₁ ρ₂ : Matrix C C ℂ,
      IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
      (∀ a : Fin N, traceRight (diagBlock U ρ₁ a) = traceRight (diagBlock U ρ₂ a)) →
      traceRight (V * ρ₁ * Vᴴ) = traceRight (V * ρ₂ * Vᴴ) := by
    intro ρ₁ ρ₂ hρ₁ hρ₂ h_eq
    have h_rel := (h ρ₁ ρ₂ hρ₁ hρ₂).1
    rw [algebraicRelEntropyLeft_eq_zero_of_traceRight_eq U h_eq] at h_rel
    exact eq_of_relativeEntropy_eq_zero
      (isDensityMatrix_traceRight (isDensityMatrix_conj_isometry V hV hρ₁))
      (isDensityMatrix_traceRight (isDensityMatrix_conj_isometry V hV hρ₂))
      h_rel
  have hR_same := sliceR_same_of_agree_left U hU V h_agree_left
  have hR_orth := sliceR_orth_of_agree_left U hU V h_agree_left
  have hRb_same := sliceRb_same_of_agree_right U hU V h_agree_right
  have hRb_orth := sliceRb_orth_of_agree_right U hU V h_agree_right
  intro O hO O' hO'
  have hO_left : O ∈ blockAlgebraLeft U := by
    rw [← hMU]; exact hO
  have h_union : (M : Set (Matrix C C ℂ)) ∪ star (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U := by
    rw [Set.union_eq_left.mpr (fun a ha => by simpa using star_mem (s := M) ha), hMU]
  have hO'_right : O' ∈ blockAlgebraRight U := by
    rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, h_union,
      HarlowTASI.centralizer_blockAlgebraLeft U hU] at hO'
    exact hO'
  rcases hO_left with ⟨x, rfl⟩
  rcases hO'_right with ⟨y, rfl⟩
  let W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ := V * Uᴴ
  have hW_def : W = V * Uᴴ := rfl
  have hWU : W * U = V := by
    rw [hW_def, Matrix.mul_assoc, hU.1, Matrix.mul_one]
  clear_value W
  rw [← hW_def] at hR_same hR_orth hRb_same hRb_orth
  refine ⟨familyLift (sliceR W) x, familyLift (sliceRb W) y, ?_, ?_, ?_, ?_⟩
  · calc (familyLift (sliceR W) x ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V
        = (familyLift (sliceR W) x ⊗ₖ (1 : Matrix Rb Rb ℂ)) * (W * U) := by rw [hWU]
      _ = ((familyLift (sliceR W) x ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W) * U := by
            rw [← Matrix.mul_assoc]
      _ = (W * blockLeftOp (drb := drb) x) * U := by
            rw [familyLift_sliceR_intertwine W hR_same hR_orth x]
      _ = V * (Uᴴ * blockLeftOp (drb := drb) x * U) := by
            rw [hW_def]; simp only [Matrix.mul_assoc]
  · rw [familyLift_conjTranspose]
    have h_adj : (Uᴴ * blockLeftOp (drb := drb) x * U)ᴴ =
        Uᴴ * blockLeftOp (drb := drb) (fun a => (x a)ᴴ) * U := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, blockLeftOp_conjTranspose,
        Matrix.mul_assoc]
    rw [h_adj]
    calc (familyLift (sliceR W) (fun a => (x a)ᴴ) ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V
        = (familyLift (sliceR W) (fun a => (x a)ᴴ) ⊗ₖ (1 : Matrix Rb Rb ℂ)) * (W * U) := by rw [hWU]
      _ = ((familyLift (sliceR W) (fun a => (x a)ᴴ) ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W) * U := by
            rw [← Matrix.mul_assoc]
      _ = (W * blockLeftOp (drb := drb) (fun a => (x a)ᴴ)) * U := by
            rw [familyLift_sliceR_intertwine W hR_same hR_orth (fun a => (x a)ᴴ)]
      _ = V * (Uᴴ * blockLeftOp (drb := drb) (fun a => (x a)ᴴ) * U) := by
            rw [hW_def]; simp only [Matrix.mul_assoc]
  · calc ((1 : Matrix R R ℂ) ⊗ₖ familyLift (sliceRb W) y) * V
        = ((1 : Matrix R R ℂ) ⊗ₖ familyLift (sliceRb W) y) * (W * U) := by rw [hWU]
      _ = (((1 : Matrix R R ℂ) ⊗ₖ familyLift (sliceRb W) y) * W) * U := by
            rw [← Matrix.mul_assoc]
      _ = (W * blockRightOp (dr := dr) y) * U := by
            rw [familyLift_sliceRb_intertwine W hRb_same hRb_orth y]
      _ = V * (Uᴴ * blockRightOp (dr := dr) y * U) := by
            rw [hW_def]; simp only [Matrix.mul_assoc]
  · rw [familyLift_conjTranspose]
    have h_adj : (Uᴴ * blockRightOp (dr := dr) y * U)ᴴ =
        Uᴴ * blockRightOp (dr := dr) (fun a => (y a)ᴴ) * U := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, blockRightOp_conjTranspose,
        Matrix.mul_assoc]
    rw [h_adj]
    calc ((1 : Matrix R R ℂ) ⊗ₖ familyLift (sliceRb W) (fun a => (y a)ᴴ)) * V
        = ((1 : Matrix R R ℂ) ⊗ₖ familyLift (sliceRb W) (fun a => (y a)ᴴ)) * (W * U) := by rw [hWU]
      _ = (((1 : Matrix R R ℂ) ⊗ₖ familyLift (sliceRb W) (fun a => (y a)ᴴ)) * W) * U := by
            rw [← Matrix.mul_assoc]
      _ = (W * blockRightOp (dr := dr) (fun a => (y a)ᴴ)) * U := by
            rw [familyLift_sliceRb_intertwine W hRb_same hRb_orth (fun a => (y a)ᴴ)]
      _ = V * (Uᴴ * blockRightOp (dr := dr) (fun a => (y a)ᴴ) * U) := by
            rw [hW_def]; simp only [Matrix.mul_assoc]

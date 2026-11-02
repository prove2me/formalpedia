-- Prove2me | solution 1 for HarlowTASI.ewr_rt_imp_jlms
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:21:41.852255+00:00
-- url     : https://prove2.me/submissions/012614b5-181c-4b36-b5b2-c86a90c6e927

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras
import Theorems.Thm_HarlowTASI_centralizer_blockAlgebraLeft
import Theorems.Thm_HarlowTASI_ewr_duality_imp_factorization
import Theorems.Thm_HarlowTASI_factorizedCode_reducedStates

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open Matrix
open scoped Kronecker ComplexOrder

namespace HarlowTASI_RtImpJlms

open HarlowTASI

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

/-! ### General spectral formula `relEntFormula` and `relEnt_udiag` -/

noncomputable def relEntFormula {k l : Type} [Fintype k] [Fintype l]
    (W : Matrix k l ℂ) (f : k → ℝ) (g : l → ℝ) : EReal :=
  ∑ r : k, ∑ s : l,
    if f r = 0 ∨ ‖W r s‖ = 0 then (0 : EReal)
    else if g s = 0 then ⊤
    else (((‖W r s‖ ^ 2 * f r * (Real.log (f r) - Real.log (g s)) : ℝ)) : EReal)

def matScale {α β : Type} (φ : ℝ → ℝ → ℝ) (W : Matrix α β ℂ) (a : α → ℝ) (b : β → ℝ) :
    Matrix α β ℂ :=
  Matrix.of fun i j => W i j * (φ (a i) (b j) : ℂ)

@[simp]
lemma matScale_apply {α β : Type} (φ : ℝ → ℝ → ℝ) (W : Matrix α β ℂ)
    (a : α → ℝ) (b : β → ℝ) (i : α) (j : β) :
    matScale φ W a b i j = W i j * (φ (a i) (b j) : ℂ) := rfl

lemma matScale_intertwine_right {n k : Type} [Fintype n] [Fintype k]
    (φ : ℝ → ℝ → ℝ) (W₁ : Matrix n n ℂ) (lam₁ lam₂ : n → ℝ)
    (W₂ : Matrix k k ℂ) (f g : k → ℝ) (M₁ M₂ : Matrix n k ℂ)
    (hM₁ : ∀ i r, M₁ i r ≠ 0 → lam₁ i = f r)
    (hM₂ : ∀ j s, M₂ j s ≠ 0 → lam₂ j = g s)
    (hW₂ : W₂ = M₁ᴴ * W₁ * M₂) :
    matScale φ W₂ f g = M₁ᴴ * matScale φ W₁ lam₁ lam₂ * M₂ := by
  ext r s
  rw [matScale_apply, hW₂, mul_apply, mul_apply]
  simp only [mul_apply, conjTranspose_apply, matScale_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : M₁ i r = 0
  · simp [h1]
  · by_cases h2 : M₂ j s = 0
    · simp [h2]
    · rw [hM₁ i r h1, hM₂ j s h2]
      ring

lemma matScale_intertwine_left {n k : Type} [Fintype n] [Fintype k]
    (φ : ℝ → ℝ → ℝ) (hφ0 : ∀ y, φ 0 y = 0)
    (W₁ : Matrix n n ℂ) (lam₁ lam₂ : n → ℝ)
    (W₂ : Matrix k k ℂ) (f g : k → ℝ) (M₁ M₂ : Matrix n k ℂ)
    (hM₁ : ∀ i r, M₁ i r ≠ 0 → lam₁ i = f r)
    (hM₂ : ∀ j s, M₂ j s ≠ 0 → lam₂ j = g s)
    (hW₁ : ∀ i j, lam₁ i ≠ 0 → (M₁ * W₂ * M₂ᴴ) i j = W₁ i j) :
    matScale φ W₁ lam₁ lam₂ = M₁ * matScale φ W₂ f g * M₂ᴴ := by
  ext i j
  have h_sum : (M₁ * matScale φ W₂ f g * M₂ᴴ) i j =
      (M₁ * W₂ * M₂ᴴ) i j * (φ (lam₁ i) (lam₂ j) : ℂ) := by
    rw [mul_apply, mul_apply]
    simp only [mul_apply, conjTranspose_apply, matScale_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h1 : M₁ i r = 0
    · simp [h1]
    · by_cases h2 : M₂ j s = 0
      · simp [h2]
      · rw [← hM₁ i r h1, ← hM₂ j s h2]
        ring
  rw [h_sum, matScale_apply]
  by_cases hlam : lam₁ i = 0
  · simp [hlam, hφ0]
  · rw [hW₁ i j hlam]

lemma trace_conjTranspose_matScale_re {α β : Type} [Fintype α] [Fintype β]
    (φ : ℝ → ℝ → ℝ) (W : Matrix α β ℂ) (a : α → ℝ) (b : β → ℝ) :
    (Wᴴ * matScale φ W a b).trace.re =
      ∑ i : α, ∑ j : β, ‖W i j‖ ^ 2 * φ (a i) (b j) := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, matScale_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h_norm : star (W i j) * (W i j * (φ (a i) (b j) : ℂ)) =
      (((‖W i j‖ ^ 2 * φ (a i) (b j) : ℝ)) : ℂ) := by
    calc star (W i j) * (W i j * (φ (a i) (b j) : ℂ))
        = (W i j * star (W i j)) * (φ (a i) (b j) : ℂ) := by ring
      _ = (((‖W i j‖ ^ 2 * φ (a i) (b j) : ℝ)) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, Complex.normSq_eq_norm_sq]
  rw [h_norm, Complex.ofReal_re]

lemma relEntFormula_eq_top_iff {k l : Type} [Fintype k] [Fintype l]
    (W : Matrix k l ℂ) (f : k → ℝ) (g : l → ℝ) :
    (∃ r s, ¬(f r = 0 ∨ ‖W r s‖ = 0) ∧ g s = 0) →
    relEntFormula W f g = ⊤ := by
  rintro ⟨r, s, hrs, hgs⟩
  unfold relEntFormula
  let T : k → l → EReal := fun r' s' =>
    if f r' = 0 ∨ ‖W r' s'‖ = 0 then (0 : EReal)
    else if g s' = 0 then ⊤
    else (((‖W r' s'‖ ^ 2 * f r' * (Real.log (f r') - Real.log (g s')) : ℝ)) : EReal)
  change ∑ r' : k, ∑ s' : l, T r' s' = ⊤
  have hT_ne_bot : ∀ r' s', T r' s' ≠ ⊥ := by
    intro r' s'
    dsimp [T]
    split_ifs <;> [decide; decide; exact EReal.coe_ne_bot _]
  have h_row_ne_bot : ∀ r', ∑ s' : l, T r' s' ≠ ⊥ :=
    fun r' => ereal_sum_ne_bot Finset.univ (fun s' => T r' s') (fun s' _ => hT_ne_bot r' s')
  have hT_top : T r s = ⊤ := by
    dsimp [T]
    rw [if_neg hrs, if_pos hgs]
  have hrow_top : ∑ s' : l, T r s' = ⊤ :=
    ereal_sum_eq_top_of_mem Finset.univ (fun s' => T r s')
      (fun s' _ => hT_ne_bot r s') (Finset.mem_univ s) hT_top
  exact ereal_sum_eq_top_of_mem Finset.univ (fun r' => ∑ s' : l, T r' s')
    (fun r' _ => h_row_ne_bot r') (Finset.mem_univ r) hrow_top

lemma relEntFormula_eq_coe_of_no_top {k l : Type} [Fintype k] [Fintype l]
    (W : Matrix k l ℂ) (f : k → ℝ) (g : l → ℝ)
    (h_no_top : ¬∃ r s, ¬(f r = 0 ∨ ‖W r s‖ = 0) ∧ g s = 0) :
    relEntFormula W f g =
      (((∑ r : k, ∑ s : l,
        ‖W r s‖ ^ 2 * (f r * (Real.log (f r) - Real.log (g s))) : ℝ)) : EReal) := by
  unfold relEntFormula
  rw [← ereal_coe_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← ereal_coe_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hrs : f r = 0 ∨ ‖W r s‖ = 0
  · rw [if_pos hrs]
    rcases hrs with hfr | hw
    · simp [hfr]
    · simp [hw]
  · have hgs : g s ≠ 0 := fun h0 => h_no_top ⟨r, s, hrs, h0⟩
    rw [if_neg hrs, if_neg hgs, mul_assoc]

lemma relEntFormula_eq_of_intertwine {n k : Type} [Fintype n] [Fintype k]
    (W₁ : Matrix n n ℂ) (lam₁ lam₂ : n → ℝ)
    (W₂ : Matrix k k ℂ) (f g : k → ℝ) (M₁ M₂ : Matrix n k ℂ)
    (hM₁ : ∀ i r, M₁ i r ≠ 0 → lam₁ i = f r)
    (hM₂ : ∀ j s, M₂ j s ≠ 0 → lam₂ j = g s)
    (hW₂ : W₂ = M₁ᴴ * W₁ * M₂)
    (hW₁ : ∀ i j, lam₁ i ≠ 0 → (M₁ * W₂ * M₂ᴴ) i j = W₁ i j) :
    relEntFormula W₁ lam₁ lam₂ = relEntFormula W₂ f g := by
  let φ₁ : ℝ → ℝ → ℝ := fun x y => if x = 0 then 0 else if y = 0 then 1 else 0
  have hφ₁0 : ∀ y, φ₁ 0 y = 0 := fun _ => if_pos rfl
  have hY₁ := matScale_intertwine_right φ₁ W₁ lam₁ lam₂ W₂ f g M₁ M₂ hM₁ hM₂ hW₂
  have hZ₁ := matScale_intertwine_left φ₁ hφ₁0 W₁ lam₁ lam₂ W₂ f g M₁ M₂ hM₁ hM₂ hW₁
  have h_entry_zero_iff : ∀ {α β : Type} (W : Matrix α β ℂ) (a : α → ℝ) (b : β → ℝ) (i : α) (j : β),
      matScale φ₁ W a b i j ≠ 0 ↔ ¬(a i = 0 ∨ ‖W i j‖ = 0) ∧ b j = 0 := by
    intro α β W a b i j
    simp only [matScale_apply, φ₁, not_or, norm_ne_zero_iff]
    by_cases ha : a i = 0
    · simp [ha]
    · by_cases hb : b j = 0
      · simp [ha, hb]
      · simp [ha, hb]
  have h_top_iff : (∃ i j, ¬(lam₁ i = 0 ∨ ‖W₁ i j‖ = 0) ∧ lam₂ j = 0) ↔
      (∃ r s, ¬(f r = 0 ∨ ‖W₂ r s‖ = 0) ∧ g s = 0) := by
    simp only [← h_entry_zero_iff]
    constructor
    · rintro ⟨i, j, hij⟩
      by_contra h_all
      have hY0 : matScale φ₁ W₂ f g = 0 := by
        ext r s
        by_contra hrs
        exact h_all ⟨r, s, hrs⟩
      rw [hZ₁, hY0, Matrix.mul_zero, Matrix.zero_mul] at hij
      exact hij rfl
    · rintro ⟨r, s, hrs⟩
      by_contra h_all
      have hZ0 : matScale φ₁ W₁ lam₁ lam₂ = 0 := by
        ext i j
        by_contra hij
        exact h_all ⟨i, j, hij⟩
      rw [hY₁, hZ0, Matrix.mul_zero, Matrix.zero_mul] at hrs
      exact hrs rfl
  by_cases h_top : ∃ i j, ¬(lam₁ i = 0 ∨ ‖W₁ i j‖ = 0) ∧ lam₂ j = 0
  · rw [relEntFormula_eq_top_iff W₁ lam₁ lam₂ h_top,
      relEntFormula_eq_top_iff W₂ f g (h_top_iff.mp h_top)]
  · have h_top2 : ¬∃ r s, ¬(f r = 0 ∨ ‖W₂ r s‖ = 0) ∧ g s = 0 :=
      fun h2 => h_top (h_top_iff.mpr h2)
    rw [relEntFormula_eq_coe_of_no_top W₁ lam₁ lam₂ h_top,
      relEntFormula_eq_coe_of_no_top W₂ f g h_top2]
    congr 1
    let φ₂ : ℝ → ℝ → ℝ := fun x y => x * (Real.log x - Real.log y)
    have hφ₂0 : ∀ y, φ₂ 0 y = 0 := fun _ => by simp [φ₂]
    have hZ₂ := matScale_intertwine_left φ₂ hφ₂0 W₁ lam₁ lam₂ W₂ f g M₁ M₂ hM₁ hM₂ hW₁
    rw [← trace_conjTranspose_matScale_re φ₂ W₁ lam₁ lam₂,
      ← trace_conjTranspose_matScale_re φ₂ W₂ f g]
    congr 1
    calc (W₁ᴴ * matScale φ₂ W₁ lam₁ lam₂).trace
        = (W₁ᴴ * (M₁ * matScale φ₂ W₂ f g * M₂ᴴ)).trace := by rw [hZ₂]
      _ = ((W₁ᴴ * M₁ * matScale φ₂ W₂ f g) * M₂ᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = (M₂ᴴ * (W₁ᴴ * M₁ * matScale φ₂ W₂ f g)).trace := Matrix.trace_mul_comm _ _
      _ = ((M₁ᴴ * W₁ * M₂)ᴴ * matScale φ₂ W₂ f g).trace := by
            simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (W₂ᴴ * matScale φ₂ W₂ f g).trace := by rw [← hW₂]

lemma relativeEntropy_eq_relEntFormula {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    relativeEntropy A B =
      relEntFormula ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hB.eigenvectorUnitary : Matrix n n ℂ))
        hA.eigenvalues hB.eigenvalues := by
  unfold relativeEntropy relEntFormula
  rw [dif_pos ⟨hA, hB⟩]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h_inner : ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
      (hB.eigenvectorUnitary : Matrix n n ℂ)) i j =
      inner ℂ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) := by
    rw [mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Matrix.IsHermitian.eigenvectorUnitary_apply, mul_comm]
  rw [h_inner]

lemma relEnt_udiag {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (P Q : Matrix n k ℂ) (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1) (hPQ : P * Pᴴ = Q * Qᴴ)
    (f g : k → ℝ)
    (hAP : A = P * diagonal (fun r => (f r : ℂ)) * Pᴴ)
    (hBQ : B = Q * diagonal (fun s => (g s : ℂ)) * Qᴴ) :
    relativeEntropy A B = relEntFormula (Pᴴ * Q) f g := by
  rw [relativeEntropy_eq_relEntFormula A B hA hB]
  let U₁ : Matrix n n ℂ := hA.eigenvectorUnitary
  let U₂ : Matrix n n ℂ := hB.eigenvectorUnitary
  have hU₁_left : U₁ᴴ * U₁ = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU₁_right : U₁ * U₁ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hU₂_left : U₂ᴴ * U₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hB.eigenvectorUnitary.2
  have hU₂_right : U₂ * U₂ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hB.eigenvectorUnitary.2
  have hA_spec : A = U₁ * diagonal (fun i => (hA.eigenvalues i : ℂ)) * U₁ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hB_spec : B = U₂ * diagonal (fun j => (hB.eigenvalues j : ℂ)) * U₂ᴴ := by
    conv_lhs => rw [hB.spectral_theorem]
    rfl
  let M₁ : Matrix n k ℂ := U₁ᴴ * P
  let M₂ : Matrix n k ℂ := U₂ᴴ * Q
  have hU₁A : diagonal (fun i => (hA.eigenvalues i : ℂ)) * U₁ᴴ = U₁ᴴ * A := by
    conv_rhs => rw [hA_spec]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU₁_left, Matrix.one_mul]
  have hU₂B : diagonal (fun j => (hB.eigenvalues j : ℂ)) * U₂ᴴ = U₂ᴴ * B := by
    conv_rhs => rw [hB_spec]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU₂_left, Matrix.one_mul]
  have hM₁_comm : diagonal (fun i => (hA.eigenvalues i : ℂ)) * M₁ =
      M₁ * diagonal (fun r => (f r : ℂ)) := by
    dsimp [M₁]
    rw [← Matrix.mul_assoc, hU₁A, hAP]
    simp only [Matrix.mul_assoc, hP, Matrix.mul_one]
  have hM₂_comm : diagonal (fun j => (hB.eigenvalues j : ℂ)) * M₂ =
      M₂ * diagonal (fun s => (g s : ℂ)) := by
    dsimp [M₂]
    rw [← Matrix.mul_assoc, hU₂B, hBQ]
    simp only [Matrix.mul_assoc, hQ, Matrix.mul_one]
  have hM₁_eig : ∀ i r, M₁ i r ≠ 0 → hA.eigenvalues i = f r := by
    intro i r hne
    have h_eq := congr_fun (congr_fun hM₁_comm i) r
    rw [diagonal_mul, mul_diagonal, mul_comm (M₁ i r)] at h_eq
    exact Complex.ofReal_injective (mul_right_cancel₀ hne h_eq)
  have hM₂_eig : ∀ j s, M₂ j s ≠ 0 → hB.eigenvalues j = g s := by
    intro j s hne
    have h_eq := congr_fun (congr_fun hM₂_comm j) s
    rw [diagonal_mul, mul_diagonal, mul_comm (M₂ j s)] at h_eq
    exact Complex.ofReal_injective (mul_right_cancel₀ hne h_eq)
  have hW₂ : Pᴴ * Q = M₁ᴴ * (U₁ᴴ * U₂) * M₂ := by
    dsimp [M₁, M₂]
    calc Pᴴ * Q = Pᴴ * (1 : Matrix n n ℂ) * (1 : Matrix n n ℂ) * Q := by
          rw [Matrix.mul_one, Matrix.mul_one]
      _ = Pᴴ * (U₁ * U₁ᴴ) * (U₂ * U₂ᴴ) * Q := by rw [hU₁_right, hU₂_right]
      _ = (U₁ᴴ * P)ᴴ * (U₁ᴴ * U₂) * (U₂ᴴ * Q) := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hW₁ : ∀ i j, hA.eigenvalues i ≠ 0 →
      (M₁ * (Pᴴ * Q) * M₂ᴴ) i j = (U₁ᴴ * U₂) i j := by
    intro i j hlam
    have h_prod : M₁ * (Pᴴ * Q) * M₂ᴴ = U₁ᴴ * (P * Pᴴ) * U₂ := by
      dsimp [M₁, M₂]
      calc U₁ᴴ * P * (Pᴴ * Q) * (U₂ᴴ * Q)ᴴ
          = U₁ᴴ * (P * Pᴴ) * (Q * Qᴴ) * U₂ := by
            simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = U₁ᴴ * (P * Pᴴ) * (P * Pᴴ) * U₂ := by rw [← hPQ]
        _ = U₁ᴴ * (P * (Pᴴ * P) * Pᴴ) * U₂ := by simp only [Matrix.mul_assoc]
        _ = U₁ᴴ * (P * Pᴴ) * U₂ := by rw [hP, Matrix.mul_one]
    have h_proj : diagonal (fun i' => (hA.eigenvalues i' : ℂ)) * (U₁ᴴ * (P * Pᴴ) * U₂) =
        diagonal (fun i' => (hA.eigenvalues i' : ℂ)) * (U₁ᴴ * U₂) := by
      have hAP_proj : A * (P * Pᴴ) = A := by
        calc A * (P * Pᴴ) = P * diagonal (fun r => (f r : ℂ)) * (Pᴴ * P) * Pᴴ := by
              rw [hAP]; simp only [Matrix.mul_assoc]
          _ = A := by rw [hP, Matrix.mul_one, ← hAP]
      calc diagonal (fun i' => (hA.eigenvalues i' : ℂ)) * (U₁ᴴ * (P * Pᴴ) * U₂)
          = (diagonal (fun i' => (hA.eigenvalues i' : ℂ)) * U₁ᴴ) * (P * Pᴴ) * U₂ := by
            simp only [Matrix.mul_assoc]
        _ = U₁ᴴ * (A * (P * Pᴴ)) * U₂ := by rw [hU₁A]; simp only [Matrix.mul_assoc]
        _ = (U₁ᴴ * A) * U₂ := by rw [hAP_proj, Matrix.mul_assoc]
        _ = diagonal (fun i' => (hA.eigenvalues i' : ℂ)) * (U₁ᴴ * U₂) := by
            rw [← hU₁A, Matrix.mul_assoc]
    rw [h_prod]
    have h_entry := congr_fun (congr_fun h_proj i) j
    rw [diagonal_mul, diagonal_mul] at h_entry
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hlam) h_entry
  exact relEntFormula_eq_of_intertwine (U₁ᴴ * U₂) hA.eigenvalues hB.eigenvalues
    (Pᴴ * Q) f g M₁ M₂ hM₁_eig hM₂_eig hW₂ hW₁

/-! ### Corollaries of `relEnt_udiag`: isometry, blockDiagonal', Kronecker, scalar split -/

lemma isHermitian_conj {m n : Type} [Fintype n] (W : Matrix m n ℂ)
    {X : Matrix n n ℂ} (hX : X.IsHermitian) : (W * X * Wᴴ).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

lemma relEnt_isom {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : IsIsometry W)
    (X Y : Matrix n n ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    relativeEntropy (W * X * Wᴴ) (W * Y * Wᴴ) = relativeEntropy X Y := by
  have hWX : (W * X * Wᴴ).IsHermitian := isHermitian_conj W hX
  have hWY : (W * Y * Wᴴ).IsHermitian := isHermitian_conj W hY
  let U₁ : Matrix n n ℂ := hX.eigenvectorUnitary
  let U₂ : Matrix n n ℂ := hY.eigenvectorUnitary
  have hU₁_left : U₁ᴴ * U₁ = 1 := Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
  have hU₁_right : U₁ * U₁ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2
  have hU₂_left : U₂ᴴ * U₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hY.eigenvectorUnitary.2
  have hU₂_right : U₂ * U₂ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hY.eigenvectorUnitary.2
  have hW' : Wᴴ * W = 1 := hW
  have hP : (W * U₁)ᴴ * (W * U₁) = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW', Matrix.one_mul, hU₁_left]
  have hQ : (W * U₂)ᴴ * (W * U₂) = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW', Matrix.one_mul, hU₂_left]
  have hPQ : (W * U₁) * (W * U₁)ᴴ = (W * U₂) * (W * U₂)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc W * U₁ * (U₁ᴴ * Wᴴ) = W * (U₁ * U₁ᴴ) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = W * (U₂ * U₂ᴴ) * Wᴴ := by rw [hU₁_right, hU₂_right]
      _ = W * U₂ * (U₂ᴴ * Wᴴ) := by simp only [Matrix.mul_assoc]
  have hX_spec : X = U₁ * diagonal (fun i => (hX.eigenvalues i : ℂ)) * U₁ᴴ := by
    conv_lhs => rw [hX.spectral_theorem]
    rfl
  have hY_spec : Y = U₂ * diagonal (fun j => (hY.eigenvalues j : ℂ)) * U₂ᴴ := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have hWXP : W * X * Wᴴ = (W * U₁) * diagonal (fun i => (hX.eigenvalues i : ℂ)) * (W * U₁)ᴴ := by
    conv_lhs => rw [hX_spec]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hWYQ : W * Y * Wᴴ = (W * U₂) * diagonal (fun j => (hY.eigenvalues j : ℂ)) * (W * U₂)ᴴ := by
    conv_lhs => rw [hY_spec]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [relEnt_udiag (W * X * Wᴴ) (W * Y * Wᴴ) hWX hWY (W * U₁) (W * U₂) hP hQ hPQ
    hX.eigenvalues hY.eigenvalues hWXP hWYQ]
  have hPQ_inner : (W * U₁)ᴴ * (W * U₂) = U₁ᴴ * U₂ := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW', Matrix.one_mul]
  rw [hPQ_inner, ← relativeEntropy_eq_relEntFormula X Y hX hY]

lemma relEnt_blockDiag {ι : Type} [Fintype ι] [DecidableEq ι]
    {o : ι → Type} [∀ a, Fintype (o a)] [∀ a, DecidableEq (o a)]
    (X Y : ∀ a, Matrix (o a) (o a) ℂ)
    (hX : ∀ a, (X a).IsHermitian) (hY : ∀ a, (Y a).IsHermitian) :
    relativeEntropy (blockDiagonal' X) (blockDiagonal' Y) =
      ∑ a, relativeEntropy (X a) (Y a) := by
  have hBX : (blockDiagonal' X).IsHermitian := by
    unfold IsHermitian
    rw [blockDiagonal'_conjTranspose]
    exact congr_arg _ (funext fun a => (hX a).eq)
  have hBY : (blockDiagonal' Y).IsHermitian := by
    unfold IsHermitian
    rw [blockDiagonal'_conjTranspose]
    exact congr_arg _ (funext fun a => (hY a).eq)
  let U₁ : ∀ a, Matrix (o a) (o a) ℂ := fun a => (hX a).eigenvectorUnitary
  let U₂ : ∀ a, Matrix (o a) (o a) ℂ := fun a => (hY a).eigenvectorUnitary
  have hU₁_left : ∀ a, (U₁ a)ᴴ * U₁ a = 1 :=
    fun a => Matrix.mem_unitaryGroup_iff'.mp (hX a).eigenvectorUnitary.2
  have hU₁_right : ∀ a, U₁ a * (U₁ a)ᴴ = 1 :=
    fun a => Matrix.mem_unitaryGroup_iff.mp (hX a).eigenvectorUnitary.2
  have hU₂_left : ∀ a, (U₂ a)ᴴ * U₂ a = 1 :=
    fun a => Matrix.mem_unitaryGroup_iff'.mp (hY a).eigenvectorUnitary.2
  have hU₂_right : ∀ a, U₂ a * (U₂ a)ᴴ = 1 :=
    fun a => Matrix.mem_unitaryGroup_iff.mp (hY a).eigenvectorUnitary.2
  have hX_spec : ∀ a, X a = U₁ a * diagonal (fun i => ((hX a).eigenvalues i : ℂ)) * (U₁ a)ᴴ := by
    intro a
    conv_lhs => rw [(hX a).spectral_theorem]
    rfl
  have hY_spec : ∀ a, Y a = U₂ a * diagonal (fun j => ((hY a).eigenvalues j : ℂ)) * (U₂ a)ᴴ := by
    intro a
    conv_lhs => rw [(hY a).spectral_theorem]
    rfl
  let P := blockDiagonal' U₁
  let Q := blockDiagonal' U₂
  have hP : Pᴴ * P = 1 := by
    dsimp [P]
    rw [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
    simp_rw [hU₁_left]
    exact blockDiagonal'_one
  have hQ : Qᴴ * Q = 1 := by
    dsimp [Q]
    rw [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
    simp_rw [hU₂_left]
    exact blockDiagonal'_one
  have hPQ : P * Pᴴ = Q * Qᴴ := by
    dsimp [P, Q]
    rw [blockDiagonal'_conjTranspose, blockDiagonal'_conjTranspose,
      ← blockDiagonal'_mul, ← blockDiagonal'_mul]
    simp_rw [hU₁_right, hU₂_right]
  have hBXP : blockDiagonal' X =
      P * diagonal (fun r : Σ a, o a => ((hX r.1).eigenvalues r.2 : ℂ)) * Pᴴ := by
    dsimp [P]
    rw [← blockDiagonal'_diagonal (fun a i => ((hX a).eigenvalues i : ℂ)),
      blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, ← blockDiagonal'_mul]
    exact congr_arg _ (funext hX_spec)
  have hBYQ : blockDiagonal' Y =
      Q * diagonal (fun s : Σ a, o a => ((hY s.1).eigenvalues s.2 : ℂ)) * Qᴴ := by
    dsimp [Q]
    rw [← blockDiagonal'_diagonal (fun a j => ((hY a).eigenvalues j : ℂ)),
      blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, ← blockDiagonal'_mul]
    exact congr_arg _ (funext hY_spec)
  rw [relEnt_udiag (blockDiagonal' X) (blockDiagonal' Y) hBX hBY P Q hP hQ hPQ
    (fun r => (hX r.1).eigenvalues r.2) (fun s => (hY s.1).eigenvalues s.2) hBXP hBYQ]
  have hPQ_inner : Pᴴ * Q = blockDiagonal' (fun a => (U₁ a)ᴴ * U₂ a) := by
    dsimp [P, Q]
    rw [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
  rw [hPQ_inner]
  unfold relEntFormula
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [relativeEntropy_eq_relEntFormula (X a) (Y a) (hX a) (hY a)]
  unfold relEntFormula
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [blockDiagonal'_apply_eq]
  · intro b _ hba
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : blockDiagonal' (fun c => (U₁ c)ᴴ * U₂ c) ⟨a, i⟩ ⟨b, j⟩ = 0 := by
      rw [blockDiagonal'_apply, dif_neg (Ne.symm hba)]
    simp [h0]
  · intro ha; exact (ha (Finset.mem_univ a)).elim

lemma ereal_sum_prob_mul {q : Type} [Fintype q] (c : q → ℝ)
    (hc_nonneg : ∀ k, 0 ≤ c k) (hc_sum : ∑ k : q, c k = 1)
    (t : EReal) (ht : t ≠ ⊥) :
    ∑ k : q, (if c k = 0 then (0 : EReal) else ((c k : ℝ) : EReal) * t) = t := by
  induction t using EReal.rec with
  | bot => exact (ht rfl).elim
  | coe r =>
    have h_term : ∀ k : q,
        (if c k = 0 then (0 : EReal) else ((c k : ℝ) : EReal) * ((r : ℝ) : EReal)) =
        (((c k * r : ℝ)) : EReal) := by
      intro k
      by_cases hk : c k = 0
      · simp [hk]
      · rw [if_neg hk, ← EReal.coe_mul]
    simp_rw [h_term]
    rw [ereal_coe_sum, ← Finset.sum_mul, hc_sum, one_mul]
  | top =>
    have h_exists : ∃ k : q, c k ≠ 0 := by
      by_contra h_all
      have h0 : ∑ k : q, c k = 0 := Finset.sum_eq_zero fun k _ => by
        by_contra hk; exact h_all ⟨k, hk⟩
      linarith
    rcases h_exists with ⟨k₀, hk₀⟩
    have hk₀_pos : 0 < c k₀ := lt_of_le_of_ne (hc_nonneg k₀) (Ne.symm hk₀)
    let f : q → EReal := fun k =>
      if c k = 0 then (0 : EReal) else ((c k : ℝ) : EReal) * ⊤
    have hf_ne_bot : ∀ k ∈ (Finset.univ : Finset q), f k ≠ ⊥ := by
      intro k _
      dsimp [f]
      by_cases hk : c k = 0
      · simp [hk]
      · rw [if_neg hk, EReal.coe_mul_top_of_pos (lt_of_le_of_ne (hc_nonneg k) (Ne.symm hk))]
        decide
    have hf_top : f k₀ = ⊤ := by
      dsimp [f]
      rw [if_neg hk₀, EReal.coe_mul_top_of_pos hk₀_pos]
    exact ereal_sum_eq_top_of_mem Finset.univ f hf_ne_bot (Finset.mem_univ k₀) hf_top

lemma relEnt_zero_left {n : Type} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    relativeEntropy (0 : Matrix n n ℂ) Y = 0 := by
  by_cases hY : Y.IsHermitian
  · have h0 : (0 : Matrix n n ℂ).IsHermitian := isHermitian_zero
    let U₂ : Matrix n n ℂ := hY.eigenvectorUnitary
    have hU₂_left : U₂ᴴ * U₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hY.eigenvectorUnitary.2
    have h0P : (0 : Matrix n n ℂ) = U₂ * diagonal (fun _ : n => ((0 : ℝ) : ℂ)) * U₂ᴴ := by simp
    have hYQ : Y = U₂ * diagonal (fun j => (hY.eigenvalues j : ℂ)) * U₂ᴴ := by
      conv_lhs => rw [hY.spectral_theorem]
      rfl
    rw [relEnt_udiag 0 Y h0 hY U₂ U₂ hU₂_left hU₂_left rfl (fun _ => 0) hY.eigenvalues h0P hYQ]
    unfold relEntFormula
    simp
  · unfold relativeEntropy
    have hnot : ¬((0 : Matrix n n ℂ).IsHermitian ∧ Y.IsHermitian) := fun h => hY h.2
    rw [dif_neg hnot]

lemma relEntTerm_mul_right {w x y c : ℝ} (hc : 0 ≤ c) :
    (if x * c = 0 ∨ w = 0 then (0 : EReal)
     else if y * c = 0 then ⊤
     else (((w ^ 2 * (x * c) * (Real.log (x * c) - Real.log (y * c)) : ℝ)) : EReal)) =
    if c = 0 then (0 : EReal)
    else ((c : ℝ) : EReal) *
      (if x = 0 ∨ w = 0 then (0 : EReal)
       else if y = 0 then ⊤
       else (((w ^ 2 * x * (Real.log x - Real.log y) : ℝ)) : EReal)) := by
  by_cases hc0 : c = 0
  · subst hc0; simp
  · rw [if_neg hc0]
    have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hxc : x * c = 0 ↔ x = 0 := mul_eq_zero_iff_right hc0
    have hyc : y * c = 0 ↔ y = 0 := mul_eq_zero_iff_right hc0
    by_cases hxw : x = 0 ∨ w = 0
    · have hxwc : x * c = 0 ∨ w = 0 := hxw.imp_left hxc.mpr
      rw [if_pos hxwc, if_pos hxw, mul_zero]
    · have hxwc : ¬(x * c = 0 ∨ w = 0) := fun h => hxw (h.imp_left hxc.mp)
      rw [if_neg hxwc, if_neg hxw]
      have hx0 : x ≠ 0 := (not_or.mp hxw).1
      by_cases hy0 : y = 0
      · rw [if_pos (hyc.mpr hy0), if_pos hy0, EReal.coe_mul_top_of_pos hc_pos]
      · rw [if_neg (fun h => hy0 (hyc.mp h)), if_neg hy0, ← EReal.coe_mul]
        congr 1
        rw [Real.log_mul hx0 hc0, Real.log_mul hy0 hc0]
        ring

lemma relEntTerm_mul_left {w x y c : ℝ} (hc : 0 ≤ c) :
    (if c * x = 0 ∨ w = 0 then (0 : EReal)
     else if c * y = 0 then ⊤
     else (((w ^ 2 * (c * x) * (Real.log (c * x) - Real.log (c * y)) : ℝ)) : EReal)) =
    if c = 0 then (0 : EReal)
    else ((c : ℝ) : EReal) *
      (if x = 0 ∨ w = 0 then (0 : EReal)
       else if y = 0 then ⊤
       else (((w ^ 2 * x * (Real.log x - Real.log y) : ℝ)) : EReal)) := by
  rw [mul_comm c x, mul_comm c y]
  exact relEntTerm_mul_right hc

lemma relEnt_kron_right {p q : Type} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (X Y : Matrix p p ℂ) (K : Matrix q q ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hK : K.PosSemidef)
    (hK_tr : X = 0 ∨ K.trace = 1) :
    relativeEntropy (X ⊗ₖ K) (Y ⊗ₖ K) = relativeEntropy X Y := by
  rcases hK_tr with rfl | htr
  · rw [zero_kronecker, relEnt_zero_left, relEnt_zero_left]
  · have hHK : K.IsHermitian := hK.isHermitian
    have hXK : (X ⊗ₖ K).IsHermitian := by
      unfold IsHermitian; rw [conjTranspose_kronecker, hX.eq, hHK.eq]
    have hYK : (Y ⊗ₖ K).IsHermitian := by
      unfold IsHermitian; rw [conjTranspose_kronecker, hY.eq, hHK.eq]
    let U₁ : Matrix p p ℂ := hX.eigenvectorUnitary
    let U₂ : Matrix p p ℂ := hY.eigenvectorUnitary
    let UK : Matrix q q ℂ := hHK.eigenvectorUnitary
    have hU₁_left : U₁ᴴ * U₁ = 1 := Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
    have hU₁_right : U₁ * U₁ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2
    have hU₂_left : U₂ᴴ * U₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hY.eigenvectorUnitary.2
    have hU₂_right : U₂ * U₂ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hY.eigenvectorUnitary.2
    have hUK_left : UKᴴ * UK = 1 := Matrix.mem_unitaryGroup_iff'.mp hHK.eigenvectorUnitary.2
    have hX_spec : X = U₁ * diagonal (fun i => (hX.eigenvalues i : ℂ)) * U₁ᴴ := by
      conv_lhs => rw [hX.spectral_theorem]
      rfl
    have hY_spec : Y = U₂ * diagonal (fun j => (hY.eigenvalues j : ℂ)) * U₂ᴴ := by
      conv_lhs => rw [hY.spectral_theorem]
      rfl
    have hK_spec : K = UK * diagonal (fun k => (hHK.eigenvalues k : ℂ)) * UKᴴ := by
      conv_lhs => rw [hHK.spectral_theorem]
      rfl
    have hP : (U₁ ⊗ₖ UK)ᴴ * (U₁ ⊗ₖ UK) = 1 := by
      rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU₁_left, hUK_left, one_kronecker_one]
    have hQ : (U₂ ⊗ₖ UK)ᴴ * (U₂ ⊗ₖ UK) = 1 := by
      rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU₂_left, hUK_left, one_kronecker_one]
    have hPQ : (U₁ ⊗ₖ UK) * (U₁ ⊗ₖ UK)ᴴ = (U₂ ⊗ₖ UK) * (U₂ ⊗ₖ UK)ᴴ := by
      rw [conjTranspose_kronecker, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
        hU₁_right, hU₂_right]
    have hXKP : X ⊗ₖ K = (U₁ ⊗ₖ UK) *
        diagonal (fun ik : p × q => ((hX.eigenvalues ik.1 * hHK.eigenvalues ik.2 : ℝ) : ℂ)) *
        (U₁ ⊗ₖ UK)ᴴ := by
      have hD : diagonal (fun ik : p × q => ((hX.eigenvalues ik.1 * hHK.eigenvalues ik.2 : ℝ) : ℂ)) =
          diagonal (fun i => (hX.eigenvalues i : ℂ)) ⊗ₖ diagonal (fun k => (hHK.eigenvalues k : ℂ)) := by
        rw [diagonal_kronecker_diagonal]; congr 1; funext ik; push_cast; rfl
      rw [hD, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, ← hX_spec, ← hK_spec]
    have hYKQ : Y ⊗ₖ K = (U₂ ⊗ₖ UK) *
        diagonal (fun jl : p × q => ((hY.eigenvalues jl.1 * hHK.eigenvalues jl.2 : ℝ) : ℂ)) *
        (U₂ ⊗ₖ UK)ᴴ := by
      have hD : diagonal (fun jl : p × q => ((hY.eigenvalues jl.1 * hHK.eigenvalues jl.2 : ℝ) : ℂ)) =
          diagonal (fun j => (hY.eigenvalues j : ℂ)) ⊗ₖ diagonal (fun l => (hHK.eigenvalues l : ℂ)) := by
        rw [diagonal_kronecker_diagonal]; congr 1; funext jl; push_cast; rfl
      rw [hD, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, ← hY_spec, ← hK_spec]
    rw [relEnt_udiag (X ⊗ₖ K) (Y ⊗ₖ K) hXK hYK (U₁ ⊗ₖ UK) (U₂ ⊗ₖ UK) hP hQ hPQ
      (fun ik => hX.eigenvalues ik.1 * hHK.eigenvalues ik.2)
      (fun jl => hY.eigenvalues jl.1 * hHK.eigenvalues jl.2) hXKP hYKQ]
    have hPQ_inner : (U₁ ⊗ₖ UK)ᴴ * (U₂ ⊗ₖ UK) = (U₁ᴴ * U₂) ⊗ₖ (1 : Matrix q q ℂ) := by
      rw [conjTranspose_kronecker, ← mul_kronecker_mul, hUK_left]
    rw [hPQ_inner, relativeEntropy_eq_relEntFormula X Y hX hY]
    have hc_nonneg : ∀ k : q, 0 ≤ hHK.eigenvalues k := hK.eigenvalues_nonneg
    have hc_sum : ∑ k : q, hHK.eigenvalues k = 1 := by
      have htr' := hHK.trace_eq_sum_eigenvalues
      rw [htr] at htr'
      have hre := congr_arg Complex.re htr'
      simpa [Complex.re_sum] using hre.symm
    unfold relEntFormula
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h_inner_sum : ∀ k : q, ∀ j : p,
        ∑ l : q,
          (if hX.eigenvalues i * hHK.eigenvalues k = 0 ∨
              ‖((U₁ᴴ * U₂) ⊗ₖ (1 : Matrix q q ℂ)) (i, k) (j, l)‖ = 0 then (0 : EReal)
           else if hY.eigenvalues j * hHK.eigenvalues l = 0 then ⊤
           else (((‖((U₁ᴴ * U₂) ⊗ₖ (1 : Matrix q q ℂ)) (i, k) (j, l)‖ ^ 2 *
             (hX.eigenvalues i * hHK.eigenvalues k) *
             (Real.log (hX.eigenvalues i * hHK.eigenvalues k) -
               Real.log (hY.eigenvalues j * hHK.eigenvalues l)) : ℝ)) : EReal)) =
        if hHK.eigenvalues k = 0 then (0 : EReal)
        else ((hHK.eigenvalues k : ℝ) : EReal) *
          (if hX.eigenvalues i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0 then (0 : EReal)
           else if hY.eigenvalues j = 0 then ⊤
           else (((‖(U₁ᴴ * U₂) i j‖ ^ 2 * hX.eigenvalues i *
             (Real.log (hX.eigenvalues i) - Real.log (hY.eigenvalues j)) : ℝ)) : EReal)) := by
      intro k j
      rw [Finset.sum_eq_single k]
      · simp only [kroneckerMap_apply, one_apply_eq, mul_one]
        exact relEntTerm_mul_right (hc_nonneg k)
      · intro l _ hlk
        simp [kroneckerMap_apply, one_apply_ne (Ne.symm hlk)]
      · intro hk; exact (hk (Finset.mem_univ k)).elim
    simp_rw [Fintype.sum_prod_type, h_inner_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine ereal_sum_prob_mul hHK.eigenvalues hc_nonneg hc_sum _ ?_
    split_ifs <;> [decide; decide; exact EReal.coe_ne_bot _]

lemma relEnt_kron_left {p q : Type} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (K : Matrix q q ℂ) (X Y : Matrix p p ℂ)
    (hK : K.PosSemidef) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hK_tr : X = 0 ∨ K.trace = 1) :
    relativeEntropy (K ⊗ₖ X) (K ⊗ₖ Y) = relativeEntropy X Y := by
  rcases hK_tr with rfl | htr
  · rw [kronecker_zero, relEnt_zero_left, relEnt_zero_left]
  · have hHK : K.IsHermitian := hK.isHermitian
    have hKX : (K ⊗ₖ X).IsHermitian := by
      unfold IsHermitian; rw [conjTranspose_kronecker, hHK.eq, hX.eq]
    have hKY : (K ⊗ₖ Y).IsHermitian := by
      unfold IsHermitian; rw [conjTranspose_kronecker, hHK.eq, hY.eq]
    let U₁ : Matrix p p ℂ := hX.eigenvectorUnitary
    let U₂ : Matrix p p ℂ := hY.eigenvectorUnitary
    let UK : Matrix q q ℂ := hHK.eigenvectorUnitary
    have hU₁_left : U₁ᴴ * U₁ = 1 := Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
    have hU₁_right : U₁ * U₁ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2
    have hU₂_left : U₂ᴴ * U₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hY.eigenvectorUnitary.2
    have hU₂_right : U₂ * U₂ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hY.eigenvectorUnitary.2
    have hUK_left : UKᴴ * UK = 1 := Matrix.mem_unitaryGroup_iff'.mp hHK.eigenvectorUnitary.2
    have hX_spec : X = U₁ * diagonal (fun i => (hX.eigenvalues i : ℂ)) * U₁ᴴ := by
      conv_lhs => rw [hX.spectral_theorem]
      rfl
    have hY_spec : Y = U₂ * diagonal (fun j => (hY.eigenvalues j : ℂ)) * U₂ᴴ := by
      conv_lhs => rw [hY.spectral_theorem]
      rfl
    have hK_spec : K = UK * diagonal (fun k => (hHK.eigenvalues k : ℂ)) * UKᴴ := by
      conv_lhs => rw [hHK.spectral_theorem]
      rfl
    have hP : (UK ⊗ₖ U₁)ᴴ * (UK ⊗ₖ U₁) = 1 := by
      rw [conjTranspose_kronecker, ← mul_kronecker_mul, hUK_left, hU₁_left, one_kronecker_one]
    have hQ : (UK ⊗ₖ U₂)ᴴ * (UK ⊗ₖ U₂) = 1 := by
      rw [conjTranspose_kronecker, ← mul_kronecker_mul, hUK_left, hU₂_left, one_kronecker_one]
    have hPQ : (UK ⊗ₖ U₁) * (UK ⊗ₖ U₁)ᴴ = (UK ⊗ₖ U₂) * (UK ⊗ₖ U₂)ᴴ := by
      rw [conjTranspose_kronecker, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
        hU₁_right, hU₂_right]
    have hKXP : K ⊗ₖ X = (UK ⊗ₖ U₁) *
        diagonal (fun ki : q × p => ((hHK.eigenvalues ki.1 * hX.eigenvalues ki.2 : ℝ) : ℂ)) *
        (UK ⊗ₖ U₁)ᴴ := by
      have hD : diagonal (fun ki : q × p => ((hHK.eigenvalues ki.1 * hX.eigenvalues ki.2 : ℝ) : ℂ)) =
          diagonal (fun k => (hHK.eigenvalues k : ℂ)) ⊗ₖ diagonal (fun i => (hX.eigenvalues i : ℂ)) := by
        rw [diagonal_kronecker_diagonal]; congr 1; funext ki; push_cast; rfl
      rw [hD, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, ← hK_spec, ← hX_spec]
    have hKYQ : K ⊗ₖ Y = (UK ⊗ₖ U₂) *
        diagonal (fun lj : q × p => ((hHK.eigenvalues lj.1 * hY.eigenvalues lj.2 : ℝ) : ℂ)) *
        (UK ⊗ₖ U₂)ᴴ := by
      have hD : diagonal (fun lj : q × p => ((hHK.eigenvalues lj.1 * hY.eigenvalues lj.2 : ℝ) : ℂ)) =
          diagonal (fun l => (hHK.eigenvalues l : ℂ)) ⊗ₖ diagonal (fun j => (hY.eigenvalues j : ℂ)) := by
        rw [diagonal_kronecker_diagonal]; congr 1; funext lj; push_cast; rfl
      rw [hD, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, ← hK_spec, ← hY_spec]
    rw [relEnt_udiag (K ⊗ₖ X) (K ⊗ₖ Y) hKX hKY (UK ⊗ₖ U₁) (UK ⊗ₖ U₂) hP hQ hPQ
      (fun ki => hHK.eigenvalues ki.1 * hX.eigenvalues ki.2)
      (fun lj => hHK.eigenvalues lj.1 * hY.eigenvalues lj.2) hKXP hKYQ]
    have hPQ_inner : (UK ⊗ₖ U₁)ᴴ * (UK ⊗ₖ U₂) = (1 : Matrix q q ℂ) ⊗ₖ (U₁ᴴ * U₂) := by
      rw [conjTranspose_kronecker, ← mul_kronecker_mul, hUK_left]
    rw [hPQ_inner, relativeEntropy_eq_relEntFormula X Y hX hY]
    have hc_nonneg : ∀ k : q, 0 ≤ hHK.eigenvalues k := hK.eigenvalues_nonneg
    have hc_sum : ∑ k : q, hHK.eigenvalues k = 1 := by
      have htr' := hHK.trace_eq_sum_eigenvalues
      rw [htr] at htr'
      have hre := congr_arg Complex.re htr'
      simpa [Complex.re_sum] using hre.symm
    unfold relEntFormula
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h_inner_sum : ∀ k : q,
        ∑ lj : q × p,
          (if hHK.eigenvalues k * hX.eigenvalues i = 0 ∨
              ‖((1 : Matrix q q ℂ) ⊗ₖ (U₁ᴴ * U₂)) (k, i) lj‖ = 0 then (0 : EReal)
           else if hHK.eigenvalues lj.1 * hY.eigenvalues lj.2 = 0 then ⊤
           else (((‖((1 : Matrix q q ℂ) ⊗ₖ (U₁ᴴ * U₂)) (k, i) lj‖ ^ 2 *
             (hHK.eigenvalues k * hX.eigenvalues i) *
             (Real.log (hHK.eigenvalues k * hX.eigenvalues i) -
               Real.log (hHK.eigenvalues lj.1 * hY.eigenvalues lj.2)) : ℝ)) : EReal)) =
        ∑ j : p,
          (if hHK.eigenvalues k = 0 then (0 : EReal)
           else ((hHK.eigenvalues k : ℝ) : EReal) *
             (if hX.eigenvalues i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0 then (0 : EReal)
              else if hY.eigenvalues j = 0 then ⊤
              else (((‖(U₁ᴴ * U₂) i j‖ ^ 2 * hX.eigenvalues i *
                (Real.log (hX.eigenvalues i) - Real.log (hY.eigenvalues j)) : ℝ)) : EReal))) := by
      intro k
      rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
      · refine Finset.sum_congr rfl fun j _ => ?_
        simp only [kroneckerMap_apply, one_apply_eq, one_mul]
        exact relEntTerm_mul_left (hc_nonneg k)
      · intro l _ hlk
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [kroneckerMap_apply, one_apply_ne (Ne.symm hlk)]
      · intro hk; exact (hk (Finset.mem_univ k)).elim
    simp_rw [h_inner_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine ereal_sum_prob_mul hHK.eigenvalues hc_nonneg hc_sum _ ?_
    split_ifs <;> [decide; decide; exact EReal.coe_ne_bot _]

lemma relativeEntropy_ne_bot {n : Type} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) : relativeEntropy X Y ≠ ⊥ := by
  unfold relativeEntropy
  split_ifs with h
  · refine ereal_sum_ne_bot Finset.univ _ fun i _ => ?_
    refine ereal_sum_ne_bot Finset.univ _ fun j _ => ?_
    split_ifs <;> [decide; decide; exact EReal.coe_ne_bot _]
  · decide

lemma ereal_coe_mul_ne_bot {c : ℝ} {z : EReal} (hc : 0 ≤ c) (hz : z ≠ ⊥) :
    ((c : ℝ) : EReal) * z ≠ ⊥ := by
  induction z using EReal.rec with
  | bot => exact (hz rfl).elim
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
  | top =>
    rcases eq_or_lt_of_le hc with rfl | hc_pos
    · simp
    · rw [EReal.coe_mul_top_of_pos hc_pos]; decide

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

lemma unitary_mul_entry_norm_sq {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (i j : n) :
    ‖((hX.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hY.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2 =
      ‖inner ℂ (hX.eigenvectorBasis i) (hY.eigenvectorBasis j)‖ ^ 2 := by
  congr 2
  rw [mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Matrix.IsHermitian.eigenvectorUnitary_apply, mul_comm]

lemma unitary_mul_row_sum_eq_one {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (i : n) :
    ∑ j : n, ‖((hX.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
      (hY.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2 = 1 := by
  simp_rw [unitary_mul_entry_norm_sq hX hY]
  rw [onb_sum_inner_sq_left hY.eigenvectorBasis (hX.eigenvectorBasis i),
    hX.eigenvectorBasis.orthonormal.1 i, one_pow]

lemma unitary_mul_col_sum_eq_one {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (j : n) :
    ∑ i : n, ‖((hX.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
      (hY.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2 = 1 := by
  simp_rw [unitary_mul_entry_norm_sq hX hY]
  rw [onb_sum_inner_sq_right hX.eigenvectorBasis (hY.eigenvectorBasis j),
    hY.eigenvectorBasis.orthonormal.1 j, one_pow]

lemma relEnt_smul_split {n : Type} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (p q : ℝ) (hp : X.trace = (p : ℂ)) (hq : Y.trace = (q : ℂ)) :
    relativeEntropy X Y =
      classicalRelTerm p q +
        ((p : ℝ) : EReal) * relativeEntropy (((p : ℂ))⁻¹ • X) (((q : ℂ))⁻¹ • Y) := by
  have hp_nonneg : 0 ≤ p := by
    have h := (Complex.nonneg_iff.mp hX.trace_nonneg).1
    rw [hp, Complex.ofReal_re] at h
    exact h
  have hq_nonneg : 0 ≤ q := by
    have h := (Complex.nonneg_iff.mp hY.trace_nonneg).1
    rw [hq, Complex.ofReal_re] at h
    exact h
  by_cases hp0 : p = 0
  · subst hp0
    have hX0 : X = 0 := hX.trace_eq_zero_iff.mp (by simpa using hp)
    subst hX0
    rw [relEnt_zero_left]
    simp [classicalRelTerm]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp0)
    by_cases hq0 : q = 0
    · subst hq0
      have hY0 : Y = 0 := hY.trace_eq_zero_iff.mp (by simpa using hq)
      subst hY0
      have h_cl : classicalRelTerm p 0 = ⊤ := by
        unfold classicalRelTerm; rw [if_neg hp0, if_pos rfl]
      rw [h_cl, EReal.top_add_of_ne_bot
        (ereal_coe_mul_ne_bot hp_nonneg (relativeEntropy_ne_bot _ _))]
      have hHX : X.IsHermitian := hX.isHermitian
      let U₁ : Matrix n n ℂ := hHX.eigenvectorUnitary
      have hU₁_left : U₁ᴴ * U₁ = 1 := Matrix.mem_unitaryGroup_iff'.mp hHX.eigenvectorUnitary.2
      have hX_spec : X = U₁ * diagonal (fun i => (hHX.eigenvalues i : ℂ)) * U₁ᴴ := by
        conv_lhs => rw [hHX.spectral_theorem]
        rfl
      have h0_spec : (0 : Matrix n n ℂ) = U₁ * diagonal (fun _ : n => ((0 : ℝ) : ℂ)) * U₁ᴴ := by simp
      rw [relEnt_udiag X 0 hHX isHermitian_zero U₁ U₁ hU₁_left hU₁_left rfl
        hHX.eigenvalues (fun _ => 0) hX_spec h0_spec, hU₁_left]
      have h_sum_p : ∑ i : n, hHX.eigenvalues i = p := by
        have htr := hHX.trace_eq_sum_eigenvalues
        rw [hp] at htr
        have hre := congr_arg Complex.re htr
        simpa [Complex.re_sum] using hre.symm
      have h_ex : ∃ i : n, hHX.eigenvalues i ≠ 0 := by
        by_contra h_all
        have h0 : ∑ i : n, hHX.eigenvalues i = 0 := Finset.sum_eq_zero fun i _ => by
          by_contra hi; exact h_all ⟨i, hi⟩
        linarith
      rcases h_ex with ⟨i₀, hi₀⟩
      refine relEntFormula_eq_top_iff 1 hHX.eigenvalues (fun _ => 0) ⟨i₀, i₀, ?_, rfl⟩
      rw [not_or, one_apply_eq, norm_one]
      exact ⟨hi₀, one_ne_zero⟩
    · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq0)
      let X' : Matrix n n ℂ := ((p : ℂ))⁻¹ • X
      let Y' : Matrix n n ℂ := ((q : ℂ))⁻¹ • Y
      have hX'_psd : X'.PosSemidef := by
        dsimp [X']
        rw [← Complex.ofReal_inv]
        exact hX.smul (by simpa using inv_nonneg.mpr hp_nonneg)
      have hY'_psd : Y'.PosSemidef := by
        dsimp [Y']
        rw [← Complex.ofReal_inv]
        exact hY.smul (by simpa using inv_nonneg.mpr hq_nonneg)
      have hHX : X.IsHermitian := hX.isHermitian
      have hHY : Y.IsHermitian := hY.isHermitian
      have hHX' : X'.IsHermitian := hX'_psd.isHermitian
      have hHY' : Y'.IsHermitian := hY'_psd.isHermitian
      let U₁ : Matrix n n ℂ := hHX'.eigenvectorUnitary
      let U₂ : Matrix n n ℂ := hHY'.eigenvectorUnitary
      have hU₁_left : U₁ᴴ * U₁ = 1 := Matrix.mem_unitaryGroup_iff'.mp hHX'.eigenvectorUnitary.2
      have hU₁_right : U₁ * U₁ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hHX'.eigenvectorUnitary.2
      have hU₂_left : U₂ᴴ * U₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hHY'.eigenvectorUnitary.2
      have hU₂_right : U₂ * U₂ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hHY'.eigenvectorUnitary.2
      have hPQ : U₁ * U₁ᴴ = U₂ * U₂ᴴ := by rw [hU₁_right, hU₂_right]
      have hX'_spec : X' = U₁ * diagonal (fun i => (hHX'.eigenvalues i : ℂ)) * U₁ᴴ := by
        conv_lhs => rw [hHX'.spectral_theorem]
        rfl
      have hY'_spec : Y' = U₂ * diagonal (fun j => (hHY'.eigenvalues j : ℂ)) * U₂ᴴ := by
        conv_lhs => rw [hHY'.spectral_theorem]
        rfl
      have hX_eq : X = ((p : ℝ) : ℂ) • X' := by
        change X = ((p : ℝ) : ℂ) • (((p : ℝ) : ℂ)⁻¹ • X)
        rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hp0), one_smul]
      have hY_eq : Y = ((q : ℝ) : ℂ) • Y' := by
        change Y = ((q : ℝ) : ℂ) • (((q : ℝ) : ℂ)⁻¹ • Y)
        rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hq0), one_smul]
      have hXP : X = U₁ * diagonal (fun i => ((p * hHX'.eigenvalues i : ℝ) : ℂ)) * U₁ᴴ := by
        conv_lhs => rw [hX_eq, hX'_spec]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
        congr 2; ext i j; simp [diagonal_apply]
      have hYQ : Y = U₂ * diagonal (fun j => ((q * hHY'.eigenvalues j : ℝ) : ℂ)) * U₂ᴴ := by
        conv_lhs => rw [hY_eq, hY'_spec]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
        congr 2; ext i j; simp [diagonal_apply]
      rw [relEnt_udiag X Y hHX hHY U₁ U₂ hU₁_left hU₂_left hPQ
        (fun i => p * hHX'.eigenvalues i) (fun j => q * hHY'.eigenvalues j) hXP hYQ]
      change _ = classicalRelTerm p q + ((p : ℝ) : EReal) * relativeEntropy X' Y'
      rw [relativeEntropy_eq_relEntFormula X' Y' hHX' hHY']
      have h_cl : classicalRelTerm p q = ((p * Real.log (p / q) : ℝ) : EReal) := by
        unfold classicalRelTerm; rw [if_neg hp0, if_neg hq0]
      rw [h_cl]
      let lam₁ := hHX'.eigenvalues
      let lam₂ := hHY'.eigenvalues
      let w : n → n → ℝ := fun i j => ‖(U₁ᴴ * U₂) i j‖ ^ 2
      have h_top_iff :
          (∃ i j, ¬(p * lam₁ i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0) ∧ q * lam₂ j = 0) ↔
          (∃ i j, ¬(lam₁ i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0) ∧ lam₂ j = 0) := by
        simp only [mul_eq_zero, hp0, hq0, false_or]
      by_cases h_top : ∃ i j, ¬(lam₁ i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0) ∧ lam₂ j = 0
      · rw [relEntFormula_eq_top_iff (U₁ᴴ * U₂) (fun i => p * lam₁ i) (fun j => q * lam₂ j)
          (h_top_iff.mpr h_top),
          relEntFormula_eq_top_iff (U₁ᴴ * U₂) lam₁ lam₂ h_top,
          EReal.coe_mul_top_of_pos hp_pos,
          EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      · have h_top_pq : ¬∃ i j, ¬(p * lam₁ i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0) ∧ q * lam₂ j = 0 :=
          fun h => h_top (h_top_iff.mp h)
        rw [relEntFormula_eq_coe_of_no_top (U₁ᴴ * U₂) (fun i => p * lam₁ i) (fun j => q * lam₂ j) h_top_pq,
          relEntFormula_eq_coe_of_no_top (U₁ᴴ * U₂) lam₁ lam₂ h_top,
          ← EReal.coe_mul, ← EReal.coe_add]
        congr 1
        change ∑ i : n, ∑ j : n, w i j * ((p * lam₁ i) * (Real.log (p * lam₁ i) - Real.log (q * lam₂ j))) =
          p * Real.log (p / q) + p * ∑ i : n, ∑ j : n, w i j * (lam₁ i * (Real.log (lam₁ i) - Real.log (lam₂ j)))
        have hw_sum_j : ∀ i, ∑ j : n, w i j = 1 := unitary_mul_row_sum_eq_one hHX' hHY'
        have hlam₁_sum : ∑ i : n, lam₁ i = 1 := by
          have htr := hHX'.trace_eq_sum_eigenvalues
          have htr1 : X'.trace = 1 := by
            dsimp [X']
            rw [trace_smul, hp, smul_eq_mul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hp0)]
          rw [htr1] at htr
          have hre := congr_arg Complex.re htr
          simpa [lam₁, Complex.re_sum] using hre.symm
        have h_term : ∀ i j : n,
            w i j * ((p * lam₁ i) * (Real.log (p * lam₁ i) - Real.log (q * lam₂ j))) =
            w i j * lam₁ i * (p * Real.log (p / q)) +
              p * (w i j * (lam₁ i * (Real.log (lam₁ i) - Real.log (lam₂ j)))) := by
          intro i j
          by_cases hij : lam₁ i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0
          · rcases hij with h1 | h2
            · simp [h1]
            · have hw0 : w i j = 0 := by dsimp [w]; rw [h2, zero_pow two_ne_zero]
              simp [hw0]
          · have h2_ne : lam₂ j ≠ 0 := fun h0 => h_top ⟨i, j, hij, h0⟩
            have h1_ne : lam₁ i ≠ 0 := (not_or.mp hij).1
            rw [Real.log_mul hp0 h1_ne, Real.log_mul hq0 h2_ne, Real.log_div hp0 hq0]
            ring
        simp_rw [h_term, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          hw_sum_j, one_mul, hlam₁_sum, one_mul]

/-! ### Midpoint strict concavity of `vonNeumannEntropy` -/

lemma log_add_one_le_and_eq {x : ℝ} (hx : 0 < x) :
    Real.log x + 1 ≤ x ∧ (Real.log x + 1 = x ↔ x = 1) := by
  have hle : Real.log x + 1 ≤ x := by
    have h := Real.add_one_le_exp (Real.log x)
    rwa [Real.exp_log hx] at h
  refine ⟨hle, ⟨fun heq => ?_, fun h1 => by subst h1; simp⟩⟩
  by_contra hne
  have hstrict := Real.log_lt_sub_one_of_pos hx hne
  linarith

lemma relativeEntropy_nonneg {n : Type} [Fintype n] [DecidableEq n]
    {ρ σ : Matrix n n ℂ} (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    0 ≤ relativeEntropy ρ σ := by
  have hHρ : ρ.IsHermitian := hρ.1.isHermitian
  have hHσ : σ.IsHermitian := hσ.1.isHermitian
  rw [relativeEntropy_eq_relEntFormula ρ σ hHρ hHσ]
  let U₁ : Matrix n n ℂ := hHρ.eigenvectorUnitary
  let U₂ : Matrix n n ℂ := hHσ.eigenvectorUnitary
  let w : n → n → ℝ := fun i j => ‖(U₁ᴴ * U₂) i j‖ ^ 2
  let p := hHρ.eigenvalues
  let q := hHσ.eigenvalues
  by_cases h_top : ∃ i j, ¬(p i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0) ∧ q j = 0
  · rw [relEntFormula_eq_top_iff (U₁ᴴ * U₂) p q h_top]
    exact le_top
  · rw [relEntFormula_eq_coe_of_no_top (U₁ᴴ * U₂) p q h_top, EReal.coe_nonneg]
    change 0 ≤ ∑ i : n, ∑ j : n, w i j * (p i * (Real.log (p i) - Real.log (q j)))
    have hp_nonneg : ∀ i, 0 ≤ p i := hρ.1.eigenvalues_nonneg
    have hq_nonneg : ∀ j, 0 ≤ q j := hσ.1.eigenvalues_nonneg
    have hp_sum : ∑ i : n, p i = 1 := by
      have htr := hHρ.trace_eq_sum_eigenvalues
      rw [hρ.2] at htr
      have hre := congr_arg Complex.re htr
      simpa [p, Complex.re_sum] using hre.symm
    have hq_sum : ∑ j : n, q j = 1 := by
      have htr := hHσ.trace_eq_sum_eigenvalues
      rw [hσ.2] at htr
      have hre := congr_arg Complex.re htr
      simpa [q, Complex.re_sum] using hre.symm
    have h_lower_le : ∀ i j : n,
        w i j * (p i - q j) ≤
          w i j * (p i * (Real.log (p i) - Real.log (q j))) := by
      intro i j
      by_cases hij : p i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0
      · rcases hij with hpi | hwij
        · rw [hpi, zero_sub, zero_mul, mul_zero, mul_neg, Left.neg_nonpos_iff]
          exact mul_nonneg (sq_nonneg _) (hq_nonneg j)
        · have hw0 : w i j = 0 := by dsimp [w]; rw [hwij, zero_pow two_ne_zero]
          simp [hw0]
      · have hqj : q j ≠ 0 := fun h0 => h_top ⟨i, j, hij, h0⟩
        have hpi : p i ≠ 0 := (not_or.mp hij).1
        have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)
        have hq_pos : 0 < q j := lt_of_le_of_ne (hq_nonneg j) (Ne.symm hqj)
        have hlog := (log_add_one_le_and_eq (div_pos hq_pos hp_pos)).1
        rw [Real.log_div hq_pos.ne' hp_pos.ne'] at hlog
        have hlog2 : p i - q j ≤ p i * (Real.log (p i) - Real.log (q j)) := by
          have hmul := mul_le_mul_of_nonneg_left hlog hp_pos.le
          have hcancel : p i * (q j / p i) = q j := mul_div_cancel₀ (q j) hp_pos.ne'
          linarith
        exact mul_le_mul_of_nonneg_left hlog2 (sq_nonneg _)
    have hw_sum_j : ∀ i, ∑ j : n, w i j = 1 := unitary_mul_row_sum_eq_one hHρ hHσ
    have hw_sum_i : ∀ j, ∑ i : n, w i j = 1 := unitary_mul_col_sum_eq_one hHρ hHσ
    have h_lower_sum : ∑ i : n, ∑ j : n, w i j * (p i - q j) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [Finset.sum_comm (f := fun i j => w i j * q j)]
      simp_rw [← Finset.sum_mul, hw_sum_j, hw_sum_i, one_mul, hp_sum, hq_sum, sub_self]
    rw [← h_lower_sum]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_lower_le i j

lemma diag_conj_eigenvectorUnitary_re {n : Type} [Fintype n] [DecidableEq n]
    {X M : Matrix n n ℂ} (hX : X.IsHermitian) (hM : M.IsHermitian) (j : n) :
    (((hM.eigenvectorUnitary : Matrix n n ℂ)ᴴ * X *
      (hM.eigenvectorUnitary : Matrix n n ℂ)) j j).re =
      ∑ i : n, ‖((hX.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hM.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2 * hX.eigenvalues i := by
  let U_X : Matrix n n ℂ := hX.eigenvectorUnitary
  let U_M : Matrix n n ℂ := hM.eigenvectorUnitary
  have hX_spec : X = U_X * diagonal (fun i => (hX.eigenvalues i : ℂ)) * U_Xᴴ := by
    conv_lhs => rw [hX.spectral_theorem]
    rfl
  have h_prod : U_Mᴴ * X * U_M =
      (U_Xᴴ * U_M)ᴴ * diagonal (fun i => (hX.eigenvalues i : ℂ)) * (U_Xᴴ * U_M) := by
    conv_lhs => rw [hX_spec]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  change ((U_Mᴴ * X * U_M) j j).re = ∑ i : n, ‖(U_Xᴴ * U_M) i j‖ ^ 2 * hX.eigenvalues i
  rw [h_prod, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h_term : star ((U_Xᴴ * U_M) i j) * (hX.eigenvalues i : ℂ) * (U_Xᴴ * U_M) i j =
      (((‖(U_Xᴴ * U_M) i j‖ ^ 2 * hX.eigenvalues i : ℝ)) : ℂ) := by
    calc star ((U_Xᴴ * U_M) i j) * (hX.eigenvalues i : ℂ) * (U_Xᴴ * U_M) i j
        = ((U_Xᴴ * U_M) i j * star ((U_Xᴴ * U_M) i j)) * (hX.eigenvalues i : ℂ) := by ring
      _ = (((‖(U_Xᴴ * U_M) i j‖ ^ 2 * hX.eigenvalues i : ℝ)) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, Complex.normSq_eq_norm_sq]
  rw [h_term, Complex.ofReal_re]

lemma diag_self_eigenvectorUnitary_re {n : Type} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (j : n) :
    (((hM.eigenvectorUnitary : Matrix n n ℂ)ᴴ * M *
      (hM.eigenvectorUnitary : Matrix n n ℂ)) j j).re = hM.eigenvalues j := by
  rw [diag_conj_eigenvectorUnitary_re hM hM j]
  let U_M : Matrix n n ℂ := hM.eigenvectorUnitary
  have hU_M : U_Mᴴ * U_M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM.eigenvectorUnitary.2
  change ∑ i : n, ‖(U_Mᴴ * U_M) i j‖ ^ 2 * hM.eigenvalues i = hM.eigenvalues j
  rw [hU_M, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [one_apply_ne hij]
  · intro hj; exact (hj (Finset.mem_univ j)).elim

lemma vonNeumannEntropy_eq_neg_sum_mul_log {n : Type} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    ∑ i : n, hX.eigenvalues i * Real.log (hX.eigenvalues i) = -vonNeumannEntropy X := by
  unfold vonNeumannEntropy
  rw [dif_pos hX, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.negMulLog]

lemma relEnt_le_dominate {n : Type} [Fintype n] [DecidableEq n]
    {X M : Matrix n n ℂ} (hX : IsDensityMatrix X) (hM : M.IsHermitian)
    (h_dom : ∀ j : n,
      (1 / 2 : ℝ) * (∑ i : n, ‖((hX.1.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hM.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2 * hX.1.isHermitian.eigenvalues i) ≤
      hM.eigenvalues j) :
    relativeEntropy X M =
      (((-vonNeumannEntropy X -
        ∑ j : n,
          (∑ i : n, ‖((hX.1.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
            (hM.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2 * hX.1.isHermitian.eigenvalues i) *
            Real.log (hM.eigenvalues j) : ℝ)) : EReal) := by
  have hHX : X.IsHermitian := hX.1.isHermitian
  rw [relativeEntropy_eq_relEntFormula X M hHX hM]
  let U₁ : Matrix n n ℂ := hHX.eigenvectorUnitary
  let U₂ : Matrix n n ℂ := hM.eigenvectorUnitary
  let w : n → n → ℝ := fun i j => ‖(U₁ᴴ * U₂) i j‖ ^ 2
  let p := hHX.eigenvalues
  let q := hM.eigenvalues
  have hp_nonneg : ∀ i, 0 ≤ p i := hX.1.eigenvalues_nonneg
  have h_no_top : ¬∃ i j, ¬(p i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0) ∧ q j = 0 := by
    rintro ⟨i, j, hij, hqj⟩
    have hpi : p i ≠ 0 := (not_or.mp hij).1
    have hwij : ‖(U₁ᴴ * U₂) i j‖ ≠ 0 := (not_or.mp hij).2
    have h_pos : 0 < w i j * p i :=
      mul_pos (sq_pos_of_ne_zero hwij) (lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi))
    have h_le_sum : w i j * p i ≤ ∑ i' : n, w i' j * p i' :=
      Finset.single_le_sum (f := fun i' => w i' j * p i')
        (fun i' _ => mul_nonneg (sq_nonneg _) (hp_nonneg i')) (Finset.mem_univ i)
    have h_dom_j := h_dom j
    change (1 / 2 : ℝ) * (∑ i' : n, w i' j * p i') ≤ q j at h_dom_j
    linarith
  rw [relEntFormula_eq_coe_of_no_top (U₁ᴴ * U₂) p q h_no_top]
  congr 1
  change ∑ i : n, ∑ j : n, w i j * (p i * (Real.log (p i) - Real.log (q j))) =
    -vonNeumannEntropy X - ∑ j : n, (∑ i : n, w i j * p i) * Real.log (q j)
  have hw_sum_j : ∀ i, ∑ j : n, w i j = 1 := unitary_mul_row_sum_eq_one hHX hM
  simp_rw [mul_sub, ← mul_assoc, Finset.sum_sub_distrib]
  have h_first : ∑ i : n, ∑ j : n, w i j * p i * Real.log (p i) = -vonNeumannEntropy X := by
    rw [← vonNeumannEntropy_eq_neg_sum_mul_log hHX]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [mul_assoc, ← Finset.sum_mul, hw_sum_j, one_mul]
    rfl
  have h_second : ∑ i : n, ∑ j : n, w i j * p i * Real.log (q j) =
      ∑ j : n, (∑ i : n, w i j * p i) * Real.log (q j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
  rw [h_first, h_second]

lemma eq_of_relativeEntropy_eq_zero {n : Type} [Fintype n] [DecidableEq n]
    {ρ σ : Matrix n n ℂ} (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (h_zero : relativeEntropy ρ σ = 0) : ρ = σ := by
  have hHρ : ρ.IsHermitian := hρ.1.isHermitian
  have hHσ : σ.IsHermitian := hσ.1.isHermitian
  rw [relativeEntropy_eq_relEntFormula ρ σ hHρ hHσ] at h_zero
  let U₁ : Matrix n n ℂ := hHρ.eigenvectorUnitary
  let U₂ : Matrix n n ℂ := hHσ.eigenvectorUnitary
  let w : n → n → ℝ := fun i j => ‖(U₁ᴴ * U₂) i j‖ ^ 2
  let p := hHρ.eigenvalues
  let q := hHσ.eigenvalues
  have h_no_top : ¬∃ i j, ¬(p i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0) ∧ q j = 0 := by
    intro h_top
    rw [relEntFormula_eq_top_iff (U₁ᴴ * U₂) p q h_top] at h_zero
    exact EReal.top_ne_zero h_zero
  rw [relEntFormula_eq_coe_of_no_top (U₁ᴴ * U₂) p q h_no_top, EReal.coe_eq_zero] at h_zero
  change ∑ i : n, ∑ j : n, w i j * (p i * (Real.log (p i) - Real.log (q j))) = 0 at h_zero
  have hp_nonneg : ∀ i, 0 ≤ p i := hρ.1.eigenvalues_nonneg
  have hq_nonneg : ∀ j, 0 ≤ q j := hσ.1.eigenvalues_nonneg
  have hp_sum : ∑ i : n, p i = 1 := by
    have htr := hHρ.trace_eq_sum_eigenvalues
    rw [hρ.2] at htr
    have hre := congr_arg Complex.re htr
    simpa [p, Complex.re_sum] using hre.symm
  have hq_sum : ∑ j : n, q j = 1 := by
    have htr := hHσ.trace_eq_sum_eigenvalues
    rw [hσ.2] at htr
    have hre := congr_arg Complex.re htr
    simpa [q, Complex.re_sum] using hre.symm
  have h_lower_le : ∀ i j : n,
      w i j * (p i - q j) ≤
        w i j * (p i * (Real.log (p i) - Real.log (q j))) := by
    intro i j
    by_cases hij : p i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0
    · rcases hij with hpi | hwij
      · rw [hpi, zero_sub, zero_mul, mul_zero, mul_neg, Left.neg_nonpos_iff]
        exact mul_nonneg (sq_nonneg _) (hq_nonneg j)
      · have hw0 : w i j = 0 := by dsimp [w]; rw [hwij, zero_pow two_ne_zero]
        simp [hw0]
    · have hqj : q j ≠ 0 := fun h0 => h_no_top ⟨i, j, hij, h0⟩
      have hpi : p i ≠ 0 := (not_or.mp hij).1
      have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)
      have hq_pos : 0 < q j := lt_of_le_of_ne (hq_nonneg j) (Ne.symm hqj)
      have hlog := (log_add_one_le_and_eq (div_pos hq_pos hp_pos)).1
      rw [Real.log_div hq_pos.ne' hp_pos.ne'] at hlog
      have hlog2 : p i - q j ≤ p i * (Real.log (p i) - Real.log (q j)) := by
        have hmul := mul_le_mul_of_nonneg_left hlog hp_pos.le
        have hcancel : p i * (q j / p i) = q j := mul_div_cancel₀ (q j) hp_pos.ne'
        linarith
      exact mul_le_mul_of_nonneg_left hlog2 (sq_nonneg _)
  have hw_sum_j : ∀ i, ∑ j : n, w i j = 1 := unitary_mul_row_sum_eq_one hHρ hHσ
  have hw_sum_i : ∀ j, ∑ i : n, w i j = 1 := unitary_mul_col_sum_eq_one hHρ hHσ
  have h_lower_sum : ∑ i : n, ∑ j : n, w i j * (p i - q j) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [Finset.sum_comm (f := fun i j => w i j * q j)]
    simp_rw [← Finset.sum_mul, hw_sum_j, hw_sum_i, one_mul, hp_sum, hq_sum, sub_self]
  have h_sum_eq : ∑ i : n, ∑ j : n, w i j * (p i - q j) =
      ∑ i : n, ∑ j : n, w i j * (p i * (Real.log (p i) - Real.log (q j))) := by
    rw [h_lower_sum, h_zero]
  have h_row_eq : ∀ i ∈ (Finset.univ : Finset n),
      ∑ j : n, w i j * (p i - q j) =
        ∑ j : n, w i j * (p i * (Real.log (p i) - Real.log (q j))) :=
    (Finset.sum_eq_sum_iff_of_le fun i _ => Finset.sum_le_sum fun j _ => h_lower_le i j).mp h_sum_eq
  have h_term_eq : ∀ i j : n,
      w i j * (p i - q j) = w i j * (p i * (Real.log (p i) - Real.log (q j))) := by
    intro i j
    exact (Finset.sum_eq_sum_iff_of_le fun j' _ => h_lower_le i j').mp
      (h_row_eq i (Finset.mem_univ i)) j (Finset.mem_univ j)
  have hpq_eq : ∀ i j : n, (U₁ᴴ * U₂) i j ≠ 0 → (p i : ℂ) = (q j : ℂ) := by
    intro i j hij_ne
    congr 1
    have hwij : 0 < w i j := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hij_ne)
    have h_eq : p i - q j = p i * (Real.log (p i) - Real.log (q j)) :=
      mul_left_cancel₀ hwij.ne' (h_term_eq i j)
    by_cases hpi : p i = 0
    · rw [hpi] at h_eq ⊢
      linarith
    · have hij_not : ¬(p i = 0 ∨ ‖(U₁ᴴ * U₂) i j‖ = 0) :=
        not_or.mpr ⟨hpi, norm_ne_zero_iff.mpr hij_ne⟩
      have hqj : q j ≠ 0 := fun h0 => h_no_top ⟨i, j, hij_not, h0⟩
      have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)
      have hq_pos : 0 < q j := lt_of_le_of_ne (hq_nonneg j) (Ne.symm hqj)
      have h_log_eq : Real.log (q j / p i) + 1 = q j / p i := by
        rw [Real.log_div hq_pos.ne' hp_pos.ne']
        have hdiv : (p i - q j) / p i = (p i * (Real.log (p i) - Real.log (q j))) / p i := by
          rw [h_eq]
        rw [sub_div, div_self hp_pos.ne', mul_div_cancel_left₀ _ hp_pos.ne'] at hdiv
        linarith
      have h1 := (log_add_one_le_and_eq (div_pos hq_pos hp_pos)).2.mp h_log_eq
      exact ((div_eq_one_iff_eq hp_pos.ne').mp h1).symm
  have hU₁_mul : U₁ * U₁ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hHρ.eigenvectorUnitary.2
  have hU₂_mul : U₂ * U₂ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hHσ.eigenvectorUnitary.2
  have h_comm : diagonal (fun i => (p i : ℂ)) * (U₁ᴴ * U₂) =
      (U₁ᴴ * U₂) * diagonal (fun j => (q j : ℂ)) := by
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases h0 : (U₁ᴴ * U₂) i j = 0
    · rw [h0, mul_zero, zero_mul]
    · rw [hpq_eq i j h0, mul_comm]
  have hρ_spec : ρ = U₁ * diagonal (fun i => (p i : ℂ)) * U₁ᴴ := by
    conv_lhs => rw [hHρ.spectral_theorem]
    rfl
  have hσ_spec : σ = U₂ * diagonal (fun j => (q j : ℂ)) * U₂ᴴ := by
    conv_lhs => rw [hHσ.spectral_theorem]
    rfl
  calc ρ = U₁ * diagonal (fun i => (p i : ℂ)) * U₁ᴴ * (U₂ * U₂ᴴ) := by
          rw [← hρ_spec, hU₂_mul, Matrix.mul_one]
    _ = U₁ * (diagonal (fun i => (p i : ℂ)) * (U₁ᴴ * U₂)) * U₂ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = U₁ * ((U₁ᴴ * U₂) * diagonal (fun j => (q j : ℂ))) * U₂ᴴ := by
          rw [h_comm]
    _ = (U₁ * U₁ᴴ) * (U₂ * diagonal (fun j => (q j : ℂ)) * U₂ᴴ) := by
          simp only [Matrix.mul_assoc]
    _ = σ := by rw [hU₁_mul, Matrix.one_mul, ← hσ_spec]

lemma isDensityMatrix_midpoint {n : Type} [Fintype n] [DecidableEq n]
    {X₁ X₂ : Matrix n n ℂ} (hX₁ : IsDensityMatrix X₁) (hX₂ : IsDensityMatrix X₂) :
    IsDensityMatrix ((1 / 2 : ℂ) • X₁ + (1 / 2 : ℂ) • X₂) := by
  refine ⟨?_, ?_⟩
  · have h_half : (0 : ℂ) ≤ 1 / 2 := by
      rw [one_div, ← Complex.ofReal_ofNat, ← Complex.ofReal_inv]
      simp
    exact (hX₁.1.smul h_half).add (hX₂.1.smul h_half)
  · simp [Matrix.trace_add, Matrix.trace_smul, hX₁.2, hX₂.2]
    norm_num

lemma vonNeumannEntropy_midpoint_eq {n : Type} [Fintype n] [DecidableEq n]
    {X₁ X₂ : Matrix n n ℂ} (hX₁ : IsDensityMatrix X₁) (hX₂ : IsDensityMatrix X₂)
    (h_eq : vonNeumannEntropy ((1 / 2 : ℂ) • X₁ + (1 / 2 : ℂ) • X₂) =
      (1 / 2 : ℝ) * vonNeumannEntropy X₁ + (1 / 2 : ℝ) * vonNeumannEntropy X₂) :
    X₁ = X₂ := by
  let M : Matrix n n ℂ := (1 / 2 : ℂ) • X₁ + (1 / 2 : ℂ) • X₂
  have hM : IsDensityMatrix M := isDensityMatrix_midpoint hX₁ hX₂
  have hHM : M.IsHermitian := hM.1.isHermitian
  have hHX₁ : X₁.IsHermitian := hX₁.1.isHermitian
  have hHX₂ : X₂.IsHermitian := hX₂.1.isHermitian
  let U_M : Matrix n n ℂ := hHM.eigenvectorUnitary
  let U₁ : Matrix n n ℂ := hHX₁.eigenvectorUnitary
  let U₂ : Matrix n n ℂ := hHX₂.eigenvectorUnitary
  let a₁ : n → ℝ := fun j =>
    ∑ i : n, ‖(U₁ᴴ * U_M) i j‖ ^ 2 * hHX₁.eigenvalues i
  let a₂ : n → ℝ := fun j =>
    ∑ i : n, ‖(U₂ᴴ * U_M) i j‖ ^ 2 * hHX₂.eigenvalues i
  have ha₁_nonneg : ∀ j, 0 ≤ a₁ j := fun j =>
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hX₁.1.eigenvalues_nonneg i)
  have ha₂_nonneg : ∀ j, 0 ≤ a₂ j := fun j =>
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hX₂.1.eigenvalues_nonneg i)
  have hq_split : ∀ j : n, hHM.eigenvalues j = (1 / 2 : ℝ) * a₁ j + (1 / 2 : ℝ) * a₂ j := by
    intro j
    have h0 := diag_self_eigenvectorUnitary_re hHM j
    have h1 := diag_conj_eigenvectorUnitary_re hHX₁ hHM j
    have h2 := diag_conj_eigenvectorUnitary_re hHX₂ hHM j
    change ((U_Mᴴ * M * U_M) j j).re = hHM.eigenvalues j at h0
    change ((U_Mᴴ * X₁ * U_M) j j).re = a₁ j at h1
    change ((U_Mᴴ * X₂ * U_M) j j).re = a₂ j at h2
    have h_mat : U_Mᴴ * M * U_M =
        (1 / 2 : ℂ) • (U_Mᴴ * X₁ * U_M) + (1 / 2 : ℂ) • (U_Mᴴ * X₂ * U_M) := by
      dsimp [M]
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have h_re : ((U_Mᴴ * M * U_M) j j).re =
        (1 / 2 : ℝ) * ((U_Mᴴ * X₁ * U_M) j j).re + (1 / 2 : ℝ) * ((U_Mᴴ * X₂ * U_M) j j).re := by
      rw [h_mat]
      simp [Matrix.add_apply, Matrix.smul_apply]
    linarith
  have h_dom₁ : ∀ j : n, (1 / 2 : ℝ) * a₁ j ≤ hHM.eigenvalues j := by
    intro j; linarith [hq_split j, ha₂_nonneg j]
  have h_dom₂ : ∀ j : n, (1 / 2 : ℝ) * a₂ j ≤ hHM.eigenvalues j := by
    intro j; linarith [hq_split j, ha₁_nonneg j]
  have h_rel₁ := relEnt_le_dominate hX₁ hHM h_dom₁
  have h_rel₂ := relEnt_le_dominate hX₂ hHM h_dom₂
  let r₁ : ℝ := -vonNeumannEntropy X₁ - ∑ j : n, a₁ j * Real.log (hHM.eigenvalues j)
  let r₂ : ℝ := -vonNeumannEntropy X₂ - ∑ j : n, a₂ j * Real.log (hHM.eigenvalues j)
  change relativeEntropy X₁ M = (r₁ : EReal) at h_rel₁
  change relativeEntropy X₂ M = (r₂ : EReal) at h_rel₂
  have hr₁_nonneg : 0 ≤ r₁ := by
    have h0 := relativeEntropy_nonneg hX₁ hM
    rwa [h_rel₁, EReal.coe_nonneg] at h0
  have hr₂_nonneg : 0 ≤ r₂ := by
    have h0 := relativeEntropy_nonneg hX₂ hM
    rwa [h_rel₂, EReal.coe_nonneg] at h0
  have h_sum_r : (1 / 2 : ℝ) * r₁ + (1 / 2 : ℝ) * r₂ =
      vonNeumannEntropy M - ((1 / 2 : ℝ) * vonNeumannEntropy X₁ + (1 / 2 : ℝ) * vonNeumannEntropy X₂) := by
    dsimp [r₁, r₂]
    have h_log_sum : ∑ j : n, ((1 / 2 : ℝ) * a₁ j + (1 / 2 : ℝ) * a₂ j) * Real.log (hHM.eigenvalues j) =
        -vonNeumannEntropy M := by
      simp_rw [← hq_split]
      exact vonNeumannEntropy_eq_neg_sum_mul_log hHM
    have h_lin : (1 / 2 : ℝ) * (∑ j : n, a₁ j * Real.log (hHM.eigenvalues j)) +
        (1 / 2 : ℝ) * (∑ j : n, a₂ j * Real.log (hHM.eigenvalues j)) =
        ∑ j : n, ((1 / 2 : ℝ) * a₁ j + (1 / 2 : ℝ) * a₂ j) * Real.log (hHM.eigenvalues j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    linarith
  have hr₁_zero : r₁ = 0 := by linarith
  have h_rel₁_zero : relativeEntropy X₁ M = 0 := by rw [h_rel₁, hr₁_zero, EReal.coe_zero]
  have hX₁M : X₁ = M := eq_of_relativeEntropy_eq_zero hX₁ hM h_rel₁_zero
  have hr₂_zero : r₂ = 0 := by linarith
  have h_rel₂_zero : relativeEntropy X₂ M = 0 := by rw [h_rel₂, hr₂_zero, EReal.coe_zero]
  have hX₂M : X₂ = M := eq_of_relativeEntropy_eq_zero hX₂ hM h_rel₂_zero
  exact hX₁M.trans hX₂M.symm

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

lemma psd_diagBlock {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    {ρ : Matrix C C ℂ} (hρ : ρ.PosSemidef) (a : Fin N) :
    (diagBlock U ρ a).PosSemidef := by
  unfold diagBlock
  exact (hρ.mul_mul_conjTranspose_same U).submatrix _

lemma traceLeft_add {A B : Type} [Fintype A] (X Y : Matrix (A × B) (A × B) ℂ) :
    traceLeft (X + Y) = traceLeft X + traceLeft Y := by
  ext i j; simp [traceLeft, Finset.sum_add_distrib]

lemma traceLeft_smul {A B : Type} [Fintype A] (c : ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    traceLeft (c • X) = c • traceLeft X := by
  ext i j; simp [traceLeft, Finset.mul_sum]

lemma traceRight_add {A B : Type} [Fintype B] (X Y : Matrix (A × B) (A × B) ℂ) :
    traceRight (X + Y) = traceRight X + traceRight Y := by
  ext i j; simp [traceRight, Finset.sum_add_distrib]

lemma traceRight_smul {A B : Type} [Fintype B] (c : ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    traceRight (c • X) = c • traceRight X := by
  ext i j; simp [traceRight, Finset.mul_sum]

lemma diagBlock_midpoint {C : Type} [Fintype C] {N : ℕ} {dr drb : Fin N → ℕ}
    (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ₁ ρ₂ : Matrix C C ℂ) (a : Fin N) :
    diagBlock U ((1 / 2 : ℂ) • ρ₁ + (1 / 2 : ℂ) • ρ₂) a =
      (1 / 2 : ℂ) • diagBlock U ρ₁ a + (1 / 2 : ℂ) • diagBlock U ρ₂ a := by
  ext ij kl
  simp [diagBlock, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]

lemma half_smul_add_half_smul {α : Type*} [AddCommMonoid α] [Module ℂ α] (x : α) :
    (1 / 2 : ℂ) • x + (1 / 2 : ℂ) • x = x := by
  rw [← add_smul]
  norm_num

lemma algebraicEntropyRight_eq_of_traceLeft_eq {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    {ρ₁ ρ₂ : Matrix C C ℂ}
    (h_eq : ∀ a : Fin N, traceLeft (diagBlock U ρ₁ a) = traceLeft (diagBlock U ρ₂ a)) :
    algebraicEntropyRight U ρ₁ = algebraicEntropyRight U ρ₂ := by
  have hw : ∀ a : Fin N, blockWeight U ρ₁ a = blockWeight U ρ₂ a := by
    intro a
    unfold blockWeight
    rw [← tr_traceLeft (diagBlock U ρ₁ a), ← tr_traceLeft (diagBlock U ρ₂ a), h_eq a]
  have hs : ∀ a : Fin N, blockStateRight U ρ₁ a = blockStateRight U ρ₂ a := by
    intro a
    unfold blockStateRight
    rw [hw a, h_eq a]
  unfold algebraicEntropyRight
  simp_rw [hw, hs]

lemma algebraicEntropyLeft_eq_of_traceRight_eq {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    {ρ₁ ρ₂ : Matrix C C ℂ}
    (h_eq : ∀ a : Fin N, traceRight (diagBlock U ρ₁ a) = traceRight (diagBlock U ρ₂ a)) :
    algebraicEntropyLeft U ρ₁ = algebraicEntropyLeft U ρ₂ := by
  have hw : ∀ a : Fin N, blockWeight U ρ₁ a = blockWeight U ρ₂ a := by
    intro a
    unfold blockWeight
    rw [← tr_traceRight (diagBlock U ρ₁ a), ← tr_traceRight (diagBlock U ρ₂ a), h_eq a]
  have hs : ∀ a : Fin N, blockStateLeft U ρ₁ a = blockStateLeft U ρ₂ a := by
    intro a
    unfold blockStateLeft
    rw [hw a, h_eq a]
  unfold algebraicEntropyLeft
  simp_rw [hw, hs]

lemma agree_left_of_rt {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (L : Matrix C C ℂ)
    (h_rt : ∀ ρ : Matrix C C ℂ, IsDensityMatrix ρ →
      ((vonNeumannEntropy (traceLeft (V * ρ * Vᴴ)) : ℝ) : ℂ) =
        (ρ * L).trace + ((algebraicEntropyRight U ρ : ℝ) : ℂ))
    (ρ₁ ρ₂ : Matrix C C ℂ) (hρ₁ : IsDensityMatrix ρ₁) (hρ₂ : IsDensityMatrix ρ₂)
    (h_eq : ∀ a : Fin N, traceLeft (diagBlock U ρ₁ a) = traceLeft (diagBlock U ρ₂ a)) :
    traceLeft (V * ρ₁ * Vᴴ) = traceLeft (V * ρ₂ * Vᴴ) := by
  let ρ_mid : Matrix C C ℂ := (1 / 2 : ℂ) • ρ₁ + (1 / 2 : ℂ) • ρ₂
  have hρ_mid : IsDensityMatrix ρ_mid := isDensityMatrix_midpoint hρ₁ hρ₂
  have h_mid_eq : ∀ a : Fin N, traceLeft (diagBlock U ρ_mid a) = traceLeft (diagBlock U ρ₁ a) := by
    intro a
    dsimp [ρ_mid]
    rw [diagBlock_midpoint, traceLeft_add, traceLeft_smul, traceLeft_smul, ← h_eq a,
      half_smul_add_half_smul]
  have h_alg_mid : algebraicEntropyRight U ρ_mid = algebraicEntropyRight U ρ₁ :=
    algebraicEntropyRight_eq_of_traceLeft_eq U h_mid_eq
  have h_alg_2 : algebraicEntropyRight U ρ₂ = algebraicEntropyRight U ρ₁ :=
    (algebraicEntropyRight_eq_of_traceLeft_eq U h_eq).symm
  have h_tr_mid : (ρ_mid * L).trace = (1 / 2 : ℂ) * (ρ₁ * L).trace + (1 / 2 : ℂ) * (ρ₂ * L).trace := by
    dsimp [ρ_mid]
    simp [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
  have h1 := h_rt ρ₁ hρ₁
  have h2 := h_rt ρ₂ hρ₂
  have hm := h_rt ρ_mid hρ_mid
  rw [h_alg_mid, h_tr_mid] at hm
  rw [h_alg_2] at h2
  have h_comb : ((vonNeumannEntropy (traceLeft (V * ρ_mid * Vᴴ)) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((vonNeumannEntropy (traceLeft (V * ρ₁ * Vᴴ)) : ℝ) : ℂ) +
      (1 / 2 : ℂ) * ((vonNeumannEntropy (traceLeft (V * ρ₂ * Vᴴ)) : ℝ) : ℂ) := by
    linear_combination hm - (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2
  have h_re := congr_arg Complex.re h_comb
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
    sub_zero] at h_re
  have h_re' : vonNeumannEntropy (traceLeft (V * ρ_mid * Vᴴ)) =
      (1 / 2 : ℝ) * vonNeumannEntropy (traceLeft (V * ρ₁ * Vᴴ)) +
      (1 / 2 : ℝ) * vonNeumannEntropy (traceLeft (V * ρ₂ * Vᴴ)) := by
    convert h_re using 2 <;> norm_num
  have h_lhs_split : traceLeft (V * ρ_mid * Vᴴ) =
      (1 / 2 : ℂ) • traceLeft (V * ρ₁ * Vᴴ) + (1 / 2 : ℂ) • traceLeft (V * ρ₂ * Vᴴ) := by
    dsimp [ρ_mid]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, traceLeft_add, traceLeft_smul, traceLeft_smul]
  rw [h_lhs_split] at h_re'
  exact vonNeumannEntropy_midpoint_eq
    (isDensityMatrix_traceLeft (isDensityMatrix_conj_isometry V hV hρ₁))
    (isDensityMatrix_traceLeft (isDensityMatrix_conj_isometry V hV hρ₂))
    h_re'

lemma agree_right_of_rt {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (L : Matrix C C ℂ)
    (h_rt : ∀ ρ : Matrix C C ℂ, IsDensityMatrix ρ →
      ((vonNeumannEntropy (traceRight (V * ρ * Vᴴ)) : ℝ) : ℂ) =
        (ρ * L).trace + ((algebraicEntropyLeft U ρ : ℝ) : ℂ))
    (ρ₁ ρ₂ : Matrix C C ℂ) (hρ₁ : IsDensityMatrix ρ₁) (hρ₂ : IsDensityMatrix ρ₂)
    (h_eq : ∀ a : Fin N, traceRight (diagBlock U ρ₁ a) = traceRight (diagBlock U ρ₂ a)) :
    traceRight (V * ρ₁ * Vᴴ) = traceRight (V * ρ₂ * Vᴴ) := by
  let ρ_mid : Matrix C C ℂ := (1 / 2 : ℂ) • ρ₁ + (1 / 2 : ℂ) • ρ₂
  have hρ_mid : IsDensityMatrix ρ_mid := isDensityMatrix_midpoint hρ₁ hρ₂
  have h_mid_eq : ∀ a : Fin N, traceRight (diagBlock U ρ_mid a) = traceRight (diagBlock U ρ₁ a) := by
    intro a
    dsimp [ρ_mid]
    rw [diagBlock_midpoint, traceRight_add, traceRight_smul, traceRight_smul, ← h_eq a,
      half_smul_add_half_smul]
  have h_alg_mid : algebraicEntropyLeft U ρ_mid = algebraicEntropyLeft U ρ₁ :=
    algebraicEntropyLeft_eq_of_traceRight_eq U h_mid_eq
  have h_alg_2 : algebraicEntropyLeft U ρ₂ = algebraicEntropyLeft U ρ₁ :=
    (algebraicEntropyLeft_eq_of_traceRight_eq U h_eq).symm
  have h_tr_mid : (ρ_mid * L).trace = (1 / 2 : ℂ) * (ρ₁ * L).trace + (1 / 2 : ℂ) * (ρ₂ * L).trace := by
    dsimp [ρ_mid]
    simp [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
  have h1 := h_rt ρ₁ hρ₁
  have h2 := h_rt ρ₂ hρ₂
  have hm := h_rt ρ_mid hρ_mid
  rw [h_alg_mid, h_tr_mid] at hm
  rw [h_alg_2] at h2
  have h_comb : ((vonNeumannEntropy (traceRight (V * ρ_mid * Vᴴ)) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((vonNeumannEntropy (traceRight (V * ρ₁ * Vᴴ)) : ℝ) : ℂ) +
      (1 / 2 : ℂ) * ((vonNeumannEntropy (traceRight (V * ρ₂ * Vᴴ)) : ℝ) : ℂ) := by
    linear_combination hm - (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2
  have h_re := congr_arg Complex.re h_comb
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
    sub_zero] at h_re
  have h_re' : vonNeumannEntropy (traceRight (V * ρ_mid * Vᴴ)) =
      (1 / 2 : ℝ) * vonNeumannEntropy (traceRight (V * ρ₁ * Vᴴ)) +
      (1 / 2 : ℝ) * vonNeumannEntropy (traceRight (V * ρ₂ * Vᴴ)) := by
    convert h_re using 2 <;> norm_num
  have h_lhs_split : traceRight (V * ρ_mid * Vᴴ) =
      (1 / 2 : ℂ) • traceRight (V * ρ₁ * Vᴴ) + (1 / 2 : ℂ) • traceRight (V * ρ₂ * Vᴴ) := by
    dsimp [ρ_mid]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, traceRight_add, traceRight_smul, traceRight_smul]
  rw [h_lhs_split] at h_re'
  exact vonNeumannEntropy_midpoint_eq
    (isDensityMatrix_traceRight (isDensityMatrix_conj_isometry V hV hρ₁))
    (isDensityMatrix_traceRight (isDensityMatrix_conj_isometry V hV hρ₂))
    h_re'

lemma conjTranspose_mul_self_transpose {m n : Type} [Fintype m] (A : Matrix m n ℂ) :
    (Aᴴ * A)ᵀ = (A.map star)ᴴ * (A.map star) := by
  ext i j
  simp [mul_apply, mul_comm]

lemma posSemidef_conjTranspose_mul_self_transpose {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) :
    ((Aᴴ * A)ᵀ).PosSemidef := by
  rw [conjTranspose_mul_self_transpose]
  exact posSemidef_conjTranspose_mul_self (A.map star)

lemma diagBlock_eq_zero_of_not_pos {C : Type} [Fintype C] {N : ℕ} {dr drb : Fin N → ℕ}
    (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ : Matrix C C ℂ) (a : Fin N)
    (h : ¬(0 < dr a ∧ 0 < drb a)) :
    diagBlock U ρ a = 0 := by
  ext ⟨i, j⟩ _
  by_cases hdr : 0 < dr a
  · have hdrb : ¬(0 < drb a) := fun hdrb => h ⟨hdr, hdrb⟩
    exact (hdrb j.pos).elim
  · exact (hdr i.pos).elim

lemma traceRight_zero {A B : Type} [Fintype B] :
    traceRight (0 : Matrix (A × B) (A × B) ℂ) = 0 := by
  ext i j; simp [traceRight]

lemma traceLeft_zero {A B : Type} [Fintype A] :
    traceLeft (0 : Matrix (A × B) (A × B) ℂ) = 0 := by
  ext i j; simp [traceLeft]

lemma isHermitian_blockDiagonal' {k : Type} [DecidableEq k] {d : k → Type}
    {X : ∀ a : k, Matrix (d a) (d a) ℂ} (hX : ∀ a : k, (X a).IsHermitian) :
    (blockDiagonal' X).IsHermitian := by
  rw [Matrix.IsHermitian, blockDiagonal'_conjTranspose]
  congr 1; funext a; exact (hX a).eq

lemma isHermitian_kronecker {m q : Type}
    {X : Matrix m m ℂ} {Y : Matrix q q ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (X ⊗ₖ Y).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_kronecker, hX.eq, hY.eq]

lemma traceRight_trace_eq_blockWeight {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    {ρ : Matrix C C ℂ} (hρ : ρ.PosSemidef) (a : Fin N) :
    (traceRight (diagBlock U ρ a)).trace = (blockWeight U ρ a : ℂ) := by
  have hpsd := psd_traceRight (psd_diagBlock U hρ a)
  have him : (traceRight (diagBlock U ρ a)).trace.im = 0 :=
    (Complex.nonneg_iff.mp hpsd.trace_nonneg).2.symm
  have hre : (traceRight (diagBlock U ρ a)).trace.re = blockWeight U ρ a := by
    rw [tr_traceRight]; rfl
  exact Complex.ext hre (by simp [him])

lemma traceLeft_trace_eq_blockWeight {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    {ρ : Matrix C C ℂ} (hρ : ρ.PosSemidef) (a : Fin N) :
    (traceLeft (diagBlock U ρ a)).trace = (blockWeight U ρ a : ℂ) := by
  have hpsd := psd_traceLeft (psd_diagBlock U hρ a)
  have him : (traceLeft (diagBlock U ρ a)).trace.im = 0 :=
    (Complex.nonneg_iff.mp hpsd.trace_nonneg).2.symm
  have hre : (traceLeft (diagBlock U ρ a)).trace.re = blockWeight U ρ a := by
    rw [tr_traceLeft]; rfl
  exact Complex.ext hre (by simp [him])

lemma jlms_of_factorization {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ)
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (m mb : Fin N → ℕ) (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWR : IsIsometry WR) (hWRb : IsIsometry WRb)
    (hχ_tr : ∀ a, 0 < dr a → 0 < drb a → (χ a * (χ a)ᴴ).trace = 1)
    (h_red : ∀ ρ : Matrix C C ℂ,
      traceRight (V * ρ * Vᴴ) =
          WR * blockDiagonal' (fun a => traceRight (diagBlock U ρ a) ⊗ₖ (χ a * (χ a)ᴴ)) * WRᴴ ∧
      traceLeft (V * ρ * Vᴴ) =
          WRb * blockDiagonal' (fun a => ((χ a)ᴴ * χ a)ᵀ ⊗ₖ traceLeft (diagBlock U ρ a)) * WRbᴴ)
    (ρ σ : Matrix C C ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    relativeEntropy (traceRight (V * ρ * Vᴴ)) (traceRight (V * σ * Vᴴ)) =
        algebraicRelEntropyLeft U ρ σ ∧
    relativeEntropy (traceLeft (V * ρ * Vᴴ)) (traceLeft (V * σ * Vᴴ)) =
        algebraicRelEntropyRight U ρ σ := by
  have h_red_ρ := h_red ρ
  have h_red_σ := h_red σ
  have h_psd_R_ρ : ∀ a, (traceRight (diagBlock U ρ a)).PosSemidef :=
    fun a => psd_traceRight (psd_diagBlock U hρ.1 a)
  have h_psd_R_σ : ∀ a, (traceRight (diagBlock U σ a)).PosSemidef :=
    fun a => psd_traceRight (psd_diagBlock U hσ.1 a)
  have h_psd_L_ρ : ∀ a, (traceLeft (diagBlock U ρ a)).PosSemidef :=
    fun a => psd_traceLeft (psd_diagBlock U hρ.1 a)
  have h_psd_L_σ : ∀ a, (traceLeft (diagBlock U σ a)).PosSemidef :=
    fun a => psd_traceLeft (psd_diagBlock U hσ.1 a)
  have h_psd_χR : ∀ a, (χ a * (χ a)ᴴ).PosSemidef :=
    fun a => posSemidef_self_mul_conjTranspose (χ a)
  have h_psd_χL : ∀ a, (((χ a)ᴴ * χ a)ᵀ).PosSemidef :=
    fun a => posSemidef_conjTranspose_mul_self_transpose (χ a)
  constructor
  · rw [h_red_ρ.1, h_red_σ.1]
    have hH_blk_ρ : ∀ a, (traceRight (diagBlock U ρ a) ⊗ₖ (χ a * (χ a)ᴴ)).IsHermitian :=
      fun a => isHermitian_kronecker (h_psd_R_ρ a).isHermitian (h_psd_χR a).isHermitian
    have hH_blk_σ : ∀ a, (traceRight (diagBlock U σ a) ⊗ₖ (χ a * (χ a)ᴴ)).IsHermitian :=
      fun a => isHermitian_kronecker (h_psd_R_σ a).isHermitian (h_psd_χR a).isHermitian
    rw [relEnt_isom WR hWR _ _ (isHermitian_blockDiagonal' hH_blk_ρ) (isHermitian_blockDiagonal' hH_blk_σ)]
    rw [relEnt_blockDiag _ _ hH_blk_ρ hH_blk_σ]
    unfold algebraicRelEntropyLeft
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h_or_R : traceRight (diagBlock U ρ a) = 0 ∨ (χ a * (χ a)ᴴ).trace = 1 := by
      by_cases h_pos : 0 < dr a ∧ 0 < drb a
      · exact Or.inr (hχ_tr a h_pos.1 h_pos.2)
      · left; rw [diagBlock_eq_zero_of_not_pos U ρ a h_pos, traceRight_zero]
    rw [relEnt_kron_right _ _ _ (h_psd_R_ρ a).isHermitian (h_psd_R_σ a).isHermitian
      (h_psd_χR a) h_or_R]
    exact relEnt_smul_split _ _ (h_psd_R_ρ a) (h_psd_R_σ a)
      (blockWeight U ρ a) (blockWeight U σ a)
      (traceRight_trace_eq_blockWeight U hρ.1 a) (traceRight_trace_eq_blockWeight U hσ.1 a)
  · rw [h_red_ρ.2, h_red_σ.2]
    have hH_blk_ρ : ∀ a, (((χ a)ᴴ * χ a)ᵀ ⊗ₖ traceLeft (diagBlock U ρ a)).IsHermitian :=
      fun a => isHermitian_kronecker (h_psd_χL a).isHermitian (h_psd_L_ρ a).isHermitian
    have hH_blk_σ : ∀ a, (((χ a)ᴴ * χ a)ᵀ ⊗ₖ traceLeft (diagBlock U σ a)).IsHermitian :=
      fun a => isHermitian_kronecker (h_psd_χL a).isHermitian (h_psd_L_σ a).isHermitian
    rw [relEnt_isom WRb hWRb _ _ (isHermitian_blockDiagonal' hH_blk_ρ) (isHermitian_blockDiagonal' hH_blk_σ)]
    rw [relEnt_blockDiag _ _ hH_blk_ρ hH_blk_σ]
    unfold algebraicRelEntropyRight
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h_or_L : traceLeft (diagBlock U ρ a) = 0 ∨ (((χ a)ᴴ * χ a)ᵀ).trace = 1 := by
      by_cases h_pos : 0 < dr a ∧ 0 < drb a
      · right; rw [Matrix.trace_transpose, Matrix.trace_mul_comm, hχ_tr a h_pos.1 h_pos.2]
      · left; rw [diagBlock_eq_zero_of_not_pos U ρ a h_pos, traceLeft_zero]
    rw [relEnt_kron_left _ _ _ (h_psd_χL a) (h_psd_L_ρ a).isHermitian (h_psd_L_σ a).isHermitian
      h_or_L]
    exact relEnt_smul_split _ _ (h_psd_L_ρ a) (h_psd_L_σ a)
      (blockWeight U ρ a) (blockWeight U σ a)
      (traceLeft_trace_eq_blockWeight U hρ.1 a) (traceLeft_trace_eq_blockWeight U hσ.1 a)


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


end HarlowTASI_RtImpJlms

open HarlowTASI HarlowTASI_RtImpJlms in
theorem solution {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U)
    (h : ∃ L ∈ M ⊓ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
        ∀ ρ : Matrix C C ℂ, IsDensityMatrix ρ →
          ((vonNeumannEntropy (traceRight (V * ρ * Vᴴ)) : ℝ) : ℂ) =
              (ρ * L).trace + ((algebraicEntropyLeft U ρ : ℝ) : ℂ) ∧
          ((vonNeumannEntropy (traceLeft (V * ρ * Vᴴ)) : ℝ) : ℂ) =
              (ρ * L).trace + ((algebraicEntropyRight U ρ : ℝ) : ℂ)) :
    ∀ ρ σ : Matrix C C ℂ, IsDensityMatrix ρ → IsDensityMatrix σ →
        relativeEntropy (traceRight (V * ρ * Vᴴ)) (traceRight (V * σ * Vᴴ)) =
            algebraicRelEntropyLeft U ρ σ ∧
        relativeEntropy (traceLeft (V * ρ * Vᴴ)) (traceLeft (V * σ * Vᴴ)) =
            algebraicRelEntropyRight U ρ σ := by
  rcases h with ⟨L, _, hL_rt⟩
  have h_agree_left : ∀ ρ₁ ρ₂ : Matrix C C ℂ,
      IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
      (∀ a : Fin N, traceLeft (diagBlock U ρ₁ a) = traceLeft (diagBlock U ρ₂ a)) →
      traceLeft (V * ρ₁ * Vᴴ) = traceLeft (V * ρ₂ * Vᴴ) :=
    agree_left_of_rt V hV U L (fun ρ hρ => (hL_rt ρ hρ).2)
  have h_agree_right : ∀ ρ₁ ρ₂ : Matrix C C ℂ,
      IsDensityMatrix ρ₁ → IsDensityMatrix ρ₂ →
      (∀ a : Fin N, traceRight (diagBlock U ρ₁ a) = traceRight (diagBlock U ρ₂ a)) →
      traceRight (V * ρ₁ * Vᴴ) = traceRight (V * ρ₂ * Vᴴ) :=
    agree_right_of_rt V hV U L (fun ρ hρ => (hL_rt ρ hρ).1)
  have hR_same := sliceR_same_of_agree_left U hU V h_agree_left
  have hR_orth := sliceR_orth_of_agree_left U hU V h_agree_left
  have hRb_same := sliceRb_same_of_agree_right U hU V h_agree_right
  have hRb_orth := sliceRb_orth_of_agree_right U hU V h_agree_right
  have h_duality : ∀ O ∈ M, ∀ O' ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
      ∃ (OR : Matrix R R ℂ) (ORb : Matrix Rb Rb ℂ),
        (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
        (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ ∧
        ((1 : Matrix R R ℂ) ⊗ₖ ORb) * V = V * O' ∧
        ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * V = V * O'ᴴ := by
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
  rcases HarlowTASI.ewr_duality_imp_factorization V hV M N dr drb U hU hMU h_duality with
    ⟨m, mb, χ, WR, WRb, hWR, hWRb, hχ_tr, hVU⟩
  have h_red := HarlowTASI.factorizedCode_reducedStates V N dr drb U hU m mb χ WR WRb hWR hWRb hVU
  exact jlms_of_factorization V N dr drb U m mb χ WR WRb hWR hWRb hχ_tr h_red

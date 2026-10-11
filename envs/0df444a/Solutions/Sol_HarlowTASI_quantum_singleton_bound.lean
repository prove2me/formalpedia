-- Prove2me | solution 1 for HarlowTASI.quantum_singleton_bound
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T13:59:37.946995+00:00
-- url     : https://prove2.me/submissions/1795abb3-3293-4f61-ba5e-af6d986e0e4f

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Finset ComplexConjugate Matrix
open scoped Kronecker

namespace HarlowTASI

/-- merge two partial assignments into an assignment on `{i // p i}` according to `q`. -/
def qsbMrg {ι β : Type} {p q P Q : ι → Prop} [DecidablePred q]
    (hP : ∀ i, p i → q i → P i) (hQ : ∀ i, p i → ¬ q i → Q i)
    (x : {i // P i} → β) (y : {i // Q i} → β) : {i // p i} → β :=
  fun j => if h : q j.1 then x ⟨j.1, hP _ j.2 h⟩ else y ⟨j.1, hQ _ j.2 h⟩

theorem qsb_sum_mrg {ι β : Type} {p q P Q : ι → Prop} [DecidablePred q]
    [Fintype {i // p i}] [Fintype {i // P i}] [Fintype {i // Q i}] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (hP : ∀ i, p i → q i → P i) (hQ : ∀ i, p i → ¬ q i → Q i)
    (hP' : ∀ i, P i → p i ∧ q i) (hQ' : ∀ i, Q i → p i ∧ ¬ q i)
    {M : Type} [AddCommMonoid M] (G : ({i // p i} → β) → M) :
    ∑ r, G r = ∑ x, ∑ y, G (qsbMrg hP hQ x y) := by
  let e : (({i // P i} → β) × ({i // Q i} → β)) ≃ ({i // p i} → β) :=
    { toFun := fun xy => qsbMrg hP hQ xy.1 xy.2
      invFun := fun r => (fun i => r ⟨i.1, (hP' _ i.2).1⟩, fun i => r ⟨i.1, (hQ' _ i.2).1⟩)
      left_inv := by
        rintro ⟨x, y⟩
        ext i
        · simp [qsbMrg, (hP' _ i.2).2]
        · simp [qsbMrg, (hQ' _ i.2).2]
      right_inv := by
        intro r
        funext j
        by_cases h : q j.1 <;> simp [qsbMrg, h] }
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm


theorem qsb_frob {P Q : Type} [Fintype P] [Fintype Q] (M : P → Q → ℂ) :
    ∑ q, ∑ q', Complex.normSq (∑ p, M p q * conj (M p q')) =
      ∑ p, ∑ p', Complex.normSq (∑ q, M p q * conj (M p' q)) := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
  calc _ = ∑ q, ∑ p, ∑ q', ∑ p', M p q * conj (M p q') * (conj (M p' q) * M p' q') := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, ∑ q', ∑ p', M p q * conj (M p q') * (conj (M p' q) * M p' q') := Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ p', ∑ q', M p q * conj (M p q') * (conj (M p' q) * M p' q') := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          exact Finset.sum_comm
    _ = ∑ p, ∑ p', ∑ q, ∑ q', M p q * conj (M p q') * (conj (M p' q) * M p' q') := by
          refine Finset.sum_congr rfl fun p _ => ?_
          exact Finset.sum_comm
    _ = _ := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ =>
            Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
          ring

theorem qsb_half {C α1 α2 α3 : Type} [Fintype C] [Fintype α1] [Fintype α2] [Fintype α3]
    [DecidableEq C] (T : C → α1 → α2 → α3 → ℂ) (c1 : α1 → α1 → ℂ) (c2 : α2 → α2 → ℂ)
    (E1 : ∀ s t a b, ∑ a2, ∑ a3, conj (T s a a2 a3) * T t b a2 a3 = if s = t then c1 a b else 0)
    (E2 : ∀ s t a b, ∑ a1, ∑ a3, conj (T s a1 a a3) * T t a1 b a3 = if s = t then c2 a b else 0) :
    (Fintype.card C : ℝ) * ∑ a, ∑ b, Complex.normSq (c2 a b) ≤
      (Fintype.card α3 : ℝ) * ∑ a, ∑ b, Complex.normSq (c1 a b) := by
  set D : ℝ := (Fintype.card C : ℝ)
  set N : ℝ := (Fintype.card α3 : ℝ)
  -- the matrix M_{(s,a1),(a2,a3)}
  let M : C × α1 → α2 × α3 → ℂ := fun p q => T p.1 p.2 q.1 q.2
  let ρ : α2 × α3 → α2 × α3 → ℂ := fun q q' => ∑ p, M p q * conj (M p q')
  -- Step A
  have hA : ∑ q, ∑ q', Complex.normSq (ρ q q') = D * ∑ a, ∑ b, Complex.normSq (c1 a b) := by
    rw [qsb_frob M]
    have : ∀ p p' : C × α1, ∑ q, M p q * conj (M p' q) =
        conj (if p.1 = p'.1 then c1 p.2 p'.2 else 0) := by
      intro p p'
      rw [← E1, Fintype.sum_prod_type]
      simp only [M, map_sum, map_mul, Complex.conj_conj]
    simp only [this, Fintype.sum_prod_type, Complex.normSq_conj]
    have h2 : ∀ s : C, ∀ a : α1, (∑ t : C, ∑ b : α1,
        Complex.normSq (if s = t then c1 a b else 0)) = ∑ b, Complex.normSq (c1 a b) := by
      intro s a
      rw [Finset.sum_eq_single s (by intro t _ ht; simp [Ne.symm ht]) (by simp)]
      simp
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, D]
  -- Step B
  have hB : ∀ a b, ∑ a3, ρ (a, a3) (b, a3) = D * c2 b a := by
    intro a b
    simp only [ρ, M, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have : ∀ s : C, ∑ a3, ∑ a1, T s a1 a a3 * conj (T s a1 b a3) = c2 b a := by
      intro s
      rw [Finset.sum_comm]
      have := E2 s s b a
      simp only [if_true] at this
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, D]
    push_cast; ring
  -- Step C
  have hC : ∀ a b, Complex.normSq (∑ a3, ρ (a, a3) (b, a3)) ≤
      N * ∑ a3, ∑ b3, Complex.normSq (ρ (a, a3) (b, b3)) := by
    intro a b
    have h1 : Complex.normSq (∑ a3, ρ (a, a3) (b, a3)) ≤ (∑ a3, ‖ρ (a, a3) (b, a3)‖) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      gcongr
      exact norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset α3))
      (f := fun a3 => ‖ρ (a, a3) (b, a3)‖)
    have h3 : ∀ a3, ‖ρ (a, a3) (b, a3)‖ ^ 2 ≤ ∑ b3, Complex.normSq (ρ (a, a3) (b, b3)) := by
      intro a3
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (f := fun b3 => Complex.normSq (ρ (a, a3) (b, b3)))
        (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a3)
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ N * ∑ a3, ∑ b3, Complex.normSq (ρ (a, a3) (b, b3)) := by
        simp only [Finset.card_univ, N]
        gcongr with a3 _
        exact h3 a3
  have hK1 : 0 ≤ ∑ a, ∑ b, Complex.normSq (c1 a b) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have key : D * (D * ∑ a, ∑ b, Complex.normSq (c2 a b)) ≤
      D * (N * ∑ a, ∑ b, Complex.normSq (c1 a b)) := by
    have e1 : D * (D * ∑ a, ∑ b, Complex.normSq (c2 a b)) =
        ∑ a, ∑ b, Complex.normSq (∑ a3, ρ (a, a3) (b, a3)) := by
      simp only [hB, Complex.normSq_mul, Complex.normSq_ofReal]
      rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => ?_
      ring
    have e2 : ∑ a, ∑ b, (N * ∑ a3, ∑ b3, Complex.normSq (ρ (a, a3) (b, b3))) =
        N * (D * ∑ a, ∑ b, Complex.normSq (c1 a b)) := by
      rw [← hA, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      simp only [Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [e1]
    calc _ ≤ ∑ a, ∑ b, (N * ∑ a3, ∑ b3, Complex.normSq (ρ (a, a3) (b, b3))) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hC a b
      _ = _ := by rw [e2]; ring
  rcases hD.lt_or_eq with hD' | hD'
  · exact le_of_mul_le_mul_left key hD'
  · rw [← hD']; simp only [zero_mul]; positivity

theorem qsb_abstract {C α1 α2 α3 : Type} [Fintype C] [Fintype α1] [Fintype α2] [Fintype α3]
    [DecidableEq C] (T : C → α1 → α2 → α3 → ℂ) (c1 : α1 → α1 → ℂ) (c2 : α2 → α2 → ℂ)
    (E1 : ∀ s t a b, ∑ a2, ∑ a3, conj (T s a a2 a3) * T t b a2 a3 = if s = t then c1 a b else 0)
    (E2 : ∀ s t a b, ∑ a1, ∑ a3, conj (T s a1 a a3) * T t a1 b a3 = if s = t then c2 a b else 0)
    (hT : ∃ s a1 a2 a3, T s a1 a2 a3 ≠ 0) :
    Fintype.card C ≤ Fintype.card α3 := by
  have h1 := qsb_half T c1 c2 E1 E2
  have h2 := qsb_half (fun s x y z => T s y x z) c2 c1 E2 E1
  obtain ⟨s, a1, a2, a3, hne⟩ := hT
  have hpos : 0 < Complex.normSq (T s a1 a2 a3) := Complex.normSq_pos.2 hne
  have hc1 : c1 a1 a1 = ((∑ x, ∑ y, Complex.normSq (T s a1 x y) : ℝ) : ℂ) := by
    have := E1 s s a1 a1
    rw [if_pos rfl] at this
    rw [← this]; push_cast
    simp only [Complex.normSq_eq_conj_mul_self]
  have hc2 : c2 a2 a2 = ((∑ x, ∑ y, Complex.normSq (T s x a2 y) : ℝ) : ℂ) := by
    have := E2 s s a2 a2
    rw [if_pos rfl] at this
    rw [← this]; push_cast
    simp only [Complex.normSq_eq_conj_mul_self]
  have hr1 : 0 < ∑ x, ∑ y, Complex.normSq (T s a1 x y) :=
    lt_of_lt_of_le hpos (le_trans
      (Finset.single_le_sum (f := fun y => Complex.normSq (T s a1 a2 y))
        (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a3))
      (Finset.single_le_sum (f := fun x => ∑ y, Complex.normSq (T s a1 x y))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a2)))
  have hr2 : 0 < ∑ x, ∑ y, Complex.normSq (T s x a2 y) :=
    lt_of_lt_of_le hpos (le_trans
      (Finset.single_le_sum (f := fun y => Complex.normSq (T s a1 a2 y))
        (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a3))
      (Finset.single_le_sum (f := fun x => ∑ y, Complex.normSq (T s x a2 y))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a1)))
  have K1 : 0 < ∑ a, ∑ b, Complex.normSq (c1 a b) := by
    have : 0 < Complex.normSq (c1 a1 a1) := by
      rw [hc1, Complex.normSq_ofReal]; positivity
    exact lt_of_lt_of_le this (le_trans
      (Finset.single_le_sum (f := fun b => Complex.normSq (c1 a1 b))
        (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a1))
      (Finset.single_le_sum (f := fun a => ∑ b, Complex.normSq (c1 a b))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a1)))
  have K2 : 0 < ∑ a, ∑ b, Complex.normSq (c2 a b) := by
    have : 0 < Complex.normSq (c2 a2 a2) := by
      rw [hc2, Complex.normSq_ofReal]; positivity
    exact lt_of_lt_of_le this (le_trans
      (Finset.single_le_sum (f := fun b => Complex.normSq (c2 a2 b))
        (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a2))
      (Finset.single_le_sum (f := fun a => ∑ b, Complex.normSq (c2 a b))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a2)))
  have : (Fintype.card C : ℝ) ≤ Fintype.card α3 := by
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_right h K1, mul_lt_mul_of_pos_right h K2]
  exact_mod_cast this

theorem qsb_erasure {n d : ℕ} {C : Type} [Fintype C] [DecidableEq C]
    (V : Matrix (Fin n → Fin d) C ℂ) (B : Finset (Fin n)) (hB : AccessibleFrom V B) :
    ∃ c : ({i // i ∉ B} → Fin d) → ({i // i ∉ B} → Fin d) → ℂ, ∀ s t a b,
      ∑ r, conj (splitAt B V (r, a) s) * splitAt B V (r, b) t = if s = t then c a b else 0 := by
  have : ∀ a b : {i // i ∉ B} → Fin d, ∃ c : ℂ, ∀ s t,
      ∑ r, conj (splitAt B V (r, a) s) * splitAt B V (r, b) t = if s = t then c else 0 := by
    intro a b
    set W := splitAt B V
    let X : Matrix (({i // i ∈ B} → Fin d) × ({i // i ∉ B} → Fin d))
        (({i // i ∈ B} → Fin d) × ({i // i ∉ B} → Fin d)) ℂ :=
      (1 : Matrix ({i // i ∈ B} → Fin d) ({i // i ∈ B} → Fin d) ℂ) ⊗ₖ Matrix.single a b 1
    let K : Matrix C C ℂ := Wᴴ * X * W
    have hcomm : ∀ O : Matrix C C ℂ, K * O = O * K := by
      intro O
      obtain ⟨OA, h1, h2⟩ := hB O
      let Y : Matrix (({i // i ∈ B} → Fin d) × ({i // i ∉ B} → Fin d))
          (({i // i ∈ B} → Fin d) × ({i // i ∉ B} → Fin d)) ℂ :=
        OA ⊗ₖ (1 : Matrix ({i // i ∉ B} → Fin d) ({i // i ∉ B} → Fin d) ℂ)
      have h1' : Y * W = W * O := h1
      have hX : X * Y = Y * X := by
        simp only [X, Y, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
      have hW' : Wᴴ * Y = O * Wᴴ := by
        have := congrArg conjTranspose h2
        simpa [Y, W, conjTranspose_mul, conjTranspose_kronecker] using this
      calc K * O = Wᴴ * X * (W * O) := by simp only [K, Matrix.mul_assoc]
        _ = Wᴴ * X * (Y * W) := by rw [h1']
        _ = Wᴴ * (X * Y) * W := by simp only [Matrix.mul_assoc]
        _ = (Wᴴ * Y) * X * W := by rw [hX]; simp only [Matrix.mul_assoc]
        _ = O * K := by rw [hW']; simp only [K, Matrix.mul_assoc]
    obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_single (M := K)
      (fun i j _ => (hcomm (Matrix.single i j 1)).symm)
    refine ⟨c, fun s t => ?_⟩
    have hst := congrFun (congrFun hc s) t
    rw [scalar_apply, diagonal_apply] at hst
    rw [hst]
    simp only [K, X, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.single_apply, conjTranspose_apply, Fintype.sum_prod_type]
    simp [ite_and, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  choose c hc using this
  exact ⟨c, fun s t a b => hc a b s t⟩


theorem qsb_main {n d k : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k)
    (V : Matrix (Fin n → Fin d) (Fin k → Fin d) ℂ) (hV : IsIsometry V)
    (hsymm : ∀ A B : Finset (Fin n), A.card = B.card →
      (AccessibleFrom V A ↔ AccessibleFrom V B))
    (A : Finset (Fin n)) (hA : AccessibleFrom V A) :
    n + k ≤ 2 * A.card := by
  set m := A.card with hm
  have hmn : m ≤ n := by simpa using A.card_le_univ
  let B1 : Finset (Fin n) := univ.filter (fun i => (i : ℕ) < m)
  let B2 : Finset (Fin n) := univ.filter (fun i => ¬ (i : ℕ) < n - m)
  have hB1c : B1.card = m := by simp [B1, Fin.card_filter_val_lt, hmn]
  have hB2c : B2.card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun i : Fin n => (i : ℕ) < n - m)
    simp only [Fin.card_filter_val_lt, card_univ, Fintype.card_fin] at this
    simp only [B2]; omega
  have hacc1 : AccessibleFrom V B1 := (hsymm A B1 hB1c.symm).1 hA
  have hacc2 : AccessibleFrom V B2 := (hsymm A B2 hB2c.symm).1 hA
  obtain ⟨c1, hc1⟩ := qsb_erasure V B2 hacc2
  obtain ⟨c2, hc2⟩ := qsb_erasure V B1 hacc1
  let T : (Fin k → Fin d) → (({i // i ∉ B2 ∧ i ∈ B1} → Fin d) × ({i // i ∉ B2 ∧ i ∉ B1} → Fin d)) →
      ({i // i ∈ B2 ∧ i ∉ B1} → Fin d) → ({i // i ∈ B2 ∧ i ∈ B1} → Fin d) → ℂ :=
    fun s p a2 a3 => V (fun i => if h2 : i ∈ B2 then (if h1 : i ∈ B1 then a3 ⟨i, h2, h1⟩
      else a2 ⟨i, h2, h1⟩) else (if h1 : i ∈ B1 then p.1 ⟨i, h2, h1⟩ else p.2 ⟨i, h2, h1⟩)) s
  -- merges
  let mR2 := @qsbMrg (Fin n) (Fin d) (fun i => i ∈ B2) (fun i => i ∈ B1)
    (fun i => i ∈ B2 ∧ i ∈ B1) (fun i => i ∈ B2 ∧ i ∉ B1) _
    (fun _ h2 h1 => ⟨h2, h1⟩) (fun _ h2 h1 => ⟨h2, h1⟩)
  let mC2 := @qsbMrg (Fin n) (Fin d) (fun i => i ∉ B2) (fun i => i ∈ B1)
    (fun i => i ∉ B2 ∧ i ∈ B1) (fun i => i ∉ B2 ∧ i ∉ B1) _
    (fun _ h2 h1 => ⟨h2, h1⟩) (fun _ h2 h1 => ⟨h2, h1⟩)
  let mR1 := @qsbMrg (Fin n) (Fin d) (fun i => i ∈ B1) (fun i => i ∈ B2)
    (fun i => i ∈ B2 ∧ i ∈ B1) (fun i => i ∉ B2 ∧ i ∈ B1) _
    (fun _ h1 h2 => ⟨h2, h1⟩) (fun _ h1 h2 => ⟨h2, h1⟩)
  let mC1 := @qsbMrg (Fin n) (Fin d) (fun i => i ∉ B1) (fun i => i ∈ B2)
    (fun i => i ∈ B2 ∧ i ∉ B1) (fun i => i ∉ B2 ∧ i ∉ B1) _
    (fun _ h1 h2 => ⟨h2, h1⟩) (fun _ h1 h2 => ⟨h2, h1⟩)
  have g2 : ∀ s p a2 a3, splitAt B2 V (mR2 a3 a2, mC2 p.1 p.2) s = T s p a2 a3 := by
    intro s p a2 a3
    simp only [splitAt, submatrix_apply, T, mR2, mC2,
      qsbMrg, id]
    congr 1
  have g1 : ∀ s p a2 a3, splitAt B1 V (mR1 a3 p.1, mC1 a2 p.2) s = T s p a2 a3 := by
    intro s p a2 a3
    simp only [splitAt, submatrix_apply, T, mR1, mC1,
      qsbMrg, id]
    congr 1; funext i
    by_cases h1 : i ∈ B1 <;> by_cases h2 : i ∈ B2 <;> simp [h1, h2, qsbMrg, Equiv.piEquivPiSubtypeProd]
  have g1' : ∀ s p1 u a2 a3, splitAt B1 V (mR1 a3 p1, mC1 a2 u) s = T s (p1, u) a2 a3 :=
    fun s p1 u a2 a3 => g1 s (p1, u) a2 a3
  have E1 : ∀ s t (a b : ({i // i ∉ B2 ∧ i ∈ B1} → Fin d) × ({i // i ∉ B2 ∧ i ∉ B1} → Fin d)),
      ∑ a2, ∑ a3, conj (T s a a2 a3) * T t b a2 a3 =
        if s = t then c1 (mC2 a.1 a.2) (mC2 b.1 b.2) else 0 := by
    intro s t a b
    rw [← hc1 s t (mC2 a.1 a.2) (mC2 b.1 b.2)]
    refine Eq.symm ((qsb_sum_mrg (p := fun i => i ∈ B2) (q := fun i => i ∈ B1)
      (P := fun i => i ∈ B2 ∧ i ∈ B1) (Q := fun i => i ∈ B2 ∧ i ∉ B1)
      (fun _ h2 h1 => ⟨h2, h1⟩) (fun _ h2 h1 => ⟨h2, h1⟩) (fun _ h => h) (fun _ h => h) _).trans ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    exact congrArg₂ (fun x y => conj x * y) (g2 s a y x) (g2 t b y x)
  have E2 : ∀ s t (a b : {i // i ∈ B2 ∧ i ∉ B1} → Fin d),
      ∑ a1, ∑ a3, conj (T s a1 a a3) * T t a1 b a3 =
        if s = t then ∑ u, c2 (mC1 a u) (mC1 b u) else 0 := by
    intro s t a b
    have key : ∀ u, ∑ y, ∑ x, conj (T s (y, u) a x) * T t (y, u) b x =
        if s = t then c2 (mC1 a u) (mC1 b u) else 0 := by
      intro u
      rw [← hc2 s t (mC1 a u) (mC1 b u)]
      refine Eq.symm ((qsb_sum_mrg (p := fun i => i ∈ B1) (q := fun i => i ∈ B2)
        (P := fun i => i ∈ B2 ∧ i ∈ B1) (Q := fun i => i ∉ B2 ∧ i ∈ B1)
        (fun _ h1 h2 => ⟨h2, h1⟩) (fun _ h1 h2 => ⟨h2, h1⟩) (fun _ h => ⟨h.2, h.1⟩)
        (fun _ h => ⟨h.2, h.1⟩) _).trans ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      exact congrArg₂ (fun x y => conj x * y) (g1' s y u a x) (g1' t y u b x)
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [key]
    by_cases h : s = t <;> simp [h]
  have hT : ∃ s a1 a2 a3, T s a1 a2 a3 ≠ 0 := by
    let s0 : Fin k → Fin d := fun _ => ⟨0, by omega⟩
    obtain ⟨x, hx⟩ : ∃ x, V x s0 ≠ 0 := by
      by_contra h
      push Not at h
      have := congrFun (congrFun hV s0) s0
      simp [mul_apply, h] at this
    refine ⟨s0, (fun j => x j.1, fun j => x j.1), fun j => x j.1, fun j => x j.1, ?_⟩
    show V _ s0 ≠ 0
    convert hx using 2
    funext i
    split_ifs <;> rfl
  have hcard := qsb_abstract T _ _ E1 E2 hT
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype] at hcard
  have hI : (univ.filter fun i => i ∈ B2 ∧ i ∈ B1) = B2 ∩ B1 := by ext; simp
  rw [hI] at hcard
  have hle := (Nat.pow_le_pow_iff_right (by omega : 1 < d)).1 hcard
  have hu := Finset.card_union_add_card_inter B2 B1
  have hun : (B2 ∪ B1).card = n ∨ (B2 ∩ B1).card = 0 := by
    by_cases h : n < 2 * m
    · left
      rw [show B2 ∪ B1 = univ by ext i; have := i.isLt; simp [B1, B2]; omega]
      simp
    · right
      rw [Finset.card_eq_zero]
      ext i
      simp [B1, B2]
      omega
  omega

end HarlowTASI

open HarlowTASI

theorem solution {n d k : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k)
    (V : Matrix (Fin n → Fin d) (Fin k → Fin d) ℂ) (hV : IsIsometry V)
    (hsymm : ∀ A B : Finset (Fin n), A.card = B.card →
      (AccessibleFrom V A ↔ AccessibleFrom V B))
    (A : Finset (Fin n)) (hA : AccessibleFrom V A) :
    n + k ≤ 2 * A.card :=
  qsb_main hd hk V hV hsymm A hA

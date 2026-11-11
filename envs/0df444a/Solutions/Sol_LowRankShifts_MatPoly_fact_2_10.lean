-- Prove2me | solution 1 for LowRankShifts.MatPoly.fact_2_10
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:29:14.869748+00:00
-- url     : https://prove2.me/submissions/07a52d9e-53bc-4009-b16f-c85579548cd7

import Mathlib

set_option autoImplicit false

open MvPolynomial in
theorem cube_aux {F : Type*} [Field F] (n : ℕ) (g : MvPolynomial (Fin n) F)
    (hg : g.totalDegree < n) :
    ∑ S : Finset (Fin n), (-1 : F) ^ S.card *
      MvPolynomial.eval (fun i => if i ∈ S then (1 : F) else 0) g = 0 := by
  classical
  have h1 : ∀ S : Finset (Fin n), (-1 : F) ^ S.card *
      MvPolynomial.eval (fun i => if i ∈ S then (1 : F) else 0) g =
      ∑ m ∈ g.support, (-1 : F) ^ S.card * (coeff m g *
        m.prod fun j e => (if j ∈ S then (1 : F) else 0) ^ e) := by
    intro S
    conv_lhs => rw [g.as_sum]
    rw [map_sum, Finset.mul_sum]
    simp only [eval_monomial]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨i, hi⟩ : ∃ i, m i = 0 := by
    by_contra h
    push Not at h
    have h2 := le_totalDegree hm
    have h3 : n ≤ m.sum fun _ e => e := by
      have hs : m.support = Finset.univ := by
        ext j; simp [Finsupp.mem_support_iff, h j]
      rw [Finsupp.sum, hs]
      calc n = ∑ _j : Fin n, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j _ => Nat.one_le_iff_ne_zero.mpr (h j))
    omega
  let φ : Finset (Fin n) → Finset (Fin n) := fun S => if i ∈ S then S.erase i else insert i S
  have hprod : ∀ S : Finset (Fin n), (m.prod fun j e => (if j ∈ φ S then (1 : F) else 0) ^ e) =
      m.prod fun j e => (if j ∈ S then (1 : F) else 0) ^ e := by
    intro S
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hj) hi
    by_cases hj' : j ∈ S <;> by_cases hi' : i ∈ S <;> simp [φ, hj', hi', hji]
  apply Finset.sum_involution (fun S _ => φ S)
  · intro S _
    rw [hprod]
    simp only [φ]
    split_ifs with h
    · rw [Finset.card_erase_of_mem h]
      have : 0 < S.card := Finset.card_pos.mpr ⟨i, h⟩
      obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by omega⟩
      rw [hk]; simp [pow_succ]
    · rw [Finset.card_insert_of_notMem h]
      rw [pow_succ]; ring
  · intro S _ _
    simp only [φ]
    split_ifs with h
    · intro e
      have : i ∈ S.erase i := by rw [e]; exact h
      simp at this
    · intro e
      have : i ∈ S := by rw [← e]; exact Finset.mem_insert_self _ _
      exact h this
  · intro S _; exact Finset.mem_univ _
  · intro S _
    by_cases h : i ∈ S
    · simp only [φ, h, if_true, Finset.notMem_erase, if_false]
      exact Finset.insert_erase h
    · simp only [φ, h, if_false, Finset.mem_insert_self, if_true]
      exact Finset.erase_insert h

open MvPolynomial in
theorem solution {F : Type*} [Field F] {ℓ d : ℕ} (f : MvPolynomial (Fin ℓ) F)
    (hf : f.totalDegree ≤ d) (x : Fin ℓ → F) (a : Fin (d + 1) → Fin ℓ → F) :
    ∑ S : Finset (Fin (d + 1)),
      (-1 : F) ^ S.card * MvPolynomial.eval (x + ∑ i ∈ S, a i) f = 0 := by
  classical
  let ψ : Fin ℓ → MvPolynomial (Fin (d + 1)) F :=
    fun j => C (x j) + ∑ i : Fin (d + 1), C (a i j) * X i
  have hψ : ∀ j, (ψ j).totalDegree ≤ 1 := by
    intro j
    refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine totalDegree_finsetSum_le (fun i _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C]
    simp [totalDegree_X]
  have hdeg : (bind₁ ψ f).totalDegree < d + 1 := by
    have : (bind₁ ψ f).totalDegree ≤ d := by
      conv_lhs => rw [f.as_sum]
      rw [map_sum]
      refine totalDegree_finsetSum_le (fun m hm => ?_)
      rw [bind₁_monomial]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_finsetProd _ _).trans ?_
      calc ∑ j ∈ m.support, (ψ j ^ m j).totalDegree
          ≤ ∑ j ∈ m.support, m j * 1 :=
            Finset.sum_le_sum (fun j _ => (totalDegree_pow _ _).trans
              (Nat.mul_le_mul_left _ (hψ j)))
        _ = m.sum fun _ e => e := by simp [Finsupp.sum]
        _ ≤ f.totalDegree := le_totalDegree hm
        _ ≤ d := hf
    omega
  have key := cube_aux (d + 1) (bind₁ ψ f) hdeg
  rw [← key]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  have := eval₂Hom_bind₁ (RingHom.id F) (fun i : Fin (d + 1) => if i ∈ S then (1 : F) else 0)
    ψ f
  have e2 : (fun j => (eval₂Hom (RingHom.id F) (fun i : Fin (d + 1) => if i ∈ S then (1 : F) else 0))
      (ψ j)) = x + ∑ i ∈ S, a i := by
    ext j
    simp [ψ, Finset.sum_apply, Pi.add_apply, Finset.sum_ite_mem, ite_mul]
  rw [e2] at this
  exact this.symm

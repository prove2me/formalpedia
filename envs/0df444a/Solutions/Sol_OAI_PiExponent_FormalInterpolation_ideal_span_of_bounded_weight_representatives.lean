-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.ideal_span_of_bounded_weight_representatives
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:43:34.380452+00:00
-- url     : https://prove2.me/submissions/5d40e453-ee26-4133-a9a9-2521dc7bcc66

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
theorem h41_bnd_mul {m : Nat} (w : Fin (m + 1) → Real) (B1 B2 : Real)
    (p q : MvPolynomial (Fin (m + 1)) Complex)
    (hp : ∀ a ∈ p.support, ∑ i, w i * (a i : Real) ≤ B1)
    (hq : ∀ a ∈ q.support, ∑ i, w i * (a i : Real) ≤ B2) :
    ∀ a ∈ (p * q).support, ∑ i, w i * (a i : Real) ≤ B1 + B2 := by
  classical
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q ha)
  have h1 := hp x hx
  have h2 := hq y hy
  have : ∑ i, w i * (((x + y) i : ℕ) : Real) = ∑ i, w i * (x i : Real) + ∑ i, w i * (y i : Real) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add]
    ring
  rw [this]; linarith

theorem h41_bnd_sub {m : Nat} (w : Fin (m + 1) → Real) (B : Real)
    (p q : MvPolynomial (Fin (m + 1)) Complex)
    (hp : ∀ a ∈ p.support, ∑ i, w i * (a i : Real) ≤ B)
    (hq : ∀ a ∈ q.support, ∑ i, w i * (a i : Real) ≤ B) :
    ∀ a ∈ (p - q).support, ∑ i, w i * (a i : Real) ≤ B := by
  classical
  intro a ha
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ p q ha) with h | h
  · exact hp a h
  · exact hq a h

theorem h41_bnd_mono {m : Nat} (w : Fin (m + 1) → Real) (B B' : Real) (hB : B ≤ B')
    (p : MvPolynomial (Fin (m + 1)) Complex)
    (hp : ∀ a ∈ p.support, ∑ i, w i * (a i : Real) ≤ B) :
    ∀ a ∈ p.support, ∑ i, w i * (a i : Real) ≤ B' :=
  fun a ha => (hp a ha).trans hB

theorem h41_bnd_C {m : Nat} (w : Fin (m + 1) → Real) (c : Complex) :
    ∀ a ∈ (MvPolynomial.C c : MvPolynomial (Fin (m + 1)) Complex).support,
      ∑ i, w i * (a i : Real) ≤ 0 := by
  classical
  intro a ha
  have := MvPolynomial.support_monomial_subset ha
  rw [Finset.mem_singleton] at this
  subst this; simp

theorem solution
    (m : Nat) (w : Fin (m + 1) → Real) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (D : Real) (hD : 0 ≤ D)
    (hrep : ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
        P - Q ∈ I ∧
        ∀ a ∈ Q.support, ∑ i, w i * (a i : Real) ≤ D) :
    Ideal.span {P : MvPolynomial (Fin (m + 1)) Complex |
      P ∈ I ∧
      ∀ a ∈ P.support, ∑ i, w i * (a i : Real) ≤ D + ∑ i, w i} = I := by
  classical
  set G := Ideal.span {P : MvPolynomial (Fin (m + 1)) Complex |
      P ∈ I ∧ ∀ a ∈ P.support, ∑ i, w i * (a i : Real) ≤ D + ∑ i, w i} with hG
  have hsw : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hGI : G ≤ I := by
    rw [hG, Ideal.span_le]
    intro P hP; exact hP.1
  have hmemG : ∀ P : MvPolynomial (Fin (m + 1)) Complex, P ∈ I →
      (∀ a ∈ P.support, ∑ i, w i * (a i : Real) ≤ D + ∑ i, w i) → P ∈ G :=
    fun P h1 h2 => Ideal.subset_span ⟨h1, h2⟩
  -- monomial claim
  have hmono : ∀ n : ℕ, ∀ a : Fin (m + 1) →₀ ℕ, a.degree = n →
      ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ Q.support, ∑ i, w i * (b i : Real) ≤ D) ∧
        MvPolynomial.monomial a 1 - Q ∈ G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro a ha
    by_cases hsmall : ∑ i, w i * (a i : Real) ≤ D + ∑ i, w i
    · obtain ⟨Q, hQI, hQb⟩ := hrep (MvPolynomial.monomial a 1)
      refine ⟨Q, hQb, hmemG _ hQI ?_⟩
      apply h41_bnd_sub
      · intro b hb
        have := MvPolynomial.support_monomial_subset hb
        rw [Finset.mem_singleton] at this
        subst this; exact hsmall
      · exact h41_bnd_mono w D _ (by linarith) Q hQb
    · have hne : ∃ i, a i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hsmall
        simp [hcon]
        linarith
      obtain ⟨i, hi⟩ := hne
      set b := a - Finsupp.single i 1 with hb
      have hab : a = b + Finsupp.single i 1 := by
        ext j
        simp only [hb, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
        by_cases hj : j = i
        · subst hj; simp; omega
        · simp [Ne.symm hj]
      have hdeg : b.degree < n := by
        rw [← ha, hab, map_add, Finsupp.degree_single]
        omega
      obtain ⟨Qb, hQbb, hQbG⟩ := ih _ hdeg b rfl
      let Q1 := MvPolynomial.X i * Qb
      have hQ1b : ∀ c ∈ Q1.support, ∑ j, w j * (c j : Real) ≤ D + ∑ j, w j := by
        have hX : ∀ c ∈ (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) Complex).support,
            ∑ j, w j * (c j : Real) ≤ ∑ j, w j := by
          intro c hc
          rw [MvPolynomial.support_X, Finset.mem_singleton] at hc
          subst hc
          apply Finset.sum_le_sum
          intro j _
          simp only [Finsupp.single_apply]
          split_ifs <;> simp [(hw j).le]
        have := h41_bnd_mul w _ _ _ _ hX hQbb
        intro c hc; have := this c hc; linarith
      obtain ⟨Q2, hQ2I, hQ2b⟩ := hrep Q1
      refine ⟨Q2, hQ2b, ?_⟩
      have h1 : Q1 - Q2 ∈ G := hmemG _ hQ2I
        (h41_bnd_sub w _ _ _ hQ1b (h41_bnd_mono w D _ (by linarith) Q2 hQ2b))
      have h2 : MvPolynomial.X i * (MvPolynomial.monomial b 1 - Qb) ∈ G :=
        Ideal.mul_mem_left _ _ hQbG
      have h3 : MvPolynomial.monomial a (1 : Complex) - Q2 =
          MvPolynomial.X i * (MvPolynomial.monomial b 1 - Qb) + (Q1 - Q2) := by
        have hm : MvPolynomial.monomial a (1 : Complex) =
            MvPolynomial.X i * MvPolynomial.monomial b 1 := by
          rw [hab, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm (Finsupp.single i 1) b]
        rw [hm]
        simp only [Q1]
        ring
      rw [h3]; exact G.add_mem h2 h1
  -- general claim
  have hgen : ∀ P : MvPolynomial (Fin (m + 1)) Complex, ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
      (∀ b ∈ Q.support, ∑ i, w i * (b i : Real) ≤ D) ∧ P - Q ∈ G := by
    intro P
    induction P using MvPolynomial.induction_on' with
    | monomial a c =>
      obtain ⟨Q, hQb, hQG⟩ := hmono _ a rfl
      refine ⟨MvPolynomial.C c * Q, ?_, ?_⟩
      · have := h41_bnd_mul w 0 D _ _ (h41_bnd_C w c) hQb
        intro b hb; have := this b hb; linarith
      · have : MvPolynomial.monomial a c - MvPolynomial.C c * Q =
            MvPolynomial.C c * (MvPolynomial.monomial a 1 - Q) := by
          rw [mul_sub, MvPolynomial.C_mul_monomial, mul_one]
        rw [this]; exact Ideal.mul_mem_left _ _ hQG
    | add p q hp hq =>
      obtain ⟨Qp, hpb, hpG⟩ := hp
      obtain ⟨Qq, hqb, hqG⟩ := hq
      refine ⟨Qp + Qq, ?_, ?_⟩
      · intro b hb
        rcases Finset.mem_union.mp (MvPolynomial.support_add hb) with h | h
        · exact hpb b h
        · exact hqb b h
      · have : p + q - (Qp + Qq) = (p - Qp) + (q - Qq) := by ring
        rw [this]; exact G.add_mem hpG hqG
  apply le_antisymm hGI
  intro P hP
  obtain ⟨Q, hQb, hQG⟩ := hgen P
  have hQI : Q ∈ I := by
    have := hGI hQG
    have h2 : Q = P - (P - Q) := by ring
    rw [h2]; exact I.sub_mem hP this
  have hQG' : Q ∈ G := hmemG Q hQI (h41_bnd_mono w D _ (by linarith) Q hQb)
  have h2 : P = (P - Q) + Q := by ring
  rw [h2]; exact G.add_mem hQG hQG'


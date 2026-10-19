-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.power_generator_block_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:07:18.44578+00:00
-- url     : https://prove2.me/submissions/4823efda-2006-4495-9888-bbd57cde56cc

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
/-- weight-bounded polynomials -/
def pieWB {m : Nat} (w0 : Real) (w : Fin m → Real) (B : Real)
    (P : MvPolynomial (Fin (m + 1)) Complex) : Prop :=
  ∀ a ∈ P.support, ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ B

theorem pieWB_mono {m : Nat} {w0 : Real} {w : Fin m → Real} {B B' : Real} (h : B ≤ B')
    {P : MvPolynomial (Fin (m + 1)) Complex} (hP : pieWB w0 w B P) : pieWB w0 w B' P :=
  fun a ha => (hP a ha).trans h

theorem pieWB_add {m : Nat} {w0 : Real} {w : Fin m → Real} {B : Real}
    {P Q : MvPolynomial (Fin (m + 1)) Complex} (hP : pieWB w0 w B P) (hQ : pieWB w0 w B Q) :
    pieWB w0 w B (P + Q) := by
  classical
  intro a ha
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h
  · exact hQ a h

theorem pieWB_sum {m : Nat} {w0 : Real} {w : Fin m → Real} {B : Real} {ι : Type*}
    (s : Finset ι) (P : ι → MvPolynomial (Fin (m + 1)) Complex)
    (hP : ∀ i ∈ s, pieWB w0 w B (P i)) : pieWB w0 w B (∑ i ∈ s, P i) := by
  classical
  intro a ha
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ha)
  exact hP i hi a hai

theorem pieWB_mul {m : Nat} {w0 : Real} {w : Fin m → Real} {B B' : Real}
    {P Q : MvPolynomial (Fin (m + 1)) Complex} (hP : pieWB w0 w B P) (hQ : pieWB w0 w B' Q) :
    pieWB w0 w (B + B') (P * Q) := by
  classical
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q ha)
  have := add_le_add (hP x hx) (hQ y hy)
  simp only [Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  exact this

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (s : Nat) (hs : 0 < s)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (hspan : Ideal.span (S : Set (MvPolynomial (Fin (m + 1)) Complex)) = I ^ s)
    (D : Real)
    (hdeg : ∀ P ∈ S, ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ D)
    (C : Real)
    (hbase : ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : WeightedPolynomial w0 w C, P - Q.val ∈ I ^ s)
    (k n : Nat) (hn : n ≤ (k + 1) * s)
    (P : MvPolynomial (Fin (m + 1)) Complex) :
    ∃ Q : WeightedPolynomial w0 w (C + (k : Real) * max D 0),
      P - Q.val ∈ I ^ n := by
  classical
  suffices key : ∀ k n, n ≤ (k + 1) * s → ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q, pieWB w0 w (C + (k : Real) * max D 0) Q ∧ P - Q ∈ I ^ n by
    obtain ⟨Q, hQ, hPQ⟩ := key k n hn P
    exact ⟨⟨Q, hQ⟩, hPQ⟩
  intro k
  induction k with
  | zero =>
    intro n hn P
    obtain ⟨Q, hQ⟩ := hbase P
    refine ⟨Q.val, ?_, Ideal.pow_le_pow_right (by omega) hQ⟩
    have := Q.2
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact this
  | succ k ih =>
    intro n hn P
    obtain ⟨Q0, hQ0⟩ := hbase P
    have hE : P - Q0.val ∈ Ideal.span (S : Set (MvPolynomial (Fin (m + 1)) Complex)) := by
      rw [hspan]; exact hQ0
    obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp hE
    have hn' : n - s ≤ (k + 1) * s := by
      have : (k + 1 + 1) * s = (k + 1) * s + s := by ring
      omega
    choose Qg hQg hgQ using fun G : MvPolynomial (Fin (m + 1)) Complex => ih (n - s) hn' (g G)
    refine ⟨Q0.val + ∑ G ∈ S, Qg G * G, ?_, ?_⟩
    · have hD : D ≤ max D 0 := le_max_left _ _
      have hD0 : 0 ≤ max D 0 := le_max_right _ _
      have hB : C + (k : Real) * max D 0 + D ≤ C + ((k + 1 : ℕ) : Real) * max D 0 := by
        push_cast; nlinarith
      apply pieWB_add
      · exact pieWB_mono (by push_cast; nlinarith) Q0.2
      · apply pieWB_sum
        intro G hG
        exact pieWB_mono hB (pieWB_mul (hQg G) (hdeg G hG))
    · have : P - (Q0.val + ∑ G ∈ S, Qg G * G) = ∑ G ∈ S, (g G - Qg G) * G := by
        have h2 : P - Q0.val = ∑ G ∈ S, g G * G := by rw [← hg]; simp [smul_eq_mul]
        rw [sub_add_eq_sub_sub, h2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun G _ => by ring)
      rw [this]
      refine Ideal.sum_mem _ (fun G hG => ?_)
      have hGs : G ∈ I ^ s := by
        rw [← hspan]; exact Ideal.subset_span hG
      have := Ideal.mul_mem_mul (hgQ G) hGs
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this

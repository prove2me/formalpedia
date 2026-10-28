-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_bounded_word_prime_selection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:18:13.243504+00:00
-- url     : https://prove2.me/submissions/4c2efb61-d631-4b14-b0a6-2e3e47293b10

import Mathlib
import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace PiS37PS

theorem word_append {m : Nat} (a b : List (Fin (m + 1)))
    (F : MvPolynomial (Fin (m + 1)) Complex) :
    logarithmicFrameWord (a ++ b) F = logarithmicFrameWord a (logarithmicFrameWord b F) := by
  induction a with
  | nil => rfl
  | cons i a ih => simp [logarithmicFrameWord, ih]

theorem cost_append {m : Nat} (v : Fin (m + 1) → Rat) (a b : List (Fin (m + 1))) :
    logarithmicFrameCost v (a ++ b) = logarithmicFrameCost v a + logarithmicFrameCost v b := by
  simp [logarithmicFrameCost, List.map_append, List.sum_append]

theorem cost_nil {m : Nat} (v : Fin (m + 1) → Rat) :
    logarithmicFrameCost v ([] : List (Fin (m + 1))) = 0 := by
  simp [logarithmicFrameCost]

theorem cost_ge {m : Nat} (v : Fin (m + 1) → Rat) (δ : Real)
    (hδ : ∀ i, δ ≤ (v i : Real)) (word : List (Fin (m + 1))) :
    (word.length : Real) * δ ≤ logarithmicFrameCost v word := by
  induction word with
  | nil => simp [logarithmicFrameCost]
  | cons i w ih =>
    have := hδ i
    simp only [logarithmicFrameCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    push_cast
    linarith

theorem gens_finite {m : Nat} (v : Fin (m + 1) → Rat) (hv : ∀ i, 0 < (v i : Real))
    (F : MvPolynomial (Fin (m + 1)) Complex) (B : Real) :
    {f | ∃ word : List (Fin (m + 1)), f = logarithmicFrameWord word F ∧
        logarithmicFrameCost v word ≤ B}.Finite := by
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : Real, 0 < δ ∧ ∀ i, δ ≤ (v i : Real) := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun i => (v i : Real)), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]; intro i _; exact hv i
    · intro i; exact Finset.inf'_le _ (Finset.mem_univ i)
  refine ((List.finite_length_le (Fin (m + 1)) ⌊B / δ⌋₊).image
    (fun w => logarithmicFrameWord w F)).subset ?_
  rintro f ⟨w, rfl, hw⟩
  refine ⟨w, ?_, rfl⟩
  simp only [Set.mem_setOf_eq]
  have h1 := cost_ge v δ hδ w
  have h2 : (w.length : Real) ≤ B / δ := by
    rw [le_div_iff₀ hδ0]; linarith
  exact Nat.le_floor h2

end PiS37PS

open PiS37PS in
theorem solution
    {m : Nat} (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real)) (hv : ∀ i, 0 < (v i : Real))
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin (m + 1)) Complex) (hF : F ≠ 0)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [Q.IsPrime]
    (hwords : ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real) →
        logarithmicFrameWord word F ∈ Q) :
    ∃ P : Ideal (MvPolynomial (Fin (m + 1)) Complex),
      P.IsPrime ∧ P ≠ ⊥ ∧ P ≤ Q ∧
      ∃ S : Finset (MvPolynomial (Fin (m + 1)) Complex),
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P ∧
        F ∈ S ∧
        (∀ f ∈ S, ∃ word : List (Fin (m + 1)),
          f = logarithmicFrameWord word F ∧
          logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real)) ∧
        (∀ f ∈ S, ∀ word : List (Fin (m + 1)),
          logarithmicFrameCost v word <
            ((sigma : Real) / ((m : Real) + 2)) * (N : Real) →
          logarithmicFrameWord word f ∈ P) := by
  set c : Real := ((sigma : Real) / ((m : Real) + 2)) * (N : Real) with hc
  have hNr : (0 : Real) < N := by exact_mod_cast hN
  have hm2 : (0 : Real) < (m : Real) + 2 := by positivity
  have hc0 : 0 < c := by positivity
  -- k * c ≤ σ N for k ≤ m + 2
  have hkc : ∀ k : Nat, k ≤ m + 2 → (k : Real) * c ≤ (sigma : Real) * (N : Real) := by
    intro k hk
    have hk' : (k : Real) ≤ (m : Real) + 2 := by exact_mod_cast hk
    rw [hc, show (k : Real) * ((sigma : Real) / ((m : Real) + 2) * (N : Real)) =
      ((k : Real) / ((m : Real) + 2)) * ((sigma : Real) * N) by field_simp]
    have : (k : Real) / ((m : Real) + 2) ≤ 1 := by rw [div_le_one hm2]; exact hk'
    have hsN : 0 ≤ (sigma : Real) * N := by positivity
    nlinarith
  let gens : Nat → Set (MvPolynomial (Fin (m + 1)) Complex) := fun k => {f | ∃ word : List (Fin (m + 1)),
    f = logarithmicFrameWord word F ∧ logarithmicFrameCost v word ≤ (k : Real) * c}
  let J : Nat → Ideal (MvPolynomial (Fin (m + 1)) Complex) := fun k => Ideal.span (gens k)
  have hJmono : ∀ k, J k ≤ J (k + 1) := by
    intro k
    apply Ideal.span_mono
    rintro f ⟨w, rfl, hw⟩
    refine ⟨w, rfl, le_trans hw ?_⟩
    push_cast; nlinarith
  have hJmono' : ∀ k l, k ≤ l → J k ≤ J l := by
    intro k l hkl
    induction hkl with
    | refl => exact le_rfl
    | step _ ih => exact le_trans ih (hJmono _)
  have hJQ : ∀ k, k ≤ m + 2 → J k ≤ Q := by
    intro k hk
    rw [Ideal.span_le]
    rintro f ⟨w, rfl, hw⟩
    exact hwords w (le_trans hw (hkc k hk))
  have hFJ : ∀ k, F ∈ J k := by
    intro k
    apply Ideal.subset_span
    refine ⟨[], rfl, ?_⟩
    rw [cost_nil]; positivity
  let A : Nat → Set (Ideal (MvPolynomial (Fin (m + 1)) Complex)) := fun k => {P | P.IsPrime ∧ J k ≤ P ∧ P ≤ Q}
  have hQA : ∀ k, k ≤ m + 2 → Q ∈ A k := fun k hk => ⟨inferInstance, hJQ k hk, le_rfl⟩
  let hgt : Nat → ℕ∞ := fun k => sInf ((fun P : Ideal (MvPolynomial (Fin (m + 1)) Complex) => P.height) '' A k)
  have hgt_le : ∀ k, ∀ P ∈ A k, hgt k ≤ P.height := fun k P hP =>
    sInf_le ⟨P, hP, rfl⟩
  have hgt_mem : ∀ k, k ≤ m + 2 → ∃ P ∈ A k, P.height = hgt k := by
    intro k hk
    have hne : ((fun P : Ideal (MvPolynomial (Fin (m + 1)) Complex) => P.height) '' A k).Nonempty := ⟨_, Q, hQA k hk, rfl⟩
    exact csInf_mem hne
  have hgt_mono : ∀ k, hgt k ≤ hgt (k + 1) := by
    intro k
    apply le_sInf
    rintro _ ⟨P, ⟨hP1, hP2, hP3⟩, rfl⟩
    exact hgt_le k P ⟨hP1, le_trans (hJmono k) hP2, hP3⟩
  -- lower bound: every prime containing F has height ≥ 1
  have hgt0 : 1 ≤ hgt 0 := by
    apply le_sInf
    rintro _ ⟨P, ⟨hP1, hP2, hP3⟩, rfl⟩
    have hPne : P ≠ ⊥ := by
      intro h; apply hF; have := hP2 (hFJ 0); rw [h] at this; exact (Submodule.mem_bot _).1 this
    rw [Order.one_le_iff_ne_zero]
    intro h0
    exact hPne (Ideal.height_eq_zero_iff_eq_bot.1 h0)
  -- upper bound by Krull dimension
  have hQdim : Q.height ≤ (m + 1 : Nat) := by
    have h1 := Ideal.height_le_ringKrullDim_of_isPrime (I := Q)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 : ((Q.height : ℕ∞) : WithBot ℕ∞) ≤ (((m + 1 : Nat) : ℕ∞) : WithBot ℕ∞) := by
      simpa using h1
    exact WithBot.coe_le_coe.1 h2
  -- pigeonhole
  obtain ⟨k, hk, hkeq⟩ : ∃ k, k ≤ m ∧ hgt (k + 1) ≤ hgt k := by
    by_contra hcon
    push_neg at hcon
    have hind : ∀ k, k ≤ m + 1 → ((k + 1 : Nat) : ℕ∞) ≤ hgt k := by
      intro k hk
      induction k with
      | zero => simpa using hgt0
      | succ k ih =>
        have h1 := ih (by omega)
        have h2 := hcon k (by omega)
        have h3 : hgt k + 1 ≤ hgt (k + 1) := Order.add_one_le_of_lt h2
        calc ((k + 1 + 1 : Nat) : ℕ∞) = ((k + 1 : Nat) : ℕ∞) + 1 := by push_cast; ring
          _ ≤ hgt k + 1 := by gcongr
          _ ≤ hgt (k + 1) := h3
    have h1 := hind (m + 1) le_rfl
    have h2 := le_trans h1 (le_trans (hgt_le (m + 1) Q (hQA (m + 1) (by omega))) hQdim)
    have : m + 1 + 1 ≤ m + 1 := by exact_mod_cast h2
    omega
  obtain ⟨P, ⟨hP1, hP2, hP3⟩, hPh⟩ := hgt_mem (k + 1) (by omega)
  have hfin := (gens_finite v hv F ((k : Real) * c))
  refine ⟨P, hP1, ?_, hP3, hfin.toFinset, ?_, ?_, ?_, ?_⟩
  · intro h; apply hF; have := hP2 (hFJ (k + 1)); rw [h] at this
    exact (Submodule.mem_bot _).1 this
  · rw [Set.Finite.coe_toFinset]
    refine ⟨⟨hP1, le_trans (hJmono k) hP2⟩, ?_⟩
    rintro q ⟨hq1, hq2⟩ hqP
    have h1 : hgt k ≤ q.height := hgt_le k q ⟨hq1, hq2, le_trans hqP hP3⟩
    have h2 : P.height ≤ q.height := by rw [hPh]; exact le_trans hkeq h1
    exact (Ideal.eq_of_le_of_height_le q hqP h2).ge
  · rw [Set.Finite.mem_toFinset]
    refine ⟨[], rfl, ?_⟩
    rw [cost_nil]; positivity
  · intro f hf
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨w, rfl, hw⟩ := hf
    exact ⟨w, rfl, le_trans hw (hkc k (by omega))⟩
  · intro f hf word hword
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨w, rfl, hw⟩ := hf
    rw [← word_append]
    apply hP2
    apply Ideal.subset_span
    refine ⟨word ++ w, rfl, ?_⟩
    rw [cost_append]
    push_cast
    linarith

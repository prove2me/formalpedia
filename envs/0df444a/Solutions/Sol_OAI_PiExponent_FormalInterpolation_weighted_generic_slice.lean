-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_generic_slice
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:09:14.605569+00:00
-- url     : https://prove2.me/submissions/7429377f-cf54-456a-85c5-595d86ec548e

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib

open OAI.PiExponent.FormalInterpolation

namespace A3S48GS

abbrev R (m : ℕ) := MvPolynomial (Fin (m + 1)) ℂ

lemma span_deg {m : ℕ} (w : Fin (m + 1) → ℚ) (H : ℝ) (S : Set (R m))
    (hS : ∀ g ∈ S, logarithmicDegreeBound w H g) :
    ∀ v ∈ Submodule.span ℂ S, logarithmicDegreeBound w H v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => intro a ha; simp at ha
  | add x y _ _ hx hy =>
    intro a ha
    rcases Finset.mem_union.1 (MvPolynomial.support_add ha) with h | h
    · exact hx a h
    · exact hy a h
  | smul c x _ hx =>
    intro a ha
    exact hx a (MvPolynomial.support_smul ha)

lemma span_le {m : ℕ} (S : Set (R m)) :
    ∀ v ∈ Submodule.span ℂ S, v ∈ Ideal.span S := by
  intro v hv
  have : Submodule.span ℂ S ≤ (Ideal.span S).restrictScalars ℂ :=
    Submodule.span_le.2 (fun x hx => Ideal.subset_span hx)
  exact this hv

lemma krull {m i : ℕ} (g : Fin i → R m) {Q : Ideal (R m)}
    (hQ : Q ∈ (Ideal.span (Set.range g)).minimalPrimes) : Q.height ≤ i := by
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (s := Finset.univ.image g) (p := Q) (by simpa using hQ)
  refine h.trans ?_
  exact_mod_cast (Finset.card_image_le.trans (by simp))

lemma step {m : ℕ} (S : Set (R m)) (P : Ideal (R m)) [P.IsPrime]
    (hmin : (Ideal.span S).IsMinimalPrime P) (h : ℕ) (hP : P.height = h) :
    ∀ i ≤ h, ∃ g : Fin i → R m, (∀ j, g j ∈ Submodule.span ℂ S) ∧
      ∀ Q ∈ (Ideal.span (Set.range g)).minimalPrimes, Q ≤ P → (i : ℕ∞) ≤ Q.height := by
  intro i
  induction i with
  | zero => intro _; exact ⟨Fin.elim0, fun j => j.elim0, fun _ _ _ => by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨g, hgV, hg⟩ := ih (by omega)
    set V := Submodule.span ℂ S
    set M : Set (Ideal (R m)) := {Q | Q ∈ (Ideal.span (Set.range g)).minimalPrimes ∧ Q ≤ P}
    have hMfin : M.Finite :=
      (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset (fun Q hQ => hQ.1)
    haveI : Finite M := hMfin
    let p : M → Subspace ℂ V := fun Q => ((Q.1).restrictScalars ℂ).comap V.subtype
    have hp : ∀ Q : M, p Q ≠ ⊤ := by
      intro Q hQ
      have hVQ : ∀ v ∈ V, v ∈ Q.1 := by
        intro v hv
        have : (⟨v, hv⟩ : V) ∈ p Q := hQ ▸ Submodule.mem_top
        exact this
      have hSQ : Ideal.span S ≤ Q.1 :=
        Ideal.span_le.2 (fun x hx => hVQ x (Submodule.subset_span hx))
      have hQprime : Q.1.IsPrime := Q.2.1.1.1
      have hQP : Q.1 = P := hmin.eq_of_le ⟨hQprime, hSQ⟩ Q.2.2
      have h1 := krull g Q.2.1
      rw [hQP, hP] at h1
      norm_cast at h1
      omega
    have hcov : ⋃ Q : M, (p Q : Set V) ≠ Set.univ := by
      intro hc
      obtain ⟨Q, hQ⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hc
      exact hp Q hQ
    obtain ⟨⟨v, hvV⟩, hv⟩ : ∃ x : V, x ∉ ⋃ Q : M, (p Q : Set V) := by
      by_contra hcon
      push Not at hcon
      exact hcov (Set.eq_univ_of_forall hcon)
    simp only [Set.mem_iUnion, not_exists] at hv
    have hvQ : ∀ Q ∈ M, v ∉ Q := fun Q hQ h => hv ⟨Q, hQ⟩ h
    refine ⟨Fin.cons v g, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hvV
      · simpa using hgV j
    · intro Q' hQ' hQ'P
      rw [Fin.range_cons] at hQ'
      haveI : Q'.IsPrime := hQ'.1.1
      have hle : Ideal.span (Set.range g) ≤ Q' :=
        (Ideal.span_mono (Set.subset_insert _ _)).trans hQ'.1.2
      obtain ⟨Q, hQ, hQQ'⟩ := Ideal.exists_minimalPrimes_le hle
      haveI : Q.IsPrime := hQ.1.1
      have hQM : Q ∈ M := ⟨hQ, hQQ'.trans hQ'P⟩
      have hvQ' : v ∈ Q' := hQ'.1.2 (Ideal.subset_span (Set.mem_insert _ _))
      have hlt : Q < Q' := lt_of_le_of_ne hQQ' (fun e => hvQ Q hQM (e ▸ hvQ'))
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h2 := hg Q hQ (hQQ'.trans hQ'P)
      calc ((i + 1 : ℕ) : ℕ∞) = (i : ℕ∞) + 1 := by norm_cast
        _ ≤ Q.height + 1 := by gcongr
        _ ≤ Q'.height := h1

end A3S48GS

open A3S48GS in
theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ g ∈ S, logarithmicDegreeBound w H g)
    (A : Finset (Fin (m + 1))) (hcard : A.card = P.height) :
    ∃ f : Fin A.card → MvPolynomial (Fin (m + 1)) Complex,
      (∀ j, f j ∈ Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) ∧
      (∀ j, logarithmicDegreeBound w H (f j)) ∧
      (Ideal.span (Set.range f)).IsMinimalPrime P := by
  obtain ⟨f, hfV, hf⟩ := step (S : Set (R m)) P hminimal A.card hcard.symm A.card le_rfl
  refine ⟨f, fun j => span_le _ _ (hfV j),
    fun j => span_deg w H _ (fun g hg => hdegree g hg) _ (hfV j), ?_⟩
  have hfP : Ideal.span (Set.range f) ≤ P := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hminimal.le (span_le _ _ (hfV j))
  refine ⟨⟨inferInstance, hfP⟩, ?_⟩
  rintro q ⟨hq, hfq⟩ hqP
  obtain ⟨Q, hQ, hQq⟩ := Ideal.exists_minimalPrimes_le hfq
  haveI : Q.IsPrime := hQ.1.1
  have hQP : Q ≤ P := hQq.trans hqP
  have h1 := hf Q hQ hQP
  have hQeq : Q = P := by
    by_contra hne
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hQP hne)
    rw [← hcard] at h2
    have h3 : (A.card : ℕ∞) + 1 ≤ A.card := (by gcongr : (A.card : ℕ∞) + 1 ≤ Q.height + 1).trans h2
    norm_cast at h3
    omega
  exact hQeq ▸ hQq

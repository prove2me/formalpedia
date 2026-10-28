-- Prove2me | solution 1 for MPECRelax.ScholtesConv.mpec_mfcq_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:54:48.951356+00:00
-- url     : https://prove2.me/submissions/490ad90d-7554-4d93-aa7a-b1a3e3270596

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC

open scoped RealInnerProductSpace

open MPECRelax.ScholtesConv in
theorem solution {n m p l : ℕ} (P : MPEC n m p l) (xs : E n) (hxs : P.Feasible xs) :
    P.MPEC_MFCQ xs ↔
      (LinearIndependent ℝ
          (Sum.elim (fun i : Fin p => gradient (P.h i) xs)
            (Sum.elim (fun i : ↥(P.I00 xs ∪ P.I0p xs) => gradient (P.G i) xs)
              (fun i : ↥(P.I00 xs ∪ P.Ip0 xs) => gradient (P.H i) xs))) ∧
        ∃ d : E n, (∀ i ∈ P.Ig xs, ⟪gradient (P.g i) xs, d⟫ < 0) ∧
          (∀ i, ⟪gradient (P.h i) xs, d⟫ = 0) ∧
          (∀ i ∈ P.I00 xs ∪ P.I0p xs, ⟪gradient (P.G i) xs, d⟫ = 0) ∧
          (∀ i ∈ P.I00 xs ∪ P.Ip0 xs, ⟪gradient (P.H i) xs, d⟫ = 0)) := by
  unfold MPEC.MPEC_MFCQ NLP.IsMFCQ
  let e : (Fin p ⊕ ↥(P.I00 xs ∪ P.I0p xs) ⊕ ↥(P.I00 xs ∪ P.Ip0 xs)) ≃
      (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs)) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.setCongr (Set.union_comm _ _))
      (Equiv.setCongr (Set.union_comm _ _)))
  have hfam : (fun j => gradient ((P.TNLP xs).h j) xs) ∘ e =
      Sum.elim (fun i : Fin p => gradient (P.h i) xs)
        (Sum.elim (fun i : ↥(P.I00 xs ∪ P.I0p xs) => gradient (P.G i) xs)
          (fun i : ↥(P.I00 xs ∪ P.Ip0 xs) => gradient (P.H i) xs)) := by
    funext j
    rcases j with i | i | i <;> rfl
  have hLI : LinearIndependent ℝ (fun j => gradient ((P.TNLP xs).h j) xs) ↔
      LinearIndependent ℝ (Sum.elim (fun i : Fin p => gradient (P.h i) xs)
        (Sum.elim (fun i : ↥(P.I00 xs ∪ P.I0p xs) => gradient (P.G i) xs)
          (fun i : ↥(P.I00 xs ∪ P.Ip0 xs) => gradient (P.H i) xs))) := by
    rw [← hfam, linearIndependent_equiv]
  have hact : ∀ d : E n, (∀ i ∈ (P.TNLP xs).activeSet xs, ⟪gradient ((P.TNLP xs).g i) xs, d⟫ < 0) ↔
      (∀ i ∈ P.Ig xs, ⟪gradient (P.g i) xs, d⟫ < 0) := by
    intro d
    constructor
    · intro h i hi
      exact h (Sum.inl i) hi
    · intro h j hj
      rcases j with i | i | i
      · exact h i hj
      · exfalso
        have h1 : -P.H i xs = 0 := hj
        have h2 := i.2.2
        linarith
      · exfalso
        have h1 : -P.G i xs = 0 := hj
        have h2 := i.2.1
        linarith
  have heq : ∀ d : E n, (∀ j, ⟪gradient ((P.TNLP xs).h j) xs, d⟫ = 0) ↔
      ((∀ i, ⟪gradient (P.h i) xs, d⟫ = 0) ∧
        (∀ i ∈ P.I00 xs ∪ P.I0p xs, ⟪gradient (P.G i) xs, d⟫ = 0) ∧
        (∀ i ∈ P.I00 xs ∪ P.Ip0 xs, ⟪gradient (P.H i) xs, d⟫ = 0)) := by
    intro d
    constructor
    · intro h
      refine ⟨fun i => h (Sum.inl i), fun i hi => ?_, fun i hi => ?_⟩
      · exact h (Sum.inr (Sum.inl ⟨i, (Set.union_comm _ _) ▸ hi⟩))
      · exact h (Sum.inr (Sum.inr ⟨i, (Set.union_comm _ _) ▸ hi⟩))
    · rintro ⟨h1, h2, h3⟩ j
      rcases j with i | i | i
      · exact h1 i
      · exact h2 i.1 ((Set.union_comm _ _) ▸ i.2)
      · exact h3 i.1 ((Set.union_comm _ _) ▸ i.2)
  rw [hLI]
  simp only [hact, heq]

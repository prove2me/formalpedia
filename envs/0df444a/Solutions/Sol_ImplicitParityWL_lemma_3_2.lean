-- Prove2me | solution 1 for ImplicitParityWL.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:22:37.718825+00:00
-- url     : https://prove2.me/submissions/f0aa8eca-2f17-4350-9f9b-5c82f41aad0b

import Mathlib
import Definitions.Def_ImplicitParityWL_PebbleGame

open ImplicitParityWL

namespace Aux_lemma_3_2

lemma card_eq_of_hclass {K V W : Type*} [Fintype V] [Fintype W]
    (G : ColoredGraph K V) (H : ColoredGraph K W)
    (hclass : ∀ A : K, Nat.card {p : V // G.χ p = A} = Nat.card {q : W // H.χ q = A}) :
    Fintype.card V = Fintype.card W := by
  classical
  have hequiv : ∀ A : K, Nonempty ({p : V // G.χ p = A} ≃ {q : W // H.χ q = A}) := by
    intro A
    have hA := hclass A
    simp only [Nat.card_eq_fintype_card] at hA
    exact Fintype.card_eq.mp hA
  let fA : ∀ A : K, {p : V // G.χ p = A} ≃ {q : W // H.χ q = A} := fun A => Classical.choice (hequiv A)
  exact Fintype.card_congr
    ((Equiv.sigmaFiberEquiv G.χ).symm.trans ((Equiv.sigmaCongrRight fA).trans (Equiv.sigmaFiberEquiv H.χ)))

end Aux_lemma_3_2

theorem solution {K V W : Type*} [Fintype V] [Fintype W] (G : ColoredGraph K V)
    (H : ColoredGraph K W) (hclass : ∀ A : K, Nat.card {p : V // G.χ p = A} = Nat.card {q : W // H.χ q = A})
    (m : ℕ) (_hm : 1 ≤ m) (r : ℕ) (S : GameState V W m) :
    Survives G H r S ↔ SurvivesCF G H r S := by
  classical
  have hcard : Fintype.card V = Fintype.card W := Aux_lemma_3_2.card_eq_of_hclass G H hclass
  induction r generalizing S with
  | zero =>
    simp [Survives, SurvivesCF, hcard]
  | succ r ih =>
    constructor
    · rintro ⟨_, hS⟩ i A
      obtain ⟨f, hf⟩ := hS i
      have hχ : ∀ p : V, G.χ p = H.χ (f p) := by
        intro p
        have hpi := (hf p).1 i i p p (f p) (f p) (by simp [GameState.place]) (by simp [GameState.place])
        exact hpi.2.2
      let g : {p : V // G.χ p = A} → {q : W // H.χ q = A} :=
        fun p => ⟨f p.1, by rw [← hχ p.1, p.2]⟩
      have hg_inj : Function.Injective g := by
        intro p₁ p₂ h
        ext
        exact f.injective (congrArg Subtype.val h)
      have hcardA : Fintype.card {p : V // G.χ p = A} = Fintype.card {q : W // H.χ q = A} := by
        have h := hclass A
        rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
      have hg_bij : Function.Bijective g :=
        (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, hcardA⟩
      let fA := Equiv.ofBijective g hg_bij
      have hfA_apply : ∀ p : {p : V // G.χ p = A}, (fA p).1 = f p.1 := fun _ => rfl
      refine ⟨fA, ?_, ?_⟩
      · intro p
        rw [hfA_apply]
        exact ⟨(hf p.1).1, (ih _).mp (hf p.1).2⟩
      · intro q
        have hq : q.1 = f (fA.symm q).1 := by
          conv_lhs => rw [← fA.apply_symm_apply q]
          exact hfA_apply (fA.symm q)
        rw [hq]
        exact ⟨(hf (fA.symm q).1).1, (ih _).mp (hf (fA.symm q).1).2⟩
    · intro hCF
      refine ⟨hcard, fun i => ?_⟩
      let fA : ∀ A : K, {p : V // G.χ p = A} ≃ {q : W // H.χ q = A} :=
        fun A => Classical.choose (hCF i A)
      have hfA : ∀ A : K,
          (∀ p, PartialIso G H (S.place i (p.1, (fA A p).1)) ∧
            SurvivesCF G H r (S.place i (p.1, (fA A p).1))) ∧
          (∀ q, PartialIso G H (S.place i ((fA A |>.symm q).1, q.1)) ∧
            SurvivesCF G H r (S.place i ((fA A |>.symm q).1, q.1))) :=
        fun A => Classical.choose_spec (hCF i A)
      let f : V ≃ W :=
        (Equiv.sigmaFiberEquiv G.χ).symm.trans
          ((Equiv.sigmaCongrRight fA).trans (Equiv.sigmaFiberEquiv H.χ))
      refine ⟨f, fun p => ?_⟩
      have hfp : f p = (fA (G.χ p) ⟨p, rfl⟩).1 := rfl
      rw [hfp]
      have hp := (hfA (G.χ p)).1 ⟨p, rfl⟩
      exact ⟨hp.1, (ih _).mpr hp.2⟩

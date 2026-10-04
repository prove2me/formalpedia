-- Prove2me | solution 1 for HJMEilenberg.finiteIndex_filter
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T11:02:29.579384+00:00
-- url     : https://prove2.me/submissions/224eddbe-0fbd-41a5-93ba-78e077c98c4c

import Definitions.Def_HJMEilenberg_Formations
import Mathlib.Data.Fintype.Prod

open MSKleene

namespace HJMEilenberg

private def interLeft {S : Type} {sig : Signature S} {A : Algebra sig}
    (Phi Psi : Congruence A) (s : S) :
    Quotient ((Congruence.inter Phi Psi).setoid s) →
      Quotient (Phi.setoid s) :=
  Quotient.map id (fun _ _ h => h.1)

private def interRight {S : Type} {sig : Signature S} {A : Algebra sig}
    (Phi Psi : Congruence A) (s : S) :
    Quotient ((Congruence.inter Phi Psi).setoid s) →
      Quotient (Psi.setoid s) :=
  Quotient.map id (fun _ _ h => h.2)

private def interEmbedding {S : Type} {sig : Signature S} {A : Algebra sig}
    (Phi Psi : Congruence A) :
    (Σ s, Quotient ((Congruence.inter Phi Psi).setoid s)) →
      (Σ s, Quotient (Phi.setoid s)) ×
        (Σ s, Quotient (Psi.setoid s)) :=
  fun z =>
    (⟨z.1, interLeft Phi Psi z.1 z.2⟩,
      ⟨z.1, interRight Phi Psi z.1 z.2⟩)

private theorem interEmbedding_injective {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi Psi : Congruence A) :
    Function.Injective (interEmbedding Phi Psi) := by
  rintro ⟨s, q⟩ ⟨t, r⟩ h
  have hs : s = t := congrArg (fun z => z.1.1) h
  subst t
  have hLeft : (⟨s, interLeft Phi Psi s q⟩ :
      Σ u, Quotient (Phi.setoid u)) =
      ⟨s, interLeft Phi Psi s r⟩ := congrArg Prod.fst h
  have hRight : (⟨s, interRight Phi Psi s q⟩ :
      Σ u, Quotient (Psi.setoid u)) =
      ⟨s, interRight Phi Psi s r⟩ := congrArg Prod.snd h
  have hPhi : interLeft Phi Psi s q = interLeft Phi Psi s r :=
    eq_of_heq ((Sigma.mk.inj_iff.mp hLeft).2)
  have hPsi : interRight Phi Psi s q = interRight Phi Psi s r :=
    eq_of_heq ((Sigma.mk.inj_iff.mp hRight).2)
  refine (Sigma.mk.inj_iff).2 ⟨rfl, ?_⟩
  apply heq_of_eq
  revert hPhi hPsi
  refine Quotient.inductionOn q ?_
  intro x
  refine Quotient.inductionOn r ?_
  intro y hPhi hPsi
  apply Quotient.sound
  constructor
  · apply Quotient.exact
    exact hPhi
  · apply Quotient.exact
    exact hPsi

private def quotientProjection {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi Psi : Congruence A) (h : Phi ≤ Psi) :
    (Σ s, Quotient (Phi.setoid s)) → (Σ s, Quotient (Psi.setoid s)) :=
  fun z => ⟨z.1, Quotient.map id (fun _ _ hxy => h z.1 _ _ hxy) z.2⟩

private theorem quotientProjection_surjective {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi Psi : Congruence A) (h : Phi ≤ Psi) :
    Function.Surjective (quotientProjection Phi Psi h) := by
  rintro ⟨s, q⟩
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨⟨s, Quotient.mk'' x⟩, rfl⟩

end HJMEilenberg

theorem solution {S : Type} [Finite S] {sig : Signature S}
    (A : Algebra sig) :
    HJMEilenberg.Congruence.FiniteIndex
        (HJMEilenberg.Congruence.top A) ∧
      (∀ Phi Psi : HJMEilenberg.Congruence A,
        Phi.FiniteIndex → Psi.FiniteIndex →
          (HJMEilenberg.Congruence.inter Phi Psi).FiniteIndex) ∧
      (∀ Phi Psi : HJMEilenberg.Congruence A,
        Phi.FiniteIndex → Phi ≤ Psi → Psi.FiniteIndex) := by
  open HJMEilenberg in
    constructor
    · unfold Congruence.FiniteIndex SFinite
      apply Finite.of_injective
        (fun z : Σ s, Quotient ((Congruence.top A).setoid s) => z.1)
      rintro ⟨s, q⟩ ⟨t, r⟩ h
      cases h
      refine (Sigma.mk.inj_iff).2 ⟨rfl, ?_⟩
      revert r
      refine Quotient.inductionOn q ?_
      intro x r
      refine Quotient.inductionOn r ?_
      intro y
      exact heq_of_eq (Quotient.sound trivial)
    · constructor
      · intro Phi Psi hPhi hPsi
        unfold Congruence.FiniteIndex SFinite at hPhi hPsi ⊢
        haveI : Finite (Σ s, Quotient (Phi.setoid s)) := hPhi
        haveI : Finite (Σ s, Quotient (Psi.setoid s)) := hPsi
        letI : Fintype (Σ s, Quotient (Phi.setoid s)) := Fintype.ofFinite _
        letI : Fintype (Σ s, Quotient (Psi.setoid s)) := Fintype.ofFinite _
        haveI : Finite
            ((Σ s, Quotient (Phi.setoid s)) ×
              (Σ s, Quotient (Psi.setoid s))) :=
          Fintype.finite (inferInstance : Fintype
            ((Σ s, Quotient (Phi.setoid s)) ×
              (Σ s, Quotient (Psi.setoid s))))
        exact Finite.of_injective (interEmbedding Phi Psi)
          (interEmbedding_injective Phi Psi)
      · intro Phi Psi hPhi hle
        unfold Congruence.FiniteIndex SFinite at hPhi ⊢
        haveI : Finite (Σ s, Quotient (Phi.setoid s)) := hPhi
        exact Finite.of_surjective (quotientProjection Phi Psi hle)
          (quotientProjection_surjective Phi Psi hle)

-- Prove2me | solution 1 for HJMEilenberg.recover_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T11:29:05.635281+00:00
-- url     : https://prove2.me/submissions/a27ae91e-490b-465d-a472-3487e0b84e5f

import Definitions.Def_HJMEilenberg_Formations

open MSKleene
open HJMEilenberg

private def quotientClassLanguage {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi : Congruence A)
    (q : Σ s, Quotient (Phi.setoid s)) : Language A :=
  fun s => {x | (⟨s, Quotient.mk'' x⟩ : Σ t, Quotient (Phi.setoid t)) = q}

private theorem quotientClass_saturated {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi : Congruence A)
    (q : Σ s, Quotient (Phi.setoid s)) :
    Saturated Phi (quotientClassLanguage Phi q) := by
  intro s x y hxy
  have hmk : (⟨s, Quotient.mk'' x⟩ : Σ t, Quotient (Phi.setoid t)) =
      ⟨s, Quotient.mk'' y⟩ :=
    (Sigma.mk.inj_iff).2 ⟨rfl, heq_of_eq (Quotient.sound hxy)⟩
  constructor
  · intro hx
    exact hmk.symm.trans hx
  · intro hy
    exact hmk.trans hy

private def congruenceListInter {S : Type} {sig : Signature S}
    {A : Algebra sig} : List (Congruence A) → Congruence A
  | [] => Congruence.top A
  | Phi :: Phis => Congruence.inter Phi (congruenceListInter Phis)

private theorem congruenceListInter_selected {S : Type} {sig : Signature S}
    (F : FiniteIndexCongruenceFormation sig) (X : SSet S)
    (Phis : List (Congruence (freeAlgebra sig X)))
    (hPhis : ∀ Phi ∈ Phis, Phi ∈ F.congruences X) :
    congruenceListInter Phis ∈ F.congruences X := by
  induction Phis with
  | nil =>
      rcases F.nonempty X with ⟨Psi, hPsi⟩
      apply F.upward_closed X hPsi
      intro s x y hxy
      trivial
  | cons Phi Phis ih =>
      apply F.inter_closed X
      · exact hPhis Phi (by simp)
      · exact ih (fun Psi hPsi => hPhis Psi (by simp [hPsi]))

private theorem congruenceListInter_le_of_mem {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phis : List (Congruence A)) (Phi : Congruence A)
    (hPhi : Phi ∈ Phis) : congruenceListInter Phis ≤ Phi := by
  induction Phis with
  | nil => simp at hPhi
  | cons Psi Phis ih =>
      simp only [List.mem_cons] at hPhi
      rcases hPhi with rfl | hPhi
      · intro s x y hxy
        exact hxy.1
      · intro s x y hxy
        exact ih hPhi s x y hxy.2

theorem solution {S : Type} [Finite S] {sig : Signature S}
    (F : FiniteIndexCongruenceFormation sig)
    (L : RegularLanguageFormation sig)
    (hL : ∀ X : SSet S, L.languages X = languagesOf F X) :
    ∀ X : SSet S, congruencesOf L X = F.congruences X := by
  intro X
  ext Phi
  constructor
  · rintro ⟨hPhiFinite, hPhiLanguages⟩
    classical
    let Q := Σ s, Quotient (Phi.setoid s)
    haveI : Finite Q := hPhiFinite
    letI : Fintype Q := Fintype.ofFinite Q
    have hWitness : ∀ q : Q, ∃ Psi : Congruence (freeAlgebra sig X),
        Psi ∈ F.congruences X ∧ Saturated Psi (quotientClassLanguage Phi q) := by
      intro q
      have hClassL : quotientClassLanguage Phi q ∈ L.languages X :=
        hPhiLanguages _ (quotientClass_saturated Phi q)
      have hClassF : quotientClassLanguage Phi q ∈ languagesOf F X := by
        rw [← hL X]
        exact hClassL
      exact hClassF
    choose Psi hPsiSelected hPsiSaturates using hWitness
    let Phis : List (Congruence (freeAlgebra sig X)) :=
      (Finset.univ : Finset Q).toList.map Psi
    have hPhisSelected : ∀ Theta ∈ Phis, Theta ∈ F.congruences X := by
      intro Theta hTheta
      rcases List.mem_map.mp hTheta with ⟨q, hq, rfl⟩
      exact hPsiSelected q
    have hMeetSelected : congruenceListInter Phis ∈ F.congruences X :=
      congruenceListInter_selected F X Phis hPhisSelected
    apply F.upward_closed X hMeetSelected
    intro s x y hxy
    let q : Q := ⟨s, Quotient.mk'' x⟩
    have hqMem : Psi q ∈ Phis := by
      apply List.mem_map.mpr
      exact ⟨q, Finset.mem_toList.mpr (Finset.mem_univ q), rfl⟩
    have hPsiXY : (Psi q).Rel s x y :=
      congruenceListInter_le_of_mem Phis (Psi q) hqMem s x y hxy
    have hxClass : x ∈ quotientClassLanguage Phi q s := rfl
    have hyClass : y ∈ quotientClassLanguage Phi q s :=
      (hPsiSaturates q s x y hPsiXY).1 hxClass
    have hQuot : (Quotient.mk'' y : Quotient (Phi.setoid s)) =
        Quotient.mk'' x := eq_of_heq ((Sigma.mk.inj_iff.mp hyClass).2)
    exact (Phi.setoid s).symm (Quotient.exact hQuot)
  · intro hPhi
    refine ⟨F.finite_index X hPhi, ?_⟩
    intro K hK
    rw [hL X]
    exact ⟨Phi, hPhi, hK⟩

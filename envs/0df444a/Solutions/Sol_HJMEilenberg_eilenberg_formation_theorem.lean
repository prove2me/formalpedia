-- Prove2me | solution 1 for HJMEilenberg.eilenberg_formation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T11:34:36.233463+00:00
-- url     : https://prove2.me/submissions/c24de807-c420-49b1-b03d-270ea9dffd8f

import Definitions.Def_HJMEilenberg_Formations
import Theorems.Thm_HJMEilenberg_congruence_to_languages
import Theorems.Thm_HJMEilenberg_languages_to_congruences
import Theorems.Thm_HJMEilenberg_recover_congruence
import Theorems.Thm_HJMEilenberg_recover_languages

open MSKleene
open HJMEilenberg

private noncomputable def languagesFrom {S : Type} [Finite S]
    {sig : Signature S} (F : FiniteIndexCongruenceFormation sig) :
    RegularLanguageFormation sig :=
  Classical.choose (congruence_to_languages F)

private theorem languagesFrom_spec {S : Type} [Finite S]
    {sig : Signature S} (F : FiniteIndexCongruenceFormation sig) :
    ∀ X : SSet S, (languagesFrom F).languages X = languagesOf F X :=
  Classical.choose_spec (congruence_to_languages F)

private noncomputable def congruencesFrom {S : Type} [Finite S]
    {sig : Signature S} (L : RegularLanguageFormation sig) :
    FiniteIndexCongruenceFormation sig :=
  Classical.choose (languages_to_congruences L)

private theorem congruencesFrom_spec {S : Type} [Finite S]
    {sig : Signature S} (L : RegularLanguageFormation sig) :
    ∀ X : SSet S, (congruencesFrom L).congruences X = congruencesOf L X :=
  Classical.choose_spec (languages_to_congruences L)

private theorem congruencesFrom_languagesFrom {S : Type} [Finite S]
    {sig : Signature S} (F : FiniteIndexCongruenceFormation sig) :
    congruencesFrom (languagesFrom F) = F := by
  apply FiniteIndexCongruenceFormation.ext
  intro X Phi
  rw [congruencesFrom_spec]
  rw [recover_congruence F (languagesFrom F) (languagesFrom_spec F) X]

private theorem languagesFrom_congruencesFrom {S : Type} [Finite S]
    {sig : Signature S} (L : RegularLanguageFormation sig) :
    languagesFrom (congruencesFrom L) = L := by
  apply RegularLanguageFormation.ext
  intro X K
  rw [languagesFrom_spec]
  rw [recover_languages L (congruencesFrom L) (congruencesFrom_spec L) X]

private theorem languagesFrom_monotone {S : Type} [Finite S]
    {sig : Signature S} : Monotone
      (languagesFrom : FiniteIndexCongruenceFormation sig →
        RegularLanguageFormation sig) := by
  intro F G hFG X K hK
  rw [languagesFrom_spec] at hK ⊢
  rcases hK with ⟨Phi, hPhi, hSat⟩
  exact ⟨Phi, hFG X hPhi, hSat⟩

private theorem congruencesFrom_monotone {S : Type} [Finite S]
    {sig : Signature S} : Monotone
      (congruencesFrom : RegularLanguageFormation sig →
        FiniteIndexCongruenceFormation sig) := by
  intro L K hLK X Phi hPhi
  rw [congruencesFrom_spec] at hPhi ⊢
  exact ⟨hPhi.1, fun M hM => hLK X (hPhi.2 M hM)⟩

theorem solution {S : Type} [Finite S] (sig : Signature S) :
    ∃ e : FiniteIndexCongruenceFormation sig ≃o
        RegularLanguageFormation sig,
      (∀ (F : FiniteIndexCongruenceFormation sig) (X : SSet S),
        (e F).languages X = languagesOf F X) ∧
      (∀ (L : RegularLanguageFormation sig) (X : SSet S),
        (e.symm L).congruences X = congruencesOf L X) := by
  let equiv : FiniteIndexCongruenceFormation sig ≃
      RegularLanguageFormation sig :=
    { toFun := languagesFrom
      invFun := congruencesFrom
      left_inv := congruencesFrom_languagesFrom
      right_inv := languagesFrom_congruencesFrom }
  let e : FiniteIndexCongruenceFormation sig ≃o
      RegularLanguageFormation sig :=
    equiv.toOrderIso languagesFrom_monotone congruencesFrom_monotone
  refine ⟨e, ?_, ?_⟩
  · intro F X
    exact languagesFrom_spec F X
  · intro L X
    exact congruencesFrom_spec L X

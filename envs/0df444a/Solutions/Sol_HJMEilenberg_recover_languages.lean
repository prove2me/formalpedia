-- Prove2me | solution 1 for HJMEilenberg.recover_languages
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T11:29:55.423577+00:00
-- url     : https://prove2.me/submissions/0e12b84a-4e25-4bdb-9b55-f275ca448d1c

import Definitions.Def_HJMEilenberg_Formations
import Theorems.Thm_HJMEilenberg_syntactic_universal

open MSKleene
open HJMEilenberg

theorem solution {S : Type} [Finite S] {sig : Signature S}
    (L : RegularLanguageFormation sig)
    (F : FiniteIndexCongruenceFormation sig)
    (hF : ∀ X : SSet S, F.congruences X = congruencesOf L X) :
    ∀ X : SSet S, languagesOf F X = L.languages X := by
  intro X
  ext K
  constructor
  · rintro ⟨Phi, hPhi, hK⟩
    have hPhi' : Phi ∈ congruencesOf L X := by
      rw [← hF X]
      exact hPhi
    exact hPhi'.2 K hK
  · intro hK
    let Omega := syntacticCongruence (freeAlgebra sig X) K
    have hOmegaSat : Saturated Omega K :=
      (syntactic_universal (freeAlgebra sig X) K).1
    have hOmega : Omega ∈ congruencesOf L X := by
      refine ⟨L.regular X hK, ?_⟩
      intro M hM
      apply L.inter_saturated X hK hK
      intro s x y hxy
      exact hM s x y hxy.1
    have hOmegaF : Omega ∈ F.congruences X := by
      rw [hF X]
      exact hOmega
    exact ⟨Omega, hOmegaF, hOmegaSat⟩

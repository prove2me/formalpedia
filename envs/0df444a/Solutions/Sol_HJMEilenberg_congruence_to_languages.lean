-- Prove2me | solution 1 for HJMEilenberg.congruence_to_languages
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T11:06:31.463977+00:00
-- url     : https://prove2.me/submissions/19779195-d269-4d99-9b19-c974991c11a1

import Definitions.Def_HJMEilenberg_Formations
import Theorems.Thm_HJMEilenberg_syntactic_universal

open MSKleene
open HJMEilenberg

theorem solution {S : Type} [Finite S] {sig : Signature S}
    (F : HJMEilenberg.FiniteIndexCongruenceFormation sig) :
    ∃ L : HJMEilenberg.RegularLanguageFormation sig,
      ∀ X : SSet S, L.languages X = HJMEilenberg.languagesOf F X := by
  let L : RegularLanguageFormation sig :=
    { languages := languagesOf F
      regular := by
        intro X K hK
        rcases hK with ⟨Phi, hPhi, hSat⟩
        unfold Regular
        apply F.finite_index X
        exact F.upward_closed X hPhi
          ((syntactic_universal (freeAlgebra sig X) K).2 Phi |>.1 hSat)
      top_saturated := by
        intro X K hSat
        rcases F.nonempty X with ⟨Phi, hPhi⟩
        refine ⟨Congruence.top (freeAlgebra sig X), ?_, hSat⟩
        apply F.upward_closed X hPhi
        intro s x y hxy
        trivial
      inter_saturated := by
        intro X K N hK hN M hSat
        rcases hK with ⟨Phi, hPhi, hKSat⟩
        rcases hN with ⟨Psi, hPsi, hNSat⟩
        have hSynK : syntacticCongruence (freeAlgebra sig X) K ∈
            F.congruences X :=
          F.upward_closed X hPhi
            ((syntactic_universal (freeAlgebra sig X) K).2 Phi |>.1 hKSat)
        have hSynN : syntacticCongruence (freeAlgebra sig X) N ∈
            F.congruences X :=
          F.upward_closed X hPsi
            ((syntactic_universal (freeAlgebra sig X) N).2 Psi |>.1 hNSat)
        exact ⟨Congruence.inter
            (syntacticCongruence (freeAlgebra sig X) K)
            (syntacticCongruence (freeAlgebra sig X) N),
          F.inter_closed X hSynK hSynN, hSat⟩
      pullback_saturated := by
        intro X Y M hM f hEpi K hSat
        rcases hM with ⟨Theta, hTheta, hMSat⟩
        have hSynM : syntacticCongruence (freeAlgebra sig Y) M ∈
            F.congruences Y :=
          F.upward_closed Y hTheta
            ((syntactic_universal (freeAlgebra sig Y) M).2 Theta |>.1 hMSat)
        exact ⟨Congruence.pullback f
            (syntacticCongruence (freeAlgebra sig Y) M),
          F.pullback_closed X Y
            (syntacticCongruence (freeAlgebra sig Y) M) hSynM f hEpi,
          hSat⟩ }
  exact ⟨L, fun X => rfl⟩

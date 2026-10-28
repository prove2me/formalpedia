-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:38:36.59792+00:00
-- url     : https://prove2.me/submissions/23e86141-8abe-495e-9425-3e041d00c97d

import Mathlib
import Definitions.Def_OAIEGC000

section
-- module Solutions.OAIEG.SeedContraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem h1_boundary_cert_60 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 60).1 j - h1Coeff (triangleEdges 60).2.1 j +
      h1Coeff (triangleEdges 60).2.2 j = if j = 60 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_61 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 61).1 j - h1Coeff (triangleEdges 61).2.1 j +
      h1Coeff (triangleEdges 61).2.2 j = if j = 61 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_62 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 62).1 j - h1Coeff (triangleEdges 62).2.1 j +
      h1Coeff (triangleEdges 62).2.2 j = if j = 62 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_63 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 63).1 j - h1Coeff (triangleEdges 63).2.1 j +
      h1Coeff (triangleEdges 63).2.2 j = if j = 63 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_64 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 64).1 j - h1Coeff (triangleEdges 64).2.1 j +
      h1Coeff (triangleEdges 64).2.2 j = if j = 64 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_65 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 65).1 j - h1Coeff (triangleEdges 65).2.1 j +
      h1Coeff (triangleEdges 65).2.2 j = if j = 65 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_66 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 66).1 j - h1Coeff (triangleEdges 66).2.1 j +
      h1Coeff (triangleEdges 66).2.2 j = if j = 66 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_67 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 67).1 j - h1Coeff (triangleEdges 67).2.1 j +
      h1Coeff (triangleEdges 67).2.2 j = if j = 67 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_68 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 68).1 j - h1Coeff (triangleEdges 68).2.1 j +
      h1Coeff (triangleEdges 68).2.2 j = if j = 68 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_69 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 69).1 j - h1Coeff (triangleEdges 69).2.1 j +
      h1Coeff (triangleEdges 69).2.2 j = if j = 69 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_70 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 70).1 j - h1Coeff (triangleEdges 70).2.1 j +
      h1Coeff (triangleEdges 70).2.2 j = if j = 70 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_71 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 71).1 j - h1Coeff (triangleEdges 71).2.1 j +
      h1Coeff (triangleEdges 71).2.2 j = if j = 71 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_72 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 72).1 j - h1Coeff (triangleEdges 72).2.1 j +
      h1Coeff (triangleEdges 72).2.2 j = if j = 72 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_73 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 73).1 j - h1Coeff (triangleEdges 73).2.1 j +
      h1Coeff (triangleEdges 73).2.2 j = if j = 73 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_74 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 74).1 j - h1Coeff (triangleEdges 74).2.1 j +
      h1Coeff (triangleEdges 74).2.2 j = if j = 74 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_75 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 75).1 j - h1Coeff (triangleEdges 75).2.1 j +
      h1Coeff (triangleEdges 75).2.2 j = if j = 75 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_76 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 76).1 j - h1Coeff (triangleEdges 76).2.1 j +
      h1Coeff (triangleEdges 76).2.2 j = if j = 76 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_77 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 77).1 j - h1Coeff (triangleEdges 77).2.1 j +
      h1Coeff (triangleEdges 77).2.2 j = if j = 77 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_78 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 78).1 j - h1Coeff (triangleEdges 78).2.1 j +
      h1Coeff (triangleEdges 78).2.2 j = if j = 78 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_79 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 79).1 j - h1Coeff (triangleEdges 79).2.1 j +
      h1Coeff (triangleEdges 79).2.2 j = if j = 79 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_80 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 80).1 j - h1Coeff (triangleEdges 80).2.1 j +
      h1Coeff (triangleEdges 80).2.2 j = if j = 80 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_81 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 81).1 j - h1Coeff (triangleEdges 81).2.1 j +
      h1Coeff (triangleEdges 81).2.2 j = if j = 81 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_82 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 82).1 j - h1Coeff (triangleEdges 82).2.1 j +
      h1Coeff (triangleEdges 82).2.2 j = if j = 82 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_83 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 83).1 j - h1Coeff (triangleEdges 83).2.1 j +
      h1Coeff (triangleEdges 83).2.2 j = if j = 83 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_84 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 84).1 j - h1Coeff (triangleEdges 84).2.1 j +
      h1Coeff (triangleEdges 84).2.2 j = if j = 84 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_85 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 85).1 j - h1Coeff (triangleEdges 85).2.1 j +
      h1Coeff (triangleEdges 85).2.2 j = if j = 85 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_86 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 86).1 j - h1Coeff (triangleEdges 86).2.1 j +
      h1Coeff (triangleEdges 86).2.2 j = if j = 86 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_87 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 87).1 j - h1Coeff (triangleEdges 87).2.1 j +
      h1Coeff (triangleEdges 87).2.2 j = if j = 87 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_88 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 88).1 j - h1Coeff (triangleEdges 88).2.1 j +
      h1Coeff (triangleEdges 88).2.2 j = if j = 88 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_89 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 89).1 j - h1Coeff (triangleEdges 89).2.1 j +
      h1Coeff (triangleEdges 89).2.2 j = if j = 89 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_blk_2_oai (t : Fin 270) (hb : 60 ≤ t.val ∧ t.val < 90) (j : Fin 270) :
    h1Coeff (triangleEdges t).1 j - h1Coeff (triangleEdges t).2.1 j +
      h1Coeff (triangleEdges t).2.2 j = if j = t then 1 else 0 := by
  rcases t with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact h1_boundary_cert_60 j
  · exact h1_boundary_cert_61 j
  · exact h1_boundary_cert_62 j
  · exact h1_boundary_cert_63 j
  · exact h1_boundary_cert_64 j
  · exact h1_boundary_cert_65 j
  · exact h1_boundary_cert_66 j
  · exact h1_boundary_cert_67 j
  · exact h1_boundary_cert_68 j
  · exact h1_boundary_cert_69 j
  · exact h1_boundary_cert_70 j
  · exact h1_boundary_cert_71 j
  · exact h1_boundary_cert_72 j
  · exact h1_boundary_cert_73 j
  · exact h1_boundary_cert_74 j
  · exact h1_boundary_cert_75 j
  · exact h1_boundary_cert_76 j
  · exact h1_boundary_cert_77 j
  · exact h1_boundary_cert_78 j
  · exact h1_boundary_cert_79 j
  · exact h1_boundary_cert_80 j
  · exact h1_boundary_cert_81 j
  · exact h1_boundary_cert_82 j
  · exact h1_boundary_cert_83 j
  · exact h1_boundary_cert_84 j
  · exact h1_boundary_cert_85 j
  · exact h1_boundary_cert_86 j
  · exact h1_boundary_cert_87 j
  · exact h1_boundary_cert_88 j
  · exact h1_boundary_cert_89 j

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_2_oai := @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_2_oai

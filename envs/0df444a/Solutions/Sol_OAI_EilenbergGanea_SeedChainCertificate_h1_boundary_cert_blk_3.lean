-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:40:03.421322+00:00
-- url     : https://prove2.me/submissions/3b62f1a4-4ae2-4a20-8f3e-0822fa2d8ef0

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

theorem h1_boundary_cert_90 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 90).1 j - h1Coeff (triangleEdges 90).2.1 j +
      h1Coeff (triangleEdges 90).2.2 j = if j = 90 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_91 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 91).1 j - h1Coeff (triangleEdges 91).2.1 j +
      h1Coeff (triangleEdges 91).2.2 j = if j = 91 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_92 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 92).1 j - h1Coeff (triangleEdges 92).2.1 j +
      h1Coeff (triangleEdges 92).2.2 j = if j = 92 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_93 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 93).1 j - h1Coeff (triangleEdges 93).2.1 j +
      h1Coeff (triangleEdges 93).2.2 j = if j = 93 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_94 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 94).1 j - h1Coeff (triangleEdges 94).2.1 j +
      h1Coeff (triangleEdges 94).2.2 j = if j = 94 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_95 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 95).1 j - h1Coeff (triangleEdges 95).2.1 j +
      h1Coeff (triangleEdges 95).2.2 j = if j = 95 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_96 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 96).1 j - h1Coeff (triangleEdges 96).2.1 j +
      h1Coeff (triangleEdges 96).2.2 j = if j = 96 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_97 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 97).1 j - h1Coeff (triangleEdges 97).2.1 j +
      h1Coeff (triangleEdges 97).2.2 j = if j = 97 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_98 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 98).1 j - h1Coeff (triangleEdges 98).2.1 j +
      h1Coeff (triangleEdges 98).2.2 j = if j = 98 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_99 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 99).1 j - h1Coeff (triangleEdges 99).2.1 j +
      h1Coeff (triangleEdges 99).2.2 j = if j = 99 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_100 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 100).1 j - h1Coeff (triangleEdges 100).2.1 j +
      h1Coeff (triangleEdges 100).2.2 j = if j = 100 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_101 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 101).1 j - h1Coeff (triangleEdges 101).2.1 j +
      h1Coeff (triangleEdges 101).2.2 j = if j = 101 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_102 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 102).1 j - h1Coeff (triangleEdges 102).2.1 j +
      h1Coeff (triangleEdges 102).2.2 j = if j = 102 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_103 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 103).1 j - h1Coeff (triangleEdges 103).2.1 j +
      h1Coeff (triangleEdges 103).2.2 j = if j = 103 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_104 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 104).1 j - h1Coeff (triangleEdges 104).2.1 j +
      h1Coeff (triangleEdges 104).2.2 j = if j = 104 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_105 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 105).1 j - h1Coeff (triangleEdges 105).2.1 j +
      h1Coeff (triangleEdges 105).2.2 j = if j = 105 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_106 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 106).1 j - h1Coeff (triangleEdges 106).2.1 j +
      h1Coeff (triangleEdges 106).2.2 j = if j = 106 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_107 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 107).1 j - h1Coeff (triangleEdges 107).2.1 j +
      h1Coeff (triangleEdges 107).2.2 j = if j = 107 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_108 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 108).1 j - h1Coeff (triangleEdges 108).2.1 j +
      h1Coeff (triangleEdges 108).2.2 j = if j = 108 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_109 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 109).1 j - h1Coeff (triangleEdges 109).2.1 j +
      h1Coeff (triangleEdges 109).2.2 j = if j = 109 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_110 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 110).1 j - h1Coeff (triangleEdges 110).2.1 j +
      h1Coeff (triangleEdges 110).2.2 j = if j = 110 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_111 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 111).1 j - h1Coeff (triangleEdges 111).2.1 j +
      h1Coeff (triangleEdges 111).2.2 j = if j = 111 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_112 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 112).1 j - h1Coeff (triangleEdges 112).2.1 j +
      h1Coeff (triangleEdges 112).2.2 j = if j = 112 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_113 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 113).1 j - h1Coeff (triangleEdges 113).2.1 j +
      h1Coeff (triangleEdges 113).2.2 j = if j = 113 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_114 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 114).1 j - h1Coeff (triangleEdges 114).2.1 j +
      h1Coeff (triangleEdges 114).2.2 j = if j = 114 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_115 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 115).1 j - h1Coeff (triangleEdges 115).2.1 j +
      h1Coeff (triangleEdges 115).2.2 j = if j = 115 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_116 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 116).1 j - h1Coeff (triangleEdges 116).2.1 j +
      h1Coeff (triangleEdges 116).2.2 j = if j = 116 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_117 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 117).1 j - h1Coeff (triangleEdges 117).2.1 j +
      h1Coeff (triangleEdges 117).2.2 j = if j = 117 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_118 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 118).1 j - h1Coeff (triangleEdges 118).2.1 j +
      h1Coeff (triangleEdges 118).2.2 j = if j = 118 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_119 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 119).1 j - h1Coeff (triangleEdges 119).2.1 j +
      h1Coeff (triangleEdges 119).2.2 j = if j = 119 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_blk_3_oai (t : Fin 270) (hb : 90 ≤ t.val ∧ t.val < 120) (j : Fin 270) :
    h1Coeff (triangleEdges t).1 j - h1Coeff (triangleEdges t).2.1 j +
      h1Coeff (triangleEdges t).2.2 j = if j = t then 1 else 0 := by
  rcases t with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact h1_boundary_cert_90 j
  · exact h1_boundary_cert_91 j
  · exact h1_boundary_cert_92 j
  · exact h1_boundary_cert_93 j
  · exact h1_boundary_cert_94 j
  · exact h1_boundary_cert_95 j
  · exact h1_boundary_cert_96 j
  · exact h1_boundary_cert_97 j
  · exact h1_boundary_cert_98 j
  · exact h1_boundary_cert_99 j
  · exact h1_boundary_cert_100 j
  · exact h1_boundary_cert_101 j
  · exact h1_boundary_cert_102 j
  · exact h1_boundary_cert_103 j
  · exact h1_boundary_cert_104 j
  · exact h1_boundary_cert_105 j
  · exact h1_boundary_cert_106 j
  · exact h1_boundary_cert_107 j
  · exact h1_boundary_cert_108 j
  · exact h1_boundary_cert_109 j
  · exact h1_boundary_cert_110 j
  · exact h1_boundary_cert_111 j
  · exact h1_boundary_cert_112 j
  · exact h1_boundary_cert_113 j
  · exact h1_boundary_cert_114 j
  · exact h1_boundary_cert_115 j
  · exact h1_boundary_cert_116 j
  · exact h1_boundary_cert_117 j
  · exact h1_boundary_cert_118 j
  · exact h1_boundary_cert_119 j

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_3_oai := @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_3_oai

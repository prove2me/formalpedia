-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:40:47.034988+00:00
-- url     : https://prove2.me/submissions/032e7883-0140-4dc1-9b26-aeb0c28188a1

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

theorem h1_boundary_cert_120 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 120).1 j - h1Coeff (triangleEdges 120).2.1 j +
      h1Coeff (triangleEdges 120).2.2 j = if j = 120 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_121 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 121).1 j - h1Coeff (triangleEdges 121).2.1 j +
      h1Coeff (triangleEdges 121).2.2 j = if j = 121 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_122 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 122).1 j - h1Coeff (triangleEdges 122).2.1 j +
      h1Coeff (triangleEdges 122).2.2 j = if j = 122 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_123 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 123).1 j - h1Coeff (triangleEdges 123).2.1 j +
      h1Coeff (triangleEdges 123).2.2 j = if j = 123 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_124 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 124).1 j - h1Coeff (triangleEdges 124).2.1 j +
      h1Coeff (triangleEdges 124).2.2 j = if j = 124 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_125 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 125).1 j - h1Coeff (triangleEdges 125).2.1 j +
      h1Coeff (triangleEdges 125).2.2 j = if j = 125 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_126 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 126).1 j - h1Coeff (triangleEdges 126).2.1 j +
      h1Coeff (triangleEdges 126).2.2 j = if j = 126 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_127 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 127).1 j - h1Coeff (triangleEdges 127).2.1 j +
      h1Coeff (triangleEdges 127).2.2 j = if j = 127 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_128 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 128).1 j - h1Coeff (triangleEdges 128).2.1 j +
      h1Coeff (triangleEdges 128).2.2 j = if j = 128 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_129 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 129).1 j - h1Coeff (triangleEdges 129).2.1 j +
      h1Coeff (triangleEdges 129).2.2 j = if j = 129 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_130 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 130).1 j - h1Coeff (triangleEdges 130).2.1 j +
      h1Coeff (triangleEdges 130).2.2 j = if j = 130 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_131 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 131).1 j - h1Coeff (triangleEdges 131).2.1 j +
      h1Coeff (triangleEdges 131).2.2 j = if j = 131 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_132 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 132).1 j - h1Coeff (triangleEdges 132).2.1 j +
      h1Coeff (triangleEdges 132).2.2 j = if j = 132 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_133 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 133).1 j - h1Coeff (triangleEdges 133).2.1 j +
      h1Coeff (triangleEdges 133).2.2 j = if j = 133 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_134 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 134).1 j - h1Coeff (triangleEdges 134).2.1 j +
      h1Coeff (triangleEdges 134).2.2 j = if j = 134 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_135 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 135).1 j - h1Coeff (triangleEdges 135).2.1 j +
      h1Coeff (triangleEdges 135).2.2 j = if j = 135 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_136 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 136).1 j - h1Coeff (triangleEdges 136).2.1 j +
      h1Coeff (triangleEdges 136).2.2 j = if j = 136 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_137 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 137).1 j - h1Coeff (triangleEdges 137).2.1 j +
      h1Coeff (triangleEdges 137).2.2 j = if j = 137 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_138 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 138).1 j - h1Coeff (triangleEdges 138).2.1 j +
      h1Coeff (triangleEdges 138).2.2 j = if j = 138 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_139 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 139).1 j - h1Coeff (triangleEdges 139).2.1 j +
      h1Coeff (triangleEdges 139).2.2 j = if j = 139 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_140 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 140).1 j - h1Coeff (triangleEdges 140).2.1 j +
      h1Coeff (triangleEdges 140).2.2 j = if j = 140 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_141 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 141).1 j - h1Coeff (triangleEdges 141).2.1 j +
      h1Coeff (triangleEdges 141).2.2 j = if j = 141 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_142 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 142).1 j - h1Coeff (triangleEdges 142).2.1 j +
      h1Coeff (triangleEdges 142).2.2 j = if j = 142 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_143 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 143).1 j - h1Coeff (triangleEdges 143).2.1 j +
      h1Coeff (triangleEdges 143).2.2 j = if j = 143 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_144 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 144).1 j - h1Coeff (triangleEdges 144).2.1 j +
      h1Coeff (triangleEdges 144).2.2 j = if j = 144 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_145 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 145).1 j - h1Coeff (triangleEdges 145).2.1 j +
      h1Coeff (triangleEdges 145).2.2 j = if j = 145 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_146 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 146).1 j - h1Coeff (triangleEdges 146).2.1 j +
      h1Coeff (triangleEdges 146).2.2 j = if j = 146 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_147 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 147).1 j - h1Coeff (triangleEdges 147).2.1 j +
      h1Coeff (triangleEdges 147).2.2 j = if j = 147 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_148 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 148).1 j - h1Coeff (triangleEdges 148).2.1 j +
      h1Coeff (triangleEdges 148).2.2 j = if j = 148 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_149 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 149).1 j - h1Coeff (triangleEdges 149).2.1 j +
      h1Coeff (triangleEdges 149).2.2 j = if j = 149 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_blk_4_oai (t : Fin 270) (hb : 120 ≤ t.val ∧ t.val < 150) (j : Fin 270) :
    h1Coeff (triangleEdges t).1 j - h1Coeff (triangleEdges t).2.1 j +
      h1Coeff (triangleEdges t).2.2 j = if j = t then 1 else 0 := by
  rcases t with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact h1_boundary_cert_120 j
  · exact h1_boundary_cert_121 j
  · exact h1_boundary_cert_122 j
  · exact h1_boundary_cert_123 j
  · exact h1_boundary_cert_124 j
  · exact h1_boundary_cert_125 j
  · exact h1_boundary_cert_126 j
  · exact h1_boundary_cert_127 j
  · exact h1_boundary_cert_128 j
  · exact h1_boundary_cert_129 j
  · exact h1_boundary_cert_130 j
  · exact h1_boundary_cert_131 j
  · exact h1_boundary_cert_132 j
  · exact h1_boundary_cert_133 j
  · exact h1_boundary_cert_134 j
  · exact h1_boundary_cert_135 j
  · exact h1_boundary_cert_136 j
  · exact h1_boundary_cert_137 j
  · exact h1_boundary_cert_138 j
  · exact h1_boundary_cert_139 j
  · exact h1_boundary_cert_140 j
  · exact h1_boundary_cert_141 j
  · exact h1_boundary_cert_142 j
  · exact h1_boundary_cert_143 j
  · exact h1_boundary_cert_144 j
  · exact h1_boundary_cert_145 j
  · exact h1_boundary_cert_146 j
  · exact h1_boundary_cert_147 j
  · exact h1_boundary_cert_148 j
  · exact h1_boundary_cert_149 j

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_4_oai := @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_4_oai

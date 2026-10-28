-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:42:15.689495+00:00
-- url     : https://prove2.me/submissions/d6e153ed-0e10-408d-9320-505ba00cdf41

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

theorem h1_boundary_cert_180 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 180).1 j - h1Coeff (triangleEdges 180).2.1 j +
      h1Coeff (triangleEdges 180).2.2 j = if j = 180 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_181 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 181).1 j - h1Coeff (triangleEdges 181).2.1 j +
      h1Coeff (triangleEdges 181).2.2 j = if j = 181 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_182 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 182).1 j - h1Coeff (triangleEdges 182).2.1 j +
      h1Coeff (triangleEdges 182).2.2 j = if j = 182 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_183 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 183).1 j - h1Coeff (triangleEdges 183).2.1 j +
      h1Coeff (triangleEdges 183).2.2 j = if j = 183 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_184 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 184).1 j - h1Coeff (triangleEdges 184).2.1 j +
      h1Coeff (triangleEdges 184).2.2 j = if j = 184 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_185 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 185).1 j - h1Coeff (triangleEdges 185).2.1 j +
      h1Coeff (triangleEdges 185).2.2 j = if j = 185 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_186 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 186).1 j - h1Coeff (triangleEdges 186).2.1 j +
      h1Coeff (triangleEdges 186).2.2 j = if j = 186 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_187 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 187).1 j - h1Coeff (triangleEdges 187).2.1 j +
      h1Coeff (triangleEdges 187).2.2 j = if j = 187 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_188 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 188).1 j - h1Coeff (triangleEdges 188).2.1 j +
      h1Coeff (triangleEdges 188).2.2 j = if j = 188 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_189 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 189).1 j - h1Coeff (triangleEdges 189).2.1 j +
      h1Coeff (triangleEdges 189).2.2 j = if j = 189 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_190 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 190).1 j - h1Coeff (triangleEdges 190).2.1 j +
      h1Coeff (triangleEdges 190).2.2 j = if j = 190 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_191 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 191).1 j - h1Coeff (triangleEdges 191).2.1 j +
      h1Coeff (triangleEdges 191).2.2 j = if j = 191 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_192 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 192).1 j - h1Coeff (triangleEdges 192).2.1 j +
      h1Coeff (triangleEdges 192).2.2 j = if j = 192 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_193 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 193).1 j - h1Coeff (triangleEdges 193).2.1 j +
      h1Coeff (triangleEdges 193).2.2 j = if j = 193 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_194 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 194).1 j - h1Coeff (triangleEdges 194).2.1 j +
      h1Coeff (triangleEdges 194).2.2 j = if j = 194 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_195 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 195).1 j - h1Coeff (triangleEdges 195).2.1 j +
      h1Coeff (triangleEdges 195).2.2 j = if j = 195 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_196 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 196).1 j - h1Coeff (triangleEdges 196).2.1 j +
      h1Coeff (triangleEdges 196).2.2 j = if j = 196 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_197 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 197).1 j - h1Coeff (triangleEdges 197).2.1 j +
      h1Coeff (triangleEdges 197).2.2 j = if j = 197 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_198 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 198).1 j - h1Coeff (triangleEdges 198).2.1 j +
      h1Coeff (triangleEdges 198).2.2 j = if j = 198 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_199 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 199).1 j - h1Coeff (triangleEdges 199).2.1 j +
      h1Coeff (triangleEdges 199).2.2 j = if j = 199 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_200 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 200).1 j - h1Coeff (triangleEdges 200).2.1 j +
      h1Coeff (triangleEdges 200).2.2 j = if j = 200 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_201 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 201).1 j - h1Coeff (triangleEdges 201).2.1 j +
      h1Coeff (triangleEdges 201).2.2 j = if j = 201 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_202 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 202).1 j - h1Coeff (triangleEdges 202).2.1 j +
      h1Coeff (triangleEdges 202).2.2 j = if j = 202 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_203 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 203).1 j - h1Coeff (triangleEdges 203).2.1 j +
      h1Coeff (triangleEdges 203).2.2 j = if j = 203 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_204 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 204).1 j - h1Coeff (triangleEdges 204).2.1 j +
      h1Coeff (triangleEdges 204).2.2 j = if j = 204 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_205 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 205).1 j - h1Coeff (triangleEdges 205).2.1 j +
      h1Coeff (triangleEdges 205).2.2 j = if j = 205 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_206 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 206).1 j - h1Coeff (triangleEdges 206).2.1 j +
      h1Coeff (triangleEdges 206).2.2 j = if j = 206 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_207 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 207).1 j - h1Coeff (triangleEdges 207).2.1 j +
      h1Coeff (triangleEdges 207).2.2 j = if j = 207 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_208 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 208).1 j - h1Coeff (triangleEdges 208).2.1 j +
      h1Coeff (triangleEdges 208).2.2 j = if j = 208 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_209 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 209).1 j - h1Coeff (triangleEdges 209).2.1 j +
      h1Coeff (triangleEdges 209).2.2 j = if j = 209 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_blk_6_oai (t : Fin 270) (hb : 180 ≤ t.val ∧ t.val < 210) (j : Fin 270) :
    h1Coeff (triangleEdges t).1 j - h1Coeff (triangleEdges t).2.1 j +
      h1Coeff (triangleEdges t).2.2 j = if j = t then 1 else 0 := by
  rcases t with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact h1_boundary_cert_180 j
  · exact h1_boundary_cert_181 j
  · exact h1_boundary_cert_182 j
  · exact h1_boundary_cert_183 j
  · exact h1_boundary_cert_184 j
  · exact h1_boundary_cert_185 j
  · exact h1_boundary_cert_186 j
  · exact h1_boundary_cert_187 j
  · exact h1_boundary_cert_188 j
  · exact h1_boundary_cert_189 j
  · exact h1_boundary_cert_190 j
  · exact h1_boundary_cert_191 j
  · exact h1_boundary_cert_192 j
  · exact h1_boundary_cert_193 j
  · exact h1_boundary_cert_194 j
  · exact h1_boundary_cert_195 j
  · exact h1_boundary_cert_196 j
  · exact h1_boundary_cert_197 j
  · exact h1_boundary_cert_198 j
  · exact h1_boundary_cert_199 j
  · exact h1_boundary_cert_200 j
  · exact h1_boundary_cert_201 j
  · exact h1_boundary_cert_202 j
  · exact h1_boundary_cert_203 j
  · exact h1_boundary_cert_204 j
  · exact h1_boundary_cert_205 j
  · exact h1_boundary_cert_206 j
  · exact h1_boundary_cert_207 j
  · exact h1_boundary_cert_208 j
  · exact h1_boundary_cert_209 j

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_6_oai := @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_6_oai

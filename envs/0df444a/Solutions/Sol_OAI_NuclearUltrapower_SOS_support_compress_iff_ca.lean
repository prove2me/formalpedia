-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.support_compress_iff_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:59:08.958753+00:00
-- url     : https://prove2.me/submissions/3058591d-a6c0-40e8-bb82-df408bc14397

import Mathlib
import Definitions.Def_OAIQ229C012
import Definitions.Def_OAIQ229C015

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

theorem support_addHead_iff (p : α × ℤ) (ps : Poly α) (g : α) :
    g ∈ (addHead p ps).map Prod.fst ↔ g = p.1 ∨ g ∈ ps.map Prod.fst := by
  cases ps with
  | nil => simp [addHead]
  | cons q qs =>
    simp only [addHead]
    split_ifs with h <;> simp_all

theorem support_compress_iff_ca_oai (ps : Poly α) (g : α) :
    g ∈ (compress ps).map Prod.fst ↔ g ∈ ps.map Prod.fst := by
  induction ps with
  | nil => simp [compress]
  | cons p ps ih => simp only [compress, support_addHead_iff, ih, List.map_cons, List.mem_cons]

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.support_compress_iff_ca_oai.{u_1} := @OAI.NuclearUltrapower.SOS.support_compress_iff_ca_oai.{u_1}

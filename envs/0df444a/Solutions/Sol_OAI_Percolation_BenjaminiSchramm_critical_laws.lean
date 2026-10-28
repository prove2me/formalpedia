-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.critical_laws
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:19:41.133351+00:00
-- url     : https://prove2.me/submissions/82e4cdd9-3216-44f9-b31d-0477ced71c12

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B000
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_full_application_gap_bs
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_subdivision_gap_input_proved_bs

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm
universe u v
variable {V : Type u} {E : Type v} [Infinite V]

theorem critical_laws_oai
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : CriticalLawsConclusion G :=
  (full_application_gap_bs G hc hl hq hh (subdivision_gap_input_proved_bs G hc hl hq hh)).2

end Percolation.BenjaminiSchramm

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Percolation.BenjaminiSchramm.critical_laws_oai.{u, v} := @OAI.Percolation.BenjaminiSchramm.critical_laws_oai.{u, v}

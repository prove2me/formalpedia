-- Prove2me | solution 1 for GlobalTheory.OmAStab.continuous_invT_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:17.554323+00:00
-- url     : https://prove2.me/submissions/87690a35-821e-4a29-bd7d-7ff5392c0848

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM
open GlobalTheory GlobalTheory.OmAStab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.OmAStab
theorem _root_.solution {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => (invT h).val :=
  (Units.continuous_coe_inv (M := Matrix D D k)).matrix_transpose
end GlobalTheory.OmAStab

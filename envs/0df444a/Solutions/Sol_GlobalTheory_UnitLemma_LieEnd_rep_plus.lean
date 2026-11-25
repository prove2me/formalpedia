-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.rep_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:31.337481+00:00
-- url     : https://prove2.me/submissions/6b6ce7ac-39ff-44b7-831e-0816e12e06f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ}
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution (B : InvAlg K) (k : B.Cl) : B.Plus k.rep := ⟨Units.isUnit _, (Quot.out k).2⟩
end GlobalTheory.UnitLemma.LieEnd

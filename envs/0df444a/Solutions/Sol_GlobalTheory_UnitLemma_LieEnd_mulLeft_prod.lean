-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.mulLeft_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:27.184138+00:00
-- url     : https://prove2.me/submissions/49980312-1880-4cdb-a240-e14fb942314d

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
theorem _root_.solution (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    LinearMap.mulLeft K.E x = (LinearMap.mulLeft K.E x.1).prodMap (LinearMap.mulLeft K.E x.2) := LinearMap.ext fun y => Prod.ext (by simp) (by simp)
end GlobalTheory.UnitLemma.LieEnd

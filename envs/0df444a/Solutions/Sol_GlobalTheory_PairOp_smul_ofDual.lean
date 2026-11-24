-- Prove2me | solution 1 for GlobalTheory.PairOp.smul_ofDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:41.433707+00:00
-- url     : https://prove2.me/submissions/4898178e-ef99-4bab-b844-08215ae426dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.PairOp
theorem _root_.solution (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (c : 𝓀[k]ˣ)
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) :
    c • ofDual L f = ofDual L ⟨(c : 𝓀[k]) • f.1, smul_ne_zero c.ne_zero f.2⟩ := rfl
end GlobalTheory.PairOp

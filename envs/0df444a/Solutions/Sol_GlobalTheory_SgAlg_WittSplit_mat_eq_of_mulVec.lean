-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.mat_eq_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:42.062831+00:00
-- url     : https://prove2.me/submissions/07b3c06b-bd22-4115-8342-c71ff83e1916

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution {p q : Type} [Fintype q] [DecidableEq q] (M N : Matrix p q F)
    (h : ∀ c, M *ᵥ c = N *ᵥ c) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun c => by simpa [Matrix.toLin'_apply] using h c)
end GlobalTheory.SgAlg.WittSplit

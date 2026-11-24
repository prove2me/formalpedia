-- Prove2me | solution 1 for GlobalTheory.UTrans.le_awayLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:42.382493+00:00
-- url     : https://prove2.me/submissions/b365a177-aae7-47a5-90fb-5e11443ccc0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidAdjustIntegralAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory GlobalTheory.UTrans
namespace GlobalTheory.UTrans
theorem _root_.solution {V : Type} [AddCommGroup V] (L : AddSubgroup V) (b : ℕ) {v : V} (h : v ∈ L) :
    v ∈ awayLoc L b := ⟨1, by simp, by simpa using h⟩
end GlobalTheory.UTrans

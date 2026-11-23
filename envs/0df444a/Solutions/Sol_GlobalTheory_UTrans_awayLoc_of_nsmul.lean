-- Prove2me | solution 1 for GlobalTheory.UTrans.awayLoc_of_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:06.579983+00:00
-- url     : https://prove2.me/submissions/15a57afb-2b13-48bf-8ee5-1665e3bc283d

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
theorem _root_.solution {V : Type} [AddCommGroup V] (L : AddSubgroup V) {b K : ℕ} (hK : K.Coprime b) {v : V}
    (h : K • v ∈ awayLoc L b) : v ∈ awayLoc L b := by
  obtain ⟨K', hK', h⟩ := h
  exact ⟨K' * K, Nat.Coprime.mul_left hK' hK, by rwa [mul_smul]⟩
end GlobalTheory.UTrans

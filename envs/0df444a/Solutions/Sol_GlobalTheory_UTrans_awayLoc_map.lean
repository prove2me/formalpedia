-- Prove2me | solution 1 for GlobalTheory.UTrans.awayLoc_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:40.961175+00:00
-- url     : https://prove2.me/submissions/704c6a26-97dc-46c1-810c-47370df9c847

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidAdjustIntegralAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocal
import Theorems.Thm_GlobalTheory_UTrans_awayLoc_of_nsmul

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
theorem _root_.solution {V : Type} [AddCommGroup V] (L : AddSubgroup V) (b : ℕ) (f : V → V)
    (hf : ∀ (K : ℕ) v, f (K • v) = K • f v) (h : ∀ v ∈ L, f v ∈ awayLoc L b) :
    ∀ v ∈ awayLoc L b, f v ∈ awayLoc L b := by
  rintro v ⟨K, hK, hv⟩
  exact awayLoc_of_nsmul L hK (hf K v ▸ h _ hv)
end GlobalTheory.UTrans

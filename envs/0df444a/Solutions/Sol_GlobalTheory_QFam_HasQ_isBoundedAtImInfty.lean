-- Prove2me | solution 1 for GlobalTheory.QFam.HasQ.isBoundedAtImInfty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:15:36.6748+00:00
-- url     : https://prove2.me/submissions/1a9f56fa-be84-4e4b-903e-69eb0fa3812e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInfty
import Theorems.Thm_GlobalTheory_HasQExpansion_isBoundedAtImInfty
import Theorems.Thm_GlobalTheory_QFam_hasQ_powerSeries_bridge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
namespace HasQ
theorem _root_.solution {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N) (h : HasQ N f a) :
    UpperHalfPlane.IsBoundedAtImInfty f :=
  (hasQ_powerSeries_bridge.1 N f a |>.1 h).isBoundedAtImInfty (Nat.cast_pos.mpr hN)
end HasQ
end GlobalTheory.QFam

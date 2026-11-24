-- Prove2me | solution 1 for GlobalTheory.BK.invE_le_RpiE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:22.366659+00:00
-- url     : https://prove2.me/submissions/7fd559cc-2ccb-46d0-bd8b-8513a88e7b21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Theorems.Thm_GlobalTheory_BK_away_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ)
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
variable [NeZero e] [CompleteSpace K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution {B : Subalgebra O K⟦X⟧} [HasU B] (h : B ≤ Rpi O K l e) :
    invE l e B ≤ RpiE O K l e := away_mono h rfl
end GlobalTheory.BK

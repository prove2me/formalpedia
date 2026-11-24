-- Prove2me | solution 1 for GlobalTheory.BK.mem_tot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:34:52.533836+00:00
-- url     : https://prove2.me/submissions/6ddead71-e25a-49a4-88f4-67bc6e528e8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec

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
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [Algebra O K] {a : ℕ} {ι : Type}
namespace GlobalTheory.BK
theorem _root_.solution {B : Subalgebra O K⟦X⟧} {P : ZMod a → Submodule B (ι → K⟦X⟧)} {v : Vec K a ι} :
    v ∈ tot P ↔ ∀ τ, v τ ∈ P τ := by simp [tot]
end GlobalTheory.BK

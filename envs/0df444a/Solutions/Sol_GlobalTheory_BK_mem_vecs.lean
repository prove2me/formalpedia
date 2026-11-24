-- Prove2me | solution 1 for GlobalTheory.BK.mem_vecs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:41.696494+00:00
-- url     : https://prove2.me/submissions/97399379-2ad2-45f5-91f2-1ef46463e139

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
theorem _root_.solution {B : Subalgebra O K⟦X⟧} {v : ι → K⟦X⟧} : v ∈ vecs ι B ↔ ∀ i, v i ∈ B := Iff.rfl
end GlobalTheory.BK

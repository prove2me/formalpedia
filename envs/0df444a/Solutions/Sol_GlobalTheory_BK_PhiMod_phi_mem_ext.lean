-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.phi_mem_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:02:00.687145+00:00
-- url     : https://prove2.me/submissions/cd102a2f-8f16-4a1d-81cc-f342ebf5aa45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_mem_tot

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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
open GlobalTheory.BK.PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {B : Subalgebra O K⟦X⟧} (hB : ∀ f ∈ B, frob K l f ∈ B) {v : Vec K a ι}
    (hv : v ∈ P.Mext B) : P.phi v ∈ P.ext B :=
  mem_tot.2 fun τ => P.mem_extc.2 ⟨_, fun i => hB _ (mem_tot.1 hv (τ - 1) i), rfl⟩
end GlobalTheory.BK.PhiMod

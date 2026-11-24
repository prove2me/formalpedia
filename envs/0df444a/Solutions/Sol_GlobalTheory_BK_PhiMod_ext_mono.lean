-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.ext_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:45:19.166473+00:00
-- url     : https://prove2.me/submissions/d8c5e1d2-75e0-46e0-bbca-c709d3265d03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
omit [Fact l.Prime]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {v : Vec K a ι} (hv : v ∈ P.ext B) :
    v ∈ P.ext B' := mem_tot.2 fun τ => P.mem_extc_iff.2 fun i =>
      h (P.mem_extc_iff.1 (mem_tot.1 hv τ) i)
end GlobalTheory.BK.PhiMod

-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.Mext_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:54:05.0785+00:00
-- url     : https://prove2.me/submissions/3d68d311-55c9-459b-b47a-3deb2d31e79d

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
theorem _root_.solution {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {v : Vec K a ι} (hv : v ∈ P.Mext B) :
    v ∈ P.Mext B' := mem_tot.2 fun τ i => h (mem_tot.1 hv τ i)
end GlobalTheory.BK.PhiMod

-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.smul_tot_mem_Mext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:54:06.104349+00:00
-- url     : https://prove2.me/submissions/85470af6-67c4-491e-9825-9769a86595fd

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
theorem _root_.solution {B : Subalgebra O K⟦X⟧} {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ B)
    {v : Vec K a ι} (hv : v ∈ P.Mext B) : f • v ∈ P.Mext B :=
  mem_tot.2 fun τ i => B.mul_mem (hf τ) (mem_tot.1 hv τ i)
end GlobalTheory.BK.PhiMod

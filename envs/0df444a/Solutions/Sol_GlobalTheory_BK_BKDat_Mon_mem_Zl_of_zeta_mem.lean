-- Prove2me | solution 1 for GlobalTheory.BK.BKDat.Mon_mem_Zl_of_zeta_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:59.118736+00:00
-- url     : https://prove2.me/submissions/cec8c4da-3749-47f0-8bed-06847ea3a353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_BKDat_smul_mem_Mext
import Theorems.Thm_GlobalTheory_BK_Descent_Mon_mem_invariants
import Theorems.Thm_GlobalTheory_BK_PhiMod_Mext_mono
import Theorems.Thm_GlobalTheory_BK_mem_divE


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
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
open GlobalTheory.BK.BKDat
variable (D : BKDat O K l e a ι η H)
namespace GlobalTheory.BK.BKDat
theorem _root_.solution {y : Vec K a ι} (hy : y ∈ D.Yl)
    (hz : D.zeta y ∈ D.ext (Rpi O K l e)) : D.Mon y ∈ D.Zl := by
  refine ⟨⟨_, sub_mem (D.EN_mem_divE ?_) ?_, rfl⟩, D.desc.Mon_mem_invariants hy.2⟩
  · exact D.Mext_mono (invL_A_le_Rpi l e) hy.1
  · rw [mem_divE, Module.End.mul_apply, mulV_apply, smul_comm]
    exact D.smul_mem_Man (E_mem l e _) (D.smul_mem_Mext (A_le_Rpi l e) hz)
end GlobalTheory.BK.BKDat

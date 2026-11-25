-- Prove2me | solution 1 for GlobalTheory.BK.BKDat.smul_mem_Mext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:29.795405+00:00
-- url     : https://prove2.me/submissions/d6f36d8a-878b-47f2-aba4-79306cf307b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_mem_M
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_mem_L
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_mem_Mext_of_basis


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
omit [NeZero e]
namespace GlobalTheory.BK.BKDat
theorem _root_.solution {B : Subalgebra O K⟦X⟧} (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ D.ext B) :
    E K l e ^ η • m ∈ D.Mext B :=
  D.smul_mem_Mext_of_basis (fun i => D.upper _ (D.phi_mem_L (D.bas_mem_M i))) hB hm
end GlobalTheory.BK.BKDat

-- Prove2me | solution 1 for GlobalTheory.BK.mem_shiftE_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:05.712961+00:00
-- url     : https://prove2.me/submissions/5ff46720-53bc-404b-ab5a-2c8d45fdbd86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Ezpow_mem_invL_A_iff
import Theorems.Thm_GlobalTheory_BK_Ezpow_add
import Theorems.Thm_GlobalTheory_BK_Rot_invL


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
omit [NeZero a] [TameDescentExponentData K l e a]
namespace GlobalTheory.BK
theorem _root_.solution {P : PhiMod O K l e a ι} {i k : ℤ} (h : i ≤ k) {v : Vec K a ι}
    (hv : v ∈ shiftE l e k (P.Mext (invL l (A O K)))) :
    v ∈ shiftE l e i (P.Mext (invL l (A O K))) := by
  have := (P.Mext (invL l (A O K))).smul_mem
    ⟨_, (Ezpow_mem_invL_A_iff (e := e)).2 (sub_nonneg.2 h)⟩ hv
  rwa [Subalgebra.smul_def, smul_smul, ← Ezpow_add, show k - i + -k = -i by ring] at this
end GlobalTheory.BK

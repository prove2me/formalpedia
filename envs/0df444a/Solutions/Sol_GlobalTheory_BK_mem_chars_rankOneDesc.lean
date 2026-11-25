-- Prove2me | solution 1 for GlobalTheory.BK.mem_chars_rankOneDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:54.610885+00:00
-- url     : https://prove2.me/submissions/1d8b7c18-8e3b-4ac4-8b27-1d25597d91a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_algebraMap_omegaOne
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
omit [NeZero a] [TameDescentExponentData K l e a]
variable [TameDescentExponentData K l e 1]
namespace GlobalTheory.BK
theorem _root_.solution (j : ℤ) (c : ZMod e) :
    c ∈ (rankOneDesc (K := K) (l := l) j (omegaOne O ^ c.val)).chars 0 := by
  refine ⟨fun _ _ => 1, fun h => one_ne_zero (congrFun h ()), fun ζ => funext fun i => ?_⟩
  refine (congrArg constantCoeff (rankOneDesc_act j _ _ _ 0)).trans ?_
  simp [algebraMap_omegaOne]
end GlobalTheory.BK

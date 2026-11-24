-- Prove2me | solution 1 for GlobalTheory.BK.mem_ext_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:11.991879+00:00
-- url     : https://prove2.me/submissions/b82720ca-59d1-4e72-8f4e-94faa37dc465

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Theorems.Thm_GlobalTheory_BK_mxInv_rankOne_eq
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_mem_tot
import Theorems.Thm_GlobalTheory_BK_mem_vecs
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {l e}
namespace GlobalTheory.BK
theorem _root_.solution (j : ℤ) {B : Subalgebra O K⟦X⟧} {v : Vec K a Unit} :
    v ∈ (rankOne O K l e fun _ : ZMod a => j).ext B ↔ ∀ τ, Ezpow K l e (-j) * v τ () ∈ B := by
  simp [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, mem_vecs, Matrix.mulVec, dotProduct,
    mxInv_rankOne_eq]
end GlobalTheory.BK

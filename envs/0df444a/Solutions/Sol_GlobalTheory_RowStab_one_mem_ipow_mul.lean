-- Prove2me | solution 1 for GlobalTheory.RowStab.one_mem_ipow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:31.00683+00:00
-- url     : https://prove2.me/submissions/bbff9ebe-9e9d-40d6-854e-0228650774bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors
open GlobalTheory GlobalTheory.RowStab
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.RowStab
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) (m : ℤ) :
    (1 : K) ∈ ipow 𝔡 m * ipow 𝔡 (-m) := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    simpa using h𝔡
  unfold ipow
  rw [← FractionalIdeal.coe_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, FractionalIdeal.coe_one]
  exact Submodule.one_le.mp le_rfl
end GlobalTheory.RowStab

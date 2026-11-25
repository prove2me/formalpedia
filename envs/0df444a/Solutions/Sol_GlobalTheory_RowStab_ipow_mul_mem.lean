-- Prove2me | solution 1 for GlobalTheory.RowStab.ipow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:28.083655+00:00
-- url     : https://prove2.me/submissions/17bfd501-ceef-44dd-a112-3c3c4c158b04

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
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x y : K} (hx : x ∈ ipow 𝔡 m)
    (hy : y ∈ ipow 𝔡 n) : x * y ∈ ipow 𝔡 (m + n) := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    simpa using h𝔡
  unfold ipow at *
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]
  exact Submodule.mul_mem_mul hx hy
end GlobalTheory.RowStab

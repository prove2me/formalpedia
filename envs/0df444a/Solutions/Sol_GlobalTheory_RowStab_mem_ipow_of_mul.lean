-- Prove2me | solution 1 for GlobalTheory.RowStab.mem_ipow_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:14.412786+00:00
-- url     : https://prove2.me/submissions/07b841c9-eded-4fdf-857c-8c75eaa99c3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Theorems.Thm_GlobalTheory_RowStab_ipow_mul_mem
import Theorems.Thm_GlobalTheory_RowStab_one_mem_ipow_mul
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
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x : K}
    (h : ∀ t ∈ ipow 𝔡 (-m), t * x ∈ ipow 𝔡 n) : x ∈ ipow 𝔡 (m + n) := by
  have key : ∀ y ∈ ipow 𝔡 m * ipow 𝔡 (-m), y * x ∈ ipow 𝔡 (m + n) := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha t ht
      rw [mul_assoc]
      exact ipow_mul_mem h𝔡 ha (h t ht)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 (one_mem_ipow_mul h𝔡 m)
end GlobalTheory.RowStab

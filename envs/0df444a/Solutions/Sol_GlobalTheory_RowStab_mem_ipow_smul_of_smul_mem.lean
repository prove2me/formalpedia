-- Prove2me | solution 1 for GlobalTheory.RowStab.mem_ipow_smul_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:09:47.106066+00:00
-- url     : https://prove2.me/submissions/c31261ca-7b2e-4f23-a2d4-8c58fd674604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
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
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.RowStab
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m : ℤ} {M : Submodule (𝓞 K) V} {v : V}
    (h : ∀ t ∈ ipow 𝔡 (-m), t • v ∈ M) : v ∈ ipow 𝔡 m • M := by
  have key : ∀ y ∈ ipow 𝔡 m * ipow 𝔡 (-m), y • v ∈ ipow 𝔡 m • M := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha t ht
      rw [mul_smul]
      exact Submodule.smul_mem_smul ha (h t ht)
    · intro a b ha hb
      rw [add_smul]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 (one_mem_ipow_mul h𝔡 m)
end GlobalTheory.RowStab

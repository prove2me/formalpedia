-- Prove2me | solution 1 for GlobalTheory.RowStab.smul_mem_of_mem_ipow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:53.452916+00:00
-- url     : https://prove2.me/submissions/3ca19706-58f8-46f9-971a-b8ff2da638f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Theorems.Thm_GlobalTheory_RowStab_ipow_mul_mem
import Theorems.Thm_GlobalTheory_RowStab_ipow_zero
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
    (hv : v ∈ ipow 𝔡 m • M) {t : K} (ht : t ∈ ipow 𝔡 (-m)) : t • v ∈ M := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro a ha n hn
    have h1 : t * a ∈ ipow 𝔡 0 := by
      simpa [add_comm] using ipow_mul_mem h𝔡 ht ha
    rw [ipow_zero] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
    rw [smul_smul, ← ho, algebraMap_smul]
    exact M.smul_mem o hn
  · intro x y hx hy
    rw [smul_add]
    exact M.add_mem hx hy
end GlobalTheory.RowStab

-- Prove2me | solution 1 for GlobalTheory.RowStab.star_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:14.961379+00:00
-- url     : https://prove2.me/submissions/e6e0b1b2-7417-47f6-ad5a-167b9e30f3b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Theorems.Thm_GlobalTheory_RowStab_star_integral
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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.RowStab
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (k : ℕ) :
    ∀ x ∈ 𝔡 ^ k, ∃ y ∈ 𝔡 ^ k, (y : K) = star (x : K) := by
  induction k with
  | zero =>
    intro x _
    obtain ⟨y, hy⟩ := star_integral x
    exact ⟨y, by simp, hy⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', ea⟩ := ih a ha
      obtain ⟨b', hb', eb⟩ := h𝔡s b hb
      refine ⟨a' * b', ?_, ?_⟩
      · rw [pow_succ]; exact Submodule.mul_mem_mul ha' hb'
      · simp [ea, eb, star_mul']
    · rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
      exact ⟨a' + b', Submodule.add_mem _ ha' hb', by simp [ea, eb]⟩
end GlobalTheory.RowStab

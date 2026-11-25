-- Prove2me | solution 1 for GroundTheory.Global.exists_mem_valuation_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:24.320387+00:00
-- url     : https://prove2.me/submissions/5459a43a-79e9-40e1-8317-80305693652b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Theorems.Thm_GroundTheory_Global_mem_iff_forall_valuation_le
import Theorems.Thm_GroundTheory_Global_le_exp_sub_one_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : ∃ a ∈ I, v.valuation K a = exp (-count K v I) := by
  set P : FractionalIdeal (𝓞 K)⁰ K := (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) with hPdef
  have hP : P ≠ 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have hIP : I * P ≠ 0 := mul_ne_zero hI hP
  have hne : ¬ I ≤ I * P := fun h ↦ by
    have := count_mono K v hI h
    rw [count_mul K v hI hP, hPdef, count_self] at this
    omega
  obtain ⟨a, haI, haIP⟩ := SetLike.not_le_iff_exists.1 hne
  refine ⟨a, haI, le_antisymm ((mem_iff_forall_valuation_le hI).1 haI v) ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  apply haIP
  rw [mem_iff_forall_valuation_le hIP]
  intro w
  rw [count_mul K w hI hP]
  by_cases hw : w = v
  · subst hw
    rw [hPdef, count_self, show -(count K w I + 1) = -count K w I - 1 by ring]
    exact le_exp_sub_one_of_lt hlt
  · rw [hPdef, count_maximal_coprime K w (Ne.symm hw), add_zero]
    exact (mem_iff_forall_valuation_le hI).1 haI w
end GroundTheory.Global

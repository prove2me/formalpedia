-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_coeff_prod_X_sub_C_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:17.058869+00:00
-- url     : https://prove2.me/submissions/3935a260-3699-44d7-b27f-7dba4d9c916c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_norm_esymm_le
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {s : Multiset E} (hs : ∀ r ∈ s, ‖r‖ ≤ 1) (k : ℕ) :
    ‖((s.map fun r => X - C r).prod).coeff k‖ ≤ 1 := by
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    simpa using norm_esymm_le zero_le_one hs (Multiset.card s - k)
  · rw [coeff_eq_zero_of_natDegree_lt]
    · simp
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
end GroundTheory.PAdicHodge

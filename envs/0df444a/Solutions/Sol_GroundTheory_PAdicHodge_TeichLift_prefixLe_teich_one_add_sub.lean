-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_teich_one_add_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:42:54.145968+00:00
-- url     : https://prove2.me/submissions/d9113e11-14b3-48b6-b52d-b83a96e99c70

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_pow
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_iterate_frobeniusEquiv_symm_pow
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_norm_iterate_frobeniusEquiv_symm_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_mem_int
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_iff_exists
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_of_mem_span
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_exists_add___mul_pow_sub_5a50fafd6f50
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_exists_one_add_teich_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_π_mul_zero
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {b : L} (hb : ‖b‖ ≤ 1) (k : ℕ) :
    T.PrefixLe (T.teich (1 + b) - 1 - T.teich b) k
      ‖((((frobeniusEquiv L p).symm : L →+* L))^[k] b)‖ := by
  set b' := ((((frobeniusEquiv L p).symm : L →+* L))^[k] b) with hb'def
  have hb' : ‖b'‖ ≤ 1 := norm_iterate_frobeniusEquiv_symm_le_one hb k
  have hpow : b' ^ p ^ k = b := iterate_frobeniusEquiv_symm_pow b k
  by_cases hb0 : b' = 0
  · have : b = 0 := by rw [← hpow, hb0, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
    subst this
    rw [hb0, norm_zero]
    exact T.prefixLe_of_mem_span (by simp) le_rfl
  have h1b' : ‖1 + b'‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hb')
  obtain ⟨u0, hu0, hu0'⟩ := T.exists_eq_π_mul (T.teich (1 + b') - (1 + T.teich b'))
    (sub_mem (T.teich_mem_int h1b') (add_mem (one_mem _) (T.teich_mem_int hb')))
    (by simp [red_teich])
  obtain ⟨w, hw, hw'⟩ := T.exists_add_π_mul_pow_sub (1 + T.teich b') u0
    (add_mem (one_mem _) (T.teich_mem_int hb')) hu0 k
  obtain ⟨U, hU, hU'⟩ := T.exists_one_add_teich_pow hb' k
  refine (T.prefixLe_iff_exists hb0).2 ⟨T.π * U, mul_mem T.π_mem_int hU, ?_⟩
  have hfr : (1 + b') ^ p ^ k = 1 + b := by rw [add_pow_char_pow, one_pow, hpow]
  have e1 : T.teich (1 + b) = (1 + T.teich b' + T.π * u0) ^ p ^ k := by
    rw [← hfr, T.teich_pow]
    congr 1; rw [← hu0']; ring
  have : T.teich (1 + b) - 1 - T.teich b - T.teich b' * (T.π * U) = T.π ^ (k + 1) * w := by
    rw [e1, ← hw', hU', hpow]; ring
  rw [this]; exact T.π_pow_mul_mem le_rfl w
end GroundTheory.PAdicHodge.TeichLift

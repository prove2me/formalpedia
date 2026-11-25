-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_teich_add_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:40.840905+00:00
-- url     : https://prove2.me/submissions/5826a8a8-42c7-4294-bf6a-89f7a03d50bb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_mul
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_teich_mul
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_norm_iterate_frobeniusEquiv_symm_pow
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_of_mem_span
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_teich_one_add_sub
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
theorem _root_.solution {a e : L} (h : ‖e‖ ≤ ‖a‖) (k : ℕ) :
    T.PrefixLe (T.teich (a + e) - T.teich a - T.teich e) k
      (‖a‖ ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * ‖e‖ ^ ((p ^ k : ℕ) : ℝ)⁻¹) := by
  have hN : (p ^ k : ℕ) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  by_cases ha : a = 0
  · have he : e = 0 := by rw [ha, norm_zero] at h; exact norm_le_zero_iff.1 h
    subst ha; subst he
    exact T.prefixLe_of_mem_span (by simp) (by positivity)
  have hb : ‖e / a‖ ≤ 1 := by rw [norm_div, div_le_one (norm_pos_iff.2 ha)]; exact h
  have hae : T.teich (a + e) - T.teich a - T.teich e =
      T.teich a * (T.teich (1 + e / a) - 1 - T.teich (e / a)) := by
    have h1 : a * (1 + e / a) = a + e := by field_simp
    have h2 : a * (e / a) = e := by field_simp
    calc T.teich (a + e) - T.teich a - T.teich e
        = T.teich (a * (1 + e / a)) - T.teich a - T.teich (a * (e / a)) := by rw [h1, h2]
      _ = _ := by rw [T.teich_mul, T.teich_mul]; ring
  intro m hm
  rw [hae, coeff_teich_mul, norm_mul]
  have hD := T.prefixLe_teich_one_add_sub hb k m hm
  have hnb' : ‖((((frobeniusEquiv L p).symm : L →+* L))^[k] (e / a))‖ =
      ‖e / a‖ ^ ((p ^ k : ℕ) : ℝ)⁻¹ := by
    rw [← norm_iterate_frobeniusEquiv_symm_pow (e / a) k,
      Real.pow_rpow_inv_natCast (norm_nonneg _) hN]
  calc ‖a‖ * ‖T.coeff (T.teich (1 + e / a) - 1 - T.teich (e / a)) m‖
      ≤ ‖a‖ * ‖((((frobeniusEquiv L p).symm : L →+* L))^[k] (e / a))‖ :=
        mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = ‖a‖ ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * ‖e‖ ^ ((p ^ k : ℕ) : ℝ)⁻¹ := by
        rw [hnb', norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _),
          Real.rpow_sub (norm_pos_iff.2 ha), Real.rpow_one]
        ring
end GroundTheory.PAdicHodge.TeichLift

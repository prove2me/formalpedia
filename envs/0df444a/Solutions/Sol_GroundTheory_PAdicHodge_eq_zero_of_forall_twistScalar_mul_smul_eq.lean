-- Prove2me | solution 1 for GroundTheory.PAdicHodge.eq_zero_of_forall_twistScalar_mul_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:34.322862+00:00
-- url     : https://prove2.me/submissions/57730ac4-9053-4721-aeef-f599d6a5efff

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
import Theorems.Thm_GroundTheory_PAdicHodge_twistScalar_ne_one
import Theorems.Thm_GroundTheory_PAdicHodge_exists_gal_fix_cyclotomicLayer_cycloChar_ne_one
import Theorems.Thm_GroundTheory_PAdicHodge_cycloChar_eq_one_of_mem_cyclotomicLimitGal
import Theorems.Thm_GroundTheory_PAdicHodge_mem_cyclotomicCompletion_of_forall_smul_eq
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_mono
import Theorems.Thm_GroundTheory_PAdicHodge_mem_cyclotomicLimit
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_norm_tateTraceHat_le
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl
import Theorems.Thm_GroundTheory_PAdicHodge_smul_mem_cyclotomicCompletion
import Theorems.Thm_GroundTheory_PAdicHodge_sub_mem_closureInCp
import Theorems.Thm_GroundTheory_PAdicHodge_tateBound_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_tateTraceHat_add
import Theorems.Thm_GroundTheory_PAdicHodge_tateTraceHat_coe_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_tateTraceHat_mem
import Theorems.Thm_GroundTheory_PAdicHodge_tateTraceHat_mul
import Theorems.Thm_GroundTheory_PAdicHodge_tateTraceHat_smul
import Theorems.Thm_GroundTheory_PAdicHodge_two_le_stableIndex
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {j : ℤ} (hj : j ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), twistScalar K j σ * (σ • x) = x) : x = 0 := by

  have hxc : x ∈ cyclotomicCompletion K := by
    refine mem_cyclotomicCompletion_of_forall_smul_eq K fun σ hσ => ?_
    have h1 : twistScalar K j σ = 1 := by
      simp [twistScalar, cycloChar_eq_one_of_mem_cyclotomicLimitGal K hσ]
    simpa [h1] using hx σ

  have hR : ∀ n, stableIndex K ≤ n → tateTraceHat K n x = 0 := by
    intro n hn
    have key : ∀ σ : Gal(PadicAlgCl p/K),
        tateTraceHat K n x = twistScalar K j σ * (σ • tateTraceHat K n x) := by
      intro σ
      have hc : twistScalar K j σ =
          ((algebraMap ℚ_[p] (PadicAlgCl p) (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) :
            PadicAlgCl p) : ℂ_[p]) := rfl
      conv_lhs => rw [← hx σ]
      rw [hc, tateTraceHat_mul (IntermediateField.algebraMap_mem _ _) (smul_mem_cyclotomicCompletion σ hxc),
        tateTraceHat_smul n σ hxc]
    obtain ⟨σ, hσ, hne⟩ := exists_gal_fix_cyclotomicLayer_cycloChar_ne_one K n
    have h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ := fun ζ hζ =>
      hσ ζ (cycl_le_cyclotomicLayer K n (cycl_mono (p := p)
        ((two_le_stableIndex K).trans hn) (pow_eq_one_mem_cycl hζ)))
    obtain ⟨b, hb, hbx⟩ := tateTraceHat_mem n hxc
    have hfix : σ • tateTraceHat K n x = tateTraceHat K n x := by
      rw [← hbx, gal_smul_coe, hσ b hb]
    have h3 := key σ
    rw [hfix] at h3
    have h4 : (twistScalar K j σ - 1) * tateTraceHat K n x = 0 := by
      rw [sub_mul, one_mul, ← h3, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (twistScalar_ne_one K σ h2 hne hj))

  set c := tateBound K
  have hc0 : 0 ≤ c := tateBound_nonneg K
  have hbound : ∀ ε > 0, ‖x‖ ≤ (1 + c) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hy
    set m' := max m (stableIndex K)
    have hym : y ∈ cyclotomicLayer K m' := cyclotomicLayer_mono K (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ cyclotomicCompletion K := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ cyclotomicCompletion K := sub_mem_closureInCp hyc hxc
    have h1 : tateTraceHat K m' (y : ℂ_[p]) =
        tateTraceHat K m' ((y : ℂ_[p]) - x) + tateTraceHat K m' x := by
      rw [← tateTraceHat_add m' hsub hxc, sub_add_cancel]
    rw [tateTraceHat_coe_of_mem hym, hR m' (le_max_right _ _), add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ c * ε := by
      rw [h1]
      refine (norm_tateTraceHat_le m' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hc0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + c * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + c) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound (‖x‖ / (2 * (1 + c))) (by positivity)
  have h' : (1 + c) * (‖x‖ / (2 * (1 + c))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith
end GroundTheory.PAdicHodge

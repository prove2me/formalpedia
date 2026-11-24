-- Prove2me | solution 1 for GlobalTheory.weierstrassP_sub_weierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:31.517696+00:00
-- url     : https://prove2.me/submissions/a644a97e-b275-487c-975d-0e3b981a0782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_sigmaSign_ne_zero
import Theorems.Thm_GlobalTheory_exists_eq_const_of_periodic_of_even

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) :
    ℘[L] u - ℘[L] v = -(weierstrassSigma L (u + v) * weierstrassSigma L (u - v)) /
      (weierstrassSigma L u ^ 2 * weierstrassSigma L v ^ 2) := by
  obtain ⟨c, hc⟩ := exists_eq_const_of_periodic_of_even L
    (f := fun z => weierstrassSigma L (z + v) * weierstrassSigma L (z - v) /
      weierstrassSigma L z ^ 2 + weierstrassSigma L v ^ 2 * ℘[L] z)
    (N := fun z => weierstrassSigma L (z + v) * weierstrassSigma L (z - v) / sigmaProd L z ^ 2 +
      weierstrassSigma L v ^ 2 * (1 + z ^ 2 * weierstrassPExcept L 0 z))
    (.add (.div (by fun_prop) (by fun_prop) fun z hz =>
      pow_ne_zero _ (weierstrassSigma_ne_zero L hz)) (L.differentiableOn_weierstrassP.const_mul _))
    (fun z hz w hw => by
      have hσ := weierstrassSigma_ne_zero L hz
      have hε := sigmaSign_ne_zero L w
      have e : cexp (quasiPeriod L w * (z + v + w / 2)) * cexp (quasiPeriod L w * (z - v + w / 2)) =
          cexp (quasiPeriod L w * (z + w / 2)) ^ 2 := by
        rw [sq, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
      beta_reduce
      rw [L.weierstrassP_add_coe z ⟨w, hw⟩, add_right_comm, add_sub_right_comm,
        weierstrassSigma_add L hw, weierstrassSigma_add L hw, weierstrassSigma_add L hw]
      congr 1
      rw [div_eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hε (exp_ne_zero _)) hσ))
        (pow_ne_zero _ hσ)]
      linear_combination (sigmaSign L w ^ 2 * weierstrassSigma L (z + v) *
        weierstrassSigma L (z - v) * weierstrassSigma L z ^ 2) * e)
    (by
      have h1 := L.analyticAt_weierstrassPExcept 0
      have h2 := (differentiable_sigmaProd L).analyticAt 0
      refine .add (.div (by fun_prop) (by fun_prop) (by simp)) (by fun_prop))
    (fun z => by
      beta_reduce
      rw [show -z + v = -(z - v) by ring, show -z - v = -(z + v) by ring, weierstrassSigma_neg,
        weierstrassSigma_neg, sigmaProd_neg, L.weierstrassPExcept_neg, neg_zero]
      ring)
    (by simp; ring)
    (fun z hz => by
      have h0 : z ≠ 0 := fun h => hz (h ▸ zero_mem _)
      have h1 := sigmaProd_ne_zero L (z := z) fun h => hz h.1
      have h2 := L.weierstrassPExcept_add 0 z
      simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, div_zero] at h2
      beta_reduce
      rw [← h2, show weierstrassSigma L z = z * sigmaProd L z from rfl]
      field_simp
      ring)
  have h1 := (hc u hu).trans (hc v hv).symm
  have hσu := weierstrassSigma_ne_zero L hu
  have hσv := weierstrassSigma_ne_zero L hv
  simp only [sub_self, weierstrassSigma_zero, mul_zero, zero_div, zero_add] at h1
  field_simp at h1 ⊢
  linear_combination h1
end GlobalTheory

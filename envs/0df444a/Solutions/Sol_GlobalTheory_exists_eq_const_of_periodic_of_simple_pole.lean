-- Prove2me | solution 1 for GlobalTheory.exists_eq_const_of_periodic_of_simple_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:55.465804+00:00
-- url     : https://prove2.me/submissions/fc320327-aeee-4825-900f-1ac01a6a772d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_analyticOnNhd_weierstrassZeta
import Theorems.Thm_GlobalTheory_quasiPeriod_mul_sub
import Theorems.Thm_GlobalTheory_eq_const_of_periodic_of_tendsto

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
theorem _root_.solution {f N : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (L.lattice : Set ℂ)ᶜ)
    (hper : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, f (z + w) = f z)
    (hN : AnalyticAt ℂ N 0) (hfN : ∀ᶠ z in 𝓝[≠] 0, z * f z = N z) :
    ∃ c, ∀ z ∉ L.lattice, f z = c := by
  have ho := L.isClosed_lattice.isOpen_compl
  obtain ⟨M, hM, e⟩ := hN.exists_eq_sum_add_pow_mul 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    iteratedDeriv_zero, one_smul, pow_one, smul_eq_mul, one_mul] at e
  set r := N 0
  let h : ℂ → ℂ := fun z => f z - r * weierstrassZeta L z
  have hh : AnalyticOnNhd ℂ h (L.lattice : Set ℂ)ᶜ := fun z hz =>
    (hf.analyticOnNhd ho z hz).sub (analyticAt_const.mul (analyticOnNhd_weierstrassZeta L z hz))
  have hq : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, h (z + w) = h z - r * quasiPeriod L w := by
    intro z hz w hw
    simp only [h, hper z hz w hw, weierstrassZeta_add L hw hz]
    ring
  have hK : AnalyticAt ℂ (fun z => M z - r * weierstrassZetaExcept L 0 z) 0 :=
    hM.sub (analyticAt_const.mul (analyticAt_weierstrassZetaExcept L 0))
  have hhK : h =ᶠ[𝓝[≠] 0] fun z => M z - r * weierstrassZetaExcept L 0 z := by
    filter_upwards [hfN, self_mem_nhdsWithin] with z hz (hz0 : z ≠ 0)
    rw [e z] at hz
    refine mul_left_cancel₀ hz0 ?_
    simp only [h, weierstrassZeta_eq_inv_add]
    have : z * (1 / z) = 1 := by field_simp
    linear_combination hz - r * this
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∉ L.lattice, deriv h z = c := by
    refine ⟨_, fun z hz => eq_const_of_periodic_of_tendsto L hh.deriv.differentiableOn
      (fun z hz w hw => ?_) ((hK.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        hhK.nhdsNE_deriv.symm) hz⟩
    rw [← deriv_comp_add_const]
    refine (EventuallyEq.deriv_eq ?_).trans (deriv_sub_const (r * quasiPeriod L w))
    filter_upwards [ho.mem_nhds hz] with x hx using hq x hx w hw
  have hx := L.ω₁_div_two_notMem_lattice
  set x := L.ω₁ / 2
  have hlin : ∀ z ∉ L.lattice, h z = c * z + (h x - c * x) := fun z hz =>
    eqOn_compl_lattice_of_hasDerivAt L (g := fun z => c * z + (h x - c * x)) (f' := fun _ => c)
      (fun z hz => hc z hz ▸ (hh z hz).differentiableAt.hasDerivAt)
      (fun z _ => by simpa using ((hasDerivAt_id' z).const_mul c).add_const (h x - c * x))
      hx (by ring) hz
  have hcw : ∀ w ∈ L.lattice, c * w = -(r * quasiPeriod L w) := by
    intro w hw
    have h1 := hlin _ (add_notMem_lattice hx hw)
    rw [hq x hx w hw] at h1
    linear_combination -h1
  have hr : r = 0 := by
    have h1 := quasiPeriod_mul_sub L L.ω₁ L.ω₂
    have h2 : (((conj L.ω₁ * L.ω₂).im / latticeArea L : ℝ) : ℂ) ≠ 0 := by
      have hA := latticeArea_pos L
      refine ofReal_ne_zero.2 (div_ne_zero ?_ hA.ne')
      rwa [latticeArea_eq, abs_pos] at hA
    refine mul_right_cancel₀ (mul_ne_zero two_pi_I_ne_zero h2) ?_
    linear_combination L.ω₂ * hcw _ L.ω₁_mem_lattice - L.ω₁ * hcw _ L.ω₂_mem_lattice - r * h1
  have hc0 : c = 0 := by
    have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
    simpa [hr, h1] using hcw _ L.ω₁_mem_lattice
  exact ⟨h x, fun z hz => by simpa [h, hr, hc0] using hlin z hz⟩
end GlobalTheory

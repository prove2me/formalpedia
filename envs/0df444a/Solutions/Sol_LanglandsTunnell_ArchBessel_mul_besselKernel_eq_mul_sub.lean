-- Prove2me | solution 1 for LanglandsTunnell.ArchBessel.mul_besselKernel_eq_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6c2586ed-5e51-5108-a41b-f985a40fe52e

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel
import Theorems.Thm_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub

set_option autoImplicit false

open MeasureTheory Set Filter

namespace LanglandsTunnell
namespace ArchBessel
p2m_export "LanglandsTunnell.ArchBessel" "besselKernel integrableOn_exp_neg_mul_add_inv_mul_cpow"
namespace IndexRecAux
p2m_open "LanglandsTunnell.ArchBessel LanglandsTunnell"

noncomputable def g (x t : ℝ) : ℝ := Real.exp (-(x * (t + t⁻¹) / 2))

noncomputable def E (x t : ℝ) : ℂ := ((g x t : ℝ) : ℂ)

theorem besselKernel_eq (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ), E x t * ((t : ℂ) ^ (ν - 1)) := rfl

theorem integrableOn_E_mul_cpow (μ : ℂ) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => E x t * ((t : ℂ) ^ (μ - 1))) (Ioi 0) :=
  integrableOn_exp_neg_mul_add_inv_mul_cpow μ x hx

theorem hasDerivAt_g (x t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s => g x s) (g x t * (-(x * (1 - (t ^ 2)⁻¹) / 2))) t := by
  unfold g
  have h1 : HasDerivAt (fun s : ℝ => s + s⁻¹) (1 + (-(t ^ 2)⁻¹)) t :=
    (hasDerivAt_id t).add (hasDerivAt_inv ht)
  have h2 : HasDerivAt (fun s : ℝ => -(x * (s + s⁻¹) / 2)) (-(x * (1 + (-(t ^ 2)⁻¹)) / 2)) t :=
    ((h1.const_mul x).div_const 2).neg
  have h3 := h2.exp
  convert h3 using 1 <;> ring

theorem hasDerivAt_ofReal_cpow (ν : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ ν) (ν * (t : ℂ) ^ (ν - 1)) t := by
  have h0 : (id (t : ℂ)) ∈ Complex.slitPlane := by
    simpa [Complex.ofReal_mem_slitPlane] using ht
  have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := ν) h0).comp_ofReal
  simpa using h

noncomputable def F' (ν : ℂ) (x t : ℝ) : ℂ :=
  ν * (E x t * (t : ℂ) ^ (ν - 1)) - (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1))
    + (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν - 1 - 1))

theorem hasDerivAt_E_mul_cpow (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => E x s * (s : ℂ) ^ ν) (F' ν x t) t := by
  have hE : HasDerivAt (fun s : ℝ => E x s) ((g x t * (-(x * (1 - (t ^ 2)⁻¹) / 2)) : ℝ) : ℂ) t :=
    (hasDerivAt_g x t ht.ne').ofReal_comp
  have h := hE.mul (hasDerivAt_ofReal_cpow ν t ht)
  refine h.congr_deriv ?_
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : (t : ℂ) ^ (ν + 1 - 1) = (t : ℂ) ^ ν := by rw [add_sub_cancel_right]
  have e2 : (t : ℂ) ^ (ν - 1 - 1) = (t : ℂ) ^ ν / (t : ℂ) ^ (2 : ℕ) := by
    rw [show ν - 1 - 1 = ν - 2 by ring, Complex.cpow_sub _ _ ht0, Complex.cpow_two]
  have e3 : (t : ℂ) ^ (ν - 1) = (t : ℂ) ^ ν / (t : ℂ) := by
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one]
  simp only [F', E, e1, e2, e3]
  push_cast
  field_simp
  ring

theorem g_pos (x t : ℝ) : 0 < g x t := Real.exp_pos _

theorem norm_E_mul_cpow (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖E x t * (t : ℂ) ^ ν‖ = g x t * t ^ ν.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, E, Complex.norm_real,
    Real.norm_of_nonneg (g_pos x t).le]

theorem g_le_exp_neg_mul (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    g x t ≤ Real.exp (-(x / 2) * t) := by
  unfold g
  apply Real.exp_le_exp.mpr
  have : 0 ≤ x * t⁻¹ := by positivity
  nlinarith

theorem g_le_exp_neg_mul_inv (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    g x t ≤ Real.exp (-(x / 2) * t⁻¹) := by
  unfold g
  apply Real.exp_le_exp.mpr
  have : 0 ≤ x * t := by positivity
  nlinarith

theorem tendsto_atTop (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => E x t * (t : ℂ) ^ ν) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ν.re (x / 2) (by positivity))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_E_mul_cpow ν x t ht, mul_comm]
  exact mul_le_mul_of_nonneg_left (g_le_exp_neg_mul x t hx ht) (Real.rpow_nonneg ht.le _)

theorem tendsto_nhdsGT_zero (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => E x t * (t : ℂ) ^ ν) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-ν.re) (x / 2) (by positivity)).comp
    tendsto_inv_nhdsGT_zero
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  rw [norm_E_mul_cpow ν x t ht', Function.comp_apply, mul_comm]
  have hr : t ^ ν.re = (t⁻¹) ^ (-ν.re) := by
    rw [Real.rpow_neg (inv_nonneg.mpr ht'.le), Real.inv_rpow ht'.le, inv_inv]
  rw [hr]
  exact mul_le_mul_of_nonneg_left (g_le_exp_neg_mul_inv x t hx ht')
    (Real.rpow_nonneg (inv_nonneg.mpr ht'.le) _)

theorem integral_F' (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), F' ν x t =
      ν * besselKernel ν x - (x : ℂ) / 2 * besselKernel (ν + 1) x
        + (x : ℂ) / 2 * besselKernel (ν - 1) x := by
  have h1 : Integrable (fun t : ℝ => ν * (E x t * (t : ℂ) ^ (ν - 1))) (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow ν x hx).const_mul ν
  have h2 : Integrable (fun t : ℝ => (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow (ν + 1) x hx).const_mul _
  have h3 : Integrable (fun t : ℝ => (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν - 1 - 1)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow (ν - 1) x hx).const_mul _
  have h12 : Integrable (fun t : ℝ => ν * (E x t * (t : ℂ) ^ (ν - 1))
      - (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1))) (volume.restrict (Ioi 0)) := h1.sub h2
  unfold F'
  rw [integral_add h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul,
    integral_const_mul, besselKernel_eq, besselKernel_eq, besselKernel_eq]

theorem main (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ν * besselKernel ν x = (x : ℂ) / 2 * (besselKernel (ν + 1) x - besselKernel (ν - 1) x) := by
  classical
  let F : ℝ → ℂ := fun t => if 0 < t then E x t * (t : ℂ) ^ ν else 0
  have hFeq : EqOn F (fun t => E x t * (t : ℂ) ^ ν) (Ioi 0) := fun t ht => if_pos ht
  have hF0 : F 0 = 0 := if_neg (lt_irrefl 0)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (F' ν x t) t := by
    intro t ht
    exact (hasDerivAt_E_mul_cpow ν x t ht).congr_of_eventuallyEq
      (eventuallyEq_of_mem (Ioi_mem_nhds ht) hFeq)
  have hint : IntegrableOn (F' ν x) (Ioi 0) := by
    have h1 := (integrableOn_E_mul_cpow ν x hx).const_mul ν
    have h2 := (integrableOn_E_mul_cpow (ν + 1) x hx).const_mul ((x : ℂ) / 2)
    have h3 := (integrableOn_E_mul_cpow (ν - 1) x hx).const_mul ((x : ℂ) / 2)
    exact (h1.sub h2).add h3
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hF0]
    exact (tendsto_nhdsGT_zero ν x hx).congr' (eventuallyEq_of_mem self_mem_nhdsWithin hFeq).symm
  have hlim : Tendsto F atTop (nhds 0) :=
    (tendsto_atTop ν x hx).congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) hFeq).symm
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [hF0, sub_zero, integral_F' ν x hx] at hFTC
  linear_combination hFTC

end LanglandsTunnell.ArchBessel.IndexRecAux

p2m_open "LanglandsTunnell.ArchBessel P2MW.S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub.LanglandsTunnell.ArchBessel"

theorem solution (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ν * besselKernel ν x = (x : ℂ) / 2 * (besselKernel (ν + 1) x - besselKernel (ν - 1) x) :=
  LanglandsTunnell.ArchBessel.IndexRecAux.main ν x hx

end S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub
end P2MW
export P2MW.S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub (solution)

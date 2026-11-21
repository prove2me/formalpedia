-- Prove2me | solution 1 for MasulloRH.realTraceIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:19:24.47283+00:00
-- url     : https://prove2.me/submissions/b602f6f7-d0cc-46fb-8713-432d6a67c8bf

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
open MeasureTheory Set Filter
open MasulloRH

private theorem tail_zero {φ : ℝ → ℂ} (h : IsRationalTraceTest φ) :
    ∃ R : ℝ, ∀ t ≥ R, φ t = 0 ∧ φ t⁻¹ = 0 := by
  have h0 : (0:ℝ) ∉ tsupport φ := fun ht => (lt_irrefl (0 : ℝ)) (h.2.2.1 ht)
  have ht : φ =ᶠ[atTop] 0 :=
    (hasCompactSupport_iff_eventuallyEq.mp h.2.1).filter_mono (by rw [Filter.coclosedCompact_eq_cocompact]; exact atTop_le_cocompact)
  exact eventually_atTop.mp (ht.and (tendsto_inv_atTop_zero.eventually
    (notMem_tsupport_iff_eventuallyEq.mp h0)))

theorem solution (φ : ℝ → ℂ) (h : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) := by
  obtain ⟨R, hR⟩ := tail_zero h
  let g := fun t : ℝ => φ t + φ t⁻¹
  have hcont {t : ℝ} (ht : 0 < t) : ContinuousAt g t :=
    h.1.continuous.continuousAt.add (h.1.continuous.continuousAt.comp (continuousAt_inv₀ ht.ne'))
  have hd : DifferentiableAt ℝ g 1 := by
    have hdφ := h.1.differentiable (by decide)
    exact (hdφ 1).add ((hdφ (1:ℝ)⁻¹).comp 1 (differentiableAt_inv (by norm_num)))
  let F := fun t : ℝ => dslope g 1 t * ((Real.sqrt t / (t+1) : ℝ) : ℂ)
  have hc : ContinuousOn F (Icc 1 R) := by
    intro t ht
    have ht0 := zero_lt_one.trans_le ht.1
    have hds : ContinuousAt (dslope g 1) t := by
      by_cases he : t=1
      · subst t; exact continuousAt_dslope_same.mpr hd
      · exact (continuousAt_dslope_of_ne he).mpr (hcont ht0)
    apply ContinuousAt.continuousWithinAt
    exact hds.mul (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuous_sqrt.continuousAt.div (continuousAt_id.add continuousAt_const) (by dsimp; linarith)))
  have heq {t : ℝ} (ht : 1 < t) : F t = realTraceIntegrand φ t := by
    have hg1 : g 1 = 0 := by simp [g,h.2.2.2]
    have ht1 : ((t:ℂ)-1) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr ht.ne')
    have ht2 : ((t:ℂ)+1) ≠ 0 := by exact_mod_cast (show t+1 ≠ 0 by linarith)
    unfold F realTraceIntegrand
    rw [dslope_of_ne _ ht.ne', slope, hg1, vsub_eq_sub, sub_zero, Complex.real_smul]
    push_cast
    change _ = g t * _
    rw [show (t:ℂ)^2-1 = (t-1)*(t+1) by ring]
    field_simp
  have hb := hc.integrableOn_compact (μ := volume) isCompact_Icc
  have hsmall : IntegrableOn (realTraceIntegrand φ) (Ioc 1 R) :=
    (hb.mono_set Ioc_subset_Icc_self).congr_fun (fun t ht => heq ht.1) measurableSet_Ioc
  have hlarge : IntegrableOn (realTraceIntegrand φ) (Ioi R) := by
    apply (integrableOn_zero (ε' := ℂ)).congr_fun _ measurableSet_Ioi
    intro t ht
    obtain ⟨ht₁,ht₂⟩ := hR t (le_of_lt ht)
    simp [realTraceIntegrand,ht₁,ht₂]
  exact (hsmall.union hlarge).mono_set (fun t ht => by
    by_cases htR : t ≤ R
    · exact Or.inl ⟨ht,htR⟩
    · exact Or.inr (lt_of_not_ge htR))

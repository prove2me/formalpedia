-- Prove2me | solution 1 for InvShareComp.Exog.closed_form_profits
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:57:40.261367+00:00
-- url     : https://prove2.me/submissions/ff780d8c-eb6a-45a9-95e0-8013af002b46

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

open MeasureTheory Classical

open InvShareComp.Exog in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc 0 (P.cbar - P.δ)) :
    profitNo1 P ν I I (sHatN P ν I) (sHatN P ν I)
        = (∫ ω, (P.p * (ω.1 / 2) - P.cbar * max (ω.1 / 2 - I) 0) ∂ν)
          - P.k * (sHatN P ν I) ^ 2 - P.c * I ∧
    profitShare1 P ν t I I (sHat P ν t I) (sHat P ν t I)
        = (∫ ω, (P.p * (ω.1 / 2) - P.δ * max (min (ω.1 / 2 - I) (I - ω.2 / 2)) 0
            - P.cbar * max (max (ω.1 / 2 - I) 0 - max (I - ω.2 / 2) 0) 0) ∂ν)
          - P.k * (sHat P ν t I) ^ 2 - P.c * I := by
  have := hν.prob
  have hd : ∀ s, dDet P.β s s = 1 / 2 := by intro s; unfold dDet; ring
  set K : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 with hK
  have hae : ∀ᵐ ω ∂ν, ω ∈ K := by
    rw [ae_iff]
    exact hν.support
  have hrestr : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hint : ∀ f : ℝ × ℝ → ℝ, Continuous f → Integrable f ν := by
    intro f hf
    rw [← hrestr]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine ⟨?_, ?_⟩
  · unfold profitNo1 payNo
    rw [hd]
    congr 3
    funext ω
    rw [mul_one_div]
  · unfold profitShare1 payShare
    rw [hd]
    congr 2
    set φ1 : ℝ × ℝ → ℝ := fun ω => max (min (I - ω.1 / 2) (ω.2 / 2 - I)) 0 with hφ1
    set φ2 : ℝ × ℝ → ℝ := fun ω => max (min (ω.1 / 2 - I) (I - ω.2 / 2)) 0 with hφ2
    set G : ℝ × ℝ → ℝ := fun ω => P.p * (ω.1 / 2) - P.δ * max (min (ω.1 / 2 - I) (I - ω.2 / 2)) 0
            - P.cbar * max (max (ω.1 / 2 - I) 0 - max (I - ω.2 / 2) 0) 0 with hG
    have hc1 : Continuous φ1 := by rw [hφ1]; fun_prop
    have hc2 : Continuous φ2 := by rw [hφ2]; fun_prop
    have hcG : Continuous G := by rw [hG]; fun_prop
    have hpt : ∀ ω : ℝ × ℝ, P.p * (ω.1 * (1 / 2)) + t * max (min (I - ω.1 * (1 / 2)) (ω.2 * (1 / 2) - I)) 0
        - (t + P.δ) * max (min (ω.1 * (1 / 2) - I) (I - ω.2 * (1 / 2))) 0
        - P.cbar * max (max (ω.1 * (1 / 2) - I) 0 - max (I - ω.2 * (1 / 2)) 0) 0
        = G ω + t * (φ1 ω - φ2 ω) := by
      intro ω
      simp only [hG, hφ1, hφ2, mul_one_div]
      ring
    have hsw : ∫ ω, φ2 ω ∂ν = ∫ ω, φ1 ω ∂ν := by
      conv_lhs => rw [← hν.exch]
      rw [integral_map measurable_swap.aemeasurable hc2.aestronglyMeasurable]
      congr 1
      funext ω
      simp only [hφ1, hφ2, Prod.fst_swap, Prod.snd_swap]
      rw [min_comm]
    have hi2 : Integrable (fun ω => t * (φ1 ω - φ2 ω)) ν :=
      ((hint φ1 hc1).sub (hint φ2 hc2)).const_mul t
    have hi3 : ∫ ω, (φ1 ω - φ2 ω) ∂ν = 0 := by
      rw [integral_sub (hint φ1 hc1) (hint φ2 hc2), hsw, sub_self]
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add (hint G hcG) hi2,
      integral_const_mul, hi3, mul_zero, add_zero]

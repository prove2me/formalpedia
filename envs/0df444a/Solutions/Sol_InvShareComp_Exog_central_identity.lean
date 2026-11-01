-- Prove2me | solution 1 for InvShareComp.Exog.central_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:52:26.708233+00:00
-- url     : https://prove2.me/submissions/2606dfde-dcc7-4067-8dc6-2463179bbebf

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

open MeasureTheory Classical

open InvShareComp.Exog in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc 0 (P.cbar - P.δ)) (s : ℝ) :
    profitShare1 P ν t I I s s = centralProfit P ν I I / 2 - P.k * s ^ 2 := by
  have := hν.prob
  have hd : dDet P.β s s = 1 / 2 := by unfold dDet; ring
  set K : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 with hK
  have hae : ∀ᵐ ω ∂ν, ω ∈ K := by
    rw [ae_iff]
    exact hν.support
  have hrestr : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hint : ∀ f : ℝ × ℝ → ℝ, Continuous f → Integrable f ν := by
    intro f hf
    rw [← hrestr]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hswap : ∀ g : ℝ × ℝ → ℝ, ∫ ω, g (ω.2, ω.1) ∂ν = ∫ ω, g ω ∂ν := by
    intro g
    have h := integral_map_equiv (μ := ν) (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) g
    have hm : Measure.map (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) ν = ν := hν.exch
    rw [hm] at h
    rw [h]; rfl
  set φ1 : ℝ × ℝ → ℝ := fun ω => max (min (I - ω.1 / 2) (ω.2 / 2 - I)) 0 with hφ1
  set φ2 : ℝ × ℝ → ℝ := fun ω => max (min (ω.1 / 2 - I) (I - ω.2 / 2)) 0 with hφ2
  set G : ℝ × ℝ → ℝ := fun ω => P.p * (ω.1 / 2) - P.δ * φ2 ω
          - P.cbar * max (max (ω.1 / 2 - I) 0 - max (I - ω.2 / 2) 0) 0 with hG
  have hc1 : Continuous φ1 := by rw [hφ1]; fun_prop
  have hc2 : Continuous φ2 := by rw [hφ2]; fun_prop
  have hcG : Continuous G := by rw [hG, hφ2]; fun_prop
  have hpt : ∀ ω : ℝ × ℝ, payShare P t I I (dDet P.β s s) (dDet P.β s s) ω.1 ω.2
      = G ω + t * (φ1 ω - φ2 ω) := by
    intro ω
    simp only [payShare, hd, hG, hφ1, hφ2]
    ring_nf
  have hsw : ∫ ω, φ2 ω ∂ν = ∫ ω, φ1 ω ∂ν := by
    rw [← hswap φ2]
    congr 1
    funext ω
    simp only [hφ1, hφ2]
    rw [min_comm]
  have hi2 : Integrable (fun ω => t * (φ1 ω - φ2 ω)) ν :=
    ((hint φ1 hc1).sub (hint φ2 hc2)).const_mul t
  have hi3 : ∫ ω, (φ1 ω - φ2 ω) ∂ν = 0 := by
    rw [integral_sub (hint φ1 hc1) (hint φ2 hc2), hsw, sub_self]
  have hpay : ∫ ω, payShare P t I I (dDet P.β s s) (dDet P.β s s) ω.1 ω.2 ∂ν = ∫ ω, G ω ∂ν := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add (hint G hcG) hi2,
      integral_const_mul, hi3, mul_zero, add_zero]
  -- pointwise: centralized integrand = G + G ∘ swap
  have hcpt : ∀ ω : ℝ × ℝ, (P.p * (ω.1 / 2 + ω.2 / 2) - P.cbar * max (ω.1 / 2 + ω.2 / 2 - I - I) 0
      - P.δ * (max (min (I - ω.1 / 2) (ω.2 / 2 - I)) 0
        + max (min (I - ω.2 / 2) (ω.1 / 2 - I)) 0)) = G ω + G (ω.2, ω.1) := by
    intro ω
    have key : max (ω.1 / 2 + ω.2 / 2 - I - I) 0
        = max (max (ω.1 / 2 - I) 0 - max (I - ω.2 / 2) 0) 0
          + max (max (ω.2 / 2 - I) 0 - max (I - ω.1 / 2) 0) 0 := by
      have gen : ∀ x y : ℝ, max (x + y) 0
          = max (max x 0 - max (-y) 0) 0 + max (max y 0 - max (-x) 0) 0 := by
        intro x y
        simp only [max_def]
        split_ifs <;> linarith
      have := gen (ω.1 / 2 - I) (ω.2 / 2 - I)
      rw [show ω.1 / 2 + ω.2 / 2 - I - I = (ω.1 / 2 - I) + (ω.2 / 2 - I) by ring, this]
      congr 3 <;> ring
    have e2 : max (min (I - ω.2 / 2) (ω.1 / 2 - I)) 0 = φ2 ω := by
      simp only [hφ2]; rw [min_comm]
    have e1 : φ2 (ω.2, ω.1) = φ1 ω := by
      simp only [hφ1, hφ2]; rw [min_comm]
    rw [e2, key]
    simp only [hG, e1]
    simp only [hφ1]
    ring
  unfold profitShare1 centralProfit
  rw [hpay, integral_congr_ae (ae_of_all _ hcpt), integral_add (hint G hcG)
    (hint (fun ω => G (ω.2, ω.1)) (hcG.comp continuous_swap)), hswap G]
  ring

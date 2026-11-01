-- Prove2me | solution 1 for InvShareComp.Exog.proposition_1c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:00:08.777163+00:00
-- url     : https://prove2.me/submissions/c97545ab-cbb9-41d7-b424-54946f3d47c9

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model
import Theorems.Thm_InvShareComp_Exog_proposition_1a
import Theorems.Thm_InvShareComp_Exog_closed_form_profits

open MeasureTheory Classical

namespace InvShareAux
open MeasureTheory InvShareComp.Exog

theorem ae_supp {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) :
    ∀ᵐ ω ∂ν, ω ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
  rw [ae_iff]; exact hν.support

theorem int_cont {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : Integrable f ν := by
  have := hν.prob
  have hrestr : ν.restrict (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_supp hν)
  rw [← hrestr]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

end InvShareAux

open InvShareComp.Exog InvShareAux in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc ((P.cbar - P.δ) / 2) (P.cbar - P.δ))
    (hS : 0 ≤ SVal P ν t I) :
    piHatN P ν I ≤ piHat P ν t I := by
  have hP' := hP
  obtain ⟨hc0, hccb, hcbp, hk, hβ, hδ0, hδ⟩ := hP
  have ht' : t ∈ Set.Icc 0 (P.cbar - P.δ) := ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨cN, cS⟩ := closed_form_profits P hP' ν hν I hI t ht'
  obtain ⟨hid, hW0, -⟩ := proposition_1a P hP' ν hν I hI t ht'
  have hk2 : 0 < 2 * P.k := by linarith
  have hsH : 0 ≤ sHat P ν t I := by
    unfold sHat; exact div_nonneg (mul_nonneg hβ hS) hk2.le
  have hle : sHat P ν t I ≤ sHatN P ν I := by
    have : (P.cbar - 2 * t - P.δ) * P.β * Wval ν I / (2 * P.k) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hk2.le
      apply mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (by linarith [ht.1]) hβ) hW0
    linarith
  have hsq : P.k * sHat P ν t I ^ 2 ≤ P.k * sHatN P ν I ^ 2 := by
    have := pow_le_pow_left₀ hsH hle 2
    nlinarith
  have hpt : ∀ ω : ℝ × ℝ, P.p * (ω.1 / 2) - P.cbar * max (ω.1 / 2 - I) 0
      ≤ P.p * (ω.1 / 2) - P.δ * max (min (ω.1 / 2 - I) (I - ω.2 / 2)) 0
            - P.cbar * max (max (ω.1 / 2 - I) 0 - max (I - ω.2 / 2) 0) 0 := by
    intro ω
    have gen : ∀ u v : ℝ, P.δ * max (min u v) 0 + P.cbar * max (max u 0 - max v 0) 0
        ≤ P.cbar * max u 0 := by
      intro u v
      simp only [max_def, min_def]
      split_ifs <;> nlinarith
    linarith [gen (ω.1 / 2 - I) (I - ω.2 / 2)]
  have hint : (∫ ω, (P.p * (ω.1 / 2) - P.cbar * max (ω.1 / 2 - I) 0) ∂ν)
      ≤ ∫ ω, (P.p * (ω.1 / 2) - P.δ * max (min (ω.1 / 2 - I) (I - ω.2 / 2)) 0
            - P.cbar * max (max (ω.1 / 2 - I) 0 - max (I - ω.2 / 2) 0) 0) ∂ν :=
    integral_mono (int_cont hν _ (by fun_prop)) (int_cont hν _ (by fun_prop)) hpt
  unfold piHatN piHat
  rw [cN, cS]
  linarith

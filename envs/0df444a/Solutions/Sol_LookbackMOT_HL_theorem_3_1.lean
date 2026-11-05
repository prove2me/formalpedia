-- Prove2me | solution 1 for LookbackMOT.HL.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:31:47.042321+00:00
-- url     : https://prove2.me/submissions/6c83ac6d-065d-46ad-8d00-751a45c29b55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting
import Theorems.Thm_LookbackMOT_HL_lemma_3_3
import Theorems.Thm_LookbackMOT_HL_sec_3_4_lower_bound
import Theorems.Thm_LookbackMOT_HL_azema_yor
import Theorems.Thm_LookbackMOT_HL_lemma_3_3_step_2

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

lemma LB_expect_of_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {φ : Ω → ℝ}
    (hφ : Integrable φ P) : expect P φ = ((∫ ω, φ ω ∂P : ℝ) : EReal) := by
  unfold expect
  have h1 : ∫⁻ ω, ENNReal.ofReal (-φ ω) ∂P < ⊤ := hφ.neg.lintegral_lt_top
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ, EReal.coe_sub,
    EReal.coe_ennreal_toReal hφ.lintegral_lt_top.ne,
    EReal.coe_ennreal_toReal h1.ne]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : IsFBrownian P ℱ B)
    (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (hξ : (⨆ τ : Ω → WithTop ℝ≥0, ⨆ (_ : IsUIStop P ℱ (shift X₀ B) τ),
      ∫⁻ ω, ENNReal.ofReal (g (runMaxUpTo (shift X₀ B) τ ω)) ∂P) < ⊤)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    U P ℱ B X₀ μ g = ((∫ x, lamStar μ X₀ g x ∂μ : ℝ) : EReal) +
        J P B X₀ g (lamStar μ X₀ g) (tauStar B X₀ μ) ∧
      ((∫ x, lamStar μ X₀ g x ∂μ : ℝ) : EReal) + J P B X₀ g (lamStar μ X₀ g) (tauStar B X₀ μ) =
        ((∫ x, g x ∂ν : ℝ) : EReal) := by
  -- upper bound (Lemma 3.3)
  have hup := LookbackMOT.HL.lemma_3_3 P ℱ B hB X₀ μ hμ1 hmean g hg0 hgC1 hgmono ν hν
  have hgnn : 0 ≤ ∫ x, g x ∂ν := integral_nonneg hg0
  rw [← ofReal_integral_eq_lintegral_ofReal hνg (Filter.Eventually.of_forall hg0),
    EReal.coe_ennreal_ofReal, max_eq_left hgnn] at hup
  -- lower bound (Section 3.4)
  have hlow := LookbackMOT.HL.sec_3_4_lower_bound P ℱ B hB X₀ μ hμ1 hmean g hg0 hgC1 hgmono hξ
    ν hν hνg
  have hU : U P ℱ B X₀ μ g = ((∫ x, g x ∂ν : ℝ) : EReal) := le_antisymm hup hlow
  -- the value of μ(λ*) + J(λ*, τ*) (Azéma–Yor and Lemma 3.3 step 2)
  obtain ⟨-, hXlaw, hMlaw⟩ := LookbackMOT.HL.azema_yor P ℱ B hB X₀ μ hμ1 hmean ν hν
  obtain ⟨hlmeas, hlint, -, -⟩ :=
    LookbackMOT.HL.lemma_3_3_step_2 X₀ μ hμ1 hmean g hg0 hgC1 hgmono ν hν hνg
  set M := runMaxUpTo (shift X₀ B) (tauStar B X₀ μ)
  set Xτ := stoppedValue (shift X₀ B) (tauStar B X₀ μ)
  set L := lamStar μ X₀ g
  have hgM : Integrable (fun ω => g (M ω)) P := by
    have h := hνg
    rw [← hMlaw.map_eq] at h
    exact (integrable_map_measure h.aestronglyMeasurable hMlaw.aemeasurable).mp h
  have hLX : Integrable (fun ω => L (Xτ ω)) P := by
    have h := hlint
    rw [← hXlaw.map_eq] at h
    exact (integrable_map_measure h.aestronglyMeasurable hXlaw.aemeasurable).mp h
  have hJ : J P B X₀ g L (tauStar B X₀ μ) =
      (((∫ x, g x ∂ν) - ∫ x, L x ∂μ : ℝ) : EReal) := by
    show expect P (fun ω => g (M ω) - L (Xτ ω)) = _
    rw [LB_expect_of_integrable P (φ := fun ω => g (M ω) - L (Xτ ω)) (hgM.sub hLX),
      integral_sub hgM hLX]
    have e1 : ∫ ω, g (M ω) ∂P = ∫ x, g x ∂ν :=
      hMlaw.integral_comp (f := g) hνg.aestronglyMeasurable
    have e2 : ∫ ω, L (Xτ ω) ∂P = ∫ x, L x ∂μ :=
      hXlaw.integral_comp (f := L) hlint.aestronglyMeasurable
    rw [e1, e2]
  have hsum : ((∫ x, L x ∂μ : ℝ) : EReal) + J P B X₀ g L (tauStar B X₀ μ) =
      ((∫ x, g x ∂ν : ℝ) : EReal) := by
    rw [hJ, ← EReal.coe_add]
    congr 1
    ring
  exact ⟨hU.trans hsum.symm, hsum⟩

-- Prove2me | solution 1 for MultistageStab.Value.display_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:18:12.804663+00:00
-- url     : https://prove2.me/submissions/337b55ea-7242-44fb-abde-71f07a1b0772

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting
import Theorems.Thm_MultistageStab_Value_case_rhs_random
import Theorems.Thm_MultistageStab_Value_case_costs_random
import Theorems.Thm_MultistageStab_Value_case_both_random

open MeasureTheory ProbabilityTheory MultistageStab.Value
open scoped ENNReal

namespace MStabRed14

lemma ofReal_le_of_eps {a α : ℝ} (hα : 0 < α) {X : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ α → ENNReal.ofReal (a - ε) ≤ X) : ENNReal.ofReal a ≤ X := by
  by_cases hX : X = ⊤
  · simp [hX]
  rw [ENNReal.ofReal_le_iff_le_toReal hX]
  by_contra hcon
  push Not at hcon
  set ε := min α ((a - X.toReal) / 2)
  have hε : 0 < ε := lt_min hα (by linarith)
  have := (ENNReal.ofReal_le_iff_le_toReal hX).1 (h ε hε (min_le_left _ _))
  have : ε ≤ (a - X.toReal) / 2 := min_le_right _ _
  linarith

lemma exists_eps_opt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {D : Data} {pat : Pattern}
    {ξ : ℕ → Ω → E D.d}
    (hbot : value P D pat ξ ≠ ⊥) (htop : value P D pat ξ ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ feasible P D pat ξ, objective P D ξ x ≤ (value P D pat ξ).toReal + ε := by
  have hlt : value P D pat ξ < (((value P D pat ξ).toReal + ε : ℝ) : EReal) := by
    conv_lhs => rw [← EReal.coe_toReal htop hbot]
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  unfold value at hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨x, hx⟩ := hlt
  rw [iInf_lt_iff] at hx
  obtain ⟨hxf, hx⟩ := hx
  exact ⟨x, hxf, (EReal.coe_lt_coe_iff.1 hx).le⟩

end MStabRed14

theorem solution (D : Data) (pat : Pattern) (hpat : pat.Holds D)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D)
    (hv_bot : value P D pat ξ ≠ ⊥) (hv_top : value P D pat ξ ≠ ⊤)
    (α δ : ℝ) (R : NNReal) (hα : 0 < α) (hδ : 0 < δ)
    (hA2 : LevelBoundedWith P D pat ξ α δ R)
    (hA3 : Admissible P D pat ξ) (hX1 : Bornology.IsBounded (X1 D)) :
    ∃ L : ℝ, 0 < L ∧
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
        inputDist P D pat ξ ξ' < ENNReal.ofReal δ →
        value P D pat ξ' ≠ ⊥ → value P D pat ξ' ≠ ⊤ →
        ENNReal.ofReal ((value P D pat ξ').toReal - (value P D pat ξ).toReal) ≤
          ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
            ∑ t ∈ Finset.Icc 2 (D.T - 1),
              ⨆ xbar ∈ levelSet P D pat ξ ((value P D pat ξ).toReal + α),
                eLpNorm (xbar t - P[xbar t | sigmaGen ξ' t]) (r' pat) P) := by
  have key : ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ α →
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
        inputDist P D pat ξ ξ' < ENNReal.ofReal δ →
        value P D pat ξ' ≠ ⊥ → value P D pat ξ' ≠ ⊤ →
        ∀ xbar ∈ levelSet P D pat ξ ((value P D pat ξ).toReal + ε),
          ENNReal.ofReal ((value P D pat ξ').toReal - (value P D pat ξ).toReal - ε) ≤
            ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
              ∑ τ ∈ Finset.Icc 2 (D.T - 1),
                eLpNorm (xbar τ - P[xbar τ | sigmaGen ξ' τ]) (r' pat) P) := by
    cases pat
    · exact case_costs_random D hpat P ξ hA1 hv_bot hv_top α δ R hα hδ hA2 hA3 hX1
    · exact case_rhs_random D hpat P ξ hA1 hv_bot hv_top α δ R hα hδ hA2 hA3 hX1
    · exact case_both_random D hpat P ξ hA1 hv_bot hv_top α δ R hα hδ hA2 hA3 hX1
  obtain ⟨L, hL, hf⟩ := key
  refine ⟨L, hL, fun ξ' hξ' hd hv'bot hv'top => ?_⟩
  refine MStabRed14.ofReal_le_of_eps hα fun ε hε hεα => ?_
  obtain ⟨xbar, hxf, hxo⟩ := MStabRed14.exists_eps_opt P hv_bot hv_top hε
  refine (hf ε hε hεα ξ' hξ' hd hv'bot hv'top xbar ⟨hxf, hxo⟩).trans ?_
  gcongr with t ht
  exact le_iSup₂ (f := fun x (_ : x ∈ levelSet P D pat ξ ((value P D pat ξ).toReal + α)) =>
    eLpNorm (x t - P[x t | sigmaGen ξ' t]) (r' pat) P) xbar ⟨hxf, hxo.trans (by linarith)⟩

-- Prove2me | solution 1 for MultistageStab.Value.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:18:12.111211+00:00
-- url     : https://prove2.me/submissions/7c82f760-ca05-4768-b499-6f1c59177d7b

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting
import Theorems.Thm_MultistageStab_Value_display_14
import Theorems.Thm_MultistageStab_Value_display_15

open MeasureTheory ProbabilityTheory MultistageStab.Value
open scoped ENNReal

theorem solution (D : Data) (pat : Pattern) (hpat : pat.Holds D)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D) (hA2 : A2 P D pat ξ)
    (hA3 : Admissible P D pat ξ) (hX1 : Bornology.IsBounded (X1 D)) :
    ∃ L : ℝ, 0 < L ∧ ∃ α : ℝ, 0 < α ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
        inputDist P D pat ξ ξ' ≤ ENNReal.ofReal δ →
        value P D pat ξ' ≠ ⊥ → value P D pat ξ' ≠ ⊤ →
        ENNReal.ofReal |(value P D pat ξ).toReal - (value P D pat ξ').toReal| ≤
          ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
            ∑ t ∈ Finset.Icc 2 (D.T - 1), filtDist P D pat ξ ξ' α t) := by
  obtain ⟨hvb, hvt, α, hα, δ, hδ, R, hLB⟩ := hA2
  obtain ⟨L1, hL1, h1⟩ := display_14 D pat hpat P ξ hA1 hvb hvt α δ R hα hδ hLB hA3 hX1
  obtain ⟨L2, hL2, h2⟩ := display_15 D pat hpat P ξ hA1 hvb hvt α δ R hα hδ hLB hA3 hX1
  refine ⟨max L1 L2, lt_max_of_lt_left hL1, α, hα, δ / 2, by positivity,
    fun ξ' hξ' hd hb ht => ?_⟩
  have hd' : inputDist P D pat ξ ξ' < ENNReal.ofReal δ :=
    hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).2 (by linarith))
  rw [abs_eq_max_neg, ENNReal.ofReal_max, neg_sub]
  refine max_le ((h2 ξ' hξ' hd' hb ht).trans ?_) ((h1 ξ' hξ' hd' hb ht).trans ?_)
  · gcongr
    · exact le_max_right _ _
    · exact le_max_right _ _
  · gcongr
    · exact le_max_left _ _
    · exact le_max_left _ _

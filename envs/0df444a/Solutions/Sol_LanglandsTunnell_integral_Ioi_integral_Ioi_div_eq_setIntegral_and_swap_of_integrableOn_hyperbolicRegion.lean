-- Prove2me | solution 1 for LanglandsTunnell.integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e5e10c76-26f1-5e67-aa3d-4fb51dda2dd0

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion

set_option autoImplicit false

open MeasureTheory Set

namespace FbSwap

lemma section_fst (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ) (σ : ℝ) :
    (∫ w : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w))
      = (Ioi (0 : ℝ)).indicator (fun σ : ℝ => ∫ w in Ioi (v / σ), f (σ, w)) σ := by
  by_cases hσ : 0 < σ
  · rw [indicator_of_mem (mem_Ioi.mpr hσ), ← integral_indicator measurableSet_Ioi]
    congr 1
    funext w
    have hiff : (σ, w) ∈ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} ↔ w ∈ Ioi (v / σ) := by
      simp only [mem_setOf_eq, mem_Ioi]
      constructor
      · rintro ⟨-, -, h⟩
        rw [div_lt_iff₀ hσ]
        linarith [mul_comm σ w]
      · intro h
        have h' := (div_lt_iff₀ hσ).mp h
        refine ⟨hσ, ?_, by linarith [mul_comm σ w]⟩
        by_contra hw'
        have hw'' := not_lt.mp hw'
        nlinarith
    by_cases hmem : w ∈ Ioi (v / σ)
    · rw [indicator_of_mem hmem, indicator_of_mem (hiff.mpr hmem)]
    · rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (hiff.mp h))]
  · rw [indicator_of_notMem (fun h : σ ∈ Ioi (0:ℝ) => hσ (mem_Ioi.mp h))]
    have hzero : ∀ w : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w) = 0 := by
      intro w
      apply indicator_of_notMem
      intro h
      exact hσ h.1
    simp [hzero]

lemma section_snd (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ) (w : ℝ) :
    (∫ σ : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w))
      = (Ioi (0 : ℝ)).indicator (fun w : ℝ => ∫ σ in Ioi (v / w), f (σ, w)) w := by
  by_cases hw : 0 < w
  · rw [indicator_of_mem (mem_Ioi.mpr hw), ← integral_indicator measurableSet_Ioi]
    congr 1
    funext σ
    have hiff : (σ, w) ∈ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} ↔ σ ∈ Ioi (v / w) := by
      simp only [mem_setOf_eq, mem_Ioi]
      constructor
      · rintro ⟨-, -, h⟩
        rw [div_lt_iff₀ hw]
        linarith
      · intro h
        have h' := (div_lt_iff₀ hw).mp h
        refine ⟨?_, hw, by linarith⟩
        by_contra hs
        have hs' := not_lt.mp hs
        nlinarith
    by_cases hmem : σ ∈ Ioi (v / w)
    · rw [indicator_of_mem hmem, indicator_of_mem (hiff.mpr hmem)]
    · rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (hiff.mp h))]
  · rw [indicator_of_notMem (fun h : w ∈ Ioi (0:ℝ) => hw (mem_Ioi.mp h))]
    have hzero : ∀ σ : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w) = 0 := by
      intro σ
      apply indicator_of_notMem
      intro h
      exact hw h.2.1
    simp [hzero]

lemma measurableSet_region (v : ℝ) :
    MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_const (measurable_fst.mul measurable_snd)))

theorem main (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
    (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
      (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q := by
  have hR := measurableSet_region v
  have hint : Integrable ({q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have := hf.integrable_indicator hR
    rwa [Measure.volume_eq_prod] at this
  have key : ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q
      = ∫ q, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f q
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [integral_indicator hR, Measure.volume_eq_prod]
  constructor
  · rw [key, integral_prod _ hint, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext σ
    exact (section_fst v hv f σ).symm
  · rw [key, integral_prod_symm _ hint, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext w
    exact (section_snd v hv f w).symm

end FbSwap

theorem solution
    (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
    (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
      (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q :=
  FbSwap.main v hv f hf

end S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion
end P2MW
export P2MW.S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion (solution)

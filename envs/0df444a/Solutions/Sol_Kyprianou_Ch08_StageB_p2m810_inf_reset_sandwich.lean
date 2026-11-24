-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_inf_reset_sandwich
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:05:39.554805+00:00
-- url     : https://prove2.me/submissions/40dbfc86-24c2-467e-8500-9bbc86f354d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_first_cycle_inequalities
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_cycle_factor
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit renewal reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      let R := fun (ε b : ℝ) => ((Zscale q (W q) (x+ε) -
        W q (x+ε) * ((Zscale q (W q) ε - 1) / W q ε)) /
      (Zscale q (W q) (b+ε) -
        W q (b+ε) * ((Zscale q (W q) ε - 1) / W q ε)))
      let F := ∫ ω, discountedAt q (reflectedInfExit D.X x a ω) ∂P
      F ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < a →
        R ε a ≤ F ∧ (x ≤ a - ε → F ≤ R ε (a-ε)) := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa
  dsimp only
  let F := fun y : ℝ => ∫ ω, discountedAt q (reflectedInfExit D.X y a ω) ∂P
  obtain ⟨hF, hc⟩ := p2m810_inf_first_cycle_inequalities Ω P D ψ W hψ hW q x a hq ha hx hxa
  obtain ⟨_, hzero⟩ := p2m810_inf_first_cycle_inequalities Ω P D ψ W hψ hW q 0 a hq ha le_rfl ha.le
  refine ⟨hF, ?_⟩
  intro ε he ht
  obtain ⟨hlo, hhi⟩ := hc ε he ht
  obtain ⟨hzlo,hzhi⟩ := hzero ε he ht
  obtain ⟨ha0, hb0, hbx, hr⟩ := p2m810_inf_cycle_factor Ω P D ψ W hψ hW q x a hq ha hx hxa ε a he ha hxa
  dsimp only at *
  simp only [zero_add] at *
  have hl0 : upBeforeDownExpectation P D.X q ε (a+ε) /
      (1-downBeforeUpExpectation P D.X q ε (a+ε)) ≤ F 0 :=
    (div_le_iff₀ (sub_pos.mpr hb0)).2 (by dsimp [F] at *; linarith)
  constructor
  · rw [← hr]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl0 hbx)).trans hlo
  · intro hxa'
    have hb : 0 < a-ε := sub_pos.mpr ht
    obtain ⟨ha0', hb0', hbx', hr'⟩ := p2m810_inf_cycle_factor Ω P D ψ W hψ hW q x a hq ha hx hxa ε (a-ε) he hb hxa'
    simp only [zero_add] at hb0' hr'
    have hu0 : F 0 ≤ upBeforeDownExpectation P D.X q ε (a-ε+ε) /
        (1-downBeforeUpExpectation P D.X q ε (a-ε+ε)) :=
      (le_div_iff₀ (sub_pos.mpr hb0')).2 (by
        have h := hzhi hb.le
        dsimp [F] at *
        linarith)
    rw [← hr']
    exact (hhi hxa').trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hu0 hbx'))

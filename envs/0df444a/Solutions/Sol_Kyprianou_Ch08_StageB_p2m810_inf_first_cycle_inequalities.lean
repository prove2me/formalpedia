-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_inf_first_cycle_inequalities
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:55:48.489433+00:00
-- url     : https://prove2.me/submissions/621e7ae9-fb88-481c-8fe0-f402712e1097
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_cycle_regeneration
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_cycle_path_comparison
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_measurable_ruin_path_reward
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Combine first-cycle path comparison with strong Markov regeneration. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      let F := fun y : ℝ => ∫ ω, discountedAt q (reflectedInfExit D.X y a ω) ∂P
      let A := fun (ε b y : ℝ) => upBeforeDownExpectation P D.X q (y+ε) (b+ε)
      let B := fun (ε b y : ℝ) => downBeforeUpExpectation P D.X q (y+ε) (b+ε)
      F x ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < a →
        A ε a x + B ε a x * F 0 ≤ F x ∧
        (x ≤ a-ε → F x ≤ A ε (a-ε) x + B ε (a-ε) x * F 0) := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa
  dsimp only
  obtain ⟨hm, hb, _⟩ := source_result81_measurable_ruin_path_reward q a hq
  constructor
  · by_cases hi : Integrable (fun ω => discountedAt q (reflectedInfExit D.X x a ω)) P
    · simpa using integral_mono hi (integrable_const (1 : ℝ))
        (fun ω => (hb (reflectedInfExit D.X x a ω)).2)
    · rw [integral_undef hi]
      norm_num
  · intro ε he ht
    obtain ⟨hlo,hhi⟩ := p2m810_inf_cycle_path_comparison Ω P D ψ W hψ hW q x a hq ha hx hxa ε he ht
    dsimp only at hlo hhi
    constructor
    · have heq := p2m810_inf_cycle_regeneration Ω P D ψ W hψ hW q x a hq ha hx hxa ε a he ha hxa
      exact heq.symm.trans_le hlo
    · intro h
      have hh := hhi h
      have heq := p2m810_inf_cycle_regeneration Ω P D ψ W hψ hW q x a
        hq ha hx hxa ε (a-ε) he (sub_pos.mpr ht) h
      exact hh.trans_eq heq

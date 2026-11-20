-- Prove2me | solution 1 for LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:27:59.015857+00:00
-- url     : https://prove2.me/submissions/05913fa9-4bcb-4266-89bf-e31dca86764f

import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F000

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Probability

theorem AuxTim.ident {α : Type*} [MeasurableSpace α] {m : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    @inner ℂ _ _ (hf.star.toLp (star f)) (hg.toLp g) = ∫ x, f x * g x ∂m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.star.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply']
  simp

theorem _root_.solution {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F G : ℕ → α → ℂ} {F' G' : α → ℂ} (hF : ∀ n, MemLp (F n) 2 m) (hG : ∀ n, MemLp (G n) 2 m)
    (hF' : MemLp F' 2 m) (hG' : MemLp G' 2 m)
    (hFc : Tendsto (fun n => eLpNorm (fun x => F n x - F' x) 2 m) atTop (𝓝 0))
    (hGc : Tendsto (fun n => eLpNorm (fun x => G n x - G' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * G n x ∂m) atTop (𝓝 (∫ x, F' x * G' x ∂m)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hA : Tendsto (fun n => (hF n).star.toLp (star (F n))) atTop
      (𝓝 (hF'.star.toLp (star F'))) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => (hF n).star) _ hF'.star).2 ?_
    refine hFc.congr fun n => ?_
    rw [← star_sub, eLpNorm_star]
    rfl
  have hB : Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 (hG'.toLp G')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hG _ hG').2 hGc
  have hC := hA.inner hB (𝕜 := ℂ)
  have e1 : (fun n => @inner ℂ _ _ ((hF n).star.toLp (star (F n))) ((hG n).toLp (G n)))
      = fun n => ∫ x, F n x * G n x ∂m := funext fun n => AuxTim.ident (hF n) (hG n)
  rw [e1, AuxTim.ident hF' hG'] at hC
  exact hC

end LevyStochCalc.Probability

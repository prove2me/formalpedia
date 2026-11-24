-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_sup_zero_slope_no_crossing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:33:33.754975+00:00
-- url     : https://prove2.me/submissions/c0dedcaa-4c03-4041-ac08-6d79fb82e3a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_zero_slope_record_survival
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_certain_record_ae
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_survival_path_lower_bound
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_levy_uniform_lower_bound_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_monotone_path_no_drawdown
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_Kyprianou_Ch02_levyMonotoneOfNonnegativeMarginalsV1
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Zero slope path reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      derivWithin (W q) (Ici a) a = 0 →
      ∀ᵐ ω ∂P, reflectedSupExit D.X x a ω = ⊤ := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa hz
  obtain ⟨hq0,hs⟩ := p2m810_zero_slope_record_survival Ω P D ψ W hψ hW q 0 a hq ha le_rfl ha.le hz
  subst q
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, tauPlus D.X ((n:ℝ)+1) ω < reflectedSupExit D.X 0 a ω :=
    ae_all_iff.2 (fun n => p2m810_certain_record_ae Ω P D.X _ a (hs _ (by positivity)))
  have hb : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, -a ≤ D.X t ω := by
    filter_upwards [hall,D.levy.cadlag_ae] with ω hw hc
    exact p2m810_record_survival_path_lower_bound Ω D.X ω a ha.le
      (congrFun D.levy.start_zero ω)
      (fun T => Kyprianou.Ch01.cadlag_runningSup_bddAbove (fun t => D.X t ω) hc T) hw
  have hn := p2m810_levy_uniform_lower_bound_nonnegative Ω P D.X D.levy a
    (fun t => hb.mono (fun ω h => h t))
  filter_upwards [Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1 P D.X D.levy hn] with ω hm
  exact p2m810_monotone_path_no_drawdown Ω D.X ω x a (congrFun D.levy.start_zero ω) hm hx hxa

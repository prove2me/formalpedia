-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_causal_convolution_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:58:29.591981+00:00
-- url     : https://prove2.me/submissions/d63bece4-6d49-4229-8eab-b0a5dd1913fe

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB Set

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    IntegrableOn (fun s : ℝ => W q s * W q (x - s))
      (Set.Ioc (0 : ℝ) x) volume := by
  have hcont := (source_family_positive_monotone ψ W hW q hq).2.2
  have hIcc : ContinuousOn (W q) (Set.Icc (0 : ℝ) x) :=
    hcont.mono (by intro s hs; exact hs.1)
  have hsub : ContinuousOn (fun s : ℝ => x - s) (Set.Icc 0 x) :=
    (continuous_const.sub continuous_id).continuousOn
  have hmap : MapsTo (fun s : ℝ => x - s) (Set.Icc 0 x) (Set.Ici 0) :=
    fun s hs => sub_nonneg.mpr hs.2
  have hcomp : ContinuousOn (fun s : ℝ => W q (x - s))
      (Set.Icc (0 : ℝ) x) := by
    simpa only [Function.comp_def] using hcont.comp hsub hmap
  have hprod : ContinuousOn (fun s : ℝ => W q s * W q (x - s))
      (Set.Icc (0 : ℝ) x) := hIcc.mul hcomp
  have hint : IntegrableOn (fun s : ℝ => W q s * W q (x - s))
      (Set.Icc (0 : ℝ) x) volume := hprod.integrableOn_Icc
  exact (integrableOn_Icc_iff_integrableOn_Ioc).mp hint

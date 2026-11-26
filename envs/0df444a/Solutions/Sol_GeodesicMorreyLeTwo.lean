-- Prove2me | solution 1 for GeodesicMorreyLeTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:46.146685+00:00
-- url     : https://prove2.me/submissions/3d2c43bf-dbb6-426d-bbfb-5251bbc1c765

import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_IsGeodesicOn
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (a b : ℝ) (hab : a ≤ b) (hbnd : b ≤ γ.len) (hgeo : IsGeodesicOn γ a b) :
    morreyNorm (Measure.map γ.toFun (volume.restrict (Set.Icc a b))) ≤ 2 := by
-- BODY
  have hmeas : Measurable γ.toFun := (CurveLipschitz γ).continuous.measurable
  refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
  set S : Set ℝ := (γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc a b with hS
  have heq : Measure.map γ.toFun (volume.restrict (Set.Icc a b)) (Metric.closedBall x r) =
      volume S := by
    rw [Measure.map_apply hmeas measurableSet_closedBall,
      Measure.restrict_apply (hmeas measurableSet_closedBall)]
  rw [heq]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  · have hbdd_above : BddAbove S := ⟨b, fun t ht => ht.2.2⟩
    have hbdd_below : BddBelow S := ⟨a, fun t ht => ht.2.1⟩
    have hpair : ∀ t ∈ S, ∀ t' ∈ S, t ≤ t' + 2 * r := by
      intro t ht t' ht'
      have hdxy : dist (γ.toFun t) (γ.toFun t') ≤ 2 * r := by
        have h1 : dist (γ.toFun t) x ≤ r := ht.1
        have h2 : dist x (γ.toFun t') ≤ r := (dist_comm (γ.toFun t') x) ▸ ht'.1
        calc dist (γ.toFun t) (γ.toFun t') ≤ dist (γ.toFun t) x + dist x (γ.toFun t') :=
              dist_triangle _ _ _
          _ ≤ r + r := add_le_add h1 h2
          _ = 2 * r := by ring
      have heqd : dist (γ.toFun t) (γ.toFun t') = |t - t'| := hgeo t ht.2 t' ht'.2
      rw [heqd] at hdxy
      have := abs_le.mp hdxy
      linarith [this.1]
    have hsup_le : ∀ t' ∈ S, sSup S ≤ t' + 2 * r :=
      fun t' ht' => csSup_le hSne (fun t ht => hpair t ht t' ht')
    have hlen : sSup S - sInf S ≤ 2 * r := by
      have : sSup S - 2 * r ≤ sInf S :=
        le_csInf hSne (fun t' ht' => by linarith [hsup_le t' ht'])
      linarith
    have hSsub : S ⊆ Set.Icc (sInf S) (sSup S) :=
      fun t ht => ⟨csInf_le hbdd_below ht, le_csSup hbdd_above ht⟩
    have hvol : volume S ≤ volume (Set.Icc (sInf S) (sSup S)) := measure_mono hSsub
    rw [Real.volume_Icc] at hvol
    have hle2r : volume S ≤ ENNReal.ofReal (2 * r) :=
      hvol.trans (ENNReal.ofReal_le_ofReal hlen)
    calc volume S / ENNReal.ofReal r ≤ ENNReal.ofReal (2 * r) / ENNReal.ofReal r :=
          ENNReal.div_le_div_right hle2r _
      _ = 2 := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), mul_div_assoc,
            ENNReal.div_self (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top, mul_one]
          simp

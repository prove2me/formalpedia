-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DepthSplitAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:36:50.419622+00:00
-- url     : https://prove2.me/submissions/8f3dbaf0-98d5-4137-8a7e-4c3fa74a2bba

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49FinitePathLowerBoundAEV1
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalDepthIsLUBV1
import Theorems.Thm_Kyprianou_Ch04_exercise49StrictPassagePathFactsV1
import Theorems.Thm_Kyprianou_Ch04_exercise49DepthSplitOfLUBV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- The finite-passage deficit plus future depth equals the original all-time depth almost surely. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ w, IsCadlag (fun t => X t w))
    (hInf : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop)
    (τ : Ω → WithTop NNReal)
    (hτ : ∀ w, τ w = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0})
    (hτm : Measurable τ) (f : Ω → NNReal) (hf : Measurable f)
    (he : ∀ w, τ w ≠ ⊤ → τ w = (f w : WithTop NNReal)) :
    let V : Ω → ℝ := fun w => (⨆ q : ℚ, ENNReal.ofReal (-X (Real.toNNReal q) w)).toReal
    let W : Ω → ℝ := fun w => (⨆ q : ℚ,
      ENNReal.ofReal (-(X (f w + Real.toNNReal q) w - X (f w) w))).toReal
    ∀ᵐ w ∂P.restrict {w | τ w ≠ ⊤}, V w = -X (f w) w + W w := by
  dsimp only
  have hD : MeasurableSet {w | τ w ≠ ⊤} := (hτm (measurableSet_singleton ⊤)).compl
  have hBound := Kyprianou.Ch04.exercise49FinitePathLowerBoundAEV1 P X hX hm hc hInf
  filter_upwards [hBound.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem hD] with w hw hDw
  have hrc (t : NNReal) : ContinuousWithinAt (fun u => X u w) (Ici t) t :=
    (hc w t).1
  have hL := Kyprianou.Ch04.exercise49RationalDepthIsLUBV1 (fun t => X t w)
    (congrFun hX.start_zero w) hrc hw
  have ht := (he w hDw).symm.trans (hτ w)
  obtain ⟨hp, ht0⟩ := Kyprianou.Ch04.exercise49StrictPassagePathFactsV1
    (fun t => X t w) (congrFun hX.start_zero w) hrc (f w) ht
  have hrc' (t : NNReal) :
      ContinuousWithinAt (fun u => X (f w + u) w - X (f w) w) (Ici t) t := by
    apply ContinuousWithinAt.sub _ continuousWithinAt_const
    exact (hrc (f w + t)).comp
      (continuous_const.add continuous_id).continuousWithinAt
      (fun u hu => show f w + t ≤ f w + u from add_le_add_right hu _)
  have hb : BddAbove (range (fun u : NNReal => -(X (f w + u) w - X (f w) w))) := by
    obtain ⟨b, hb⟩ := hw
    refine ⟨b + X (f w) w, ?_⟩
    rintro _ ⟨u, rfl⟩
    linarith [hb (mem_range_self (f w + u))]
  have hL' := Kyprianou.Ch04.exercise49RationalDepthIsLUBV1
    (fun u => X (f w + u) w - X (f w) w) (by simp) hrc' hb
  exact Kyprianou.Ch04.exercise49DepthSplitOfLUBV1 (fun t => X t w) (f w)
    _ _ hp ht0 hL hL'

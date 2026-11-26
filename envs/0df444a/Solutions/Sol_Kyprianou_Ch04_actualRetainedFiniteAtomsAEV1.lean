-- Prove2me | solution 1 for Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:37:58.516695+00:00
-- url     : https://prove2.me/submissions/27d5c294-eee6-4131-951d-d92bf50b2532

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalWindowExactJumpAtomsV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousTimeMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_leftLimitTimeMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact finite retained atoms on every finite horizon of the original Levy path. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun u => X u w) (𝓝[<] t) (𝓝 (L t w)))
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w)
    (e : ℝ) (he : 0 < e) :
    ∀ᵐ w ∂P, ∀ T : NNReal, ∃ S : Finset NNReal,
      (∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |X r w - L r w|) ∧
      (N.N w).restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
        ∑ r ∈ S, Measure.dirac ((r : ℝ),X r w - L r w) := by
  let B := {x : ℝ | e < |x|}
  let D (t : NNReal) := Icc (0 : ℝ) (t : ℝ) ×ˢ B
  have hB : MeasurableSet B := measurableSet_lt measurable_const measurable_id.abs
  have hfin : ν B < ⊤ :=
    (measure_mono (show B ⊆ {x : ℝ | e ≤ |x|} from
      fun x hx => (show e < |x| from hx).le)).trans_lt
      (hν.measure_setOf_abs_ge_lt_top he)
  have hFin (n : ℕ) : ∀ᵐ w ∂P, N.N w (D n) < ⊤ := by
    filter_upwards [N.integer_valued (measurableSet_Icc.prod hB)
      (Kyprianou.Ch04.closedTimeBandIntensityFinite ν n B hfin)] with w hw
    obtain ⟨k,hk⟩ := hw
    rw [hk]
    exact ENNReal.natCast_lt_top k
  have hAll : ∀ᵐ w ∂P, ∀ n : ℕ, N.N w (D n) < ⊤ := ae_all_iff.mpr hFin
  filter_upwards [hAll,hX.cadlag_ae,hL,hN] with w hw hCad hl hn
  intro T
  obtain ⟨n,hnT⟩ := exists_nat_ge T
  have hmass : N.N w (D T) < ⊤ :=
    (measure_mono (prod_mono (Icc_subset_Icc_right (by exact_mod_cast hnT)) subset_rfl)).trans_lt
      (hw n)
  have hx := Kyprianou.Ch04.rightContinuousTimeMeasurableV1 (fun u => X u w)
    (fun u => (hCad u).1)
  have hm := Kyprianou.Ch04.leftLimitTimeMeasurableV1 (fun u => X u w)
    (fun u => L u w) hx hl
  rw [hn] at hmass
  obtain ⟨S,hS,hR⟩ := Kyprianou.Ch04.finitePhysicalWindowExactJumpAtomsV1
    X L w hx hm (D T) (measurableSet_Icc.prod hB) hmass
  refine ⟨S,?_,?_⟩
  · intro r hr
    have h := (hS r).mp hr
    exact ⟨h.1,by exact_mod_cast h.2.2.1.2,h.2.2.2⟩
  · rw [hn]
    exact hR

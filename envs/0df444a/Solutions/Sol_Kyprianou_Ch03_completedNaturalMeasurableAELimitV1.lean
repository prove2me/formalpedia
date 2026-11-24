-- Prove2me | solution 1 for Kyprianou.Ch03.completedNaturalMeasurableAELimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:18:00.054956+00:00
-- url     : https://prove2.me/submissions/6a85ba49-8197-4aa3-8270-1eea7c049159

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAEModV1
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (s : NNReal) (U : ℕ → Omega → ℝ) (V : Omega → ℝ)
    (hU : ∀ k, Measurable[F s] (U k))
    (hV : ∀ᵐ w ∂P, Tendsto (fun k => U k w) atTop (𝓝 (V w))) :
    Measurable[F s] V := by
  classical
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hV)
  have hNae : ∀ᵐ w ∂P, w ∉ N := ae_iff.mpr (by simpa using hN0)
  have hNF : MeasurableSet[F s] N :=
    completedNaturalMeasurableAEModV1 P F X hNatural s N ∅ (@MeasurableSet.empty Omega (F s))
      (hNae.mono fun w hw => by simp [hw])
  let W (w : Omega) := if w ∈ N then 0 else V w
  have hW : Measurable[F s] W := by
    letI : MeasurableSpace Omega := F s
    apply measurable_of_tendsto_metrizable
      (f := fun k w => if w ∈ N then 0 else U k w)
      (fun k => measurable_const.piecewise hNF (hU k))
    apply tendsto_pi_nhds.mpr
    intro w
    by_cases hw : w ∈ N
    · simpa only [hw, if_true, W] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [hw, if_false, W] using
        (show Tendsto (fun k => U k w) atTop (𝓝 (V w)) from
          by_contra (fun hn => hw (hN hn)))
  intro B hB
  apply completedNaturalMeasurableAEModV1 P F X hNatural s _ (W ⁻¹' B) (hW hB)
  filter_upwards [hNae] with w hw
  simp [W,hw]

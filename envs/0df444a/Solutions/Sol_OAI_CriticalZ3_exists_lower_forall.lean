-- Prove2me | solution 1 for OAI.CriticalZ3.exists_lower_forall
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:33:10.534164+00:00
-- url     : https://prove2.me/submissions/e3135dd7-3986-41f7-994a-9b5435237ff5

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Filter Topology Classical


theorem solution {I : Type uI} [Finite I] {p γ : ℝ} (hp : 0 < p)
    (g : I → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) (hgp : ∀ i, g i p < γ) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ i, g i q < γ := by
  have hU : IsOpen (⋂ i, {q : ℝ | g i q < γ}) :=
    isOpen_iInter_of_finite (fun i => isOpen_lt (hg i) continuous_const)
  have hpU : p ∈ ⋂ i, {q : ℝ | g i q < γ} := Set.mem_iInter.mpr hgp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hpU
  set δ := min ε p with hδ
  have hδpos : 0 < δ := lt_min hε hp
  have hδε : δ ≤ ε := min_le_left _ _
  have hδp : δ ≤ p := min_le_right _ _
  refine ⟨p - δ / 4, ⟨by linarith, by linarith⟩, fun i => ?_⟩
  have hmem : p - δ / 4 ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  exact Set.mem_iInter.mp (hball hmem) i


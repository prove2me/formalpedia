-- Prove2me | solution 1 for Kyprianou.Ch04.compactLeftWeightBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:55:09.20748+00:00
-- url     : https://prove2.me/submissions/ef461017-38eb-4f2b-a4b6-e5be9156da4d

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Continuous time-space weights on a cadlag left-limit path are bounded on compact horizons. -/
theorem solution (Y L : NNReal → ℝ) (f : ℝ → ℝ → ℝ)
    (hY : IsCadlag Y)
    (hL : ∀ t, 0 < t → Tendsto Y (𝓝[<] t) (𝓝 (L t)))
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (T : NNReal) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ≤ T, |f (r : ℝ) (L r)| ≤ C := by
  obtain ⟨R,hR,_,hB⟩ := (Kyprianou.Ch04.exercise41PathCompactV10
    (fun t (_ : Unit) => Y t) (fun t (_ : Unit) => L t) () hY hL T).2
  let B := max R |L 0|
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ Icc (-B) B
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  have hsub : D ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun _ hz => ⟨hz.1.1,mem_univ _⟩
  have hc : ContinuousOn (fun z : ℝ × ℝ => |f z.1 z.2|) D := (hf.mono hsub).abs
  obtain ⟨C,hC⟩ := (hD.image_of_continuousOn hc).bddAbove
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro r hr
  have hLbound : |L r| ≤ B := by
    by_cases hz : r = 0
    · rw [hz]; exact le_max_right _ _
    · exact (hB r (pos_iff_ne_zero.mpr hz) hr).trans (le_max_left _ _)
  have hmem : ((r : ℝ),L r) ∈ D :=
    ⟨⟨r.coe_nonneg,by exact_mod_cast hr⟩,abs_le.mp hLbound⟩
  exact (hC ⟨_,hmem,rfl⟩).trans (le_max_right _ _)

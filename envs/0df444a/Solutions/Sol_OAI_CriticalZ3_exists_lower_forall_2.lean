-- Prove2me | solution 2 for OAI.CriticalZ3.exists_lower_forall
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:27:45.580977+00:00
-- url     : https://prove2.me/submissions/de76b16f-2647-40b7-bfb5-8cc54dc8511e

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/QuarterFaces.lean:L356-L371
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.exists_lower_forall. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

-- ---- from OAI.Probability.CriticalZ3.QuarterFaces ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

universe uE uI uV uW

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! The 24 signed-coordinate quarter-faces, symmetry and the Harris root bound.
The probability statements here are for the actual infinite lattice laws. -/
namespace CriticalZ3
open Classical

namespace SignedSymmetry

end SignedSymmetry

end CriticalZ3

namespace ProductCylinder

end ProductCylinder

namespace CriticalZ3
open Classical

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

/-- A single strictly lower parameter preserves simultaneous finite strict bounds. -/
theorem exists_lower_forall {I : Type uI} [Finite I] {p γ : ℝ} (hp : 0 < p)
    (g : I → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) (hgp : ∀ i, g i p < γ) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ i, g i q < γ := by
  have ho : IsOpen {q | ∀ i, g i q < γ} := by
    have he : {q | ∀ i, g i q < γ} = ⋂ i, (g i) ⁻¹' Set.Iio γ := by ext q; simp
    rw [he]
    exact isOpen_iInter_of_finite (fun i => isOpen_Iio.preimage (hg i))
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho p hgp
  let a : ℝ := min (p/4) (ε/2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hap : a ≤ p/4 := min_le_left _ _
  have hae : a ≤ ε/2 := min_le_right _ _
  refine ⟨p-a,⟨by linarith,by linarith⟩,hball ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos ha]
  linarith

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3
open MeasureTheory ProbabilityTheory Classical
open Filter Topology Classical


theorem solution.{uI} : type_of% @_root_.OAI.CriticalZ3.exists_lower_forall.{uI} := @_root_.OAI.CriticalZ3.exists_lower_forall.{uI}

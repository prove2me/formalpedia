-- Prove2me | solution 1 for OAI.Problem313.logistic_coordinate_width
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:46:07.944002+00:00
-- url     : https://prove2.me/submissions/68d6b4de-1b95-44b5-b843-ac803ecbe77e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/ThresholdODE.lean:L21-L54
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.logistic_coordinate_width. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Quantile

-- ---- from OAI.Combinatorics.SharpThreshold.ThresholdODE ----
namespace OAI

noncomputable section

namespace Problem313

/-- The derivative of log odds, stated without any probability-specific definitions. -/
theorem hasDerivAt_log_odds {μ : ℝ → ℝ} {d x : ℝ}
    (hd : HasDerivAt μ d x) (hpos : 0 < μ x) (hone : μ x < 1) :
    HasDerivAt (fun t => Real.log (μ t) - Real.log (1 - μ t))
      (d / (μ x * (1 - μ x))) x := by
  have hne : μ x ≠ 0 := ne_of_gt hpos
  have hne' : 1 - μ x ≠ 0 := ne_of_gt (sub_pos.mpr hone)
  convert! (hd.log hne).sub (((hasDerivAt_const x (1 : ℝ)).sub hd).log hne') using 1
  dsimp only [Pi.sub_apply]
  field_simp
  ring

/-- Integrating a logistic differential inequality by the mean value theorem.
Continuity is needed on the closed interval, differentiability only in its interior. -/
theorem logistic_coordinate_width {μ μ' : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn μ (Set.Icc a b))
    (hμ : ∀ x ∈ Set.Icc a b, 0 < μ x ∧ μ x < 1)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt μ (μ' x) x)
    (hbound : ∀ x ∈ Set.Ioo a b, μ x * (1 - μ x) ≤ C * μ' x) :
    b - a ≤ C * ((Real.log (μ b) - Real.log (1 - μ b)) -
      (Real.log (μ a) - Real.log (1 - μ a))) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    simp
  let g : ℝ → ℝ := fun x => C * (Real.log (μ x) - Real.log (1 - μ x))
  let g' : ℝ → ℝ := fun x => C * (μ' x / (μ x * (1 - μ x)))
  have hg : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.const_mul
    exact (hcont.log (fun x hx => ne_of_gt (hμ x hx).1)).sub
      ((continuousOn_const.sub hcont).log
        (fun x hx => ne_of_gt (sub_pos.mpr (hμ x hx).2)))
  have hgd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x := by
    intro x hx
    have hμx := hμ x (Set.Ioo_subset_Icc_self hx)
    exact (hasDerivAt_log_odds (hd x hx) hμx.1 hμx.2).const_mul C
  obtain ⟨x, hx, hslope⟩ := exists_hasDerivAt_eq_slope g g' hlt hg hgd
  have hμx := hμ x (Set.Ioo_subset_Icc_self hx)
  have hden : 0 < μ x * (1 - μ x) := mul_pos hμx.1 (sub_pos.mpr hμx.2)
  have hg' : 1 ≤ g' x := by
    dsimp [g']
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hden).2 (by simpa using hbound x hx)
  rw [hslope] at hg'
  have hle := (le_div_iff₀ (sub_pos.mpr hlt)).1 hg'
  dsimp [g] at hle
  linarith

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.logistic_coordinate_width := @_root_.OAI.Problem313.logistic_coordinate_width

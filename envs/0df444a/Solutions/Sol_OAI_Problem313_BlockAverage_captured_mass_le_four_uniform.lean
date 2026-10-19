-- Prove2me | solution 1 for OAI.Problem313.BlockAverage.captured_mass_le_four_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:44:03.784141+00:00
-- url     : https://prove2.me/submissions/f397136f-52da-4aa9-9444-5370c9bbde75

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockAverage.lean:L147-L179
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BlockAverage.captured_mass_le_four_uniform. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_BlockAverage_block_upper_bound
import Theorems.Thm_OAI_Problem313_BlockAverage_capture_lower_bound

-- ---- from OAI.Combinatorics.SharpThreshold.BlockAverage ----
namespace OAI

universe u v w

noncomputable section

namespace Problem313.BlockAverage

open scoped BigOperators

/-- The algebraic block-capture argument, with arbitrary capture and incidence
constants. It separates all finite averaging from the Fourier and graph input. -/
theorem captured_mass_le
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c d : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ d) :
    (∑ s ∈ low, w s) ≤ (a * d / c) * ∑ i, I i := by
  have hlow := capture_lower_bound μ w P low c hμ hw hcapture
  have hupp := block_upper_bound μ w I P E a d hμ hI ha hblock hincidence
  have hcombined := hlow.trans hupp
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c * ∑ s ∈ low, w s ≤ a * d * ∑ i, I i := hcombined
    _ = c * ((a * d / c) * ∑ i, I i) := by field_simp [ne_of_gt hc]

/-- The factor-four consequence used for uniform vertex blocks:
capture at least `m/(2*n)` and edge incidence at most `2*m/n`. -/
theorem captured_mass_le_four
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ 4 * c) :
    (∑ s ∈ low, w s) ≤ 4 * a * ∑ i, I i := by
  have h := captured_mass_le μ w I P E low a c (4 * c)
    hμ hw hI ha hc hcapture hblock hincidence
  have hc0 : c ≠ 0 := ne_of_gt hc
  have heq : a * (4 * c) / c = 4 * a := by field_simp [ne_of_gt hc]
  simpa only [heq] using h

/-- Uniform finite sampling agrees with the normalized cardinality used by the
vertex-block counting lemmas. This also holds for an empty sampling family. -/
theorem uniform_incidence_sum
    {β : Type v} [DecidableEq β] (Ω : Finset β) (P : β → Prop)
    [DecidablePred P] :
    (∑ b : Ω, if P b.val then (1 : ℝ) / Ω.card else 0) =
      ((Ω.filter P).card : ℝ) / Ω.card := by
  rw [← Finset.sum_subtype Ω (fun _ => Iff.rfl)
    (fun b => if P b then (1 : ℝ) / Ω.card else 0)]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- Uniform-block version of the factor-four capture argument, stated entirely
with cardinal-ratio probabilities to match the combinatorial counting API. -/
theorem captured_mass_le_four_uniform
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [DecidableEq β] [Fintype ι]
    (Ω : Finset β) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hI : ∀ i, 0 ≤ I i)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤
      ((Ω.filter (fun b => P b s)).card : ℝ) / Ω.card)
    (hblock : ∀ b ∈ Ω, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i,
      ((Ω.filter (fun b => E b i)).card : ℝ) / Ω.card ≤ 4 * c) :
    (∑ s ∈ low, w s) ≤ 4 * a * ∑ i, I i := by
  apply captured_mass_le_four
    (fun _ : Ω => (1 : ℝ) / Ω.card) w I
    (fun b s => P b.val s) (fun b i => E b.val i) low a c
  · intro b
    positivity
  · exact hw
  · exact hI
  · exact ha
  · exact hc
  · intro s hs
    rw [uniform_incidence_sum Ω (fun b => P b s)]
    exact hcapture s hs
  · intro b
    exact hblock b.val b.property
  · intro i
    rw [uniform_incidence_sum Ω (fun b => E b i)]
    exact hincidence i

end Problem313.BlockAverage

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BlockAverage
open scoped BigOperators


theorem solution.{u,v,w} : type_of% @_root_.OAI.Problem313.BlockAverage.captured_mass_le_four_uniform.{u,v,w} := @_root_.OAI.Problem313.BlockAverage.captured_mass_le_four_uniform.{u,v,w}

-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.poisson_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:44:44.659194+00:00
-- url     : https://prove2.me/submissions/938b21c7-ef0e-46f1-8e0b-37cfc3c1c78d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingTail.lean:L80-L113
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.poisson_tail_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_polynomial_decay

-- ---- from OAI.Analysis.Littlewood.SamplingTail ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail

lemma poisson_tail_bound {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {A B β L : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (hL : 2*(|β| * A+B)+1≤L) :
    ∃ C : ℝ, 0≤C ∧ ∀ N b : ℝ, 0<N → |b|≤B → ∀ l : ℤ,
      L≤|(l : ℝ)| →
      N^2*‖∫ x : ℝ, g x*phase (N*β) (N*((l : ℝ)-b)) x‖≤C*latticeWeight l := by
  obtain ⟨C,hC,hbound⟩ := polynomial_decay 2 (1/4) |β| (by norm_num) (abs_nonneg β) g hg hgs 0
  refine ⟨C,hC,?_⟩
  intro N b hN hb l hl
  have hℓ : 2*(|β| * A+B)+1≤|(l : ℝ)| := hL.trans hl
  have hM : 0<N*(1+|(l : ℝ)|) := by positivity
  have ht : |N*β|≤|β| * (N*(1+|(l : ℝ)|)) := by
    rw [abs_mul,abs_of_pos hN]
    nlinarith [mul_nonneg (abs_nonneg β) (abs_nonneg (l : ℝ))]
  have hs : ∀ x∈tsupport g, 1/4*(N*(1+|(l : ℝ)|))≤|N*β*x-N*((l : ℝ)-b)| := by
    intro x hx
    have hxA : |x|≤A := abs_le.mpr (hsupp hx)
    have hβx : |β*x|≤|β| * A := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hxA (abs_nonneg β)
    have htri : |(l : ℝ)|≤|β*x-((l : ℝ)-b)|+|β*x|+|b| := by
      have h := abs_add_le ((l : ℝ)-b-β*x) (β*x+b)
      have h' := abs_add_le (β*x) b
      rw [show (l : ℝ)-b-β*x+(β*x+b)=l by ring, abs_sub_comm ((l : ℝ)-b) (β*x)] at h
      linarith
    have hlo : (1+|(l : ℝ)|)/4≤|β*x-((l : ℝ)-b)| := by
      nlinarith [mul_nonneg (abs_nonneg β) hA]
    have he : N*β*x-N*((l : ℝ)-b)=N*(β*x-((l : ℝ)-b)) := by ring
    rw [he,abs_mul,abs_of_pos hN]
    nlinarith [mul_le_mul_of_nonneg_left hlo hN.le]
  have h := hbound (N*β) (N*((l : ℝ)-b)) (N*(1+|(l : ℝ)|)) hM ht hs
  simp only [Nat.zero_add,osc,amp,pow_zero,div_one] at h
  dsimp [latticeWeight]
  rw [mul_one_div,le_div_iff₀ (by positivity : (0 : ℝ)<(1+|(l : ℝ)|)^2)]
  nlinarith only [h]

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.poisson_tail_bound := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.poisson_tail_bound

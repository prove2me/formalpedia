-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:32:19.735032+00:00
-- url     : https://prove2.me/submissions/229bb619-bf46-4902-a6c4-b7e1ab2f2ea9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothHilbert.lean:L179-L202
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_approx. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_smooth_finite_min

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothHilbert ----
namespace OAI

universe uH uX

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open Filter Topology
open scoped NNReal ContDiff
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem exists_smooth_finite_approx (S : Finset H) (hS : (0 : H) ∈ S)
    (f : H → ℝ) (hf0 : f 0 = 0)
    (hf : ∀ p ∈ S, ∀ q ∈ S, |f p-f q| ≤ dist p q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : H → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith 1 g ∧ g 0 = 0 ∧
      ∀ p ∈ S, |g p-f p| < ε := by
  let δ := ε/((S.card : ℝ)+2)
  have hden : 0 < (S.card : ℝ)+2 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hid : ((S.card : ℝ)+2)*δ = ε := mul_div_cancel₀ ε hden.ne'
  obtain ⟨g,hg,hgL,hlo,hup⟩ := exists_smooth_finite_min S hS f hf δ hδ S (by rfl)
  have hgL' : LipschitzWith 1 (fun x => g x-g 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hgL.dist_le_mul x y
  refine ⟨fun x => g x-g 0,hg.sub contDiff_const,hgL',by simp,?_⟩
  intro p hp
  have h₁ := hlo p hp
  have h₂ := hup p hp
  have h₃ := hlo 0 hS
  have h₄ := hup 0 hS
  rw [hf0] at h₃ h₄
  rw [abs_lt]
  constructor <;> nlinarith

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open Filter Topology
open scoped NNReal ContDiff


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_approx.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_approx.{uH}

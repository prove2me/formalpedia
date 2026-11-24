-- Prove2me | solution 1 for GlobalTheory.CompactAvgSchwartz.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:29.907436+00:00
-- url     : https://prove2.me/submissions/1c3a46b6-d55f-4310-b873-ab6712e7d3ba

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz
variable {S V : Type} [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.CompactAvgSchwartz
theorem _root_.solution (L Li : S → V →L[ℝ] V) (hL : Continuous L) (hLi : Continuous Li) (h : ∀ s x, Li s (L s x) = x)
    (f : SchwartzMap V ℂ) (k n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f (L s y)) x‖ ≤ M := by
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn hL.continuousOn
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hLi.continuousOn
  refine ⟨|B| ^ k * |A| ^ n * SchwartzMap.seminorm ℝ k n f, by positivity, fun s x => ?_⟩
  have hA' : ‖L s‖ ≤ |A| := (hA s (Set.mem_univ _)).trans (le_abs_self A)
  have hB' : ‖Li s‖ ≤ |B| := (hB s (Set.mem_univ _)).trans (le_abs_self B)
  have hx : ‖x‖ ≤ |B| * ‖L s x‖ :=
    calc ‖x‖ = ‖Li s (L s x)‖ := by rw [h]
      _ ≤ ‖Li s‖ * ‖L s x‖ := (Li s).le_opNorm _
      _ ≤ |B| * ‖L s x‖ := by gcongr
  have e : iteratedFDeriv ℝ n (fun y => f (L s y)) x =
      (iteratedFDeriv ℝ n f (L s x)).compContinuousLinearMap fun _ => L s :=
    (L s).iteratedFDeriv_comp_right f.smooth' x (mod_cast le_top)
  have hD : ‖iteratedFDeriv ℝ n (fun y => f (L s y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (L s x)‖ * |A| ^ n := by
    rw [e]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  have hS := SchwartzMap.le_seminorm ℝ k n f (L s x)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f (L s y)) x‖
      ≤ (|B| * ‖L s x‖) ^ k * (‖iteratedFDeriv ℝ n f (L s x)‖ * |A| ^ n) := by gcongr
    _ = |B| ^ k * |A| ^ n * (‖L s x‖ ^ k * ‖iteratedFDeriv ℝ n f (L s x)‖) := by ring
    _ ≤ |B| ^ k * |A| ^ n * SchwartzMap.seminorm ℝ k n f := by gcongr
end GlobalTheory.CompactAvgSchwartz

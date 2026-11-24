-- Prove2me | solution 1 for GlobalTheory.ThetaGroupFrame.exists_const_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:14.268838+00:00
-- url     : https://prove2.me/submissions/beedeb00-44d1-4bf2-b32f-308aa9b49e35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame
namespace GlobalTheory.ThetaGroupFrame
theorem _root_.solution {g : ℕ} {J : Type*} (D : J → Set (Fin g → ℂ))
    (G : J → (Fin g → ℂ) → ℂ) (hD : ∀ j, IsOpen (D j)) (hcov : ∀ z, ∃ j, z ∈ D j)
    (hG : ∀ j, DifferentiableOn ℂ (G j) (D j))
    (hc : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z)
    {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ j z, z ∈ D j → ∀ l ∈ S, z + l ∈ D j ∧ G j (z + l) = G j z) :
    ∃ C : ℂ, ∀ j z, z ∈ D j → G j z = C := by
  classical
  choose jOf hjOf using hcov
  let F : (Fin g → ℂ) → ℂ := fun z => G (jOf z) z
  have hFeq : ∀ j z, z ∈ D j → F z = G j z := fun j z hz => hc _ _ _ (hjOf z) hz
  have hFdiff : Differentiable ℂ F := by
    intro z
    have hmem : D (jOf z) ∈ 𝓝 z := (hD _).mem_nhds (hjOf z)
    have hev : F =ᶠ[𝓝 z] G (jOf z) := by
      filter_upwards [hmem] with w hw
      exact hFeq _ _ hw
    exact ((hG _).differentiableAt hmem).congr_of_eventuallyEq hev
  have hFper : ∀ x, ∀ l ∈ S, F (x + l) = F x := by
    intro x l hl
    have h1 := hper (jOf x) x (hjOf x) l hl
    rw [hFeq _ _ h1.1, h1.2]
  refine ⟨F 0, fun j z hz => ?_⟩
  rw [← hFeq j z hz]
  exact GlobalTheory.entire_apply_eq_of_periodic_of_span_real hFdiff hS hFper z 0
end GlobalTheory.ThetaGroupFrame

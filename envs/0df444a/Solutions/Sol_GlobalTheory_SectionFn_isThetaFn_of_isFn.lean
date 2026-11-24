-- Prove2me | solution 1 for GlobalTheory.SectionFn.isThetaFn_of_isFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:56.37188+00:00
-- url     : https://prove2.me/submissions/71fb09ca-d7ec-41b0-a40a-3b4976a4d0bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsThetaFnAndNeZeroOfIsFn
import Theorems.Thm_GlobalTheory_SectionFn_differentiable_of_isFn
import Theorems.Thm_GlobalTheory_PullHermitian_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.SectionFn
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.SectionFn
theorem _root_.solution (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsThetaFn Hm χ 1 θ := by
  refine ⟨differentiable_of_isFn u hL h, fun l z => ?_⟩
  have hper : u.ex (z + l) = u.ex z := by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h i z hi
  have h2 := h i (z + l) hi'
  rw [hper, h1, hAH.2.2.2 l i z hi] at h2
  refine mul_right_cancel₀ (u.fr_ne i _ hi') ?_
  rw [← h2, pow_one]
  unfold hermForm
  ring
end GlobalTheory.SectionFn

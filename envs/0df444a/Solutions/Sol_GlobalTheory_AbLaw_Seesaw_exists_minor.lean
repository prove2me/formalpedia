-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.exists_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:02.812507+00:00
-- url     : https://prove2.me/submissions/6f94ec86-c813-4412-bf69-40c751e8c5d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution {K m n : Type} [Field K] [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n K)
    (hA : ∀ w, A.mulVec w = 0 → w = 0) : ∃ ρ : n → m, (A.submatrix ρ id).det ≠ 0 := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A)
    (LinearMap.ker_eq_bot'.2 fun w hw => hA w (by simpa using hw))
  have h1 : LinearMap.toMatrix' L * A = 1 := by
    have := congrArg LinearMap.toMatrix' hL
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  by_contra hne
  push Not at hne
  set B := LinearMap.toMatrix' L
  have h2 : (B * A).det = ∑ ρ : n → m, (∏ i, B i (ρ i)) * (A.submatrix ρ id).det := by
    have e : B * A = fun i => ∑ j, B i j • A j := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply]
    have := (Matrix.detRowAlternating (n := n) (R := K)).toMultilinearMap.map_sum
      (fun i j => B i j • A j)
    rw [e]
    refine this.trans (Finset.sum_congr rfl fun ρ _ => ?_)
    exact (Matrix.detRowAlternating (n := n) (R := K)).toMultilinearMap.map_smul_univ _ _
  rw [h1, Matrix.det_one] at h2
  simp [hne] at h2
end GlobalTheory.AbLaw.Seesaw

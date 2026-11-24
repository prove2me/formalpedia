-- Prove2me | solution 1 for GlobalTheory.TriangularIsometryBoundedPowers.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:14.432958+00:00
-- url     : https://prove2.me/submissions/e5a15891-a7ad-4a27-b344-6bd642fa1b71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
import Theorems.Thm_GlobalTheory_TriangularIsometryBoundedPowers_exists_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TriangularIsometryBoundedPowers
open Matrix
namespace GlobalTheory.TriangularIsometryBoundedPowers
theorem _root_.solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hH : B.IsHermitian)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) :
    ∃ (F : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), F.BlockTriangular id ∧ F.det = 1 ∧
      (∀ i, μ i ≠ 0) ∧ Fᴴ * B * F = diagonal μ := by
  choose y hy1 hy0 hyB using exists_col B hB
  let F : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c j => y j c
  have hFt : F.BlockTriangular id := fun c j h => hy0 j c h
  have hFd : F.det = 1 := by
    rw [Matrix.det_of_upperTriangular hFt]
    exact Finset.prod_eq_one fun i _ => hy1 i
  have hup : ∀ i j, i < j → (Fᴴ * B * F) i j = 0 := by
    intro i j hij
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rcases lt_or_ge i a with h | h
    · have : F a i = 0 := hy0 i a h
      rw [Matrix.conjTranspose_apply, this, star_zero, zero_mul]
    · have : (B * F) a j = 0 := by
        rw [Matrix.mul_apply]
        exact hyB j a (lt_of_le_of_lt h hij)
      rw [this, mul_zero]
  have hherm : (Fᴴ * B * F)ᴴ = Fᴴ * B * F := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hH.eq, Matrix.mul_assoc]
  have hD : Fᴴ * B * F = diagonal fun i => (Fᴴ * B * F) i i := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [hup i j h, Matrix.diagonal_apply_ne _ h.ne]
    · subst h; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h.ne', ← hherm, Matrix.conjTranspose_apply, hup j i h,
        star_zero]
  have hBd : B.det ≠ 0 := hB (Fin.last n)
  refine ⟨F, _, hFt, hFd, ?_, hD⟩
  have : (diagonal fun i => (Fᴴ * B * F) i i).det ≠ 0 := by
    rw [← hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hFd]
    simpa using hBd
  rw [Matrix.det_diagonal] at this
  exact fun i => Finset.prod_ne_zero_iff.mp this i (Finset.mem_univ i)
end GlobalTheory.TriangularIsometryBoundedPowers

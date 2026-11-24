-- Prove2me | solution 1 for GlobalTheory.PolarisedLattice.real_pos_of_int_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:54.477867+00:00
-- url     : https://prove2.me/submissions/b9166703-32c2-484b-b738-96e9d8336182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.PolarisedLattice
namespace GlobalTheory.PolarisedLattice
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) : (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  set N : Matrix ι ι ℝ := M.map (Int.cast : ℤ → ℝ) with hN
  have hH : N.IsHermitian := by
    ext i j; simp [hN, hs i j]
  have hcast : ∀ x : ι → ℤ, (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) = ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ) := by
    intro x
    simp [hN, dotProduct, mulVec]
  have hq : ∀ x : ι → ℚ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) := by
    intro x
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
    choose y hy using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have hxy : (fun i => (y i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (x i : ℝ)) := by
      funext i
      have := congrArg (fun q : ℚ => (q : ℝ)) (hy i)
      simpa [Submonoid.smul_def] using this
    have h1 : (0 : ℝ) ≤ ((y ⬝ᵥ M *ᵥ y : ℤ) : ℝ) := by
      by_cases h : y = 0
      · simp [h]
      · exact_mod_cast (hp y h).le
    rw [← hcast, hxy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
    exact nonneg_of_mul_nonneg_right h1 (mul_self_pos.2 hd0)
  have hsd : N.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun x => ?_⟩
    have hd : DenseRange (Pi.map fun (_ : ι) => (Rat.cast : ℚ → ℝ)) := DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ N *ᵥ x) x ?_ (fun q => ?_)
    · exact isClosed_le continuous_const (by fun_prop)
    · exact hq q
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, h0⟩ := exists_mulVec_eq_zero_iff.2 h
    have := hp v hv
    simp [h0] at this
  refine hsd.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ ?_))
  have : N.det = (M.det : ℝ) := (Int.cast_det M).symm
  rw [this]; exact_mod_cast hdet
end GlobalTheory.PolarisedLattice

-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.ft_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:19:40.862141+00:00
-- url     : https://prove2.me/submissions/ec50d346-7a10-44b8-87bd-33885f09a7a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_pr_add_left
import Theorems.Thm_GlobalTheory_SW_FourierJ_pr_smul_swap
import Theorems.Thm_GlobalTheory_SW_FourierJ_intM_nsmul
import Theorems.Thm_GlobalTheory_SW_FourierJ_level_mul
import Theorems.Thm_GlobalTheory_SW_FourierJ_exists_den
import Theorems.Thm_GlobalTheory_SW_FourierJ_level_ch
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_add
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_eq_one_iff
import Theorems.Thm_GlobalTheory_T_rationalSchwartzBruhat_algebra_integral_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.FourierJ
theorem _root_.solution {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι ℚ → ℂ}
    (h : HasLevel R φ) (y : Matrix κ ι ℚ) (hy : ft φ y ≠ 0) : IntM ((R : ℚ) • y) := by
  classical
  intro k i
  obtain ⟨S, hS, hSy⟩ := exists_den y
  have hsb : IsSB fun x => φ x * ech (pr x y) := by
    refine ⟨R * S, Nat.mul_pos hR hS, level_ch (level_mul h S) ?_⟩
    rw [Nat.cast_mul, ← smul_smul]; exact intM_nsmul hSy R
  obtain ⟨-, -, -, -, -, hsm, -, htr⟩ := GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ hsb hsb
  set z : Matrix κ ι ℚ := -Matrix.single k i 1 with hz
  have hzi : IntM (-z) := by
    intro k' i'
    simp only [hz, neg_neg, Matrix.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  have h1 := (htr ((R : ℚ) • z)).2
  have h2 : (fun x => φ (x - (R : ℚ) • z) * ech (pr (x - (R : ℚ) • z) y)) =
      ech (((R : ℚ) • y) k i) • fun x => φ x * ech (pr x y) := by
    ext x
    have h3 : pr (-z) ((R : ℚ) • y) = ((R : ℚ) • y) k i := by
      generalize (R : ℚ) • y = w
      rw [hz, neg_neg]
      simp [pr, dotProduct, Matrix.single_apply, ite_and]
    rw [sub_eq_add_neg, ← smul_neg, h.2 x _ hzi, pr_add_left, ech_add, pr_smul_swap, h3]
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  beta_reduce at h1
  rw [h2, hsm] at h1
  have h4 : ech (((R : ℚ) • y) k i) = 1 := by
    have : ech (((R : ℚ) • y) k i) * ft φ y = 1 * ft φ y := by rw [one_mul]; exact h1
    exact mul_right_cancel₀ hy this
  obtain ⟨m, hm⟩ := (ech_eq_one_iff _).1 h4
  rw [hm]
  exact isIntegral_algebraMap (R := ℤ) (x := m)
end GlobalTheory.SW.FourierJ

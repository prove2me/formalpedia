-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.trans_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:33.413134+00:00
-- url     : https://prove2.me/submissions/13b609df-972c-49dc-97bc-454a8abe6615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_tsum_pi_prod
import Theorems.Thm_GlobalTheory_SW_FourierJ_ft_eq
import Theorems.Thm_GlobalTheory_SW_FourierJ_ft_level
import Theorems.Thm_GlobalTheory_SW_FourierJ_thS_eq
import Theorems.Thm_GlobalTheory_SW_FourierJ_tsum_supp
import Theorems.Thm_GlobalTheory_SW_FourierJ_spDen_J
import Theorems.Thm_GlobalTheory_SW_FourierJ_qm_J
import Theorems.Thm_GlobalTheory_SW_FourierJ_spAct_J
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_sum
import Theorems.Thm_GlobalTheory_SW_FourierJ_intM_iff
import Theorems.Thm_GlobalTheory_SW_FourierJ_norm_ech
import Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff
import Theorems.Thm_GlobalTheory_SW_SiegelSum_summable_norm_thetaTerm
import Theorems.Thm_GlobalTheory_T_poisson_summation_thetaSeriesRowTerm_coset
import Theorems.Thm_GlobalTheory_T_symplecticSiegelAction_mem_upperHalfSpace_and_cocycle
import Theorems.Thm_GlobalTheory_T_tsum_schwartzBruhatLevel_eq_sum_residueCosets


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
theorem _root_.solution [DecidableEq ι] {p : ℕ} (hp : Fintype.card κ = p + p) {R : ℕ} (hR : 0 < R)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) :
    TransS (Matrix.J ι ℚ) φ fun y => I ^ (Fintype.card ι * p) * ft φ y := by
  classical
  intro τ hτ ζ
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  obtain ⟨hd, hs, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι _ (SymplecticGroup.J_mem ι ℚ) τ hτ
  rw [spAct_J] at hs
  rw [spDen_J] at hd
  obtain ⟨c, hc, hrow⟩ := GlobalTheory.T.poisson_summation_thetaSeriesRowTerm_coset ι R hR τ hτ hs (Ne.isUnit hd)
  rw [spAct_J, spDen_J, qm_J, Matrix.mul_one, thS_eq, thS_eq,
    tsum_supp hR (ft_level hR h _)]
  have hsum : Summable fun x : Matrix κ ι ℚ => φ x * ∏ k, gs τ (ζ k) (x k) := by
    have := (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι φ ⟨R, hR, h⟩ τ hτ ζ).of_norm
    simpa only [gs, ← Complex.exp_sum, Finset.mul_sum] using this
  rw [GlobalTheory.T.tsum_schwartzBruhatLevel_eq_sum_residueCosets κ ι R φ _ hR h hsum]
  set V : ℂ := (R : ℂ) ^ (Fintype.card κ * Fintype.card ι) with hV
  set T : (κ → ι → Fin (R * R)) → κ → (ι → ℤ) → ℂ := fun n k m =>
    ech (rep R n k ⬝ᵥ ((R : ℚ)⁻¹ • zv m)) * gs (-τ⁻¹) (ζ k ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m) with hT
  have hTs : ∀ n k, Summable fun m => ‖T n k m‖ := fun n k => by
    simpa only [hT, norm_mul, norm_ech, one_mul] using (hrow 0 (ζ k)).2.1
  have hconst : τ.det ^ p * c ^ (p + p) = I ^ (Fintype.card ι * p) * V⁻¹ := by
    have hV0 : V ≠ 0 := pow_ne_zero _ hRc
    have h1 : (c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det)) ^ p = 1 := by
      rw [hc, one_pow]
    have h2 : ((-I) * I) ^ (Fintype.card ι * p) = 1 := by simp
    rw [eq_mul_inv_iff_mul_eq₀ hV0, hV, hp]
    calc _ = τ.det ^ p * c ^ (p + p) * (R : ℂ) ^ ((p + p) * Fintype.card ι) *
          ((-I) * I) ^ (Fintype.card ι * p) := by rw [h2, mul_one]
      _ = I ^ (Fintype.card ι * p) *
          (c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det)) ^ p := by
        simp only [mul_pow, ← pow_mul]; ring
      _ = _ := by rw [h1, mul_one]
  have hl : ∀ m : κ → ι → ℤ, I ^ (Fintype.card ι * p) * ft φ ((R : ℚ)⁻¹ • zm m) *
      ∏ k, gs (-τ⁻¹) (ζ k ᵥ* τ⁻¹) (((R : ℚ)⁻¹ • zm m) k) =
      ∑ n : κ → ι → Fin (R * R), (I ^ (Fintype.card ι * p) * V⁻¹ * φ (rep R n)) *
        ∏ k, T n k (m k) := by
    intro m
    have hm : IntM ((R : ℚ) • (R : ℚ)⁻¹ • zm m) := by
      rw [smul_smul, mul_inv_cancel₀ hR0, one_smul]; exact (intM_iff _).2 ⟨m, rfl⟩
    rw [ft_eq hR h hm, ← hV, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hT, Finset.prod_mul_distrib, pr, ech_sum, mul_assoc]
    rfl
  simp only [hl]
  rw [Summable.tsum_finsetSum fun n _ =>
    ((tsum_pi_prod κ _ (T n) (hTs n)).1.of_norm.mul_left _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [tsum_mul_left, (tsum_pi_prod κ _ (T n) (hTs n)).2]
  have hr := (tsum_pi_prod κ _ (fun k (m : ι → ℤ) => gs τ (ζ k) (rep R n k + (R : ℚ) • zv m))
    (fun k => (hrow _ _).1)).2
  have hr' : ∑' m : κ → ι → ℤ, ∏ k, gs τ (ζ k) ((rep R n + (R : ℚ) • zm m) k) =
      ∏ k, ∑' m : ι → ℤ, gs τ (ζ k) (rep R n k + (R : ℚ) • zv m) := hr
  have hp2 : Fintype.card κ / 2 = p := by omega
  have hprod : cexp (π * I * ∑ k, ζ k ⬝ᵥ τ⁻¹ *ᵥ ζ k) *
      ∏ k, ∑' m : ι → ℤ, gs τ (ζ k) (rep R n k + (R : ℚ) • zv m) =
      c ^ (p + p) * ∏ k, ∑' m, T n k m := by
    rw [Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib, ← hp, ← Finset.card_univ,
      ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => (hrow _ _).2.2
  rw [hr', hp2, ← hconst]
  linear_combination (-(τ.det ^ p * φ (rep R n))) * hprod
end GlobalTheory.SW.FourierJ

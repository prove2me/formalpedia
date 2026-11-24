-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_evenNorms_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:59:47.170272+00:00
-- url     : https://prove2.me/submissions/501687d0-1735-40a3-a6af-1da3f29d680d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitEvenOrderQuadraticNormValuesOneModFour
import Theorems.Thm_GlobalTheory_QNorm_exists_not_mem_sq_add_sub
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_evenOrderNorms_one_add_four_mul_of_no_root
import Theorems.Thm_GlobalTheory_T_exists_global_uniformizer_residue_representatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), ∃ Δ : v.adicCompletion F, EvenNorms Valued.v Δ ∧ Valued.v Δ = 1 ∧ Valued.v (Δ - 1) ≤ Valued.v (4 : v.adicCompletion F) := by
  intro F _ _ v
  obtain ⟨_, hval, hrep, -⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  obtain ⟨ρ, hρ⟩ := exists_not_mem_sq_add_sub F v
  set r : v.adicCompletion F := algebraMap F (v.adicCompletion F) (ρ : F) with hr
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have h := (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr (two_ne_zero (α := F))
    rwa [map_ofNat] at h
  have hint : ∀ a : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 := fun a => by
    rw [hval]; exact v.valuation_le_one a
  have hone : ∀ a : 𝓞 F, a ∉ v.asIdeal →
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := fun a ha => by
    rw [hval]; exact v.valuation_eq_one_iff_notMem.mpr ha
  have key : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → Valued.v (x ^ 2 + x - r) = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := hrep x hx
    set b : v.adicCompletion F := algebraMap F (v.adicCompletion F) (a : F) with hb_def
    have hb : Valued.v b ≤ 1 := hint a
    have hab : Valued.v (b ^ 2 + b - r) = 1 := by
      have h := hone (a ^ 2 + a - ρ) (hρ a)
      push_cast at h
      simpa [hb_def, hr] using h
    have h3 : Valued.v (x + b + 1) ≤ 1 :=
      Valuation.map_add_le _ (Valuation.map_add_le _ hx hb) (by simp)
    have hsmall : Valued.v ((x - b) * (x + b + 1)) < Valued.v (b ^ 2 + b - r) := by
      rw [hab, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h3) ha
    have e : x ^ 2 + x - r = (x - b) * (x + b + 1) + (b ^ 2 + b - r) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ hsmall, hab]
  refine ⟨1 + 4 * r, GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root _ Valued.v r h2 (hint ρ) key, ?_, ?_⟩
  · have h2le : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
      rw [← one_add_one_eq_two]
      exact Valuation.map_add_le _ (by simp) (by simp)
    have h4 : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    by_cases h2v : Valued.v (2 : v.adicCompletion F) = 1
    · have hx : Valued.v (-(2 : v.adicCompletion F)⁻¹) = 1 := by
        rw [Valuation.map_neg, map_inv₀, h2v, inv_one]
      have hk := key (-(2 : v.adicCompletion F)⁻¹) hx.le
      have h22 : (2 : v.adicCompletion F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      have e : 1 + 4 * r = -(2 * 2) *
          ((-(2 : v.adicCompletion F)⁻¹) ^ 2 + (-(2 : v.adicCompletion F)⁻¹) - r) := by
        linear_combination (2 * (2 : v.adicCompletion F)⁻¹ - 1) * h22
      rw [e, map_mul, hk, mul_one, Valuation.map_neg, map_mul, h2v, mul_one]
    · have h2lt : Valued.v (2 : v.adicCompletion F) < 1 := lt_of_le_of_ne h2le h2v
      have h4r : Valued.v (4 * r) < Valued.v (1 : v.adicCompletion F) := by
        rw [map_one, map_mul, h4, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint ρ))
          (lt_of_le_of_lt (mul_le_of_le_one_right' h2le) h2lt)
      rw [Valuation.map_add_eq_of_lt_left _ h4r, map_one]
  · rw [add_sub_cancel_left, map_mul]
    exact mul_le_of_le_one_right' (hint ρ)
end GlobalTheory.QNorm

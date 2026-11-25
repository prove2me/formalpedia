-- Prove2me | solution 1 for GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:59:27.833216+00:00
-- url     : https://prove2.me/submissions/348d0490-c68e-4f64-8f40-991e34e27c84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitUnfoldIntegralPartitionOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNonzeroIntegersPrincipalIdealsUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIntegralThetaMellinInterchangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegralNonzeroIntegerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ArchFactorMulPSeriesEqIntegral
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
import Theorems.Thm_GlobalTheory_CMVal_IsLatSum_unique
import Theorems.Thm_GlobalTheory_CMVal_IsToricSum_unique
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HeckeMellin_term_zero
import Theorems.Thm_GlobalTheory_HeckeStrip_norm_wt
import Theorems.Thm_GlobalTheory_HeckeStrip_wt_mul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompletedLStripBounds_IsCompletedL_unique
import Theorems.Thm_GlobalTheory_T_hasSum_integral_theta_mellin_interchange
import Theorems.Thm_GlobalTheory_T_heckeMellinGaussIntegral_nonzero_integer
import Theorems.Thm_GlobalTheory_T_heckeMellinGaussIntegrand_unit_mul
import Theorems.Thm_GlobalTheory_T_orbit_unfold_integral_partition_of_unity
import Theorems.Thm_GlobalTheory_T_sum_nonzero_integers_principal_ideals_units
import Theorems.Thm_ReciprocityTheory_Cheb_summable_absNorm_rpow_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellin
namespace GlobalTheory.HeckeMellin
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  intro K _ _ _ I _ φ hφ n hn F C hF hinv p hp hp0 hsum s hs
  haveI : Countable (𝓞 K) := (RingOfIntegers.basis K).equivFun.injective.countable
  haveI : Countable (𝓞 K)ˣ := (Units.val_injective (α := 𝓞 K)).countable
  have hs0 : 0 < s.re := by linarith
  set tm : 𝓞 K → (I → ℝ) → ℂ := fun α => GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) with htm
  have hulog_inv : ∀ u : (𝓞 K)ˣ, GlobalTheory.HeckeTheta.ulog φ u⁻¹ = - GlobalTheory.HeckeTheta.ulog φ u := by
    intro u; funext i
    simp only [GlobalTheory.HeckeTheta.ulog, Pi.neg_apply]
    rw [← Real.log_inv, ← inv_pow, ← norm_inv, ← map_inv₀]
    congr 4
    have h := congrArg (fun x : 𝓞 K => (x : K)) (Units.inv_mul u)
    push_cast at h
    exact eq_inv_of_mul_eq_one_left h
  have hsum' : ∀ y, HasSum (fun u : (𝓞 K)ˣ => p (y - GlobalTheory.HeckeTheta.ulog φ u)) 1 := by
    intro y
    rw [← (Equiv.inv (𝓞 K)ˣ).hasSum_iff]
    simpa [Function.comp_def, hulog_inv, sub_neg_eq_add] using hsum y
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hsum y) 1 (fun u _ => hp0 _)
    have h1 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h1] using h
  have hemb0 : GlobalTheory.HeckeTheta.emb φ ((0 : 𝓞 K) : K) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  have htm0 : tm 0 = 0 := by funext y; simp only [htm, hemb0, GlobalTheory.HeckeMellin.term_zero hn]; rfl
  have hint : ∀ α : 𝓞 K, Integrable (tm α) := by
    intro α
    by_cases h : α = 0
    · subst h; rw [htm0]; exact integrable_zero _ _ _
    · exact (GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 α h).1
  have hshift : ∀ (u : (𝓞 K)ˣ) (α : 𝓞 K) y, tm ((u : 𝓞 K) * α) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * tm α (y + GlobalTheory.HeckeTheta.ulog φ u) := by
    intro u α y
    have : (((u : 𝓞 K) * α : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (α : K) := by push_cast; rfl
    simp only [htm, this]
    exact GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul K I φ hφ n s u α y
  have hwtu : ∀ u : (𝓞 K)ˣ, ‖GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K)‖ = 1 := fun u =>
    GlobalTheory.HeckeStrip.norm_wt φ n (by
      have := u.ne_zero
      exact_mod_cast this)
  have hgen : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) ≠ 0 := by
    intro J h
    haveI := J.2.2
    exact J.2.1 ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J.1).2 h)
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {(haveI := J.2.2; Submodule.IsPrincipal.generator J.1)} = J.1 := by
    intro J; haveI := J.2.2; exact Ideal.span_singleton_generator J.1

  have horb : ∀ g : 𝓞 K, g ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => ∫ y, p y * ‖tm ((u : 𝓞 K) * g) y‖) (∫ y, ‖tm g y‖) ∧
      HasSum (fun u : (𝓞 K)ˣ => F ((u : 𝓞 K) * g) * ∫ y, (p y : ℂ) * tm ((u : 𝓞 K) * g) y) (F g * ∫ y, tm g y) := by
    intro g hg
    have hO := GlobalTheory.T.orbit_unfold_integral_partition_of_unity I (𝓞 K)ˣ (GlobalTheory.HeckeTheta.ulog φ) p hp hp0 hsum' (tm g) (hint g)
    constructor
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr hO.2
      simp only [hshift, norm_mul, hwtu, one_mul]
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr (hO.1.mul_left (F g))
      have hw : F ((u : 𝓞 K) * g) * GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) = F g := by
        have h1 := hinv u g
        have hgK : (g : K) ≠ 0 := by exact_mod_cast hg
        have : (((u : 𝓞 K) * g : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (g : K) := by push_cast; rfl
        rw [this, GlobalTheory.HeckeStrip.wt_mul] at h1
        have hne : GlobalTheory.HeckeStrip.wt φ n (g : K) ≠ 0 := by
          rw [← norm_ne_zero_iff, GlobalTheory.HeckeStrip.norm_wt φ n hgK]; exact one_ne_zero
        exact mul_right_cancel₀ hne (by rw [mul_assoc, h1])
      simp only [hshift]
      rw [← hw, mul_assoc]
      congr 1
      rw [← integral_const_mul]
      congr 1; funext y; ring

  set cst : ℝ := ∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2) with hcst
  have hnorm : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖ = cst * ((Ideal.absNorm J.1 : ℕ) : ℝ) ^ (-s.re) := by
    intro J
    rw [(GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 _ (hgen J)).2.2, hspan J]
  have hb : Summable (fun J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) := by
    simp only [hnorm]
    exact (((ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal K hs).comp_injective Subtype.val_injective).mul_left cst)
  have hR := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℝ (fun α => ∫ y, p y * ‖tm α y‖) (by simp [htm0])
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J u => ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).1)
    (fun J u => le_of_eq (Real.norm_of_nonneg (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))))
    (fun J => (horb _ (hgen J)).1) hb
  have hI := GlobalTheory.T.hasSum_integral_theta_mellin_interchange I (𝓞 K) (fun α => GlobalTheory.HeckeTheta.emb φ (α : K)) F C hF n s p hp hp0 hp1 hint hR.summable
  have hU := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℂ (fun α => F α * ∫ y, (p y : ℂ) * tm α y) (by simp [htm0])
    (fun J => F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) * ∫ y, tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y) (fun J u => C * ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => C * ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).2)
    (fun J u => by
      rw [norm_mul]
      refine mul_le_mul (hF _) ((norm_integral_le_integral_norm _).trans (le_of_eq ?_)) (norm_nonneg _)
        ((norm_nonneg _).trans (hF 0))
      congr 1; funext y; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp0 y)])
    (fun J => (horb _ (hgen J)).1.mul_left C) (hb.mul_left C)
  rw [hI.unique hU, GlobalTheory.HeckeStrip.pSeries, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext J
  have h3 := (GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 _ (hgen J)).2.1
  rw [hspan J] at h3
  simp only [GlobalTheory.HeckeStrip.pval]
  linear_combination (-F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) * h3
end GlobalTheory.HeckeMellin

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KWeightMajor.string_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:46:29.735988+00:00
-- url     : https://prove2.me/submissions/0c6c8f63-100b-414a-a290-04a0a91001a2

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_isWeight_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_norm_identity
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_inner_eq_zero_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kcomm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kstab_orthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil



set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight CasK kSpan)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open GlobalTheory.CompanionTheory.KLowSpan (kcomm_apply inner_eq_zero_of_weight kstab_orthogonal)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KWeightMajor
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
namespace GlobalTheory.CompanionTheory.KWeightMajor
theorem _root_.solution (hF : KRel ε E) (hU : KUnit ε E) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hz : IsWeight E μ z) (k : ℕ) :
    (k + 1) * (μ b - μ a - k) * ‖(E a b ^ k) z‖ ^ 2 ≤ ‖(E a b ^ (k + 1)) z‖ ^ 2 := by
  induction k with
  | zero =>
    have := norm_identity hF hU he hz
    simp only [pow_zero, Module.End.one_apply, pow_one, Nat.cast_zero, zero_add, one_mul, sub_zero]
    nlinarith [sq_nonneg ‖E b a z‖]
  | succ k ih =>
    have hw1 := isWeight_pow hF he hz (k + 1)
    have hid := norm_identity hF hU he hw1
    have hE2 : (E a b ^ (k + 1 + 1)) z = E a b ((E a b ^ (k + 1)) z) := by
      rw [pow_succ', Module.End.mul_apply]
    have hE1 : (E a b ^ (k + 1)) z = E a b ((E a b ^ k) z) := by rw [pow_succ', Module.End.mul_apply]
    have hsh : shift μ a b (k + 1) b - shift μ a b (k + 1) a = μ b - μ a - 2 * ((k : ℝ) + 1) := by
      simp only [shift, if_neg hab, if_neg (Ne.symm hab), if_pos rfl, ↓reduceIte]; push_cast; ring
    have hcs : ‖(E a b ^ (k + 1)) z‖ ^ 2 ≤ ‖E b a ((E a b ^ (k + 1)) z)‖ * ‖(E a b ^ k) z‖ := by
      have h1 : inner ℂ (E b a ((E a b ^ (k + 1)) z)) ((E a b ^ k) z) =
          inner ℂ ((E a b ^ (k + 1)) z) ((E a b ^ (k + 1)) z) := by
        rw [hU b a he.symm, ← hE1]
      have h3 : ‖inner ℂ ((E a b ^ (k + 1)) z) ((E a b ^ (k + 1)) z)‖ = ‖(E a b ^ (k + 1)) z‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
      have h2 := norm_inner_le_norm (𝕜 := ℂ) (E b a ((E a b ^ (k + 1)) z)) ((E a b ^ k) z)
      rw [h1, h3] at h2
      exact h2
    have hn0 := norm_nonneg ((E a b ^ k) z)
    have hn1 := norm_nonneg ((E a b ^ (k + 1)) z)
    have hnA := norm_nonneg (E b a ((E a b ^ (k + 1)) z))
    have key : ((k : ℝ) + 1) * (μ b - μ a - k) * ‖(E a b ^ (k + 1)) z‖ ^ 2 ≤
        ‖E b a ((E a b ^ (k + 1)) z)‖ ^ 2 := by
      rcases le_or_gt (((k : ℝ) + 1) * (μ b - μ a - k)) 0 with hc | hc
      · nlinarith [mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg ‖(E a b ^ (k + 1)) z‖),
          sq_nonneg ‖E b a ((E a b ^ (k + 1)) z)‖]
      · rcases eq_or_lt_of_le hn0 with h0 | h0
        · rw [← h0, mul_zero] at hcs
          have : ‖(E a b ^ (k + 1)) z‖ = 0 := by nlinarith
          rw [this]
          nlinarith [sq_nonneg ‖E b a ((E a b ^ (k + 1)) z)‖]
        · have h4 : ((k : ℝ) + 1) * (μ b - μ a - k) * ‖(E a b ^ (k + 1)) z‖ ^ 2 * ‖(E a b ^ k) z‖ ^ 2 ≤
              ‖E b a ((E a b ^ (k + 1)) z)‖ ^ 2 * ‖(E a b ^ k) z‖ ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left ih (sq_nonneg ‖(E a b ^ (k + 1)) z‖),
              pow_le_pow_left₀ (sq_nonneg _) hcs 2]
          exact le_of_mul_le_mul_right h4 (by positivity)
    rw [hE2, hid, hsh]
    push_cast
    nlinarith [key]
end GlobalTheory.CompanionTheory.KWeightMajor

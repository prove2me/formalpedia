-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KWeightMajor.swap_weight_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:04:52.126551+00:00
-- url     : https://prove2.me/submissions/6489603f-2b4b-41df-a551-b86e999f4ea2

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_isWeight_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_string_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_exists_pow_eq_zero
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
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
theorem _root_.solution (hF : KRel ε E) (hU : KUnit ε E) {L : Submodule ℂ V} [FiniteDimensional ℂ L]
    (hL : KStab ε E L) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hzL : z ∈ L) (hz0 : z ≠ 0) (hz : IsWeight E μ z) (hle : μ a ≤ μ b) :
    ∃ z' ∈ L, z' ≠ 0 ∧ IsWeight E (μ ∘ Equiv.swap a b) z' := by
  classical
  obtain ⟨hmemz, hex⟩ := exists_pow_eq_zero hF hU hL hab he hzL hz
  obtain ⟨K, hK, hKmin⟩ : ∃ K, (E a b ^ K) z = 0 ∧ ∀ m < K, (E a b ^ m) z ≠ 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hK0 : K ≠ 0 := by
    rintro rfl
    rw [pow_zero, Module.End.one_apply] at hK
    exact hz0 hK
  obtain ⟨K', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK0
  have hu0 : (E a b ^ K') z ≠ 0 := hKmin K' (Nat.lt_succ_self _)
  have huL : (E a b ^ K') z ∈ L := hmemz K'
  have hEu : E a b ((E a b ^ K') z) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ']; exact hK
  have hνu : IsWeight E (shift μ a b K') ((E a b ^ K') z) := isWeight_pow hF he hz K'
  have hupos : 0 < ‖(E a b ^ K') z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
  have hdle : μ b - μ a ≤ K' := by
    have hsb := string_bound hF hU hab he hz K'
    rw [hK, norm_zero] at hsb
    by_contra hcon
    push Not at hcon
    have : 0 < ((K' : ℝ) + 1) * (μ b - μ a - K') * ‖(E a b ^ K') z‖ ^ 2 :=
      mul_pos (mul_pos (by positivity) (by linarith)) hupos
    nlinarith
  have hνa : shift μ a b K' a = μ a + K' := by
    simp only [shift, if_neg hab, ↓reduceIte]; ring
  have hνb : shift μ a b K' b = μ b - K' := by
    simp only [shift, if_neg (Ne.symm hab), ↓reduceIte]; ring
  have hlow : ∀ j : ℕ, E a b ((E b a ^ (j + 1)) ((E a b ^ K') z)) =
      (((((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j)) : ℝ) : ℂ) • (E b a ^ j) ((E a b ^ K') z) := by
    intro j
    induction j with
    | zero =>
      rw [zero_add, pow_one, kcomm_apply hF he he.symm, hEu, map_zero, zero_add]
      simp only [if_pos rfl, ↓reduceIte, pow_zero, Module.End.one_apply, hνu a, hνu b]
      rw [← sub_smul]
      congr 1
      push_cast
      ring
    | succ j ih =>
      rw [pow_succ' (E b a) (j + 1), Module.End.mul_apply, kcomm_apply hF he he.symm, ih, map_smul]
      simp only [if_pos rfl, ↓reduceIte]
      have hwj := isWeight_pow hF he.symm hνu (j + 1)
      rw [hwj a, hwj b, ← Module.End.mul_apply (E b a), ← pow_succ', ← sub_smul, ← add_smul]
      congr 1
      simp only [shift, if_neg hab, if_neg (Ne.symm hab), if_pos rfl, ↓reduceIte]
      push_cast
      ring
  have hnormlow : ∀ j : ℕ, ‖(E b a ^ (j + 1)) ((E a b ^ K') z)‖ ^ 2 =
      ((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j) * ‖(E b a ^ j) ((E a b ^ K') z)‖ ^ 2 := by
    intro j
    have hy : (E b a ^ (j + 1)) ((E a b ^ K') z) = E b a ((E b a ^ j) ((E a b ^ K') z)) := by
      rw [pow_succ', Module.End.mul_apply]
    have h1 : inner ℂ ((E b a ^ (j + 1)) ((E a b ^ K') z)) ((E b a ^ (j + 1)) ((E a b ^ K') z)) =
        (((((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j)) : ℝ) : ℂ) *
          inner ℂ ((E b a ^ j) ((E a b ^ K') z)) ((E b a ^ j) ((E a b ^ K') z)) := by
      calc inner ℂ ((E b a ^ (j + 1)) ((E a b ^ K') z)) ((E b a ^ (j + 1)) ((E a b ^ K') z))
          = inner ℂ ((E b a ^ (j + 1)) ((E a b ^ K') z)) (E b a ((E b a ^ j) ((E a b ^ K') z))) := by
            rw [← hy]
        _ = inner ℂ (E a b ((E b a ^ (j + 1)) ((E a b ^ K') z))) ((E b a ^ j) ((E a b ^ K') z)) :=
            (hU a b he _ _).symm
        _ = _ := by rw [hlow j, inner_smul_left, Complex.conj_ofReal]
    have h2 := congrArg Complex.re h1
    rw [Complex.re_ofReal_mul] at h2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) ((E b a ^ j) ((E a b ^ K') z)),
      RCLike.re_to_complex, RCLike.re_to_complex]
    exact h2
  obtain ⟨_, hexJ⟩ := exists_pow_eq_zero hF hU hL (Ne.symm hab) he.symm huL hνu
  obtain ⟨J, hJ, hJmin⟩ : ∃ J, (E b a ^ J) ((E a b ^ K') z) = 0 ∧ ∀ m < J, (E b a ^ m) ((E a b ^ K') z) ≠ 0 :=
    ⟨Nat.find hexJ, Nat.find_spec hexJ, fun m hm => Nat.find_min hexJ hm⟩
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [pow_zero, Module.End.one_apply] at hJ
    exact hu0 hJ
  obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ0
  have hyJ : 0 < ‖(E b a ^ J') ((E a b ^ K') z)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (hJmin J' (Nat.lt_succ_self _))) 2
  have hNJ : shift μ a b K' a - shift μ a b K' b = J' := by
    have h := hnormlow J'
    rw [hJ, norm_zero, zero_pow two_ne_zero] at h
    have h' : ((J' : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - J') = 0 := by
      rcases mul_eq_zero.mp h.symm with h2 | h2
      · exact h2
      · exact absurd h2 (ne_of_gt hyJ)
    rcases mul_eq_zero.mp h' with h3 | h3
    · have : (0 : ℝ) < (J' : ℝ) + 1 := by positivity
      linarith
    · linarith
  rw [hνa, hνb] at hNJ
  have hJle : J' ≤ 2 * K' := by
    have : (J' : ℝ) ≤ 2 * K' := by linarith
    exact_mod_cast this
  have hmR : ((2 * K' - J' : ℕ) : ℝ) = μ b - μ a := by
    rw [Nat.cast_sub hJle]
    push_cast
    linarith
  have hmle : 2 * K' - J' < K' + 1 := by
    have : ((2 * K' - J' : ℕ) : ℝ) ≤ K' := by rw [hmR]; exact hdle
    have : 2 * K' - J' ≤ K' := by exact_mod_cast this
    omega
  refine ⟨(E a b ^ (2 * K' - J')) z, hmemz _, hKmin _ hmle, ?_⟩
  have hsw : (μ ∘ Equiv.swap a b) = shift μ a b (2 * K' - J') := by
    funext c
    simp only [Function.comp_apply, shift]
    by_cases hca : c = a
    · subst hca
      rw [Equiv.swap_apply_left]
      simp only [if_pos rfl, ↓reduceIte, if_neg hab, sub_zero, mul_one]
      linarith
    · by_cases hcb : c = b
      · subst hcb
        rw [Equiv.swap_apply_right]
        simp only [if_pos rfl, ↓reduceIte, if_neg hca, zero_sub, mul_neg, mul_one]
        linarith
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
        simp only [if_neg hca, if_neg hcb, sub_zero, mul_zero, add_zero]
  rw [hsw]
  exact isWeight_pow hF he hz _
end GlobalTheory.CompanionTheory.KWeightMajor

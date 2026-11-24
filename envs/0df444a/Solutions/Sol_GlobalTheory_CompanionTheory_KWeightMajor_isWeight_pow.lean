-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KWeightMajor.isWeight_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:39.936649+00:00
-- url     : https://prove2.me/submissions/d25903f6-d3ef-4ceb-ae26-a453fda77774

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
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
theorem _root_.solution (hF : KRel ε E) {a b : Fin n} (he : ε a = ε b) {μ : Fin n → ℝ} {z : V}
    (hz : IsWeight E μ z) (k : ℕ) : IsWeight E (shift μ a b k) ((E a b ^ k) z) := by
  induction k with
  | zero =>
    intro c
    simp only [pow_zero, Module.End.one_apply, shift, Nat.cast_zero, zero_mul, add_zero]
    exact hz c
  | succ k ih =>
    intro c
    rw [pow_succ', Module.End.mul_apply, kcomm_apply hF rfl he, ih c, map_smul]
    by_cases h1 : c = a <;> by_cases h2 : b = c
    · subst h1; subst h2
      simp [shift]
    · subst h1
      have h2' : ¬ c = b := fun h => h2 h.symm
      simp only [shift, if_pos rfl, if_neg h2', if_neg h2, sub_zero, mul_one]
      push_cast
      simp only [mul_one, add_smul, one_smul]
      abel
    · subst h2
      have h1' : ¬ b = a := h1
      simp only [shift, if_pos rfl, if_neg h1', zero_sub, mul_neg, mul_one, zero_sub]
      push_cast
      simp only [sub_eq_add_neg, mul_one, add_smul, neg_add, neg_smul, one_smul]
      abel
    · have h2' : ¬ c = b := fun h => h2 h.symm
      simp only [shift, if_neg h1, if_neg h2', if_neg h2, sub_zero, mul_zero, add_zero]
end GlobalTheory.CompanionTheory.KWeightMajor

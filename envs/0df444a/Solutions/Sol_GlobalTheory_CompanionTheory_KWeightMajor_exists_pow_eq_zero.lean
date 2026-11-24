-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KWeightMajor.exists_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:31:03.528024+00:00
-- url     : https://prove2.me/submissions/6d3ffc83-527f-4027-824e-6616c8c1294b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_isWeight_pow
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
theorem _root_.solution (hF : KRel ε E) (hU : KUnit ε E) {L : Submodule ℂ V} [FiniteDimensional ℂ L]
    (hL : KStab ε E L) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hzL : z ∈ L) (hz : IsWeight E μ z) :
    (∀ k : ℕ, (E a b ^ k) z ∈ L) ∧ ∃ k : ℕ, (E a b ^ k) z = 0 := by
  have hmem : ∀ k : ℕ, (E a b ^ k) z ∈ L := by
    intro k
    induction k with
    | zero => simpa using hzL
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hL a b he _ ih
  refine ⟨hmem, ?_⟩
  by_contra hne
  push Not at hne
  have hw : ∀ k, IsWeight E (shift μ a b k) ((E a b ^ k) z) := isWeight_pow hF he hz
  have hinj : ∀ k k' : ℕ, k ≠ k' → shift μ a b k ≠ shift μ a b k' := by
    intro k k' hkk' h
    have := congrFun h a
    simp only [shift, if_neg hab, ↓reduceIte, sub_zero, mul_one, add_right_inj] at this
    exact hkk' (by exact_mod_cast this)
  let f : ℕ → L := fun k => ⟨(E a b ^ k) z, hmem k⟩
  have hli : LinearIndependent ℂ (L.subtype ∘ f) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro k; exact hne k
    · intro k k' hkk'
      exact inner_eq_zero_of_weight hU (hw k) (hw k') (hinj k k' hkk')
  haveI := (LinearIndependent.of_comp L.subtype hli).finite
  exact not_finite ℕ
end GlobalTheory.CompanionTheory.KWeightMajor

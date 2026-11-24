-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KWeightMajor.perm_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:39:01.92238+00:00
-- url     : https://prove2.me/submissions/871a9b58-0a87-4ece-8d1c-5ed18e3838e8

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_swap_weight
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
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
    (hL : KStab ε E L) : ∀ (m : ℕ) (w : Equiv.Perm (Fin n)), w.support.card = m → (∀ c, ε (w c) = ε c) →
      ∀ {μ : Fin n → ℝ} {z : V}, z ∈ L → z ≠ 0 → IsWeight E μ z →
        ∃ z' ∈ L, z' ≠ 0 ∧ IsWeight E (μ ∘ w) z' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw hεw μ z hzL hz0 hz
    by_cases h1 : w = 1
    · subst h1
      exact ⟨z, hzL, hz0, by simpa using hz⟩
    · obtain ⟨x, hx⟩ : ∃ x, w x ≠ x := by
        by_contra hcon
        push Not at hcon
        exact h1 (Equiv.ext hcon)
      have hlt := Equiv.Perm.card_support_swap_mul hx
      obtain ⟨z1, hz1L, hz10, hz1⟩ := swap_weight hF hU hL (Ne.symm hx) (hεw x).symm hzL hz0 hz
      have hεw' : ∀ c, ε ((Equiv.swap x (w x) * w) c) = ε c := by
        intro c
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        split_ifs with h2 h3
        · rw [hεw x, ← h2, hεw c]
        · rw [← hεw x, ← h3, hεw c]
        · exact hεw c
      obtain ⟨z', hz'L, hz'0, hz'⟩ := ih _ (hw ▸ hlt) (Equiv.swap x (w x) * w) rfl hεw' hz1L hz10 hz1
      refine ⟨z', hz'L, hz'0, ?_⟩
      have heq : (μ ∘ Equiv.swap x (w x)) ∘ (Equiv.swap x (w x) * w) = μ ∘ w := by
        funext c
        simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_self]
      rwa [heq] at hz'
end GlobalTheory.CompanionTheory.KWeightMajor

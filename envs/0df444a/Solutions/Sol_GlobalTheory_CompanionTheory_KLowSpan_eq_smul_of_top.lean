-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.eq_smul_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:09.573358+00:00
-- url     : https://prove2.me/submissions/204ad8a4-b5f3-404c-a2ec-baf100d45250

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kself_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_isWeight_word
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_hgt_kwt
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_inner_eq_zero_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_eq_zero_of_orth
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
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
open Formalism.REAL (KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KLowSpan
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
namespace GlobalTheory.CompanionTheory.KLowSpan
theorem _root_.solution (hF : KRel ε E) (hU : KUnit ε E) (hv0 : v ≠ 0) (hv : IsWeight E μ v) {x : V}
    (hx : x ∈ kLowSpan ε E v) (hμ : IsWeight E μ x) : ∃ c : ℂ, x = c • v := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := fun h => hv0 (inner_self_eq_zero.1 h)
  refine ⟨⟪v, x⟫_ℂ / ⟪v, v⟫_ℂ, sub_eq_zero.1 ?_⟩
  refine eq_zero_of_orth (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ kself_mem)) fun l hl => ?_
  rcases l with _ | ⟨p, l⟩
  · simp only [word_nil, Module.End.one_apply]
    rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hvv, sub_self]
  · refine inner_eq_zero_of_weight (ν' := μ) hU (isWeight_word hF hv _ hl) ?_ ?_
    · intro a
      rw [map_sub, map_smul, hμ a, hv a, smul_sub, smul_comm]
    · intro h
      have := hgt_kwt μ _ hl
      rw [h] at this
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at this
      have h0 : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
      linarith
end GlobalTheory.CompanionTheory.KLowSpan

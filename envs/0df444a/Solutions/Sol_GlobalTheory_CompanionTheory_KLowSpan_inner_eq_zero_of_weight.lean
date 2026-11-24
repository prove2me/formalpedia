-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.inner_eq_zero_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:21:01.685323+00:00
-- url     : https://prove2.me/submissions/e87c88eb-481a-4030-930b-6f340aa5641f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
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
theorem _root_.solution (hU : KUnit ε E) {ν ν' : Fin n → ℝ} {x y : V} (hx : IsWeight E ν x)
    (hy : IsWeight E ν' y) (hne : ν ≠ ν') : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have h := hU a a rfl x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have h2 : ((ν a : ℂ) - ν' a) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) ha
  · exact h3
end GlobalTheory.CompanionTheory.KLowSpan

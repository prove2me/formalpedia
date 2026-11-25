-- Prove2me | solution 1 for GlobalTheory.TorsionCharacter.exists_pow_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:45.169467+00:00
-- url     : https://prove2.me/submissions/ac1d66b8-1da7-45ce-ac19-f7cd36ede60e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacter
variable {O : Type} [CommRing O]
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace GlobalTheory.TorsionCharacter
theorem _root_.solution (a b : TWO.Ov v) (ha : ¬ IsUnit a) (hb : b ≠ 0) :
    ∃ n : ℕ, a ^ n ∈ Ideal.span {b} := by
  by_cases ha0 : a = 0
  · exact ⟨1, by simp [ha0]⟩
  have hbF : (b : F) ≠ 0 := fun h => hb (Subtype.ext h)
  have haF : (a : F) ≠ 0 := fun h => ha0 (Subtype.ext h)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff v).2 haF)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff v).2 hbF)
  have hr0 : 0 < r := by
    have h0 : (0 : ℚ) ≤ r := by have := TWO.v_nonneg v a; rw [← hr] at this; exact_mod_cast this
    refine lt_of_le_of_ne h0 fun h => ha ?_
    have hi : (a : F)⁻¹ ∈ TWO.Ov v := by
      refine TWO.exists_weight_basis_filtration (a := v a) ?_ (by rw [← hr, ← h]; rfl)
      rw [← AddValuation.map_mul, mul_inv_cancel₀ haF, AddValuation.map_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ haF))
  obtain ⟨n, hn⟩ := Archimedean.arch s hr0
  have hq : (a : F) ^ n / b ∈ TWO.Ov v := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
      ((AddValuation.ne_top_iff v).2 (div_ne_zero (pow_ne_zero n haF) hbF))
    have e : v ((a : F) ^ n / b * b) = v ((a : F) ^ n) := by rw [div_mul_cancel₀ _ hbF]
    rw [AddValuation.map_mul, AddValuation.map_pow, ← ht, ← hs, ← hr] at e
    have e' : t + s = n • r := by exact_mod_cast e
    rw [TWO.mem_Ov, ← ht]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t)
  exact ⟨n, Ideal.mem_span_singleton'.2 ⟨⟨_, hq⟩, Subtype.ext (by
    show (a : F) ^ n / b * b = ((a ^ n : TWO.Ov v) : F)
    rw [div_mul_cancel₀ _ hbF]; rfl)⟩⟩
end GlobalTheory.TorsionCharacter

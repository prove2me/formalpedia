-- Prove2me | solution 1 for GlobalTheory.UnramVal.vE_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:07:25.407825+00:00
-- url     : https://prove2.me/submissions/99afb253-c758-4267-a7f1-720126840ada

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Theorems.Thm_GlobalTheory_UnramVal_zpow_mul_unit_mem_iff
import Theorems.Thm_GlobalTheory_UnramVal_vE_zpow_mul_unit
import Theorems.Thm_GlobalTheory_UnramVal_exists_eq_zpow_mul_unit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramVal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.UnramVal
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ x y : F, x ≠ 0 → y ≠ 0 → vE L ϖ (algebraMap F E (x * y)) = vE L ϖ (algebraMap F E x) + vE L ϖ (algebraMap F E y)) ∧ vE L ϖ (algebraMap F E (ϖ : F)) = 1 ∧ (∀ x : F, x ≠ 0 → (0 ≤ vE L ϖ (algebraMap F E x) ↔ x ∈ 𝒪[F])) ∧ (∀ x : F, x ≠ 0 → ∃ u : (𝒪[F])ˣ, x = (ϖ : F) ^ (vE L ϖ (algebraMap F E x)) * ((u : 𝒪[F]) : F)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨fun x y hx hy => ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    obtain ⟨l, v, rfl⟩ := exists_eq_zpow_mul_unit hϖ hy
    have : (ϖ : F) ^ k * ((u : 𝒪[F]) : F) * ((ϖ : F) ^ l * ((v : 𝒪[F]) : F))
        = (ϖ : F) ^ (k + l) * (((u * v : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
      rw [zpow_add₀ h0, Units.val_mul, Subring.coe_mul]; ring
    rw [this, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ]
  · simpa using vE_zpow_mul_unit L hϖ 1 1
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    rw [vE_zpow_mul_unit L hϖ, zpow_mul_unit_mem_iff hϖ]
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    exact ⟨u, by rw [vE_zpow_mul_unit L hϖ]⟩
end GlobalTheory.UnramVal

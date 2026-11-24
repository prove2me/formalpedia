-- Prove2me | solution 1 for GlobalTheory.UnramVal.vE_zpow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:26.926805+00:00
-- url     : https://prove2.me/submissions/95aad70b-6d75-4073-937a-7fd5099e24c8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Theorems.Thm_GlobalTheory_UnramVal_zpow_mul_unit_mem_iff
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
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
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ)
    (u : (𝒪[F])ˣ) : vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hset : {m : ℤ | ∃ y ∈ L.O, algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))
      = algebraMap F E ((ϖ : F) ^ m) * y} = Set.Iic k := by
    ext m
    have hsplit : (ϖ : F) ^ k * ((u : 𝒪[F]) : F)
        = (ϖ : F) ^ m * ((ϖ : F) ^ (k - m) * ((u : 𝒪[F]) : F)) := by
      rw [← mul_assoc, ← zpow_add₀ h0]; congr 2; ring
    have hun : IsUnit (algebraMap F E ((ϖ : F) ^ m)) :=
      (IsUnit.mk0 _ (zpow_ne_zero m h0)).map _
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [hsplit, map_mul, ← sub_nonneg, ← zpow_mul_unit_mem_iff hϖ (k - m) u,
      ← GlobalTheory.UnramOrder.algebraMap_mem_iff L]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [hun.mul_left_cancel h]; exact hy
    · intro h; exact ⟨_, h, rfl⟩
  rw [vE, hset, csSup_Iic]
end GlobalTheory.UnramVal

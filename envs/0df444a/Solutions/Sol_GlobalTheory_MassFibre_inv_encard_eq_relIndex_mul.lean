-- Prove2me | solution 1 for GlobalTheory.MassFibre.inv_encard_eq_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:11:07.440141+00:00
-- url     : https://prove2.me/submissions/7dfcb7bb-35a4-411e-8d41-4765eab10391

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibre
import Theorems.Thm_GlobalTheory_MassFibre_card_mul_relIndex
import Theorems.Thm_GlobalTheory_MassFibre_encard_coe_subgroup
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MassFibre
namespace GlobalTheory.MassFibre
theorem _root_.solution {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K)
    (hr : H.relIndex K ≠ 0) :
    (((H : Set G).encard : ℝ≥0∞))⁻¹ = (H.relIndex K : ℝ≥0∞) * (((K : Set G).encard : ℝ≥0∞))⁻¹ := by
  have hc := card_mul_relIndex H K hle
  rw [encard_coe_subgroup, encard_coe_subgroup]
  by_cases hK : Nat.card K = 0
  · have hH : Nat.card H = 0 := by
      rw [hK] at hc
      rcases Nat.mul_eq_zero.mp hc with h | h
      · exact h
      · exact absurd h hr
    simp [hH, hK]
  · have hH : Nat.card H ≠ 0 := by
      intro h; rw [h, zero_mul] at hc; exact hK hc.symm
    rw [if_neg hH, if_neg hK, ← hc]
    push_cast
    rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hH)) (Or.inl (by simp)), mul_comm,
      mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hr) (by simp), mul_one]
end GlobalTheory.MassFibre

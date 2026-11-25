-- Prove2me | solution 1 for GlobalTheory.MassFibre.encard_coe_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:41:10.794196+00:00
-- url     : https://prove2.me/submissions/e4092516-1a6c-4be0-8af0-79a40de5ae97

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MassFibre
namespace GlobalTheory.MassFibre
theorem _root_.solution {G : Type} [Group G] (H : Subgroup G) :
    ((H : Set G).encard : ℝ≥0∞) = if Nat.card H = 0 then ⊤ else (Nat.card H : ℝ≥0∞) := by
  split_ifs with h
  · have : (H : Set G).Infinite := by
      rcases Nat.card_eq_zero.mp h with h' | h'
      · exact absurd h' (not_isEmpty_of_nonempty _)
      · exact Set.infinite_coe_iff.mp h'
    rw [Set.encard_eq_top_iff.mpr this]; rfl
  · have hf : (H : Set G).Finite := by
      have := Nat.finite_of_card_ne_zero h
      exact Set.toFinite _
    rw [← hf.cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl
end GlobalTheory.MassFibre

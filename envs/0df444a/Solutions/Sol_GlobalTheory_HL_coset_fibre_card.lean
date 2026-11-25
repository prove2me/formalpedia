-- Prove2me | solution 1 for GlobalTheory.HL.coset_fibre_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:13.075724+00:00
-- url     : https://prove2.me/submissions/f69ec9d1-e56a-4049-b093-d0096d255181

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEqInvStabilizerVolume
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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {G : Type} [Group G] (D H : Subgroup G) (h : D ≤ H) (hDH : D.relIndex H ≠ 0)
    (z : G ⧸ H) : Finite {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ∧
      Nat.card {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} = D.relIndex H := by
  let e := Subgroup.quotientEquivProdOfLE (α := G) h
  have he : ∀ y, (e y).1 = Subgroup.quotientMapOfLE h y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H a => rfl
  let e2 : {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ≃ (H ⧸ D.subgroupOf H) :=
    { toFun := fun y => (e y.1).2
      invFun := fun c => ⟨e.symm (z, c), by rw [← he, Equiv.apply_symm_apply]⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply e.injective
        rw [Equiv.apply_symm_apply]
        exact Prod.ext ((he y.1).trans y.2).symm rfl
      right_inv := fun c => by simp }
  haveI : (D.subgroupOf H).FiniteIndex := ⟨hDH⟩
  refine ⟨Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e2]
  rfl
end GlobalTheory.HL

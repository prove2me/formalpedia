-- Prove2me | solution 1 for GlobalTheory.Nef.FundId.sum_ord_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:52:39.232113+00:00
-- url     : https://prove2.me/submissions/158bd59b-92ab-4274-8cf3-207bbf0e73b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
import Theorems.Thm_GlobalTheory_Nef_FundId_ord_toRing
import Theorems.Thm_GlobalTheory_Nef_FundId_toRing_injective
import Theorems.Thm_GlobalTheory_Nef_FundId_toRing_surjective
import Theorems.Thm_GlobalTheory_Nef_FundId_deg_eq_one
import Theorems.Thm_GlobalTheory_Nef_Lib_ord_toRing
import Theorems.Thm_GroundTheory_FunctionField_IsFunctionField_of_finiteDimensional
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_ord_algebraMap
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_ord_algebraMap
import Theorems.Thm_GroundTheory_FunctionField_Place_sum_ramificationIdx_mul_inertiaDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.FundId
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.FundId
theorem _root_.solution : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (v : Place k F) (π : F), π ≠ 0 → ord v π = 1 → {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E π) = Module.finrank F E := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hF ρ hρ v π _ hπ
  classical
  haveI : GroundTheory.FunctionField.IsFunctionField k F := ⟨hF⟩
  haveI : GroundTheory.FunctionField.IsFunctionField k E :=
    GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional (k := k) (K := F)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have key : ∀ p : Place k E, ρ p = v ↔ (toRing p).LiesOver (toRing v) := by
    intro p
    have h1 : (toRing p).LiesOver (toRing (ρ p)) := by
      ext x
      exact hρ p x
    constructor
    · rintro rfl; exact h1
    · intro h
      exact toRing_injective (GroundTheory.FunctionField.Place.ext (h1.symm.trans h))
  have hfin := (toRing v).finite_liesOver (K' := E)
  have hfin' : {p | ρ p = v}.Finite := by
    refine (hfin.preimage toRing_injective.injOn).subset fun p hp => (key p).1 hp
  refine ⟨hfin', ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', ← (toRing v).sum_ramificationIdx_mul_inertiaDeg (K' := E),
    Nat.cast_sum]
  refine Finset.sum_bij (fun p _ => toRing p) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [key] using hp
  · intro p _ q _ h
    exact toRing_injective h
  · intro w hw
    obtain ⟨p, rfl⟩ := toRing_surjective w
    exact ⟨p, by simpa [key] using hw, rfl⟩
  · intro p hp
    have h : (toRing p).LiesOver (toRing v) := by simpa [key] using hp
    rw [← ord_toRing, h.ord_algebraMap, ord_toRing, hπ, GroundTheory.FunctionField.Place.inertiaDeg,
      deg_eq_one, deg_eq_one]
    simp
end GlobalTheory.Nef.FundId

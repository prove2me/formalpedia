-- Prove2me | solution 1 for GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:13:53.38746+00:00
-- url     : https://prove2.me/submissions/9e4ed63c-99f6-45d7-99dc-f44156b78827

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrderPlacesAboveEqFinrankMul
import Theorems.Thm_GlobalTheory_T_functionFieldPlaceOrder_calculus
import Theorems.Thm_GlobalTheory_T_functionFieldPlace_restriction_exists_pow
import Theorems.Thm_GlobalTheory_T_functionFieldPlace_sum_order_eq_finrank
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ
  classical
  have hunif : ∀ v : Place k F, ∃ π : F, π ≠ 0 ∧ ord v π = 1 := fun v => (GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.1
  choose π hπ0 hπ1 using hunif
  have hfib : ∀ v, {p | ρ p = v}.Finite ∧
      ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E (π v)) = Module.finrank F E :=
    fun v => GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k F E hFF ρ hρ v (π v) (hπ0 v) (hπ1 v)
  have hkey : ∀ p x, ord p (algebraMap F E x) = ord p (algebraMap F E (π (ρ p))) * ord (ρ p) x := by
    intro p x
    obtain ⟨e, -, -, he⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k F E).2 ρ hρ p
    rw [he x, he (π (ρ p)), hπ1, mul_one]
  have hpre : ∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite := by
    intro s hs
    have h : ρ ⁻¹' s = ⋃ v ∈ s, {p | ρ p = v} := by ext p; simp
    rw [h]; exact hs.biUnion fun v _ => (hfib v).1
  refine ⟨hpre, fun φ hφ => ?_⟩
  have hT := hpre _ hφ
  have hsupp : (Function.support fun p => ord p (algebraMap F E (φ (ρ p)))) ⊆ ↑hT.toFinset := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
    intro h; apply hp; rw [hkey, h, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [finsum_eq_sum_of_support_subset _ (s := hφ.toFinset) (by intro v hv; simpa using hv)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ρ) (t := hφ.toFinset) (by intro p hp; simpa using hp)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hc : ∀ p ∈ hT.toFinset.filter (fun p => ρ p = v),
      ord p (algebraMap F E (φ (ρ p))) = ord p (algebraMap F E (π v)) * ord v (φ v) := by
    intro p hp
    have hpv := (Finset.mem_filter.1 hp).2
    rw [hkey, hpv]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul]
  congr 1
  rw [← (hfib v).2, finsum_mem_eq_finite_toFinset_sum _ (hfib v).1]
  congr 1
  ext p
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hv, h⟩
end GlobalTheory.Nef

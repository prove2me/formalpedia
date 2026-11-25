-- Prove2me | solution 1 for GroundTheory.Global.trace_restrict_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:54.801339+00:00
-- url     : https://prove2.me/submissions/b60a78ae-2a0a-469b-9f85-dc8b89d61e4e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
namespace GroundTheory.Global
theorem _root_.solution (I : Subgroup G) (B : Module.End ℂ V)
    (hB : ∀ x ∈ subgroupInvariants ρ I, B x ∈ subgroupInvariants ρ I) :
    LinearMap.trace ℂ _ (B.restrict hB) =
      (Nat.card I : ℂ)⁻¹ * ∑ᶠ i : I, LinearMap.trace ℂ V (B * ρ i) := by
  classical
  have := Fintype.ofFinite I
  set W := subgroupInvariants ρ I
  have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  set e : Module.End ℂ V := (Nat.card I : ℂ)⁻¹ • ∑ i : I, ρ i with he
  have he_apply : ∀ x, e x = (Nat.card I : ℂ)⁻¹ • ∑ i : I, ρ i x := fun x => by
    rw [he, LinearMap.smul_apply, LinearMap.sum_apply]
  have he_mem : ∀ x, e x ∈ W := by
    intro x
    rw [mem_invariants_comp_subtype_iff]
    intro j hj
    rw [he_apply, map_smul, map_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨j, hj⟩ : I)) _ _ (fun i => by
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply])
  have he_id : ∀ x ∈ W, e x = x := by
    intro x hx
    rw [mem_invariants_comp_subtype_iff] at hx
    rw [he_apply, Finset.sum_congr rfl fun i _ => hx i.1 i.2, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hI,
      one_smul]
  let e' : V →ₗ[ℂ] W := e.codRestrict W he_mem
  have h1 : B.restrict hB = (e' ∘ₗ B) ∘ₗ W.subtype := by
    ext x
    simp [e', he_id _ (hB x x.2)]
  have h2 : W.subtype ∘ₗ (e' ∘ₗ B) = e ∘ₗ B := by
    ext x
    rfl
  rw [h1, LinearMap.trace_comp_comm', h2, finsum_eq_sum_of_fintype, he, LinearMap.smul_comp,
    map_smul, smul_eq_mul, ← Module.End.mul_eq_comp, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact LinearMap.trace_mul_comm ℂ (ρ i) B
end GroundTheory.Global

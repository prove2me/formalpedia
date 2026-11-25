-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_of_restrictedTensorRep_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:23:49.499369+00:00
-- url     : https://prove2.me/submissions/13a4c777-f8fd-40d4-b68f-6480be5b7df0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Uniqueness
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contract_tensorRep_single
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_IsStable_mono
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_apply_contract
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_coe_restrictedTensorRep_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_evalForm_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nontrivial_of_isIrreducible
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_tensorRep_mulSingle_tprod
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_tprod_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {V' : ι → Type*} [∀ v, AddCommGroup (V' v)] [∀ v, Module ℂ (V' v)]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {π : ∀ v, Representation ℂ (G v) (V v)}
    {π' : ∀ v, Representation ℂ (G v) (V' v)} {ξ : ∀ v, V v} {ξ' : ∀ v, V' v}
    (hirr : ∀ v, (π v).IsIrreducible) (hirr' : ∀ v, (π' v).IsIrreducible)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hξ' : ∀ᶠ v in cofinite, ξ' v ∈ fixedVectors (π' v) (K v))
    (hξ0 : ∀ᶠ v in cofinite, ξ v ≠ 0) (hξ'0 : ∀ᶠ v in cofinite, ξ' v ≠ 0)
    (Φ : (restrictedTensorRep π ξ hξ).Equiv (restrictedTensorRep π' ξ' hξ')) (v : ι) :
    Nonempty ((π v).Equiv (π' v)) := by
  classical
  haveI := hirr v
  haveI := hirr' v
  have hnt : ∀ w, ∃ u : V w, u ≠ 0 := fun w =>
    have := nontrivial_of_isIrreducible (hirr w)
    exists_ne 0
  choose e he using hnt
  set ξ₀ : ∀ w, V w := fun w => if ξ w = 0 then e w else ξ w
  have hξ₀ : IsRestricted ξ ξ₀ := hξ0.mono fun w h => by simp [ξ₀, h]
  have hξ₀0 : ∀ w, ξ₀ w ≠ 0 := fun w => by
    by_cases h : ξ w = 0 <;> simp [ξ₀, h, he w]

  let ins : V v →ₗ[ℂ] restrictedTensor ξ :=
    LinearMap.codRestrict (restrictedTensor ξ) ((PiTensorProduct.tprod ℂ).toLinearMap ξ₀ v)
      fun u => tprod_mem_restrictedTensor (hξ₀.update v u)
  have hins : ∀ u, (ins u : ⨂[ℂ] w, V w) = tprod ℂ (Function.update ξ₀ v u) := fun u => rfl
  have hinsg : ∀ (g : G v) u, ins (π v g u) = restrictedTensorRep π ξ hξ (singleHom K v g) (ins u) :=
    fun g u => Subtype.ext (by
      rw [coe_restrictedTensorRep_apply, hins, hins]
      exact (tensorRep_mulSingle_tprod (K := K) (π := π) v g _).trans (by
        rw [Function.update_idem, Function.update_self]) |>.symm)
  have hy0 : ins (e v) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    rw [hins] at this
    refine tprod_ne_zero (ξ := ξ) (hξ₀.update v (e v)) (fun w => ?_) this
    by_cases hw : w = v
    · subst hw; simp [he]
    · simp [Function.update_of_ne hw, hξ₀0 w]
  have hΦy : ((Φ (ins (e v)) : restrictedTensor ξ') : ⨂[ℂ] w, V' w) ≠ 0 := by
    intro h
    apply hy0
    have : Φ (ins (e v)) = 0 := Subtype.ext h
    exact Φ.toLinearEquiv.injective (this.trans (map_zero _).symm)
  obtain ⟨l', hl', hne⟩ := exists_evalForm_ne_zero hξ'0 (Φ (ins (e v))).2 hΦy

  let μ : Dual ℂ (V v) := evalForm ξ' l' hl' ∘ₗ (restrictedTensor ξ').subtype ∘ₗ
    Φ.toLinearEquiv.toLinearMap ∘ₗ ins
  refine nonempty_equiv_of_matrixCoeff_eq (v := e v) (l := μ)
    (w := contract ξ' l' hl' v (Φ (ins (e v)))) (m := l' v) (fun g => ?_) ⟨1, ?_⟩
  · have hΦ : ∀ (h : Πʳ w, [G w, K w]) (x : restrictedTensor ξ),
        Φ (restrictedTensorRep π ξ hξ h x) = restrictedTensorRep π' ξ' hξ' h (Φ x) :=
      fun h x => Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap h x
    show evalForm ξ' l' hl' (Φ (ins (π v g (e v))) : ⨂[ℂ] w, V' w) = _
    rw [hinsg, hΦ, coe_restrictedTensorRep_apply, ← apply_contract v, contract_tensorRep_single]
  · show evalForm ξ' l' hl' (Φ (ins (π v 1 (e v))) : ⨂[ℂ] w, V' w) ≠ 0
    rw [map_one, Module.End.one_apply]
    exact hne
end GroundTheory.Automorphic.RestrictedTensor

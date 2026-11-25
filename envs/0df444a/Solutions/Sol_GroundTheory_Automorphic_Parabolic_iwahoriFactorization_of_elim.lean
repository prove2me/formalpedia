-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.iwahoriFactorization_of_elim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:24.685917+00:00
-- url     : https://prove2.me/submissions/63aba017-7123-4d23-b859-25764cc89365

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_mul_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_levi_dual
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_inv_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
variable (β)
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (K : Subgroup (GL (Fin n) F))
    (hdiag : ∀ h ∈ K, ∀ a, (h : GL (Fin n) F) a a ≠ 0)
    (helim : ∀ h ∈ K, ∀ a, elimGL β ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a ∈ K)
    (hlevi : ∀ p (hp : p ∈ blockUpper F n β), p ∈ K →
      ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F) ∈ K)
    (hlevi' : ∀ p (hp : p ∈ blockUpper F n (OrderDual.toDual ∘ β)), p ∈ K →
      ((leviProj F n (OrderDual.toDual ∘ β) ⟨p, hp⟩ : levi F n (OrderDual.toDual ∘ β)) :
        GL (Fin n) F) ∈ K) :
    ∀ k ∈ K, ∃ z ∈ K ⊓ oppositeUnipotentRadical F n β, ∃ y ∈ K ⊓ levi F n β,
      ∃ x ∈ K ⊓ unipotentRadical F n β, k = z * y * x := by
  intro k hk
  obtain ⟨q, hq, hqk⟩ := exists_mul_mem_blockUpper K hdiag helim hk
  obtain ⟨hqK, hqP⟩ := Subgroup.mem_inf.1 hq
  set p := q⁻¹ with hp
  have hpK : p ∈ K := K.inv_mem hqK
  have hpP : p ∈ blockUpper F n (OrderDual.toDual ∘ β) := Subgroup.inv_mem _ hqP
  set h := q * k with hh
  have hhK : h ∈ K := K.mul_mem hqK hk
  set m₁ := leviProj F n (OrderDual.toDual ∘ β) ⟨p, hpP⟩ with hm₁
  set m₂ := leviProj F n β ⟨h, hqk⟩ with hm₂
  have hm₁K : (m₁ : GL (Fin n) F) ∈ K := hlevi' p hpP hpK
  have hm₂K : (m₂ : GL (Fin n) F) ∈ K := hlevi h hqk hhK
  have hu₁ := leviProj_inv_mul_mem (F := F) (β := OrderDual.toDual ∘ β) ⟨p, hpP⟩
  have hu₂ := leviProj_inv_mul_mem (F := F) (β := β) ⟨h, hqk⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hu₁ hu₂
  change (m₁ : GL (Fin n) F)⁻¹ * p ∈ oppositeUnipotentRadical F n β at hu₁
  change (m₂ : GL (Fin n) F)⁻¹ * h ∈ unipotentRadical F n β at hu₂
  refine ⟨p * (m₁ : GL (Fin n) F)⁻¹, Subgroup.mem_inf.2 ⟨K.mul_mem hpK (K.inv_mem hm₁K), ?_⟩,
    (m₁ : GL (Fin n) F) * m₂, Subgroup.mem_inf.2 ⟨K.mul_mem hm₁K hm₂K,
      (levi F n β).mul_mem (mem_levi_dual.1 m₁.2) m₂.2⟩,
    (m₂ : GL (Fin n) F)⁻¹ * h, Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem hm₂K) hhK, hu₂⟩, ?_⟩
  · have := conj_mem_unipotentRadical (levi_le_blockUpper m₁.2) hu₁
    rwa [mul_inv_cancel_left] at this
  · rw [hh, hp]
    group
end GroundTheory.Automorphic.Parabolic

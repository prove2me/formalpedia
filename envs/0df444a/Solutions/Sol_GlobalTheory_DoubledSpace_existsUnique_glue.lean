-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.existsUnique_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:07:39.992662+00:00
-- url     : https://prove2.me/submissions/bf053193-13a0-4298-9191-4d863eada576

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_left_isotropic
import Theorems.Thm_GlobalTheory_DoubledSpace_right_isotropic
import Theorems.Thm_GlobalTheory_DoubledSpace_map_fst_le
import Theorems.Thm_GlobalTheory_DoubledSpace_map_snd_le
import Theorems.Thm_GlobalTheory_DoubledSpace_map_fst_eq
import Theorems.Thm_GlobalTheory_DoubledSpace_map_snd_eq
import Theorems.Thm_GlobalTheory_DoubledSpace_reducedForm_mk
import Theorems.Thm_GlobalTheory_DoubledSpace_mem_glue
import Theorems.Thm_GlobalTheory_DoubledSpace_glue_injective
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_glue
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_eq_of_le_of_finrank_eq
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply


attribute [local simp] GlobalTheory.DoubledSpace.reducedForm_mk

set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.DoubledSpace
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0)
include hσ hh hn
namespace GlobalTheory.DoubledSpace
theorem _root_.solution {I : Submodule E (W × W)} (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
    (hd : finrank E I = finrank E W) :
    ∃! φ : Reduced h (left I) ≃ₗ[E] Reduced h (right I),
      (∀ a b, reducedForm h hh (right I) (φ a) (φ b) = reducedForm h hh (left I) a b) ∧
        I = glue h (left I) (right I) φ := by
  have m1 : ∀ p : I, p.1.1 ∈ (left I).orthogonalBilin h := fun p => map_fst_le hI ⟨_, p.2, rfl⟩
  have m2 : ∀ p : I, p.1.2 ∈ (right I).orthogonalBilin h := fun p => map_snd_le hI ⟨_, p.2, rfl⟩
  let f₁ : I →ₗ[E] Reduced h (left I) := (Submodule.mkQ _).comp
    (((LinearMap.fst E W W).domRestrict I).codRestrict _ m1)
  let f₂ : I →ₗ[E] Reduced h (right I) := (Submodule.mkQ _).comp
    (((LinearMap.snd E W W).domRestrict I).codRestrict _ m2)
  have d1 : ∀ p, f₁ p = Submodule.Quotient.mk ⟨p.1.1, m1 p⟩ := fun _ => rfl
  have d2 : ∀ p, f₂ p = Submodule.Quotient.mk ⟨p.1.2, m2 p⟩ := fun _ => rfl
  have s1 : Function.Surjective f₁ := fun a => by
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    have hx' := hx
    rw [← map_fst_eq hσ hh hn hI hd] at hx'
    obtain ⟨p, hp, rfl⟩ := hx'
    exact ⟨⟨p, hp⟩, rfl⟩
  have s2 : Function.Surjective f₂ := fun a => by
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    have hx' := hx
    rw [← map_snd_eq hσ hh hn hI hd] at hx'
    obtain ⟨p, hp, rfl⟩ := hx'
    exact ⟨⟨p, hp⟩, rfl⟩
  have key : ∀ p q, f₁ p = f₁ q ↔ f₂ p = f₂ q := fun p q => by
    rw [d1, d1, d2, d2, Submodule.Quotient.eq, Submodule.Quotient.eq]
    change (p.1.1 - q.1.1, 0) ∈ I ↔ (0, p.1.2 - q.1.2) ∈ I
    have hpq := I.sub_mem p.2 q.2
    constructor
    · intro H
      convert I.sub_mem hpq H using 1
      ext <;> simp
    · intro H
      convert I.sub_mem hpq H using 1
      ext <;> simp
  obtain ⟨φ, hφ⟩ := LinearMap.exists_linearEquiv_eq_graph (f := f₁.prod f₂) s1 s2 key
  have hf : ∀ p, φ (f₁ p) = f₂ p := fun p => by
    have : (f₁.prod f₂) p ∈ φ.toLinearMap.graph := hφ ▸ LinearMap.mem_range_self _ p
    exact Eq.symm this
  have hg : I = glue h (left I) (right I) φ := by
    refine Submodule.eq_of_le_of_finrank_eq (fun p hp => ?_) ?_
    · exact mem_glue.2 ⟨m1 ⟨p, hp⟩, m2 ⟨p, hp⟩, hf ⟨p, hp⟩⟩
    · rw [hd, finrank_glue hσ hh hn (left_isotropic hI) (right_isotropic hI)]
  refine ⟨φ, ⟨fun a b => ?_, hg⟩, ?_⟩
  · obtain ⟨p, rfl⟩ := s1 a
    obtain ⟨q, rfl⟩ := s1 b
    rw [hf, hf, d1, d1, d2, d2, reducedForm_mk, reducedForm_mk]
    exact (sub_eq_zero.1 (hI _ p.2 _ q.2)).symm
  · rintro ψ ⟨-, hψ⟩
    exact LinearEquiv.toLinearMap_injective (glue_injective (hψ.symm.trans hg))
end GlobalTheory.DoubledSpace

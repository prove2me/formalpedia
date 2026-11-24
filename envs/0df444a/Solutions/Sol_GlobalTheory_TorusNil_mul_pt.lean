-- Prove2me | solution 1 for GlobalTheory.TorusNil.mul_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:15.718806+00:00
-- url     : https://prove2.me/submissions/1ee0d93a-b0d5-44c9-a053-3219a7ebb582

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_spm_comp
import Theorems.Thm_GlobalTheory_TorusNil_pt_injective
import Theorems.Thm_GlobalTheory_TorusNil_pt_one
import Theorems.Thm_GlobalTheory_TorusNil_exists_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable {B : Over (Spec (CommRingCat.of A))} [GrpObj B] {R : Type} [CommRing R] [Algebra A R]
  (j : sp A R ⟶ B) [IsOpenImmersion j.left] (ε : R →ₐ[A] A) (hε : spm ε ≫ j = 1)
include hε
namespace GlobalTheory.TorusNil
theorem _root_.solution {C : Type} [CommRing C] [Algebra A C] (K : Ideal C) (hK : ∀ x ∈ K, IsNilpotent x)
    (φ₁ φ₂ φ : R →ₐ[A] C) (h₁ : ∀ a, φ₁ a - algebraMap A C (ε a) ∈ K)
    (h₂ : ∀ a, φ₂ a - algebraMap A C (ε a) ∈ K)
    (h : (spm φ₁ ≫ j) * (spm φ₂ ≫ j) = spm φ ≫ j) (a : R) :
    φ a - (φ₁ a + φ₂ a - algebraMap A C (ε a)) ∈ K ^ 2 := by
  set e : R →ₐ[A] C := (Algebra.ofId A C).comp ε with he
  have he1 : spm e ≫ j = 1 := pt_one j ε hε C
  let G₁ : R →ₐ[A] triples A K := (φ₁.prod (e.prod e)).codRestrict _
    (fun a => ⟨h₁ a, by simp⟩)
  let G₂ : R →ₐ[A] triples A K := (e.prod (φ₂.prod e)).codRestrict _
    (fun a => ⟨by simp, h₂ a⟩)
  have key : ∀ {D : Type} [CommRing D] [Algebra A D] (p : triples A K →ₐ[A] D),
      spm p ≫ ((spm G₁ ≫ j) * (spm G₂ ≫ j)) =
        (spm (p.comp G₁) ≫ j) * (spm (p.comp G₂) ≫ j) := by
    intro D _ _ p
    rw [MonObj.comp_mul, spm_comp, spm_comp, Category.assoc, Category.assoc]
  have k3 : spm (tr₃ K) ≫ ((spm G₁ ≫ j) * (spm G₂ ≫ j)) = 1 := by
    rw [key]
    change (spm e ≫ j) * (spm e ≫ j) = 1
    rw [he1, _root_.mul_one]
  obtain ⟨Ψ, hΨ⟩ := exists_pt j ε hε (tr₃ K) (fun c => ⟨⟨(c, c, c), by simp, by simp⟩, rfl⟩)
    (by
      rintro ⟨⟨x, y, z⟩, hx, hy⟩ h0
      obtain rfl : z = 0 := h0
      obtain ⟨n, hn⟩ := hK x (by simpa using hx)
      obtain ⟨m, hm⟩ := hK y (by simpa using hy)
      refine ⟨n + m + 1, Subtype.ext ?_⟩
      simp [pow_add, hn, hm]) _ k3
  rw [← hΨ] at key k3
  have e3 : (tr₃ K).comp Ψ = e := pt_injective j (by
    rw [spm_comp, Category.assoc, k3, he1])
  have e1 : (tr₁ K).comp Ψ = φ₁ := pt_injective j (by
    rw [spm_comp, Category.assoc, key]
    change (spm φ₁ ≫ j) * (spm e ≫ j) = _
    rw [he1, _root_.mul_one])
  have e2 : (tr₂ K).comp Ψ = φ₂ := pt_injective j (by
    rw [spm_comp, Category.assoc, key]
    change (spm e ≫ j) * (spm φ₂ ≫ j) = _
    rw [he1, _root_.one_mul])
  have s1 : (trSum K).comp G₁ = (Ideal.Quotient.mkₐ A (K ^ 2)).comp φ₁ := by
    ext a
    change Ideal.Quotient.mk _ (φ₁ a + e a - e a) = Ideal.Quotient.mk _ (φ₁ a)
    rw [add_sub_cancel_right]
  have s2 : (trSum K).comp G₂ = (Ideal.Quotient.mkₐ A (K ^ 2)).comp φ₂ := by
    ext a
    change Ideal.Quotient.mk _ (e a + φ₂ a - e a) = Ideal.Quotient.mk _ (φ₂ a)
    rw [add_sub_cancel_left]
  have e4 : (Ideal.Quotient.mkₐ A (K ^ 2)).comp φ = (trSum K).comp Ψ := pt_injective j (by
    rw [spm_comp Ψ, Category.assoc, key, s1, s2, spm_comp, spm_comp, spm_comp, Category.assoc,
      Category.assoc, Category.assoc, ← MonObj.comp_mul, h])
  rw [← Ideal.Quotient.eq]
  refine (AlgHom.congr_fun e4 a).trans ?_
  rw [← e1, ← e2]
  have := AlgHom.congr_fun e3 a
  change _ = Ideal.Quotient.mk _ (_ - e a)
  rw [← this]
  rfl
end GlobalTheory.TorusNil

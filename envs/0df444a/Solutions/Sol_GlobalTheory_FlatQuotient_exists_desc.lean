-- Prove2me | solution 1 for GlobalTheory.FlatQuotient.exists_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:33:14.848532+00:00
-- url     : https://prove2.me/submissions/3da94f84-85d5-47c1-be7d-c0d03d8bc59d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Theorems.Thm_GlobalTheory_FlatQuotient_epi_tensorHom
import Theorems.Thm_GlobalTheory_FlatQuotient_comp_eq_of_kills_kernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FlatQuotient
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.FlatQuotient
namespace _root_.GlobalTheory.FlatQuotient
theorem _root_.solution {G B B' T : Over S} [GrpObj G]
    [GrpObj B] [GrpObj B'] (q : G ⟶ B) (i : T ⟶ G) (f : G ⟶ B') [IsMonHom q] [IsMonHom f]
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hker : IsPullback i (toUnit _) q (η[B])) (hf : i ≫ f = toUnit _ ≫ η[B']) :
    ∃ β : B ⟶ B', IsMonHom β ∧ q ≫ β = f := by
  have hcomp : ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ G.left), g₁ ≫ q.left = g₂ ≫ q.left →
      g₁ ≫ f.left = g₂ ≫ f.left := by
    intro Z g₁ g₂ h
    have hw : g₂ ≫ G.hom = g₁ ≫ G.hom := by
      rw [← Over.w q, ← Category.assoc, ← h, Category.assoc]
    have key := _root_.GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel q i f hker hf (Z := Over.mk (g₁ ≫ G.hom))
      (Over.homMk g₁) (Over.homMk g₂ hw) (by ext; simpa using h)
    simpa using congrArg (fun φ => φ.left) key
  let β₀ : B.left ⟶ B'.left := EffectiveEpi.desc q.left f.left hcomp
  have hβ₀ : q.left ≫ β₀ = f.left := EffectiveEpi.fac _ _ _
  have hw : β₀ ≫ B'.hom = B.hom := by
    rw [← cancel_epi q.left, reassoc_of% hβ₀, Over.w f, Over.w q]
  let β : B ⟶ B' := Over.homMk β₀ hw
  have hqβ : q ≫ β = f := by
    ext
    simp [β, hβ₀]
  have hqq : Epi (q ⊗ₘ q) := _root_.GlobalTheory.FlatQuotient.epi_tensorHom q q
  refine ⟨β, ⟨?_, ?_⟩, hqβ⟩
  · rw [← IsMonHom.one_hom (f := q), Category.assoc, hqβ, IsMonHom.one_hom]
  · rw [← cancel_epi (q ⊗ₘ q)]
    calc (q ⊗ₘ q) ≫ μ ≫ β = μ ≫ q ≫ β := by
          rw [← Category.assoc, ← IsMonHom.mul_hom, Category.assoc]
      _ = μ ≫ f := by rw [hqβ]
      _ = (f ⊗ₘ f) ≫ μ := IsMonHom.mul_hom f
      _ = (q ⊗ₘ q) ≫ (β ⊗ₘ β) ≫ μ := by
          rw [← hqβ]
          simp
end _root_.GlobalTheory.FlatQuotient
end GlobalTheory.FlatQuotient

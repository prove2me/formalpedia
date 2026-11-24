-- Prove2me | solution 1 for GlobalTheory.AlgClosedFibre.exists_point_mem_translates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:35.248796+00:00
-- url     : https://prove2.me/submissions/13fb0a4f-2483-483f-88ac-75f43d3459d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPointMemTranslates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AlgClosedFibre
namespace GlobalTheory.AlgClosedFibre
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens),
      (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)),
      ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧
        (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by
  intro S P K _ _ t hirr U hU a c p
  let T : Over S := Over.mk t
  let E : Over S := T ⊗ P.A
  have hsm : Smooth P.A.hom := P.isAb.smooth
  have hlft : LocallyOfFiniteType (fst T P.A).left := by
    change LocallyOfFiniteType (pullback.fst t P.A.hom)
    infer_instance
  have hJ0 : JacobsonSpace T.left := by
    change JacobsonSpace (PrimeSpectrum K)
    infer_instance
  have hJ : JacobsonSpace E.left := LocallyOfFiniteType.jacobsonSpace (fst T P.A).left
  let g₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c) * snd T P.A * (fst T P.A ≫ a))
  let g₂ : E ⟶ E := lift (fst T P.A) ((snd T P.A)⁻¹ * (fst T P.A ≫ a))
  let h₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c)⁻¹ * snd T P.A * (fst T P.A ≫ a)⁻¹)
  let h₂ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ a) * (snd T P.A)⁻¹)
  have e₁ : h₁ ≫ g₁ = 𝟙 E := by
    ext1
    · simp [g₁, h₁]
    · simp [g₁, h₁, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have e₂ : h₂ ≫ g₂ = 𝟙 E := by
    ext1
    · simp [g₂, h₂]
    · simp [g₂, h₂, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have ne : ∀ {f g : E ⟶ E}, g ≫ f = 𝟙 E → ((f.left ⁻¹ᵁ U : E.left.Opens) : Set E.left).Nonempty := by
    intro f g h
    obtain ⟨w, hw⟩ := hU
    refine ⟨g.left w, ?_⟩
    change f.left (g.left w) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
    exact hw
  have hin := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) (ne e₁) (ne e₂)
  obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hin
    ((TopologicalSpace.Opens.isOpen _).inter (TopologicalSpace.Opens.isOpen _)).isLocallyClosed
  let q := pointOfClosedPoint (fst T P.A).left z hc
  have hq : q ≫ (fst T P.A).left = 𝟙 _ := pointOfClosedPoint_comp _ z hc
  have hqw : q ≫ E.hom = t := by
    rw [← Over.w (fst T P.A), ← Category.assoc, hq, Category.id_comp]
    rfl
  let Q : T ⟶ E := Over.homMk q hqw
  have hQf : Q ≫ fst T P.A = 𝟙 T := by
    ext1
    exact hq
  have hQf' : ∀ (f : T ⟶ P.A), Q ≫ fst T P.A ≫ f = f := fun f => by
    rw [← Category.assoc, hQf, Category.id_comp]
  have hqp : q p = z := pointOfClosedPoint_apply _ z hc p
  refine ⟨Q ≫ snd T P.A, ?_, ?_⟩
  · have hQ : lift (𝟙 T) (c * (Q ≫ snd T P.A) * a) = Q ≫ g₁ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₁, hQf]
      · simp only [lift_snd, Category.assoc, g₁, MonObj.comp_mul, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₁.left (q p) ∈ U
    rw [hqp]
    exact hz.1
  · have hQ : lift (𝟙 T) ((Q ≫ snd T P.A)⁻¹ * a) = Q ≫ g₂ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₂, hQf]
      · simp only [lift_snd, Category.assoc, g₂, MonObj.comp_mul, GrpObj.comp_inv, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₂.left (q p) ∈ U
    rw [hqp]
    exact hz.2
end GlobalTheory.AlgClosedFibre

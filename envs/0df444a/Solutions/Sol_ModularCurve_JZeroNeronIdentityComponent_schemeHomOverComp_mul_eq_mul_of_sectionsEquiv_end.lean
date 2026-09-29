-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponent.schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/bc543d60-9134-5554-83c2-d04ee9695e04

import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = N.L.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (F : End 𝒢) (φ : SchemeHomOver N.g N.g)
    (hF : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U (F.1.app (op U) s)).1 = (e U s).1 ≫ φ.1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t N.g) :
    NeronModelInfra.schemeHomOverComp (N.L.mul t x y) φ =
      N.L.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by

  haveI : Smooth N.g := N.smooth
  haveI : Flat N.g := inferInstance
  haveI : LocallyOfFinitePresentation N.g := inferInstance
  let π₁ := pullback.fst N.g N.g
  let π₂ := pullback.snd N.g N.g
  haveI : Flat (π₁ ≫ N.g) := inferInstance
  haveI : LocallyOfFinitePresentation (π₁ ≫ N.g) := inferInstance
  let U₀ : specInt.Fppf := Scheme.Fppf.mk (π₁ ≫ N.g)
  have hU₀ : U₀.hom = π₁ ≫ N.g := rfl
  let x₁ : SchemeHomOver U₀.hom N.g := ⟨π₁, rfl⟩
  let x₂ : SchemeHomOver U₀.hom N.g := ⟨π₂, pullback.condition.symm⟩
  let s₁ := (e U₀).symm x₁
  let s₂ := (e U₀).symm x₂

  have huniv : NeronModelInfra.schemeHomOverComp (N.L.mul U₀.hom x₁ x₂) φ =
      N.L.mul U₀.hom (NeronModelInfra.schemeHomOverComp x₁ φ) (NeronModelInfra.schemeHomOverComp x₂ φ) := by
    have hadd : F.1.app (op U₀) (s₁ + s₂) = F.1.app (op U₀) s₁ + F.1.app (op U₀) s₂ := map_add _ _ _
    have h1 : (e U₀ (F.1.app (op U₀) (s₁ + s₂))).1 = (N.L.mul U₀.hom x₁ x₂).1 ≫ φ.1 := by
      rw [hF, he_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hx : ∀ (x : SchemeHomOver U₀.hom N.g),
        e U₀ (F.1.app (op U₀) ((e U₀).symm x)) = NeronModelInfra.schemeHomOverComp x φ := by
      intro x
      apply Subtype.ext
      rw [hF, Equiv.apply_symm_apply]
      rfl
    have h2 : (e U₀ (F.1.app (op U₀) s₁ + F.1.app (op U₀) s₂)).1 =
        (N.L.mul U₀.hom (NeronModelInfra.schemeHomOverComp x₁ φ) (NeronModelInfra.schemeHomOverComp x₂ φ)).1 := by
      rw [he_add, hx, hx]
    apply Subtype.ext
    show (N.L.mul U₀.hom x₁ x₂).1 ≫ φ.1 = _
    rw [← h1, hadd]
    exact h2

  let ψ : T ⟶ pullback N.g N.g := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ1 : ψ ≫ π₁ = x.1 := pullback.lift_fst _ _ _
  have hψ : ψ ≫ U₀.hom = t := by
    calc ψ ≫ U₀.hom = ψ ≫ (π₁ ≫ N.g) := rfl
      _ = (ψ ≫ π₁) ≫ N.g := (Category.assoc _ _ _).symm
      _ = x.1 ≫ N.g := by rw [hψ1]
      _ = t := x.2
  have hx' : x = GoodReductionJacobian.schemeHomOverComp ψ hψ x₁ :=
    Subtype.ext (pullback.lift_fst _ _ _).symm
  have hy' : y = GoodReductionJacobian.schemeHomOverComp ψ hψ x₂ :=
    Subtype.ext (pullback.lift_snd _ _ _).symm

  have hswap : ∀ z : SchemeHomOver U₀.hom N.g,
      NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ z) φ =
        GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp z φ) := by
    intro z; apply Subtype.ext; simp [Category.assoc]
  have hA : N.L.mul t x y = GoodReductionJacobian.schemeHomOverComp ψ hψ (N.L.mul U₀.hom x₁ x₂) := by
    rw [hx', hy']; exact (N.L.mul_natural U₀.hom t ψ hψ x₁ x₂).symm
  have e1 : NeronModelInfra.schemeHomOverComp x φ =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x₁ φ) := by
    rw [hx']; exact hswap x₁
  have e2 : NeronModelInfra.schemeHomOverComp y φ =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x₂ φ) := by
    rw [hy']; exact hswap x₂
  have hB : N.L.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ
        (N.L.mul U₀.hom (NeronModelInfra.schemeHomOverComp x₁ φ) (NeronModelInfra.schemeHomOverComp x₂ φ)) := by
    rw [e1, e2]
    exact (N.L.mul_natural U₀.hom t ψ hψ _ _).symm
  rw [hA, hB]
  exact (hswap _).trans (congrArg _ huniv)

end S_ModularCurve_JZeroNeronIdentityComponent_schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponent_schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end (solution)

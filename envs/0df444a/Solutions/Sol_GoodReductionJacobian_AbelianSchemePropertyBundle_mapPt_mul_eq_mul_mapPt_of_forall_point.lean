-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.mapPt_mul_eq_mul_mapPt_of_forall_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5bc4dd52-b6ca-5b73-a6a3-955db66f52a6

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mapPt_mul_eq_mul_mapPt_of_forall_point

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
theorem solution
    (k : Type) [Field k] [IsAlgClosed k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of k)) (L' : RelativeGroupLaw k f')
    (hA' : AbelianSchemePropertyBundle k f')
    (u : A ⟶ A') (hu : u ≫ f' = f)
    (h1 : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      mapPt u hu (L.mul (𝟙 (Spec (CommRingCat.of k))) P Q) =
        L'.mul (𝟙 (Spec (CommRingCat.of k))) (mapPt u hu P) (mapPt u hu Q))
    {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver s f) :
    mapPt u hu (L.mul s P Q) = L'.mul s (mapPt u hu P) (mapPt u hu Q) := by
  classical
  haveI : Smooth f := hA.smooth
  haveI : IsProper f' := hA'.proper

  let t : Limits.pullback f f ⟶ Spec (CommRingCat.of k) := Limits.pullback.fst f f ≫ f
  let P₀ : SchemeHomOver t f := ⟨Limits.pullback.fst f f, rfl⟩
  let Q₀ : SchemeHomOver t f := ⟨Limits.pullback.snd f f, Limits.pullback.condition.symm⟩
  let μ : Limits.pullback f f ⟶ A := (L.mul t P₀ Q₀).1
  let μ' : Limits.pullback f f ⟶ A' := (L'.mul t (mapPt u hu P₀) (mapPt u hu Q₀)).1
  haveI : Smooth t := inferInstance
  haveI : IsReduced (Limits.pullback f f) := AlgebraicGeometry.isReduced_of_smooth_over_field (g := t) inferInstance

  have hcomp : ∀ {T T' : Scheme.{0}} (τ : T ⟶ Spec (CommRingCat.of k)) (τ' : T' ⟶ Spec (CommRingCat.of k))
      (ψ : T' ⟶ T) (hψ : ψ ≫ τ = τ') (X : SchemeHomOver τ f),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (mapPt u hu X) = mapPt u hu (GoodReductionJacobian.schemeHomOverComp ψ hψ X) := by
    intro T T' τ τ' ψ hψ X
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, mapPt_coe, Category.assoc]

  have key : μ ≫ u = μ' := by
    apply AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed t f'
    · rw [Category.assoc, hu]; exact (L.mul t P₀ Q₀).2
    · exact (L'.mul t (mapPt u hu P₀) (mapPt u hu Q₀)).2
    · intro x hx
      have e1 := congrArg Subtype.val (L.mul_natural t (𝟙 _) x hx P₀ Q₀)
      have e2 := congrArg Subtype.val (L'.mul_natural t (𝟙 _) x hx (mapPt u hu P₀) (mapPt u hu Q₀))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at e1 e2
      rw [hcomp, hcomp, ← h1] at e2
      change x ≫ μ ≫ u = x ≫ μ'
      rw [← Category.assoc, e1, e2, mapPt_coe]

  let φ : S ⟶ Limits.pullback f f := Limits.pullback.lift P.1 Q.1 (P.2.trans Q.2.symm)
  have hφ : φ ≫ t = s := by
    change φ ≫ (Limits.pullback.fst f f ≫ f) = s
    rw [← Category.assoc, Limits.pullback.lift_fst]; exact P.2
  have hP : GoodReductionJacobian.schemeHomOverComp φ hφ P₀ = P := Subtype.ext (Limits.pullback.lift_fst _ _ _)
  have hQ : GoodReductionJacobian.schemeHomOverComp φ hφ Q₀ = Q := Subtype.ext (Limits.pullback.lift_snd _ _ _)
  have m1 := congrArg Subtype.val (L.mul_natural t s φ hφ P₀ Q₀)
  have m2 := congrArg Subtype.val (L'.mul_natural t s φ hφ (mapPt u hu P₀) (mapPt u hu Q₀))
  rw [GoodReductionJacobian.schemeHomOverComp_coe, hP, hQ] at m1
  rw [GoodReductionJacobian.schemeHomOverComp_coe, hcomp, hcomp, hP, hQ] at m2
  apply Subtype.ext
  rw [mapPt_coe, ← m1, ← m2, Category.assoc, key]

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_mapPt_mul_eq_mul_mapPt_of_forall_point
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mapPt_mul_eq_mul_mapPt_of_forall_point (solution)

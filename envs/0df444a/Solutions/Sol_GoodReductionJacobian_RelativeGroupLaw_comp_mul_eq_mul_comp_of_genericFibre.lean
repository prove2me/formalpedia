-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/08438623-1c20-52e2-b3fc-907bf62dbd48

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre

universe u

open CategoryTheory

open CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)}
    {t : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)}
    [AlgebraicGeometry.IsSeparated f] [AlgebraicGeometry.Flat t]
    (G : GoodReductionJacobian.RelativeGroupLaw R f) (H : GoodReductionJacobian.RelativeGroupLaw R t)
    (φ : NeronModelInfra.SchemeHomOver t f)
    (hφ : ∀ {S : AlgebraicGeometry.Scheme.{u}} (s : S ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
        (x y : NeronModelInfra.SchemeHomOver (s ≫ NeronModelInfra.specGenericFibreInclusion R K) t),
        (H.mul _ x y).1 ≫ φ.1 =
          (G.mul _ ⟨x.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, x.2]⟩
            ⟨y.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, y.2]⟩).1)
    {S : AlgebraicGeometry.Scheme.{u}} (s : S ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (x y : NeronModelInfra.SchemeHomOver s t) :
    (H.mul s x y).1 ≫ φ.1 =
      (G.mul s ⟨x.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, x.2]⟩
        ⟨y.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, y.2]⟩).1 := by

  let P := CategoryTheory.Limits.pullback t t
  let tt : P ⟶ Spec (CommRingCat.of R) := CategoryTheory.Limits.pullback.fst t t ≫ t
  let u₁ : SchemeHomOver tt t := ⟨CategoryTheory.Limits.pullback.fst t t, rfl⟩
  let u₂ : SchemeHomOver tt t := ⟨CategoryTheory.Limits.pullback.snd t t, CategoryTheory.Limits.pullback.condition.symm⟩

  let post : ∀ {S' : Scheme.{u}} {s' : S' ⟶ Spec (CommRingCat.of R)}, SchemeHomOver s' t → SchemeHomOver s' f :=
    fun z => ⟨z.1 ≫ φ.1, by rw [Category.assoc, φ.2, z.2]⟩
  have post_comp : ∀ {S' S'' : Scheme.{u}} {s' : S' ⟶ Spec (CommRingCat.of R)} {s'' : S'' ⟶ Spec (CommRingCat.of R)}
      (ψ : S'' ⟶ S') (hψ : ψ ≫ s' = s'') (z : SchemeHomOver s' t),
      post (GoodReductionJacobian.schemeHomOverComp ψ hψ z) = GoodReductionJacobian.schemeHomOverComp ψ hψ (post z) :=
    fun ψ hψ z => Subtype.ext (Category.assoc _ _ _)

  let μ₁ : SchemeHomOver tt f := post (H.mul tt u₁ u₂)
  let μ₂ : SchemeHomOver tt f := G.mul tt (post u₁) (post u₂)
  haveI : Flat tt := inferInstance
  have hμ : μ₁ = μ₂ := by
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f tt
    apply Subtype.ext
    change CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst tt (specGenericFibreInclusion R K) ≫ μ₁.1) _ _ =
      CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst tt (specGenericFibreInclusion R K) ≫ μ₂.1) _ _
    congr 1

    set q := CategoryTheory.Limits.pullback.fst tt (specGenericFibreInclusion R K) with hq
    have hqt : q ≫ tt = CategoryTheory.Limits.pullback.snd tt (specGenericFibreInclusion R K) ≫ specGenericFibreInclusion R K :=
      CategoryTheory.Limits.pullback.condition
    have e1 : q ≫ μ₁.1 = (H.mul _ (GoodReductionJacobian.schemeHomOverComp q hqt u₁)
        (GoodReductionJacobian.schemeHomOverComp q hqt u₂)).1 ≫ φ.1 := by
      rw [← H.mul_natural tt _ q hqt u₁ u₂]; rfl
    have e2 : q ≫ μ₂.1 = (G.mul _ (GoodReductionJacobian.schemeHomOverComp q hqt (post u₁))
        (GoodReductionJacobian.schemeHomOverComp q hqt (post u₂))).1 := by
      rw [← G.mul_natural tt _ q hqt]; rfl
    rw [e1, e2, hφ, ← post_comp, ← post_comp]

  let pr : S ⟶ P := CategoryTheory.Limits.pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hpr : pr ≫ tt = s := by
    change CategoryTheory.Limits.pullback.lift x.1 y.1 _ ≫ CategoryTheory.Limits.pullback.fst t t ≫ t = s
    rw [CategoryTheory.Limits.pullback.lift_fst_assoc, x.2]
  have hx : x = GoodReductionJacobian.schemeHomOverComp pr hpr u₁ :=
    Subtype.ext (CategoryTheory.Limits.pullback.lift_fst _ _ _).symm
  have hy : y = GoodReductionJacobian.schemeHomOverComp pr hpr u₂ :=
    Subtype.ext (CategoryTheory.Limits.pullback.lift_snd _ _ _).symm
  have e3 : (H.mul s x y).1 ≫ φ.1 = pr ≫ μ₁.1 := by
    rw [hx, hy, ← H.mul_natural tt s pr hpr]; rfl
  have e4 : (G.mul s (post x) (post y)).1 = pr ≫ μ₂.1 := by
    rw [hx, hy, post_comp, post_comp, ← G.mul_natural tt s pr hpr]; rfl
  change (H.mul s x y).1 ≫ φ.1 = (G.mul s (post x) (post y)).1
  rw [e3, e4, hμ]

end S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre (solution)

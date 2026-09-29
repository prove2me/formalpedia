-- Prove2me | solution 1 for ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5870bb13-2ea1-5ef2-8ba4-d828756e8fe6

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponentGood
import Theorems.Thm_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_jZeroNeronIdentityComponentGood_of_subsingleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing

namespace SmallGood

theorem hom_specZ_ext {X : Scheme.{0}} (a b : X ⟶ Spec (CommRingCat.of ℤ)) : a = b :=
  specZIsTerminal.hom_ext a b

noncomputable def ptIso {B X T : Scheme.{0}} (f : X ⟶ B) [IsIso f] (t : T ⟶ B) : SchemeHomOver t f :=
  ⟨t ≫ inv f, by simp⟩

noncomputable def trivialLawOfIsIso (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] :
    RelativeGroupLaw R f where
  mul _ x _ := x
  one t := ptIso f t
  inv _ x := x
  mul_assoc _ _ _ _ := rfl
  one_mul t _ := (subsingleton_schemeHomOver_of_isIso t f).allEq _ _
  mul_one _ _ := rfl
  inv_mul_cancel t _ := (subsingleton_schemeHomOver_of_isIso t f).allEq _ _
  mul_natural _ _ _ _ _ _ := rfl

noncomputable def inclLoc (ℓ : ℕ) [Fact ℓ.Prime] (A' : ValuationSubring (AlgebraicClosure ℚ)) (hA' : A'.LiesOverPrime ℓ) :
    ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A' :=
  ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (GaloisRep.ratLocalizedAt ℓ).subtype).codRestrict A'.toSubring (by
    intro r
    have hr : (r : ℚ) = (r : ℚ).num / (r : ℚ).den := (Rat.num_div_den (r : ℚ)).symm
    have hcop : (r : ℚ).den.Coprime ℓ := r.2
    show (algebraMap ℚ (AlgebraicClosure ℚ)) (r : ℚ) ∈ A'.toSubring
    rw [hr, map_div₀, map_intCast, map_natCast, div_eq_mul_inv]
    exact A'.toSubring.mul_mem (intCast_mem A'.toSubring _)
      (ValuationSubring.inv_natCast_mem_of_coprime_of_liesOverPrime A' hA' hcop))

end SmallGood

open SmallGood in

theorem solution (p : ℕ) [Fact p.Prime]
    (hC : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ p → ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
      Subsingleton (JZeroC (IsLocalRing.ResidueField ↥A') p))
    (h : Subsingleton (JZero p)) : Nonempty (JZeroNeronIdentityComponentGood p) := by
  classical
  letI := heckeModuleBar p
  haveI : Subsingleton (JZero p) := h
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let g : Spec (CommRingCat.of ℤ) ⟶ Spec (CommRingCat.of ℤ) := 𝟙 _
  let L : RelativeGroupLaw ℤ g := trivialRelativeGroupLaw ℤ
  let qq := Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))
  haveI hsubZ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of ℤ)), Subsingleton (SchemeHomOver t g) :=
    fun T t => subsingleton_schemeHomOver_of_isIso t _
  let pts : JZero p ≃ SchemeHomOver qq g :=
    { toFun := fun _ => ⟨qq, Category.comp_id qq⟩
      invFun := fun _ => 0
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := fun s => Subsingleton.elim _ _ }
  have hns : ∀ n : ℕ, L.schemeNsmul n = 𝟙 _ := fun n => hom_specZ_ext _ _

  let N : JZeroNeronIdentityComponent p :=
  { G := Spec (CommRingCat.of ℤ)
    g := g
    L := L
    pts := pts
    comm := fun t x y => Subsingleton.elim _ _
    smooth := inferInstance
    separated := inferInstance
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance
    surjective := inferInstance
    fibre_preconnected := by
      intro s
      have : (g.base ⁻¹' {s} : Set _) = {s} := by ext x; simp [g]
      rw [this]; exact isPreconnected_singleton
    pts_add := fun x y => Subsingleton.elim _ _
    pts_galois := fun σ x => hom_specZ_ext _ _
    hecke := by
      intro t
      refine ⟨⟨𝟙 _, Category.id_comp _⟩, ?_, ?_⟩
      · intro T s x y; exact Subsingleton.elim _ _
      · intro x; exact hom_specZ_ext _ _
    nsmul_flat := fun n hn => by rw [hns]; infer_instance
    nsmul_surjective := fun n hn => by rw [hns]; infer_instance
    sections_finiteIndex := inferInstance
    torsion_over_p := by
      intro A hA m hm
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      constructor
      · intro _; exact (jZeroToricTorsion p A m).zero_mem
      · intro _
        refine ⟨(jZeroTorsion p m).zero_mem, ⟨Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)), Category.comp_id _⟩, ?_⟩
        exact hom_specZ_ext _ _
    proper_away := inferInstance }
  refine ⟨{ toJZeroNeronIdentityComponent := N, goodPrime := ?_ }⟩

  intro ℓ _ hℓ
  let R := ↥(GaloisRep.ratLocalizedAt ℓ)
  let bℓ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let f : pullback N.g bℓ ⟶ Spec (CommRingCat.of R) := pullback.snd N.g bℓ
  haveI hfiso : IsIso f := by
    haveI : IsIso N.g := by change IsIso (𝟙 _); infer_instance
    exact inferInstance
  haveI hsub : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)), Subsingleton (SchemeHomOver t f) :=
    fun T t => subsingleton_schemeHomOver_of_isIso t f
  let L' : RelativeGroupLaw R f := trivialLawOfIsIso R f
  let q' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))
  let pts' : JZero p ≃ SchemeHomOver q' f :=
    { toFun := fun _ => ptIso f q'
      invFun := fun _ => 0
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := fun s => Subsingleton.elim _ _ }
  refine ⟨L', pts', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t x y X Y _ _; exact hom_specZ_ext _ _
  · intro x; exact hom_specZ_ext _ _
  ·
    refine { smooth := inferInstance, proper := inferInstance, connectedFibres := ?_, hasGroupLaw := ⟨L'⟩ }
    intro s
    have hsurj : Function.Surjective f.base := f.surjective
    have hinj : Function.Injective f.base :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso f))).injective
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hsurj s; exact ⟨x, hx⟩
    · exact (Set.subsingleton_singleton.preimage hinj).isPreconnected
  · intro T t x y; exact Subsingleton.elim _ _
  · intro x y; exact Subsingleton.elim _ _
  ·
    intro σ x
    haveI : Mono f := inferInstance
    rw [← cancel_mono f]
    have h1 : (pts' (σ • x)).1 ≫ f = q' := (pts' (σ • x)).2
    have h2 : (pts' x).1 ≫ f = q' := (pts' x).2
    rw [Category.assoc, h1, h2]
    have hστ : (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (algebraMap R (AlgebraicClosure ℚ)) =
        algebraMap R (AlgebraicClosure ℚ) := by
      refine RingHom.ext fun r => ?_
      change σ (algebraMap R (AlgebraicClosure ℚ) r) = algebraMap R (AlgebraicClosure ℚ) r
      have : algebraMap R (AlgebraicClosure ℚ) r = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := rfl
      rw [this, AlgEquiv.commutes]
    change Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ))) =
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hστ]
  ·
    intro A' hA'
    haveI := hC ℓ hℓ A' hA'
    let σA : Spec (CommRingCat.of ↥A') ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (inclLoc ℓ A' hA'))
    let ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A'.subtype) ≫ σA) f :=
      { toFun := fun _ => ptIso f _
        invFun := fun _ => 0
        left_inv := fun x => Subsingleton.elim _ _
        right_inv := fun s => Subsingleton.elim _ _ }
    let ptsSp : JZeroC (ResidueField ↥A') p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A')) ≫ σA) f :=
      { toFun := fun _ => ptIso f _
        invFun := fun _ => 0
        left_inv := fun x => Subsingleton.elim _ _
        right_inv := fun s => Subsingleton.elim _ _ }
    refine ⟨σA, ptsA, ptsSp, ?_, ?_, ?_⟩
    · intro x
      haveI : Mono f := inferInstance
      rw [← cancel_mono f, (ptsA x).2, (pts' x).2]
      have hcomp : A'.subtype.comp (inclLoc ℓ A' hA') = algebraMap R (AlgebraicClosure ℚ) := RingHom.ext fun r => rfl
      change Spec.map (CommRingCat.ofHom A'.subtype) ≫ Spec.map (CommRingCat.ofHom (inclLoc ℓ A' hA')) =
        Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    · intro u v; exact Subsingleton.elim _ _
    · intro _ x
      exact ⟨ptIso f σA, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  ·
    intro t
    refine ⟨⟨𝟙 _, Category.id_comp _⟩, ?_, ?_⟩
    · intro T s x y; exact Subsingleton.elim _ _
    · intro x
      change (ptIso f q').1 = (ptIso f q').1 ≫ 𝟙 _
      rw [Category.comp_id]

end S_ModularCurve_nonempty_jZeroNeronIdentityComponentGood_of_subsingleton
end P2MW
export P2MW.S_ModularCurve_nonempty_jZeroNeronIdentityComponentGood_of_subsingleton (solution)

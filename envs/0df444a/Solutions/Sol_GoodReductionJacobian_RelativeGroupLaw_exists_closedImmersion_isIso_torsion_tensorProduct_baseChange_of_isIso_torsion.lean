-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6ee2772c-4e4b-5bb8-ac5a-9c8f8d778ead

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

namespace PDivBCAux

open GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw NeronModelInfra

universe u

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem baseChangePointToBase_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (baseChangeStr σ f)) :
    baseChangePointToBase σ ((L.baseChange σ).nsmul t' n x) = L.nsmul _ n (baseChangePointToBase σ x) := by
  induction n with
  | zero => exact baseChangePointToBase_one σ L t'
  | succ n ih => rw [nsmul_succ, nsmul_succ, baseChangePointToBase_mul, ih]

theorem baseChange_schemeNsmul_fst (n : ℕ) :
    (L.baseChange σ).schemeNsmul n ≫ pullback.fst f σ = pullback.fst f σ ≫ L.schemeNsmul n := by
  have h1 := congrArg Subtype.val (baseChangePointToBase_nsmul σ L (baseChangeStr σ f) n idPoint)
  rw [baseChangePointToBase_coe] at h1
  have h2 := congrArg Subtype.val
    (L.nsmul_natural f (pullback.snd f σ ≫ σ) (pullback.fst f σ) pullback.condition n idPoint)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
  have h3 : schemeHomOverComp (pullback.fst f σ) pullback.condition (idPoint (f := f)) =
      baseChangePointToBase σ (idPoint (f := baseChangeStr σ f)) := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, baseChangePointToBase_coe, Category.comp_id, Category.id_comp]
  rw [h3] at h2
  exact h1.trans h2.symm

theorem baseChange_schemeNsmul_snd (n : ℕ) :
    (L.baseChange σ).schemeNsmul n ≫ pullback.snd f σ = pullback.snd f σ :=
  (L.baseChange σ).schemeNsmul_over n

theorem baseChange_one_fst :
    ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1 ≫ pullback.fst f σ =
      σ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h1 := congrArg Subtype.val (baseChangePointToBase_one σ L (𝟙 (Spec (CommRingCat.of R'))))
  rw [baseChangePointToBase_coe] at h1
  have h2 := congrArg Subtype.val
    (L.one_natural (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R')) ≫ σ) σ
      (by rw [Category.comp_id, Category.id_comp]))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
  exact h1.trans h2.symm

theorem baseChange_one_snd :
    ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1 ≫ pullback.snd f σ = 𝟙 _ :=
  ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).2

end PDivBCAux

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {R : Type} [CommRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (p h : ℕ) [Fact p.Prime] (G : PDivisibleGroup R p h)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J)

    (hS1 : ∀ v : ℕ, ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))))

    (hS2 : ∀ v : ℕ, IsClosedImmersion (ι v))

    (hS5 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R B))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

    (hS6 : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (G.transition v : G.level (v + 1) →+* G.level v)) ≫ ι (v + 1) = ι v)

    (hS8 : ∀ (v : ℕ), ∃ h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1,
      IsIso (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1) (ι v) (ι v ≫ f) h3))

    (R' : Type) [CommRing R'] [Nontrivial R'] [Algebra R R'] :
    let σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R R'))

    ∃ ι' : ∀ v : ℕ, Spec (CommRingCat.of ((G.baseChange R').level v)) ⟶ pullback f σ,

      (∀ v : ℕ, ι' v ≫ pullback.snd f σ = Spec.map (CommRingCat.ofHom (algebraMap R' ((G.baseChange R').level v)))) ∧
      (∀ v : ℕ, ι' v ≫ pullback.fst f σ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* (G.baseChange R').level v)) ≫ ι v) ∧

      (∀ v : ℕ, IsClosedImmersion (ι' v)) ∧

      (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (x y : (G.baseChange R').Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v =
          ((L.baseChange σ).mul (Spec.map (CommRingCat.ofHom (algebraMap R' B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

      (∀ v : ℕ, Spec.map (CommRingCat.ofHom
          ((G.baseChange R').transition v : (G.baseChange R').level (v + 1) →+* (G.baseChange R').level v)) ≫ ι' (v + 1) = ι' v) ∧

      (∀ (v : ℕ), ∃ h3 : ι' v ≫ (L.baseChange σ).schemeNsmul (p ^ v) =
            (ι' v ≫ pullback.snd f σ) ≫ ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1,
        IsIso (pullback.lift (f := (L.baseChange σ).schemeNsmul (p ^ v)) (g := ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1)
          (ι' v) (ι' v ≫ pullback.snd f σ) h3)) ∧

      (∀ (E : NeronModelInfra.SchemeHomOver (pullback.snd f σ) (pullback.snd f σ)),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R')) (x y : NeronModelInfra.SchemeHomOver s (pullback.snd f σ)),
          NeronModelInfra.schemeHomOverComp ((L.baseChange σ).mul s x y) E =
            (L.baseChange σ).mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        ∃ ψ : ∀ v : ℕ, (G.baseChange R').level v →ₐc[R'] (G.baseChange R').level v,
          (∀ v : ℕ, ((G.baseChange R').transition v).comp (ψ (v + 1)) = (ψ v).comp ((G.baseChange R').transition v)) ∧
          ∀ v : ℕ, Spec.map (CommRingCat.ofHom (ψ v : (G.baseChange R').level v →+* (G.baseChange R').level v)) ≫ ι' v = ι' v ≫ E.1) := by
  intro σ
  haveI : Nontrivial R := (algebraMap R R').domain_nontrivial
  suffices big :
    ∃ ι' : ∀ v : ℕ, Spec (CommRingCat.of (R' ⊗[R] G.level v)) ⟶ pullback f σ,
      (∀ v : ℕ, ι' v ≫ pullback.snd f σ = Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] G.level v)))) ∧
      (∀ v : ℕ, ι' v ≫ pullback.fst f σ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)) ≫ ι v) ∧
      (∀ v : ℕ, IsClosedImmersion (ι' v)) ∧
      (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (x y : WithConv (R' ⊗[R] G.level v →ₐ[R'] B))
        (hx : (Spec.map (CommRingCat.ofHom ((WithConv.ofConv x : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' B)))
        (hy : (Spec.map (CommRingCat.ofHom ((WithConv.ofConv y : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' B))),
        Spec.map (CommRingCat.ofHom ((WithConv.ofConv (x * y) : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫ ι' v =
          ((L.baseChange σ).mul (Spec.map (CommRingCat.ofHom (algebraMap R' B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom
          (Bialgebra.TensorProduct.map (BialgHom.id R' R') (G.transition v) : R' ⊗[R] G.level (v + 1) →+* R' ⊗[R] G.level v)) ≫ ι' (v + 1) = ι' v) ∧
      (∀ (v : ℕ), ∃ h3 : ι' v ≫ (L.baseChange σ).schemeNsmul (p ^ v) =
            (ι' v ≫ pullback.snd f σ) ≫ ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1,
        IsIso (pullback.lift (f := (L.baseChange σ).schemeNsmul (p ^ v)) (g := ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1)
          (ι' v) (ι' v ≫ pullback.snd f σ) h3)) ∧
      (∀ (E : NeronModelInfra.SchemeHomOver (pullback.snd f σ) (pullback.snd f σ)),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R')) (x y : NeronModelInfra.SchemeHomOver s (pullback.snd f σ)),
          NeronModelInfra.schemeHomOverComp ((L.baseChange σ).mul s x y) E =
            (L.baseChange σ).mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        ∃ ψ : ∀ v : ℕ, R' ⊗[R] G.level v →ₐc[R'] R' ⊗[R] G.level v,
          (∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id R' R') (G.transition v)).comp (ψ (v + 1)) = (ψ v).comp (Bialgebra.TensorProduct.map (BialgHom.id R' R') (G.transition v))) ∧
          ∀ v : ℕ, Spec.map (CommRingCat.ofHom (ψ v : R' ⊗[R] G.level v →+* R' ⊗[R] G.level v)) ≫ ι' v = ι' v ≫ E.1) by
    exact big

  have hsq : ∀ v : ℕ, (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v).comp
      (algebraMap R (G.level v)) = (algebraMap R' (R' ⊗[R] G.level v)).comp (algebraMap R R') := by
    intro v
    ext r
    exact ((Algebra.TensorProduct.includeRight (R := R) (A := R') (B := G.level v)).commutes r).trans
      (IsScalarTower.algebraMap_apply R R' _ r)
  let ι' : ∀ v : ℕ, Spec (CommRingCat.of (R' ⊗[R] G.level v)) ⟶ pullback f σ := fun v =>
    pullback.lift (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        G.level v →+* R' ⊗[R] G.level v)) ≫ ι v)
      (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] G.level v))))
      (by rw [Category.assoc, hS1, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← CommRingCat.ofHom_comp, hsq])
  have hι'snd : ∀ v, ι' v ≫ pullback.snd f σ = Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] G.level v))) :=
    fun v => pullback.lift_snd _ _ _
  have hι'fst : ∀ v, ι' v ≫ pullback.fst f σ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)) ≫
        ι v := fun v => pullback.lift_fst _ _ _

  have hpb : ∀ v, IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)))
      (ι' v) (ι v) (pullback.fst f σ) := by
    intro v
    have big : IsPullback
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)))
        (ι' v ≫ pullback.snd f σ) (ι v ≫ f) σ := by
      rw [hι'snd, hS1]
      exact (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' (G.level v))).flip
    exact big.of_bot (hι'fst v).symm (IsPullback.of_hasPullback f σ)

  have h3' : ∀ v, ι' v ≫ (L.baseChange σ).schemeNsmul (p ^ v) =
      (ι' v ≫ pullback.snd f σ) ≫ ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1 := by
    intro v
    obtain ⟨h3, -⟩ := hS8 v
    apply pullback.hom_ext
    · have eL : (ι' v ≫ (L.baseChange σ).schemeNsmul (p ^ v)) ≫ pullback.fst f σ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
        rw [Category.assoc, PDivBCAux.baseChange_schemeNsmul_fst, ← Category.assoc, hι'fst, Category.assoc, h3, hS1]
      have eR : ((ι' v ≫ pullback.snd f σ) ≫ ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1) ≫
            pullback.fst f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] G.level v))) ≫ σ ≫
            (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
        rw [Category.assoc, PDivBCAux.baseChange_one_fst, hι'snd]
      rw [eL, eR, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, hsq]
    · rw [Category.assoc, PDivBCAux.baseChange_schemeNsmul_snd, Category.assoc, PDivBCAux.baseChange_one_snd,
        Category.comp_id]
  have S' : ∀ v, IsPullback (ι' v) (ι' v ≫ pullback.snd f σ) ((L.baseChange σ).schemeNsmul (p ^ v))
      ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1 := by
    intro v
    obtain ⟨h3, hiso⟩ := hS8 v
    have S : IsPullback (ι v) (ι v ≫ f) (L.schemeNsmul (p ^ v)) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
      IsPullback.of_iso_pullback ⟨h3⟩ (asIso (pullback.lift (ι v) (ι v ≫ f) h3)) (pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _)
    have T : IsPullback
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)))
        (ι' v ≫ pullback.snd f σ) (ι v ≫ f) σ := by
      rw [hι'snd, hS1]
      exact (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' (G.level v))).flip
    have C : IsPullback (pullback.fst f σ) (pullback.snd f σ) f σ := IsPullback.of_hasPullback f σ
    have B : IsPullback (pullback.fst f σ) ((L.baseChange σ).schemeNsmul (p ^ v)) (L.schemeNsmul (p ^ v))
        (pullback.fst f σ) := by
      refine IsPullback.of_bot ?_ (PDivBCAux.baseChange_schemeNsmul_fst σ L (p ^ v)).symm C
      rw [PDivBCAux.baseChange_schemeNsmul_snd, L.schemeNsmul_over]
      exact C
    have E := T.paste_horiz S
    refine IsPullback.of_right ?_ (h3' v) B
    rw [hι'fst, PDivBCAux.baseChange_one_fst]
    exact E
  let tr : ∀ v : ℕ, R' ⊗[R] G.level (v + 1) →+* R' ⊗[R] G.level v := fun v =>
    (Bialgebra.TensorProduct.map (BialgHom.id R' R') (G.transition v) : R' ⊗[R] G.level (v + 1) →+* R' ⊗[R] G.level v)
  have hS6' : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (tr v)) ≫ ι' (v + 1) = ι' v := by
    intro v
    apply pullback.hom_ext
    · rw [Category.assoc, hι'fst, hι'fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hring : (tr v).comp
          (Algebra.TensorProduct.includeRight.toRingHom : G.level (v + 1) →+* R' ⊗[R] G.level (v + 1)) =
          (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v).comp
            (G.transition v : G.level (v + 1) →+* G.level v) := by
        ext a
        rfl
      rw [hring, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hS6]
    · rw [Category.assoc, hι'snd, hι'snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      exact AlgHomClass.commutes (Bialgebra.TensorProduct.map (BialgHom.id R' R') (G.transition v)) r

  have mul_coe_eq : ∀ {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
      (X Y : NeronModelInfra.SchemeHomOver t f) (X' Y' : NeronModelInfra.SchemeHomOver t' f),
      X.1 = X'.1 → Y.1 = Y'.1 → (L.mul t X Y).1 = (L.mul t' X' Y').1 := by
    intro T t t' ht X Y X' Y' hX hY
    subst ht
    cases Subtype.ext hX
    cases Subtype.ext hY
    rfl

  have hS5' : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (x y : WithConv (R' ⊗[R] G.level v →ₐ[R'] B))
      (hx : (Spec.map (CommRingCat.ofHom ((WithConv.ofConv x : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
        Spec.map (CommRingCat.ofHom (algebraMap R' B)))
      (hy : (Spec.map (CommRingCat.ofHom ((WithConv.ofConv y : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
        Spec.map (CommRingCat.ofHom (algebraMap R' B))),
      Spec.map (CommRingCat.ofHom ((WithConv.ofConv (x * y) : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫ ι' v =
        ((L.baseChange σ).mul (Spec.map (CommRingCat.ofHom (algebraMap R' B))) ⟨_, hx⟩ ⟨_, hy⟩).1 := by
    intro v B _ _ x y hx hy
    letI : Algebra R B := ((algebraMap R' B).comp (algebraMap R R')).toAlgebra
    haveI : IsScalarTower R R' B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

    let res : WithConv (R' ⊗[R] G.level v →ₐ[R'] B) → G.Point B v := fun z =>
      PDivisibleGroup.Point.ofAlgHom
        { toRingHom := ((WithConv.ofConv z : R' ⊗[R] G.level v →ₐ[R'] B) :
              R' ⊗[R] G.level v →+* B).comp
            (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)
          commutes' := fun r => by
            change WithConv.ofConv z
                ((Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)
                  (algebraMap R (G.level v) r)) = algebraMap R' B (algebraMap R R' r)
            rw [show (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)
                (algebraMap R (G.level v) r) = algebraMap R' (R' ⊗[R] G.level v) (algebraMap R R' r) from
              RingHom.congr_fun (hsq v) r]
            exact AlgHomClass.commutes (WithConv.ofConv z) _ }
    have res_apply : ∀ (z : WithConv (R' ⊗[R] G.level v →ₐ[R'] B)) (a : G.level v), PDivisibleGroup.Point.toAlgHom (res z) a =
        WithConv.ofConv z ((1 : R') ⊗ₜ[R] a) := fun z a => rfl
    have hres_spec : ∀ z, Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (res z) : G.level v →ₐ[R] B) :
          G.level v →+* B)) =
        Spec.map (CommRingCat.ofHom ((WithConv.ofConv z : R' ⊗[R] G.level v →ₐ[R'] B) :
          R' ⊗[R] G.level v →+* B)) ≫
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* R' ⊗[R] G.level v)) := by
      intro z
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl

    have res_mul : ∀ z w, res (z * w) = res z * res w := by
      intro z w
      apply PDivisibleGroup.Point.ext
      intro a
      rw [res_apply, PDivisibleGroup.Point.mul_apply]
      change (z * w) ((1 : R') ⊗ₜ[R] a) = _
      rw [AlgHom.convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
      rw [← (Coalgebra.Repr.arbitrary R a).eq, TensorProduct.tmul_sum, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
        Algebra.TensorProduct.lift_tmul]
      rfl

    have hσB : Spec.map (CommRingCat.ofHom (algebraMap R' B)) ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hres_over : ∀ z, (Spec.map (CommRingCat.ofHom ((WithConv.ofConv z :
          R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
        Spec.map (CommRingCat.ofHom (algebraMap R' B)) →
        (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (res z) : G.level v →ₐ[R] B) :
          G.level v →+* B)) ≫ ι v) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      intro z hz
      have e1 : Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (res z) : G.level v →ₐ[R] B) :
            G.level v →+* B)) ≫ ι v ≫ f =
          ((Spec.map (CommRingCat.ofHom ((WithConv.ofConv z : R' ⊗[R] G.level v →ₐ[R'] B) :
            R' ⊗[R] G.level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ) ≫ σ := by
        rw [hres_spec, Category.assoc, ← Category.assoc _ (ι v) f]
        erw [← hι'fst]
        rw [Category.assoc, pullback.condition]
        simp only [Category.assoc]
      rw [Category.assoc, e1, hz]
      exact hσB
    have h5 := hS5 v B (res x) (res y) (hres_over x hx) (hres_over y hy)
    apply pullback.hom_ext
    ·
      rw [Category.assoc]
      erw [hι'fst]
      rw [← Category.assoc]
      erw [← hres_spec (x * y)]
      rw [res_mul, h5, GoodReductionJacobian.RelativeGroupLaw.baseChange_mul, GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      refine mul_coe_eq hσB.symm _ _ _ _ ?_ ?_
      · rw [GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc]
        erw [hι'fst]
        rw [← Category.assoc]
        erw [← hres_spec x]
      · rw [GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc]
        erw [hι'fst]
        rw [← Category.assoc]
        erw [← hres_spec y]
    · rw [Category.assoc]
      erw [hι'snd]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [((L.baseChange σ).mul (Spec.map (CommRingCat.ofHom (algebraMap R' B))) ⟨_, hx⟩ ⟨_, hy⟩).2]
      congr 2
      ext r
      exact AlgHomClass.commutes (WithConv.ofConv (x * y)) r
  refine ⟨ι', hι'snd, hι'fst, fun v => IsClosedImmersion.isStableUnderBaseChange.of_isPullback (hpb v) (hS2 v),
    hS5', hS6', ?_, ?_⟩
  ·
    intro v
    refine ⟨h3' v, ?_⟩
    have hlift : pullback.lift (ι' v) (ι' v ≫ pullback.snd f σ) (h3' v) = (S' v).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
    convert (inferInstance : IsIso (S' v).isoPullback.hom)
  ·
    intro E hE

    have hEone : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R')),
        NeronModelInfra.schemeHomOverComp ((L.baseChange σ).one s) E = (L.baseChange σ).one s := by
      intro T s
      letI := (L.baseChange σ).pointGroup s
      have h1 : NeronModelInfra.schemeHomOverComp ((L.baseChange σ).one s) E =
          (L.baseChange σ).mul s (NeronModelInfra.schemeHomOverComp ((L.baseChange σ).one s) E)
            (NeronModelInfra.schemeHomOverComp ((L.baseChange σ).one s) E) := by
        conv_lhs => rw [← (L.baseChange σ).one_mul s ((L.baseChange σ).one s)]
        exact hE s _ _

      exact right_eq_mul.mp h1
    have hEnsmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
        (x : NeronModelInfra.SchemeHomOver s (pullback.snd f σ)),
        NeronModelInfra.schemeHomOverComp ((L.baseChange σ).nsmul s n x) E =
          (L.baseChange σ).nsmul s n (NeronModelInfra.schemeHomOverComp x E) := by
      intro T s n x
      induction n with
      | zero => exact hEone s
      | succ n ih => rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, hE, ih]
    have hEsch : ∀ n : ℕ, (L.baseChange σ).schemeNsmul n ≫ E.1 = E.1 ≫ (L.baseChange σ).schemeNsmul n := by
      intro n
      have h1 := congrArg Subtype.val (hEnsmul (pullback.snd f σ) n GoodReductionJacobian.RelativeGroupLaw.idPoint)
      rw [NeronModelInfra.schemeHomOverComp_coe] at h1
      have h2 := congrArg Subtype.val
        ((L.baseChange σ).nsmul_natural (pullback.snd f σ) (pullback.snd f σ) E.1 E.2 n GoodReductionJacobian.RelativeGroupLaw.idPoint)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
      have h3 : NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.RelativeGroupLaw.idPoint (f := pullback.snd f σ)) E =
          GoodReductionJacobian.schemeHomOverComp E.1 E.2 (GoodReductionJacobian.RelativeGroupLaw.idPoint (f := pullback.snd f σ)) := by
        apply Subtype.ext
        rw [NeronModelInfra.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe, Category.comp_id,
          Category.id_comp]
      rw [h3] at h1
      exact h1.trans h2.symm
    have hEunit : ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1 ≫ E.1 =
        ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1 := by
      have := congrArg Subtype.val (hEone (𝟙 (Spec (CommRingCat.of R'))))
      rwa [NeronModelInfra.schemeHomOverComp_coe] at this

    have hw : ∀ v, (ι' v ≫ E.1) ≫ (L.baseChange σ).schemeNsmul (p ^ v) =
        (ι' v ≫ pullback.snd f σ) ≫ ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1 := by
      intro v
      rw [Category.assoc, ← hEsch, ← Category.assoc, h3', Category.assoc, hEunit]
    let e : ∀ v, Spec (CommRingCat.of (R' ⊗[R] G.level v)) ⟶ Spec (CommRingCat.of (R' ⊗[R] G.level v)) := fun v =>
      (S' v).lift (ι' v ≫ E.1) (ι' v ≫ pullback.snd f σ) (hw v)
    have he_fst : ∀ v, e v ≫ ι' v = ι' v ≫ E.1 := fun v => (S' v).lift_fst _ _ _
    have he_snd : ∀ v, e v ≫ Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] G.level v))) =
        Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] G.level v))) := by
      intro v
      rw [← hι'snd]
      exact (S' v).lift_snd _ _ _

    let ψr : ∀ v, R' ⊗[R] G.level v →+* R' ⊗[R] G.level v := fun v => (Spec.preimage (e v)).hom
    have hψr : ∀ v, Spec.map (CommRingCat.ofHom (ψr v)) = e v := fun v => by
      change Spec.map (Spec.preimage (e v)) = e v
      exact Spec.map_preimage (e v)
    have hψr_alg : ∀ v r, ψr v (algebraMap R' (R' ⊗[R] G.level v) r) = algebraMap R' (R' ⊗[R] G.level v) r := by
      intro v r
      have h1 : Spec.map (CommRingCat.ofHom ((ψr v).comp (algebraMap R' (R' ⊗[R] G.level v)))) =
          Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] G.level v))) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hψr, he_snd]
      have h2 := Spec.map_injective h1
      exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h2) r
    let ψa : ∀ v, R' ⊗[R] G.level v →ₐ[R'] R' ⊗[R] G.level v := fun v =>
      { toRingHom := ψr v, commutes' := hψr_alg v }

    have hψa_ι : ∀ v, Spec.map (CommRingCat.ofHom (ψa v : R' ⊗[R] G.level v →+* R' ⊗[R] G.level v)) ≫ ι' v = ι' v ≫ E.1 := by
      intro v
      change Spec.map (CommRingCat.ofHom (ψr v)) ≫ ι' v = ι' v ≫ E.1
      rw [hψr, he_fst]
    have hψr_tr : ∀ v, (tr v).comp (ψr (v + 1)) = (ψr v).comp (tr v) := by
      intro v
      haveI : IsClosedImmersion (ι' (v + 1)) :=
        IsClosedImmersion.isStableUnderBaseChange.of_isPullback (hpb (v + 1)) (hS2 (v + 1))
      have kL : Spec.map (CommRingCat.ofHom ((tr v).comp (ψr (v + 1)))) ≫ ι' (v + 1) = ι' v ≫ E.1 := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψr, he_fst, ← Category.assoc, hS6']
      have kR : Spec.map (CommRingCat.ofHom ((ψr v).comp (tr v))) ≫ ι' (v + 1) = ι' v ≫ E.1 := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hS6', hψr, he_fst]
      have key := kL.trans kR.symm
      have := Spec.map_injective ((cancel_mono (ι' (v + 1))).1 key)
      exact congrArg CommRingCat.Hom.hom this

    have hXpt : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (χ : WithConv (R' ⊗[R] G.level v →ₐ[R'] B)),
        (Spec.map (CommRingCat.ofHom ((WithConv.ofConv χ : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫
          ι' v) ≫ pullback.snd f σ = Spec.map (CommRingCat.ofHom (algebraMap R' B)) := by
      intro v B _ _ χ
      rw [Category.assoc, hι'snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      exact AlgHomClass.commutes (WithConv.ofConv χ) r
    let Xpt : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (χ : WithConv (R' ⊗[R] G.level v →ₐ[R'] B)),
        NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R' B))) (pullback.snd f σ) :=
      fun v B _ _ χ => ⟨_, hXpt v B χ⟩

    let prec : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B],
        WithConv (R' ⊗[R] G.level v →ₐ[R'] B) → WithConv (R' ⊗[R] G.level v →ₐ[R'] B) :=
      fun v B _ _ χ => WithConv.toConv ((WithConv.ofConv χ).comp (ψa v))
    have hT1 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (χ : WithConv (R' ⊗[R] G.level v →ₐ[R'] B)),
        NeronModelInfra.schemeHomOverComp (Xpt v B χ) E = Xpt v B (prec v B χ) := by
      intro v B _ _ χ
      apply Subtype.ext
      rw [NeronModelInfra.schemeHomOverComp_coe]
      change (Spec.map (CommRingCat.ofHom ((WithConv.ofConv χ : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B)) ≫
          ι' v) ≫ E.1 =
        Spec.map (CommRingCat.ofHom (((WithConv.ofConv χ : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B).comp
          (ψr v))) ≫ ι' v
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, hψr, he_fst]
    have hT2 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (χ₁ χ₂ : WithConv (R' ⊗[R] G.level v →ₐ[R'] B)),
        (L.baseChange σ).mul _ (Xpt v B χ₁) (Xpt v B χ₂) = Xpt v B (χ₁ * χ₂) := by
      intro v B _ _ χ₁ χ₂
      apply Subtype.ext
      exact (hS5' v B χ₁ χ₂ (hXpt v B χ₁) (hXpt v B χ₂)).symm

    have hkey : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (χ₁ χ₂ : WithConv (R' ⊗[R] G.level v →ₐ[R'] B)),
        ((WithConv.ofConv (prec v B (χ₁ * χ₂)) : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B) =
          ((WithConv.ofConv (prec v B χ₁ * prec v B χ₂) : R' ⊗[R] G.level v →ₐ[R'] B) : R' ⊗[R] G.level v →+* B) := by
      intro v B _ _ χ₁ χ₂
      haveI : IsClosedImmersion (ι' v) := IsClosedImmersion.isStableUnderBaseChange.of_isPullback (hpb v) (hS2 v)
      have h1 := hE _ (Xpt v B χ₁) (Xpt v B χ₂)
      rw [hT2, hT1, hT1, hT1, hT2] at h1
      have h2 := congrArg Subtype.val h1
      change Spec.map _ ≫ ι' v = Spec.map _ ≫ ι' v at h2
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (ι' v)).1 h2))

    have hmulψ : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (χ₁ χ₂ : WithConv (R' ⊗[R] G.level v →ₐ[R'] B))
        (a : R' ⊗[R] G.level v),
        Algebra.TensorProduct.lift (WithConv.ofConv χ₁) (WithConv.ofConv χ₂) (fun _ _ => .all _ _)
            (Coalgebra.comul (R := R') (ψa v a)) =
          Algebra.TensorProduct.lift ((WithConv.ofConv χ₁).comp (ψa v)) ((WithConv.ofConv χ₂).comp (ψa v))
            (fun _ _ => .all _ _) (Coalgebra.comul (R := R') a) := by
      intro v B _ _ χ₁ χ₂ a
      have hk : (χ₁ * χ₂) (ψa v a) = (prec v B χ₁ * prec v B χ₂) a := RingHom.congr_fun (hkey v B χ₁ χ₂) a
      rw [AlgHom.convMul_apply, AlgHom.convMul_apply] at hk
      exact hk
    have hcomul : ∀ v, (Algebra.TensorProduct.map (ψa v) (ψa v)).comp (Bialgebra.comulAlgHom R' (R' ⊗[R] G.level v)) =
        (Bialgebra.comulAlgHom R' (R' ⊗[R] G.level v)).comp (ψa v) := by
      intro v
      apply AlgHom.ext
      intro a
      have hk := hmulψ v ((R' ⊗[R] G.level v) ⊗[R'] (R' ⊗[R] G.level v))
        (WithConv.toConv (Algebra.TensorProduct.includeLeft (S := R')))
        (WithConv.toConv (Algebra.TensorProduct.includeRight (R := R') (A := R' ⊗[R] G.level v)
          (B := R' ⊗[R] G.level v))) a
      rw [Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply] at hk
      change Algebra.TensorProduct.map (ψa v) (ψa v) (Coalgebra.comul (R := R') a) = Coalgebra.comul (R := R') (ψa v a)
      rw [hk, ← (Coalgebra.Repr.arbitrary R' a).eq, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.comp_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]

    have hcounit : ∀ v, (Bialgebra.counitAlgHom R' (R' ⊗[R] G.level v)).comp (ψa v) =
        Bialgebra.counitAlgHom R' (R' ⊗[R] G.level v) := by
      intro v
      haveI : IsClosedImmersion (ι' v) := IsClosedImmersion.isStableUnderBaseChange.of_isPullback (hpb v) (hS2 v)

      have hone : Xpt v R' 1 = (L.baseChange σ).one _ := by
        letI := (L.baseChange σ).pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R' R')))
        have h1 : Xpt v R' 1 = Xpt v R' 1 * Xpt v R' 1 := by
          change Xpt v R' 1 = (L.baseChange σ).mul _ (Xpt v R' 1) (Xpt v R' 1)
          rw [hT2, _root_.mul_one]
        exact right_eq_mul.mp h1
      have h2 := hEone (Spec.map (CommRingCat.ofHom (algebraMap R' R')))
      rw [← hone, hT1] at h2
      have h3 := congrArg Subtype.val h2
      change Spec.map _ ≫ ι' v = Spec.map _ ≫ ι' v at h3
      have h4 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (ι' v)).1 h3))
      apply AlgHom.ext
      intro a
      have h5 := RingHom.congr_fun h4 a
      change (WithConv.ofConv (1 : WithConv (R' ⊗[R] G.level v →ₐ[R'] R'))) (ψa v a) =
        (WithConv.ofConv (1 : WithConv (R' ⊗[R] G.level v →ₐ[R'] R'))) a at h5
      rw [AlgHom.convOne_apply, AlgHom.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply] at h5
      exact h5
    refine ⟨fun v => BialgHom.ofAlgHom (ψa v) (hcounit v) (hcomul v), fun v => ?_, fun v => hψa_ι v⟩
    apply BialgHom.ext
    intro a
    exact RingHom.congr_fun (hψr_tr v) a

end S_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion (solution)

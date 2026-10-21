-- Prove2me | solution 1 for MazurTransfer.original_relative_point_base_cast_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T02:48:29.973764+00:00
-- url     : https://prove2.me/submissions/fc29bf6e-1c4b-4da0-8b7e-9a6de2a30193

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: change only a proved-equal base arrow of the original relative point, retaining the same underlying scheme map, endomorphism, precomposition and relative group operations.
Named downstream consumer: coefficient-map comparison between the same integral nineteen Hopf points and fixed arithmetic norm-kernel points.
-/
import Definitions.Def_MazurTransfer_OriginalRelativePointBaseCastData20261020
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativePointBaseCast
universe u
namespace MazurTransfer.OriginalRelativePointBaseCastBoundary20261020
end MazurTransfer.OriginalRelativePointBaseCastBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: change only the PROVED-EQUAL base arrow of a relative
point, retaining its underlying scheme map and relative group operations.
Named downstream consumer: canonical coefficient-map comparison between
integral nineteen Hopf points and fixed arithmetic norm-kernel points.
-/

noncomputable section
namespace MazurTransfer.OriginalRelativePointBaseCastProof20261020
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
variable {B A T : Scheme.{u}} {f : A ⟶ B} {t t' : T ⟶ B}



@[simp] theorem pointEquiv_val (h : t = t') (x : SchemeHomOver t f) :
    (pointEquiv h x).val = x.val := rfl

theorem pointEquiv_endomorphism (h : t = t') (F : SchemeHomOver f f)
    (x : SchemeHomOver t f) :
    pointEquiv h (NeronModelInfra.schemeHomOverComp x F) =
      NeronModelInfra.schemeHomOverComp (pointEquiv h x) F := Subtype.ext rfl

theorem pointEquiv_precomp {T' : Scheme.{u}} {s s' : T' ⟶ B}
    (h : t = t') (hs : s = s') (ψ : T' ⟶ T) (hψ : ψ ≫ t = s) (hψ' : ψ ≫ t' = s')
    (x : SchemeHomOver t f) :
    pointEquiv hs (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ' (pointEquiv h x) := Subtype.ext rfl

variable {R : Type u} [CommRing R] {A T : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
variable {t t' : T ⟶ Spec (CommRingCat.of R)}

theorem pointEquiv_one (h : t = t') : pointEquiv h (L.one t) = L.one t' := by
  subst h
  rfl

theorem pointEquiv_mul (h : t = t') (x y : SchemeHomOver t f) :
    pointEquiv h (L.mul t x y) = L.mul t' (pointEquiv h x) (pointEquiv h y) := by
  subst h
  rfl

end MazurTransfer.OriginalRelativePointBaseCastProof20261020

theorem solution : (∀ {B A T : Scheme.{u}} {f : A ⟶ B} {t t' : T ⟶ B}, ∀ (h : t = t') (x : SchemeHomOver t f),
(pointEquiv h x).val = x.val) ∧ (∀ {B A T : Scheme.{u}} {f : A ⟶ B} {t t' : T ⟶ B}, ∀ (h : t = t') (F : SchemeHomOver f f)
    (x : SchemeHomOver t f),
pointEquiv h (NeronModelInfra.schemeHomOverComp x F) =
      NeronModelInfra.schemeHomOverComp (pointEquiv h x) F) ∧ (∀ {B A T : Scheme.{u}} {f : A ⟶ B} {t t' : T ⟶ B}, ∀ {T' : Scheme.{u}} {s s' : T' ⟶ B}
    (h : t = t') (hs : s = s') (ψ : T' ⟶ T) (hψ : ψ ≫ t = s) (hψ' : ψ ≫ t' = s')
    (x : SchemeHomOver t f),
pointEquiv hs (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ' (pointEquiv h x)) ∧ (∀ {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {t t' : T ⟶ Spec (CommRingCat.of R)}, ∀ (h : t = t'),
pointEquiv h (L.one t) = L.one t') ∧ (∀ {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {t t' : T ⟶ Spec (CommRingCat.of R)}, ∀ (h : t = t') (x y : SchemeHomOver t f),
pointEquiv h (L.mul t x y) = L.mul t' (pointEquiv h x) (pointEquiv h y)) := by
  exact ⟨MazurTransfer.OriginalRelativePointBaseCastProof20261020.pointEquiv_val, MazurTransfer.OriginalRelativePointBaseCastProof20261020.pointEquiv_endomorphism, MazurTransfer.OriginalRelativePointBaseCastProof20261020.pointEquiv_precomp, MazurTransfer.OriginalRelativePointBaseCastProof20261020.pointEquiv_one, MazurTransfer.OriginalRelativePointBaseCastProof20261020.pointEquiv_mul⟩
#print axioms solution

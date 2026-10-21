-- Prove2me | solution 1 for MazurTransfer.original_relative_norm_preimage_point_torsor_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T00:59:58.273144+00:00
-- url     : https://prove2.me/submissions/fd61523d-6bd1-4388-9adf-1fe50fa85d04

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original point functor of a given relative endomorphism preimage has its natural kernel action, difference and principal-action equivalence over every test scheme.
Named downstream consumer: the same integral nineteen norm-preimage torsor and its selected mu19 quotient.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimagePointTorsorData20261020
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf MazurTransfer.RelativeNormPreimagePointTorsor
universe u
namespace MazurTransfer.OriginalRelativeNormPreimagePointTorsorBoundary20261020
end MazurTransfer.OriginalRelativeNormPreimagePointTorsorBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL endomorphism preimage point functor has its
natural kernel action and principal-action equivalence over EVERY test
scheme. No point over every test scheme is assumed.
Named downstream consumer: the actual integral nineteen norm-preimage
fppf torsor and its previously selected normalized mu19 quotient.
-/

noncomputable section
namespace MazurTransfer.OriginalRelativeNormPreimagePointTorsorProof20261020
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLawFiniteFlatKernelHopf
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) (F : SchemeHomOver f f)
variable (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
  NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t)
variable (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
  NeronModelInfra.schemeHomOverComp (L.mul t x y) F =
    L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F))















include hOne hMul in
theorem difference_cocycle {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a : SchemeHomOver t f}
    (x y z : preimagePoints F a) :
    (difference L F hOne hMul x z).val =
      L.mul t (difference L F hOne hMul x y).val (difference L F hOne hMul y z).val := by
  letI := L.pointGroup t
  change x.val * z.val⁻¹ = (x.val * y.val⁻¹) * (y.val * z.val⁻¹)
  simp [mul_assoc]

variable {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
variable {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')





include hMul in
theorem act_natural {a : SchemeHomOver t f} (k : kernelPoints L F t) (y : preimagePoints F a) :
    precomposePreimage F ψ hψ (act L F hMul k y) =
      act L F hMul (precomposeKernel L F ψ hψ k) (precomposePreimage F ψ hψ y) :=
  Subtype.ext (L.mul_natural t t' ψ hψ k.val y.val)

include hOne hMul in
theorem difference_natural {a : SchemeHomOver t f} (x y : preimagePoints F a) :
    precomposeKernel L F ψ hψ (difference L F hOne hMul x y) =
      difference L F hOne hMul (precomposePreimage F ψ hψ x) (precomposePreimage F ψ hψ y) := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  let pull : SchemeHomOver t f →* SchemeHomOver t' f :=
    { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
      map_one' := L.one_natural t t' ψ hψ
      map_mul' := L.mul_natural t t' ψ hψ }
  apply Subtype.ext
  change pull (x.val * y.val⁻¹) = pull x.val * (pull y.val)⁻¹
  rw [map_mul, map_inv]

end MazurTransfer.OriginalRelativeNormPreimagePointTorsorProof20261020

theorem solution : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) , ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a : SchemeHomOver t f}
    (x y z : preimagePoints F a),
(difference L F hOne hMul x z).val =
      L.mul t (difference L F hOne hMul x y).val (difference L F hOne hMul y z).val) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) , ∀ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'), ∀ {a : SchemeHomOver t f} (k : kernelPoints L F t) (y : preimagePoints F a),
precomposePreimage F ψ hψ (act L F hMul k y) =
      act L F hMul (precomposeKernel L F ψ hψ k) (precomposePreimage F ψ hψ y)) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) , ∀ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'), ∀ {a : SchemeHomOver t f} (x y : preimagePoints F a),
precomposeKernel L F ψ hψ (difference L F hOne hMul x y) =
      difference L F hOne hMul (precomposePreimage F ψ hψ x) (precomposePreimage F ψ hψ y)) := by
  exact ⟨MazurTransfer.OriginalRelativeNormPreimagePointTorsorProof20261020.difference_cocycle, MazurTransfer.OriginalRelativeNormPreimagePointTorsorProof20261020.act_natural, MazurTransfer.OriginalRelativeNormPreimagePointTorsorProof20261020.difference_natural⟩
#print axioms solution

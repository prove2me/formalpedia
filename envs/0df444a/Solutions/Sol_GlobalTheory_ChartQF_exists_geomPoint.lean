-- Prove2me | solution 1 for GlobalTheory.ChartQF.exists_geomPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:43.052613+00:00
-- url     : https://prove2.me/submissions/4867df6d-58cb-4642-8335-a9343b601032

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF
namespace GlobalTheory.ChartQF
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S) (p : Sp R)
    (hp : ξ p = ξ (closedPoint R)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) K)
      (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ ∧ RingHom.ker ev = p.asIdeal ∧
      (∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap _ K (residue _ a)) ∧
      (∀ x, x ∈ k₀ ↔ IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) x) ∧
      (∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)) ∧ ∃ P₀ : Sp k₀ ⟶ S, spMap k₀.subtype ≫ P₀ = spMap ev ≫ ξ := by
  classical
  haveI : p.asIdeal.IsPrime := p.isPrime
  haveI : IsDomain (R ⧸ p.asIdeal) := Ideal.Quotient.isDomain _

  have hcomap : p.asIdeal.comap (Scheme.stalkClosedPointTo ξ).hom = maximalIdeal (S.presheaf.stalk (ξ (closedPoint R))) := by
    have e2 : S.fromSpecStalk _ (Spec.map (Scheme.stalkClosedPointTo ξ) p) =
        S.fromSpecStalk _ (closedPoint (S.presheaf.stalk (ξ (closedPoint R)))) := by
      rw [Scheme.fromSpecStalk_closedPoint, ← Scheme.Hom.comp_apply,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hp]
    have e3 := (S.fromSpecStalk (ξ (closedPoint R))).isEmbedding.injective e2
    exact congrArg PrimeSpectrum.asIdeal e3

  let ev : R →+* AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)) :=
    (algebraMap (FractionRing (R ⧸ p.asIdeal)) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))).comp ((algebraMap (R ⧸ p.asIdeal) (FractionRing (R ⧸ p.asIdeal))).comp (Ideal.Quotient.mk p.asIdeal))
  have hker0 : ∀ (P : Ideal R) [P.IsPrime],
      RingHom.ker ((algebraMap (FractionRing (R ⧸ P)) (AlgebraicClosure (FractionRing (R ⧸ P)))).comp
        ((algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P))) = P := by
    intro P _
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap (FractionRing (R ⧸ P)) (AlgebraicClosure (FractionRing (R ⧸ P)))).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker ev = p.asIdeal := hker0 p.asIdeal
  have hev0 : ∀ a ∈ maximalIdeal (S.presheaf.stalk (ξ (closedPoint R))), (ev.comp (Scheme.stalkClosedPointTo ξ).hom) a = 0 := fun a ha => by
    rw [← hcomap] at ha
    show ev ((Scheme.stalkClosedPointTo ξ).hom a) = 0
    rw [← RingHom.mem_ker, hker]
    exact ha
  let ψ : ResidueField (S.presheaf.stalk (ξ (closedPoint R))) →+* AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)) := Ideal.Quotient.lift (maximalIdeal (S.presheaf.stalk (ξ (closedPoint R)))) (ev.comp (Scheme.stalkClosedPointTo ξ).hom) hev0
  letI alg : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) := ψ.toAlgebra
  let k₀ : Subfield (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) := (algebraicClosure (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))).toSubfield
  have hmem : ∀ x, x ∈ k₀ ↔ IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) x := fun x => mem_algebraicClosure_iff
  have hev : ∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal))) (residue (S.presheaf.stalk (ξ (closedPoint R))) a) := fun a => rfl
  have hk₀ : IsAlgClosed (algebraicClosure (ResidueField (S.presheaf.stalk (ξ (closedPoint R))))
      (AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)))) :=
    IsAlgClosure.isAlgClosed (ResidueField (S.presheaf.stalk (ξ (closedPoint R))))

  have hpts : ∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R) := by
    intro q
    haveI : q.asIdeal.IsPrime := q.isPrime
    rw [Scheme.Hom.comp_apply, ← hp]
    congr 1
    apply PrimeSpectrum.ext
    show Ideal.comap ev q.asIdeal = p.asIdeal
    rw [Ideal.eq_bot_of_prime q.asIdeal, ← RingHom.ker_eq_comap_bot, hker]

  have hψ₀ : ∀ a, (ev.comp (Scheme.stalkClosedPointTo ξ).hom) a ∈ k₀ := fun a =>
    (hmem _).mpr (by rw [RingHom.comp_apply, hev]; exact isAlgebraic_algebraMap _)
  let ψ₀ : S.presheaf.stalk (ξ (closedPoint R)) →+* k₀ := (ev.comp (Scheme.stalkClosedPointTo ξ).hom).codRestrict k₀ hψ₀
  have hP₀ : spMap k₀.subtype ≫ (Spec.map (CommRingCat.ofHom ψ₀) ≫ S.fromSpecStalk (ξ (closedPoint R))) =
      spMap ev ≫ ξ := by
    conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  exact ⟨AlgebraicClosure (FractionRing (R ⧸ p.asIdeal)), inferInstance, inferInstance, alg, ev, k₀, hk₀, hker, hev, hmem, hpts, _, hP₀⟩
end GlobalTheory.ChartQF

-- Prove2me | solution 1 for GlobalTheory.exists_algHom_lift_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:06.045986+00:00
-- url     : https://prove2.me/submissions/90d77ce8-d4b4-42b9-99c0-52322f862c14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution {B A : Type*} {R K : Type u} [CommRing B] [CommRing A]
    [CommRing R] [Field K] [Algebra B A] [Algebra B R] [Algebra B K] [Algebra.Etale B A]
    [HenselianLocalRing R] (π : R →ₐ[B] K) (hπ : Function.Surjective π) (φ : A →ₐ[B] K) :
    ∃ ψ : A →ₐ[B] R, π.comp ψ = φ := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨r, hr, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := B) (RingHom.ker φ)
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  let φ' : Localization.Away r →ₐ[B] K :=
    IsLocalization.Away.liftAlgHom r (f := φ) (Ne.isUnit hr)
  have hφ' : φ'.comp (IsScalarTower.toAlgHom B A _) = φ := by
    ext a; simp [φ']
  have hx : P.HasMap (φ' P.x) := P.hasMap.map φ'
  have hc : (π : R →+* K).comp (algebraMap B R) = algebraMap B K := π.comp_algebraMap
  have H := ((HenselianLocalRing.TFAE R).out 0 2).mp ‹HenselianLocalRing R›
  obtain ⟨a, ha, ha'⟩ := H (π : R →+* K) hπ (P.f.map (algebraMap B R)) (P.monic_f.map _) (φ' P.x)
    (by rw [eval₂_map, hc]; exact hx.1)
    (by rw [derivative_map, eval₂_map, hc]; exact hx.isUnit_derivative_f.ne_zero)
  replace ha' : π a = φ' P.x := ha'
  have hloc : IsLocalHom (π : R →+* K) := .of_surjective _ hπ
  have hA : P.HasMap a := by
    refine ⟨by rwa [aeval_def, ← Polynomial.eval_map], ?_⟩
    refine IsUnit.of_map (π : R →+* K) _ ?_
    rw [RingHom.coe_coe, ← aeval_algHom_apply, ha']
    exact hx.2
  refine ⟨((P.lift a hA).comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom B A _), ?_⟩
  rw [← hφ', ← AlgHom.comp_assoc]
  congr 1
  exact P.hom_ext (by simp [ha'])
end GlobalTheory

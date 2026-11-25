-- Prove2me | solution 1 for GlobalTheory.FibreAcyclic.exists_localRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:50.006161+00:00
-- url     : https://prove2.me/submissions/accda5e8-fec8-4476-bbd3-e4af675e87d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem
import Theorems.Thm_GlobalTheory_FibreAcyclic_regular_fibre
import Theorems.Thm_GlobalTheory_powGr_map_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]
omit [IsLocalRing R]
open AlgebraicGeometry
namespace GlobalTheory.FibreAcyclic
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : ℕ) (hf : SmoothOfRelativeDimension g f) {K : Type} [Field K]
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : IsClosed {p (closedPoint K)}) (hc : f (p (closedPoint K)) = closedPoint A) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : Algebra A R)
      (ξ : Spec (CommRingCat.of R) ⟶ X) (g₀ : R →+* K), Module.Flat A R ∧ IsPreimmersion ξ ∧
      ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A R)) ∧ IsLocalHom g₀ ∧
      Spec.map (CommRingCat.ofHom g₀) ≫ ξ = p ∧ IsRegularLocalRing (R ⧸ (maximalIdeal A).map (algebraMap A R)) ∧
      (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
  set x := p (closedPoint K) with hx
  obtain ⟨U, hU, V, hV, hxV, e, hs⟩ := hf.exists_isStandardSmoothOfRelativeDimension x
  obtain rfl : U = ⊤ := (closedPoint_mem_iff U).1 (hc ▸ e hxV)
  let ψ : CommRingCat.of A ⟶ Γ(X, V) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ V e
  letI : Algebra A Γ(X, V) := ψ.hom.toAlgebra
  have hψ : ψ.hom.IsStandardSmoothOfRelativeDimension g :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv hs
  have hss : Algebra.IsStandardSmoothOfRelativeDimension g A Γ(X, V) := hψ
  have : Algebra.IsStandardSmooth A Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hV' : hV.fromSpec ≫ f = Spec.map ψ := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp]
  let R : Type := X.presheaf.stalk x
  letI : Algebra Γ(X, V) R := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hloc : IsLocalization.AtPrime R (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  letI : Algebra A R := ((algebraMap Γ(X, V) R).comp (algebraMap A Γ(X, V))).toAlgebra
  have : IsScalarTower A Γ(X, V) R := IsScalarTower.of_algebraMap_eq' rfl
  have hq := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hp
  have : IsNoetherianRing Γ(X, V) := Algebra.FiniteType.isNoetherianRing A _
  have hm : (maximalIdeal A).map (algebraMap A Γ(X, V)) ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    have h₁ : Spec.map ψ (hV.primeIdealOf ⟨x, hxV⟩) = closedPoint A := by
      rw [← hV']
      exact (congrArg f (hV.fromSpec_primeIdealOf ⟨x, hxV⟩)).trans hc
    exact Ideal.map_le_iff_le_comap.2 (congrArg PrimeSpectrum.asIdeal h₁).ge
  have : Module.Flat Γ(X, V) R := IsLocalization.flat R (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  refine ⟨R, inferInstance, inferInstance,
    IsLocalization.isNoetherianRing (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl R inferInstance, inferInstance,
    X.fromSpecStalk x, (Scheme.stalkClosedPointTo p).hom, Module.Flat.trans A Γ(X, V) R,
    inferInstanceAs (IsPreimmersion (X.fromSpecStalk x)), ?_, inferInstance,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk p, regular_fibre g _ hm⟩
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV, IsAffineOpen.fromSpecStalk, Category.assoc, hV', ← Spec.map_comp]
  rfl
end GlobalTheory.FibreAcyclic

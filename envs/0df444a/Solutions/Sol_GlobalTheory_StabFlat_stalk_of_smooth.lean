-- Prove2me | solution 1 for GlobalTheory.StabFlat.stalk_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:12:26.993463+00:00
-- url     : https://prove2.me/submissions/eee8037c-a981-49c1-9a1b-c856763cdf42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth
import Theorems.Thm_GlobalTheory_StabFlat_localization_of_isStandardSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat
namespace GlobalTheory.StabFlat
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → IsNoetherianRing (X.presheaf.stalk x) ∧ σ ϖ ∈ nonZeroDivisors (X.presheaf.stalk x) ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ Ideal.span {σ ϖ}) ∧ ringKrullDim (X.presheaf.stalk x ⧸ Ideal.span {σ ϖ}) = g := by
  intro V _ _ _ ϖ hϖ X f g hg x hx σ hσ hn
  obtain ⟨U, hU, W, hW, hxW, e, H⟩ := hg.exists_isStandardSmoothOfRelativeDimension x
  have hfx : f x = IsLocalRing.closedPoint V := by
    refine ((congrArg f Scheme.fromSpecStalk_closedPoint.symm).trans
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ)).trans ?_
    refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
      (PrimeSpectrum.isPrime _).ne_top ?_))
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hn
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 (hfx ▸ e hxW)
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ f.appLE ⊤ W e
  have hρ : ρ.hom.IsStandardSmoothOfRelativeDimension g :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).2 H
  have hc : ρ ≫ X.presheaf.germ W x hxW = CommRingCat.ofHom σ := by
    apply Spec.map_injective
    rw [← hσ, ← hW.fromSpecStalk_eq_fromSpecStalk hxW, Spec.map_comp, Spec.map_comp, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hW e, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hl : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  haveI := hW.primeIdealOf_isMaximal_of_isClosed ⟨x, hxW⟩ hx
  have hs : algebraMap Γ(X, W) (X.presheaf.stalk x) (ρ.hom ϖ) = σ ϖ := congrArg (fun q => q.hom ϖ) hc
  haveI : (Ideal.span {ϖ}).IsMaximal := hϖ.maximalIdeal_eq ▸ IsLocalRing.maximalIdeal.isMaximal V
  rw [← hs]
  refine localization_of_isStandardSmooth (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) hρ
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal ?_
  by_contra hm
  exact hn (hs ▸ IsLocalization.map_units (X.presheaf.stalk x)
    (⟨_, hm⟩ : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl))
end GlobalTheory.StabFlat

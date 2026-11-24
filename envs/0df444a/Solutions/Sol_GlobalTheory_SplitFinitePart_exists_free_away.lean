-- Prove2me | solution 1 for GlobalTheory.SplitFinitePart.exists_free_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:48.479928+00:00
-- url     : https://prove2.me/submissions/5ca8932d-6e19-460d-b1ba-335273c1ffcf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart
namespace GlobalTheory.SplitFinitePart
theorem _root_.solution {R : Type} [CommRing R] (f₀ : R) (p : PrimeSpectrum R) (hp : f₀ ∉ p.asIdeal) (B : Type)
    [CommRing B] [Algebra (Localization.Away f₀) B] [Module.Finite (Localization.Away f₀) B]
    [Module.Flat (Localization.Away f₀) B] [Algebra.FinitePresentation (Localization.Away f₀) B] :
    ∃ (f : R) (_ : Algebra (Localization.Away f₀) (Localization.Away f)), f ∉ p.asIdeal ∧
      IsScalarTower R (Localization.Away f₀) (Localization.Away f) ∧
      Module.Free (Localization.Away f) (Localization.Away f ⊗[Localization.Away f₀] B) := by
  set A := Localization.Away f₀
  have := Module.FinitePresentation.of_finite_of_finitePresentation A B
  obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) := by
    rw [PrimeSpectrum.localization_away_comap_range A f₀]; exact hp
  have : Module.Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl B) (Localization.AtPrime q.asIdeal)
  obtain ⟨⟨r', u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers f₀) r
  have hu' : IsUnit (algebraMap R A u) := IsLocalization.map_units A u
  have hass : Associated r (algebraMap R A r') := ⟨hu'.unit, hu⟩
  have hr' : r' ∉ (PrimeSpectrum.comap (algebraMap R A) q).asIdeal := fun h => by
    have h' : algebraMap R A r' ∈ q.asIdeal := h
    rw [← show r * algebraMap R A u = algebraMap R A r' from hu] at h'
    exact (q.isPrime.mem_or_mem h').elim hr fun h'' => q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem h'' hu')
  let T := Localization.Away r
  have : IsLocalization.Away (algebraMap R A r') T := IsLocalization.Away.of_associated hass
  have : IsLocalization.Away (f₀ * r') T := IsLocalization.Away.mul' A T f₀ r'
  let e : T ≃ₐ[R] Localization.Away (f₀ * r') := IsLocalization.algEquiv (Submonoid.powers (f₀ * r')) _ _
  letI : Algebra T (Localization.Away (f₀ * r')) := e.toRingHom.toAlgebra
  letI : Algebra A (Localization.Away (f₀ * r')) := (e.toRingHom.comp (algebraMap A T)).toAlgebra
  have : IsScalarTower A T (Localization.Away (f₀ * r')) := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Free T (T ⊗[A] B) := Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) B)
  refine ⟨f₀ * r', inferInstance, fun h => ((PrimeSpectrum.comap (algebraMap R A) q).isPrime.mem_or_mem h).elim hp hr',
    IsScalarTower.of_algebraMap_eq fun x => ?_, Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A T
      (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r')) B)⟩
  change _ = e (algebraMap A T (algebraMap R A x))
  rw [← IsScalarTower.algebraMap_apply, e.commutes]
end GlobalTheory.SplitFinitePart

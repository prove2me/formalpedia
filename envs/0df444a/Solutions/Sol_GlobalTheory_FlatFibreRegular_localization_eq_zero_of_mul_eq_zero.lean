-- Prove2me | solution 1 for GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:33:40.635248+00:00
-- url     : https://prove2.me/submissions/c9752bda-8953-40c3-a1fd-1c658fee1337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Theorems.Thm_GlobalTheory_FlatFibreRegular_eq_zero_of_mul_eq_zero
import Theorems.Thm_GlobalTheory_FlatFibreRegular_isRadical_map_of_smooth
import Theorems.Thm_GlobalTheory_FlatFibreRegular_mem_of_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular
namespace GlobalTheory.FlatFibreRegular
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro A B _ _ _ _ _ b g u hgb hg
  set 𝔭 := u.asIdeal.comap (algebraMap A B)
  set L := Localization.AtPrime u.asIdeal
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : Module.Flat A L := Module.Flat.trans A B L
  have hmapeq : 𝔭.map (algebraMap A L) = (𝔭.map (algebraMap A B)).map (algebraMap B L) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s) := by
    intro s hs
    rw [IsScalarTower.algebraMap_apply A B L]
    exact IsLocalization.map_units L (⟨algebraMap A B s, hs⟩ : u.asIdeal.primeCompl)
  have hJ : 𝔭.map (algebraMap A L) ≠ ⊤ := by
    rw [hmapeq]
    refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal L).ne_top ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 le_rfl)
  have hg' : ∀ y : L, algebraMap B L g * y ∈ 𝔭.map (algebraMap A L) →
      y ∈ 𝔭.map (algebraMap A L) := by
    intro y hy
    rw [hmapeq] at hy ⊢
    exact mem_of_mul_mem u.asIdeal _ (isRadical_map_of_smooth 𝔭) g hg y hy
  apply eq_zero_of_mul_eq_zero 𝔭 hu hJ (algebraMap B L g) hg'
  rw [← map_mul, hgb, map_zero]
end GlobalTheory.FlatFibreRegular

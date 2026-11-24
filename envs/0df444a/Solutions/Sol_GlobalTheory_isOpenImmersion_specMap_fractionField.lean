-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_specMap_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:05:03.301479+00:00
-- url     : https://prove2.me/submissions/f4d02e91-5a95-4a05-8add-95e0b6b79b79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]
namespace GlobalTheory
theorem _root_.solution :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsLocalization.Away π K := by
    refine IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_)
      (fun a b hab => ⟨0, by simpa using IsFractionRing.injective O K hab⟩)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) s
    obtain ⟨n, v, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, a * (v⁻¹ : Oˣ), ?_⟩
    have h1 : algebraMap O K π ≠ 0 := by simpa using hπ.ne_zero
    have h2 : algebraMap O K v ≠ 0 := by simp
    simp only [map_mul, map_pow, map_units_inv]
    field_simp
  exact IsOpenImmersion.of_isLocalization π
end GlobalTheory

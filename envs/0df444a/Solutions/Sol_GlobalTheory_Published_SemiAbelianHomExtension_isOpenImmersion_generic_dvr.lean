-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.isOpenImmersion_generic_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:34:06.861937+00:00
-- url     : https://prove2.me/submissions/475cc1ba-7fb7-4c13-be6d-773bf1df7e59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
variable (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
  [IsFractionRing T K]
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution : IsOpenImmersion (spMap (algebraMap T K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have : IsLocalization.Away ϖ K := by
    refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, by
      rw [IsFractionRing.injective T K hxy]⟩⟩
    · rintro ⟨_, n, rfl⟩
      exact IsUnit.mk0 _ (by simp [hϖ.ne_zero])
    · obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors T) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
      refine ⟨⟨a * (u⁻¹ : Tˣ), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have hab' : z * algebraMap T K (u * ϖ ^ n) = algebraMap T K a := hu ▸ hab
      change z * algebraMap T K (ϖ ^ n) = algebraMap T K (a * (u⁻¹ : Tˣ))
      rw [map_mul, ← hab', _root_.mul_assoc, ← map_mul, mul_right_comm, Units.mul_inv, _root_.one_mul]
  exact IsOpenImmersion.of_isLocalization ϖ
end GlobalTheory.Published.SemiAbelianHomExtension

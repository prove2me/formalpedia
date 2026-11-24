-- Prove2me | solution 1 for GlobalTheory.NearFibreIso.near_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:23.49593+00:00
-- url     : https://prove2.me/submissions/5681544e-9639-40a2-a1c5-c7401934cd6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.NearFibreIso
open GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
variable (K : Type) [Field K] [Algebra R K]
namespace GlobalTheory.NearFibreIso
theorem _root_.solution [IsProper f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) : Near f @IsFinite x := by
  have hsub : (f ⁻¹' {x}).Subsingleton := by
    let k : Sp K := IsLocalRing.closedPoint K
    have hk : s x = spMap (algebraMap R K) k := by
      apply PrimeSpectrum.ext
      rw [← hx, RingHom.ker_eq_comap_bot, ← Ideal.eq_bot_of_prime k.asIdeal]
      rfl
    obtain ⟨x', hx', -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨z₁, hz₁, hz₁'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₁ x' (hy₁.trans hx'.symm)
    obtain ⟨z₂, hz₂, hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₂ x' (hy₂.trans hx'.symm)
    have hz : z₁ = z₂ :=
      (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))).isOpenEmbedding.injective
        (hz₁'.trans hz₂'.symm)
    rw [← hz₁, ← hz₂, hz]
  obtain ⟨V, hxV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hsub.finite
  refine ⟨V, f ⁻¹ᵁ V, V.ι, (f ⁻¹ᵁ V).ι, f ∣_ V, isPullback_morphismRestrict f V, inferInstance, ?_, hV⟩
  simpa using hxV
end GlobalTheory.NearFibreIso

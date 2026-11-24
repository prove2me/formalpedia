-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.smooth_away_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:42.388548+00:00
-- url     : https://prove2.me/submissions/8a03e84e-e12c-416f-99e9-2c583dd9902b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution {π : R} (h : Algebra.Smooth R (Localization.Away (algebraMap R B π)))
    (φ : B →ₐ[R] C) (hi : Function.Injective φ)
    (hs : ∀ b' : C, ∃ (n : ℕ) (b : B), algebraMap R C π ^ n * b' = φ b) :
    Algebra.Smooth R (Localization.Away (algebraMap R C π)) := by
  letI : Algebra B C := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algHom φ
  have hφ : ∀ b, algebraMap B (Localization.Away (algebraMap R C π)) b = algebraMap C _ (φ b) := fun b => rfl
  haveI : IsLocalization.Away (algebraMap R B π) (Localization.Away (algebraMap R C π)) := by
    refine IsLocalization.Away.mk _ ?_ ?_ ?_
    · rw [hφ, φ.commutes]; exact IsLocalization.Away.algebraMap_isUnit _
    · intro s
      obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R C π) s
      obtain ⟨m, b, hb⟩ := hs c
      refine ⟨n + m, b, ?_⟩
      rw [hφ, hφ, φ.commutes, ← hb, map_mul, map_pow, ← hc]; ring
    · intro a b hab
      rw [hφ, hφ] at hab
      obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap R C π) hab
      refine ⟨n, hi ?_⟩
      simpa using hn
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B π))
    (Localization.Away (algebraMap R B π)) (Localization.Away (algebraMap R C π))).restrictScalars R)
end GlobalTheory.SS.Smoothening

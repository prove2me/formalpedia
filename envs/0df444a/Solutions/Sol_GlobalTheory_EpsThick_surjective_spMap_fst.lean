-- Prove2me | solution 1 for GlobalTheory.EpsThick.surjective_spMap_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:30:00.313783+00:00
-- url     : https://prove2.me/submissions/e954d01a-c829-49e0-b846-7942bd9502be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.EpsThick
variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}
namespace GlobalTheory.EpsThick
theorem _root_.solution : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine ⟨fun x => ?_⟩
  have h : x ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)]
    intro z hz
    have hz' : z.fst = 0 := hz
    refine x.isPrime.mem_of_pow_mem 2 ?_
    have : z ^ 2 = 0 := by
      ext <;> simp [pow_two, hz']
    rw [this]
    exact zero_mem _
  exact h
end GlobalTheory.EpsThick

-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.mem_span_of_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:49.317339+00:00
-- url     : https://prove2.me/submissions/c6b901d9-4fc3-4179-bf73-63519412d9e9

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero
namespace GlobalTheory.SS.DefectZero
theorem _root_.solution (R A B D : Type) [CommRing R] [CommRing A] [CommRing B]
    [CommRing D] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra B D]
    [Algebra A D] [IsScalarTower A B D] (hs : Function.Surjective (algebraMap A B)) :
    ∃ ψ : D ⊗[A] Ω[A⁄R] →ₗ[D] D ⊗[B] Ω[B⁄R], LinearMap.ker ψ = Submodule.span D (Set.range
      fun h : RingHom.ker (algebraMap A B) => (1 : D) ⊗ₜ[A] KaehlerDifferential.D R A h.1) := by
  let c := AlgebraTensorModule.cancelBaseChange A B D D Ω[A⁄R]
  refine ⟨(mapBaseChange R A B).baseChange D ∘ₗ c.symm.toLinearMap, le_antisymm ?_ ?_⟩
  · intro v hv
    obtain ⟨v, rfl⟩ := c.surjective v
    have hv' : (mapBaseChange R A B).lTensor D v = 0 := by
      simpa [LinearMap.baseChange_eq_ltensor] using hv
    obtain ⟨w, rfl⟩ := (lTensor_exact D (mapBaseChange R A B).exact_subtype_ker_map
      (mapBaseChange_surjective R A B hs) v).mp hv'
    clear hv hv'
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | tmul d w =>
      obtain ⟨y, hy⟩ := (exact_kerCotangentToTensor_mapBaseChange R A B hs w.1).mp w.2
      obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ y
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← hy, kerCotangentToTensor_toCotangent]
      have : c (d ⊗ₜ[B] ((1 : B) ⊗ₜ[A] KaehlerDifferential.D R A y.1)) =
          d • (1 : D) ⊗ₜ[A] KaehlerDifferential.D R A y.1 := by
        simp [c, smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    simp [c, RingHom.mem_ker.mp y.2]
end GlobalTheory.SS.DefectZero

-- Prove2me | solution 1 for GlobalTheory.UniformLift.existsUnique_linearMap_lift_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:17.157827+00:00
-- url     : https://prove2.me/submissions/6aa45feb-caca-4c72-82b9-1aa8f70815d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibres
import Theorems.Thm_GlobalTheory_UniformLift_addMonoidHom_eq_of_eventuallyEq_addGroup
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_eventuallyEq_fderiv_of_eventually_add_mod_discrete
import Theorems.Thm_GlobalTheory_realLinear_eq_of_sub_mem_discrete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.UniformLift
namespace GlobalTheory.UniformLift
theorem _root_.solution {V W A : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [AddGroup A] {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {k : V → W} (hd : DifferentiableAt ℂ k 0) (h0 : k 0 = 0)
    (hk : ∀ᶠ z in 𝓝 0, ex' (k z) = ex z) : ∃! L : V →ₗ[ℂ] W, ∀ z, ex' (L z) = ex z := by
  have hadd : Tendsto (fun p : V × V ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : V × V)
  have hL := eventuallyEq_fderiv_of_eventually_add_mod_discrete hker hd h0 <| by
    filter_upwards [hadd.eventually hk, (continuous_fst.tendsto (0 : V × V)).eventually hk,
      (continuous_snd.tendsto (0 : V × V)).eventually hk] with p h1 h2 h3
    rw [AddMonoidHom.mem_ker, sub_sub, map_sub, map_add, h1, h2, h3, map_add, sub_self]
  have hL' : ex'.comp (fderiv ℂ k 0 : V →+ W) = ex := addMonoidHom_eq_of_eventuallyEq_addGroup <| by
    filter_upwards [hL, hk] with z h1 h2
    change ex' (fderiv ℂ k 0 z) = ex z
    rw [← h1, h2]
  have hL'' : ∀ z, ex' (fderiv ℂ k 0 z) = ex z := fun z => DFunLike.congr_fun hL' z
  refine ⟨(fderiv ℂ k 0 : V →ₗ[ℂ] W), hL'', fun L h => ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := L.restrictScalars ℝ)
    (L' := (fderiv ℂ k 0 : V →ₗ[ℂ] W).restrictScalars ℝ) fun x => by
      rw [AddMonoidHom.mem_ker, map_sub]
      exact sub_eq_zero.2 ((h x).trans (hL'' x).symm)
  exact LinearMap.ext fun z => DFunLike.congr_fun this z
end GlobalTheory.UniformLift

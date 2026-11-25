-- Prove2me | solution 1 for GlobalTheory.UniformLift.addMonoidHom_eq_of_eventuallyEq_addGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:34.936216+00:00
-- url     : https://prove2.me/submissions/1ad0352a-3937-4bee-80a0-9a002c4f0d6a

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
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
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
theorem _root_.solution {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddGroup A]
    {e e' : V →+ A} (h : e =ᶠ[𝓝 0] e') : e = e' := by
  ext v
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const v
  obtain ⟨j, hj⟩ := (ht.eventually h).exists
  have hv : v = (2 ^ j : ℕ) • (2⁻¹ : ℝ) ^ j • v := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp
  rw [hv, map_nsmul, map_nsmul, hj]
end GlobalTheory.UniformLift

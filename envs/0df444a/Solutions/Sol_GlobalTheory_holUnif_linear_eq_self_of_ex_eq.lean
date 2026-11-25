-- Prove2me | solution 1 for GlobalTheory.holUnif_linear_eq_self_of_ex_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:48:16.361723+00:00
-- url     : https://prove2.me/submissions/4e324fc4-1a46-43a1-9a01-03236cd36467

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLatticeAutOfIsomorphicThetaObjects
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u.ex z) (z : Fin g → ℂ) : F z = z := by
  have hmem : ∀ z, F z - z ∈ u.Λ := fun z => by
    rw [← u.ker]
    have h := u.ex_add (F z - z) z
    rw [sub_add_cancel, hF] at h
    exact mul_eq_right.1 h.symm
  have := u.discrete
  have hc : Continuous (fun z => (⟨F z - z, hmem z⟩ : u.Λ)) :=
    (F.continuous_of_finiteDimensional.sub continuous_id).subtype_mk _
  have h := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa [sub_eq_zero] using h
end GlobalTheory

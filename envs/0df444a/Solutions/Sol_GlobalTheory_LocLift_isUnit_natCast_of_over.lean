-- Prove2me | solution 1 for GlobalTheory.LocLift.isUnit_natCast_of_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:48.5198+00:00
-- url     : https://prove2.me/submissions/14fe5ddc-e34a-44dd-ab09-ed81d1010fcd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
theorem _root_.solution {K : Type} [Field K] [CharZero K] (s : X ⟶ Sp K) {k : ℕ} (hk : 0 < k) :
    IsUnit (k : Γ(X, ⊤)) := by
  have h : IsUnit (k : K) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hk.ne')
  simpa only [map_natCast] using h.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s.appTop).hom
end GlobalTheory.LocLift

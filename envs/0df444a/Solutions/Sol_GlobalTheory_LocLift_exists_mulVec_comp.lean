-- Prove2me | solution 1 for GlobalTheory.LocLift.exists_mulVec_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:25.340313+00:00
-- url     : https://prove2.me/submissions/d19199f1-96e4-4d53-b295-d4b200d45a2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
import Theorems.Thm_GlobalTheory_LocLift_IsExp_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
theorem _root_.solution {La T : Type} [AddCommGroup La] (M : T → Matrix (Fin g) (Fin g) ℂ)
    (P : T → (La →+ (Fin g → ℂ))) : ∃ P' : T → (La →+ (Fin g → ℂ)), ∀ b x, P' b x = (M b).mulVec (P b x) :=
  ⟨fun b => (Matrix.toLin' (M b)).toAddMonoidHom.comp (P b), fun b x => Matrix.toLin'_apply (M b) (P b x)⟩
end GlobalTheory.LocLift

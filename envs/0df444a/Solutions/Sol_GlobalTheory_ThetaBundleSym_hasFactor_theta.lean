-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSym.hasFactor_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:24:58.639631+00:00
-- url     : https://prove2.me/submissions/cb7bd7e6-e7d4-4545-b1f0-a0c51e13ce90

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Theorems.Thm_GlobalTheory_ThetaBundleSym_autFactor_eq
import Theorems.Thm_ReciprocityTheory_PTheta_thetaQuasiPeriod_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaBundleSym
variable {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
variable {τ} {a b : Fin g → ℝ}
namespace GlobalTheory.ThetaBundleSym
theorem _root_.solution (h1 : SiegelSubDomainStatement) (h2 : ThetaHoloStatement) (hτ : τ ∈ SiegelH (Fin g)) :
    HasFactor τ a b 1 1 (fun z => theta a b z τ) := by
  refine ⟨?_, fun n n' z => ?_⟩
  · have h3 := (h2 (Fin g) a b).comp (s := Set.univ) (f := fun z : Fin g → ℂ => (z, (fun i j => τ i j)))
      (by fun_prop) (fun z _ => h1 (Fin g) hτ)
    exact differentiableOn_univ.1 h3
  · simp only [pow_one]
    rw [thetaQuasiPeriod_holds _ a b z τ n n' hτ.1, autFactor_eq]
end GlobalTheory.ThetaBundleSym

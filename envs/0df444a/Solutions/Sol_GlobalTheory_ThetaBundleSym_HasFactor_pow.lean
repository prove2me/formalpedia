-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSym.HasFactor.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:41.632839+00:00
-- url     : https://prove2.me/submissions/93cb9a91-94e6-4170-a383-19bdd1fc07a4

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
namespace HasFactor
theorem _root_.solution {m k : ℕ} {f : (Fin g → ℂ) → ℂ} (h : HasFactor τ a b m k f) (r : ℕ) :
    HasFactor τ a b (m * r) (k * r) (fun z => f z ^ r) :=
  ⟨h.1.pow r, fun n n' z => by simp only [h.2]; rw [mul_pow, mul_pow, pow_mul, pow_mul]⟩
end HasFactor
end GlobalTheory.ThetaBundleSym

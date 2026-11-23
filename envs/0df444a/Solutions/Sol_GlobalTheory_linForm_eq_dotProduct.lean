-- Prove2me | solution 1 for GlobalTheory.linForm_eq_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:25.445348+00:00
-- url     : https://prove2.me/submissions/87ddb380-1614-4e12-95f3-49ec6c2c5577

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ) (z : Fin g → ℂ) :
    lam z = (fun i => lam (Pi.single i 1)) ⬝ᵥ z := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (Pi.single i (z i) : Fin g → ℂ) = z i • Pi.single i 1 := by
    ext j
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [h]
  rw [hs, map_smul, smul_eq_mul, mul_comm]
end GlobalTheory

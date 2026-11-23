-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.RegOn.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:34.195665+00:00
-- url     : https://prove2.me/submissions/6b3e9e42-0a19-49ca-b98e-f643931745d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c


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
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}
namespace GlobalTheory.ThetaModelGroup
namespace RegOn
theorem _root_.solution {U V : Y.left.Opens} {s : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : RegOn U s) (e : V ≤ U) :
    RegOn V s := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨resG _ e ρ, fun y' hy' => (valAt'_res _ e ρ hy').trans (hρ y' (top_le_preimage_mono _ e hy'))⟩
end RegOn
end GlobalTheory.ThetaModelGroup

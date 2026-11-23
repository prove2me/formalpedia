-- Prove2me | solution 1 for GlobalTheory.TorusEnd.exists_top_le_preimage_of_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:50.721413+00:00
-- url     : https://prove2.me/submissions/d68493ef-daf3-4af4-8cd0-e74a7b12be4f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTopLePreimageOfISupEqTop
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem


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
open GlobalTheory.TorusEnd
namespace GlobalTheory.TorusEnd
theorem _root_.solution {X : Scheme.{0}} {κ : Type*} (x : Sp ℂ ⟶ X) (U : κ → X.Opens)
    (h : ⨆ i, U i = ⊤) : ∃ i, ⊤ ≤ x ⁻¹ᵁ U i := by
  have : x (default : PrimeSpectrum ℂ) ∈ ⨆ i, U i := by rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨i, (top_le_preimage_iff_mem x _).2 hi⟩
end GlobalTheory.TorusEnd

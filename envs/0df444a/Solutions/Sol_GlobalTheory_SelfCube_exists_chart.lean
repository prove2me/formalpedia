-- Prove2me | solution 1 for GlobalTheory.SelfCube.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:09.295809+00:00
-- url     : https://prove2.me/submissions/f1756ebe-58df-4c56-b201-f7c3b1f47228

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
open GlobalTheory.CubeValues
namespace GlobalTheory.SelfCube
theorem _root_.solution (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) : ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  obtain ⟨hcov, -, -⟩ := hL
  have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  exact ⟨i, ((hv _ _).1 _).2 hi⟩
end GlobalTheory.SelfCube

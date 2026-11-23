-- Prove2me | solution 1 for GlobalTheory.SymmetricSemicharacter.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:02.784488+00:00
-- url     : https://prove2.me/submissions/2ecc96ca-adf9-4a4e-a841-6a4431f31aba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.SymmetricSemicharacter
open CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.SymmetricSemicharacter
theorem _root_.solution (hv : ValueRules) (hL : L.IsLB) (z : Fin g → ℂ) :
    ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  have h : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i, ((hv _ (u.ex z).left).1 _).2 hi⟩
end GlobalTheory.SymmetricSemicharacter

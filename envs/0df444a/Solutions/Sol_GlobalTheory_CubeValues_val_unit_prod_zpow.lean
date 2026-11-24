-- Prove2me | solution 1 for GlobalTheory.CubeValues.val_unit_prod_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:33.65386+00:00
-- url     : https://prove2.me/submissions/7e33b5aa-643d-489c-a96a-9b9b2349a745

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace

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
open GlobalTheory GlobalTheory.CubeValues
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.CubeValues
theorem _root_.solution (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {K : Type} [Fintype K]
    (f : K → Γ(X, U)ˣ) (ε : K → ℤ) :
    valAt' x U (∏ k, f k ^ ε k).val = ∏ k, valAt' x U (f k).val ^ ε k := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  have hm : ∀ w : Γ(X, U)ˣ, valAt' x U w.val = ((Units.map (e : Γ(X, U) →* ℂ) w : ℂˣ) : ℂ) :=
    fun w => he w.val
  calc valAt' x U (∏ k, f k ^ ε k).val = ((Units.map (e : Γ(X, U) →* ℂ) (∏ k, f k ^ ε k) : ℂˣ) : ℂ) := hm _
    _ = ∏ k, ((Units.map (e : Γ(X, U) →* ℂ) (f k) : ℂˣ) : ℂ) ^ ε k := by
      rw [map_prod, Units.coe_prod]
      simp only [map_zpow, Units.val_zpow_eq_zpow_val]
    _ = ∏ k, valAt' x U (f k).val ^ ε k := by simp only [hm]
end GlobalTheory.CubeValues

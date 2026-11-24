-- Prove2me | solution 1 for GlobalTheory.PullHermitian.unitVal_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:30.646322+00:00
-- url     : https://prove2.me/submissions/5cba3829-6e03-495b-840c-d63e03cfb517

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Theorems.Thm_GlobalTheory_PullHermitian_unitVal_res
import Theorems.Thm_GlobalTheory_PullHermitian_unitVal_pullU

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
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.PullHermitian
theorem _root_.solution {Y : Scheme.{0}} (L : LB Y) (φ : X ⟶ Y) (ε : ℤ) (j j' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U (fun _ => j) ⊓
      (L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U (fun _ => j')))
    (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    unitVal x h ((L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).g (fun _ => j) (fun _ => j')) =
      unitVal (x ≫ φ) h' (L.g j j') ^ ε := by
  refine (map_prod (unitVal x h) _ _).trans ?_
  rw [Fintype.prod_unique]
  refine (map_zpow (unitVal x h) _ _).trans ?_
  exact congrArg (· ^ ε) ((unitVal_res x (U := φ ⁻¹ᵁ (L.U j ⊓ L.U j')) _ h h' _).trans
    (unitVal_pullU x φ (L.U j ⊓ L.U j') h' h' _))
end GlobalTheory.PullHermitian

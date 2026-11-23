-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.tangent_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:21.509724+00:00
-- url     : https://prove2.me/submissions/2359d87e-aeb8-4232-9568-8e3b1c6145e8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_comp

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
open GlobalTheory GlobalTheory.TangentOrigin
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable {u}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution {v : epsR ℂ ⟶ A} (hv : IsTangent v) {W : A.left.Opens}
    (h : ⊤ ≤ v.left ⁻¹ᵁ W) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f : Γ(A.left, W)) :
    (evalPt (R := DualNumber ℂ) v.left W h f).fst = evalPt (u.ex 0).left W h0 f := by
  have key : ∀ (y : Sp ℂ ⟶ A.left) (hy : ⊤ ≤ y ⁻¹ᵁ W), spMap fstC ≫ v.left = y →
      (evalPt (R := DualNumber ℂ) v.left W h f).fst = evalPt y W hy f := by
    rintro y hy rfl
    exact (evalPt_spMap_comp fstC v.left W h hy f).symm
  exact key _ h0 (tangent_comp hv)
end GlobalTheory.TangentOrigin

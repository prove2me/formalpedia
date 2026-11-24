-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.evalPt_ex_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:28.714245+00:00
-- url     : https://prove2.me/submissions/f0e9752c-fde0-4869-99f3-b06f2ea1f1c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues

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
namespace GlobalTheory.TangentOrigin
theorem _root_.solution (z : Fin g → ℂ) {W : A.left.Opens} (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) (a : ℂ) :
    evalPt (u.ex z).left W h (constFn A.hom W a) = a := by
  rw [evalPt_constFn]
  have e : (u.ex z).left ≫ A.hom = spMap (RingHom.id ℂ) :=
    (ex_left_comp u z).trans (Spec.map_id _).symm
  exact (congrArg (fun y : Sp ℂ ⟶ Sp ℂ => evalPt y ⊤ le_rfl
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (evalPt_spMap _ a)
end GlobalTheory.TangentOrigin

-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.ratio_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:03.518863+00:00
-- url     : https://prove2.me/submissions/a132ccef-02c1-4c0a-b048-0585ec44bc94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
namespace GlobalTheory.AbLaw.Segre
theorem _root_.solution (s : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) : r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k => X.basicOpen (s.f k)) (nonzeroLocus s)
    (fun k => homOfLE (le_iSup (fun k => X.basicOpen (s.f k)) k)) le_rfl r 1 fun k => ?_
  have hle : X.basicOpen (s.f k) ≤ nonzeroLocus s ⊓ H.U k :=
    le_inf (le_iSup (fun k => X.basicOpen (s.f k)) k) (X.basicOpen_le _)
  have e := congrArg (rs X hle) (h k)
  simp only [map_mul, rs_rs] at e
  have u : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) := X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  have e' : rs X (hle.trans inf_le_left) r = 1 := u.mul_right_cancel (e.symm.trans (_root_.one_mul _).symm)
  exact e'.trans (map_one (rs X (hle.trans inf_le_left))).symm
end GlobalTheory.AbLaw.Segre

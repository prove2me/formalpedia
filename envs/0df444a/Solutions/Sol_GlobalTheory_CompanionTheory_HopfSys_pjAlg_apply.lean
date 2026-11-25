-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.pjAlg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:57.844816+00:00
-- url     : https://prove2.me/submissions/03a1e5ab-7b2b-4438-a8ff-61807847a57a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
variable [IsSeparated A.hom]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ)
    (z : (OSys A.hom S).obj T.1.1 ⊗[R] (OSys A.hom S).obj T.1.2) :
    pjAlg A S T z = Sec.res (A ⊗ A).hom
      (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)
      (kap A S T.1.1.unop T.1.2.unop z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)).symm)
  | tmul x y =>
    rw [pjAlg_tmul]
    refine Eq.trans ?_ (congrArg _ (Algebra.TensorProduct.lift_tmul _ _ _ _ _).symm)
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine congrArg₂ (· * ·) ?_ ?_
    · exact congrArg (fun t ↦ t.hom x) ((fst A A).left.appLE_map (U := (S.u T.1.1.unop).1) (V := Vop A S T.1.1.unop T.1.2.unop) inf_le_left
        (homOfLE (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)).op).symm
    · exact congrArg (fun t ↦ t.hom y) ((snd A A).left.appLE_map (U := (S.u T.1.2.unop).1) (V := Vop A S T.1.1.unop T.1.2.unop) inf_le_right
        (homOfLE (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)).op).symm
end GlobalTheory.CompanionTheory.HopfSys

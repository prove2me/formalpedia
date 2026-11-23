-- Prove2me | solution 1 for GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:43.445165+00:00
-- url     : https://prove2.me/submissions/0f47f69c-aa6d-4e74-9318-26c0ea4e5aba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_eq_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_glue


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
noncomputable section
open GlobalTheory GlobalTheory.EvVal
namespace GlobalTheory.EvVal
theorem _root_.solution {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (s : LB.Sec M) (t : LB.Gen M) (ht : t.IsGen) :
    ∃! v : Γ(Y, ⊤), ∀ j, s.f j =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom v * (t.s j).val := by
  obtain ⟨v, hv⟩ := TLinPf.glue M.U hc (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e := congrArg (fun x : Γ(Y, M.U i ⊓ M.U j)ˣ => (x⁻¹).val) (ht i j)
    simp only [mul_inv, ← map_inv, Units.val_mul] at e
    rw [map_mul, map_mul, s.compat i j]
    refine (congrArg (_ * ·) e).trans ?_
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]
    rfl)
  refine ⟨v, fun j => ?_, fun w hw => TLinPf.eq_local M.U hc _ _ fun j => ?_⟩
  · rw [hv j, Units.inv_mul_cancel_right]
  · rw [hv j, hw j, Units.mul_inv_cancel_right]
end GlobalTheory.EvVal

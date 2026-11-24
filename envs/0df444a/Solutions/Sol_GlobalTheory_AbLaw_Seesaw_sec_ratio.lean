-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.sec_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:00.494231+00:00
-- url     : https://prove2.me/submissions/178fc337-d405-4449-9d63-edd8f12e7b14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution {N : LB Y} (hc : ⨆ j, N.U j = ⊤) (s : LB.Sec N) (t : LB.Gen N) (ht : t.IsGen) :
    ∃ ρ : Γ(Y, ⊤), ∀ j, s.f j = rs Y le_top ρ * (t.s j).val := by
  obtain ⟨ρ, hρ⟩ := TLinPf.glue N.U hc (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at e
    have e' : rs Y (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) ((t.s i)⁻¹).val =
      ((N.g i j)⁻¹).val * rs Y (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) ((t.s j)⁻¹).val := congrArg Units.val e
    rw [map_mul, map_mul, s.compat i j, e', _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])
  refine ⟨ρ, fun j => ?_⟩
  rw [hρ j, Units.inv_mul_cancel_right]
end GlobalTheory.AbLaw.Seesaw

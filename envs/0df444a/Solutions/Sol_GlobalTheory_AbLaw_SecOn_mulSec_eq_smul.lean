-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.mulSec_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:36:55.878103+00:00
-- url     : https://prove2.me/submissions/f16ea4db-4d91-41a8-8d40-2d3b274fc70a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
open GlobalTheory.AbLaw.SecOn
open GlobalTheory.LB
variable {L M H : LB X} {V W : X.Opens}
variable {t : ℤ}
namespace GlobalTheory.AbLaw.SecOn
theorem _root_.solution (s s' : LB.Sec H) (r : Γ(X, V))
    (h : ∀ k, rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s'.f k) =
      rs X inf_le_left r * rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k))
    (x : SecOn (tw M H t) V) : mulSec M t s' V x = r • mulSec M t s V x :=
  tw_ext fun p k => by
    have e := congrArg (rs X (inf_le_inf_left V inf_le_right :
      V ⊓ (M.U p ⊓ H.U k) ≤ V ⊓ H.U k)) (h k)
    simp only [map_mul, rs_rs] at e
    rw [twCoord_smul, twCoord_mulSec, twCoord_mulSec, e, _root_.mul_assoc]
end GlobalTheory.AbLaw.SecOn

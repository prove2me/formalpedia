-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.existsUnique_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:47:46.393363+00:00
-- url     : https://prove2.me/submissions/0de92f87-a3da-4811-970e-d211ab4cab63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_existsUnique_glue
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_apply
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_restrict
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_change
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


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
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
open GlobalTheory.AbLaw.SecOn
open GlobalTheory.LB
variable {L M H : LB X} {V W : X.Opens}
namespace GlobalTheory.AbLaw.SecOn
theorem _root_.solution (hM : M.IsLB) {I : Type} (O : I → X.Opens) (hO : ∀ a, O a ≤ V)
    (hc : V ≤ ⨆ a, O a) (c : I → M.ι) (hU : ∀ a, O a ≤ M.U (c a)) (x : ∀ a, Γ(X, O a))
    (h : ∀ a b, rs X (inf_le_left : O a ⊓ O b ≤ O a) (x a) =
      rs X (inf_le_inf (hU a) (hU b)) (M.g (c a) (c b)).val *
        rs X (inf_le_right : O a ⊓ O b ≤ O b) (x b)) :
    ∃! t : SecOn M V, ∀ a, rs X (le_inf (hO a) (hU a)) (coord t (c a)) = x a := by

  have hiff : ∀ a (t : SecOn M V), rs X (le_inf (hO a) (hU a)) (coord t (c a)) = x a ↔
      restrict M (hO a) t = (chart hM (c a) (hU a)).symm (x a) := by
    intro a t
    rw [LinearEquiv.eq_symm_apply, chart_apply, coord_restrict, rs_rs]

  have hcomp : ∀ a b,
      restrict M (inf_le_left : O a ⊓ O b ≤ O a) ((chart hM (c a) (hU a)).symm (x a)) =
        restrict M (inf_le_right : O a ⊓ O b ≤ O b) ((chart hM (c b) (hU b)).symm (x b)) := by
    intro a b
    apply (chart hM (c a) ((inf_le_left : O a ⊓ O b ≤ O a).trans (hU a))).injective
    rw [chart_restrict hM (c a) (hU a) inf_le_left,
      chart_change hM (c a) (c b) _ ((inf_le_right : O a ⊓ O b ≤ O b).trans (hU b)),
      chart_restrict hM (c b) (hU b) inf_le_right, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    exact h a b
  obtain ⟨t, ht, huniq⟩ :=
    existsUnique_glue O hO hc (fun a => (chart hM (c a) (hU a)).symm (x a)) hcomp
  exact ⟨t, fun a => (hiff a t).2 (ht a), fun t' ht' => huniq t' fun a => (hiff a t').1 (ht' a)⟩
end GlobalTheory.AbLaw.SecOn

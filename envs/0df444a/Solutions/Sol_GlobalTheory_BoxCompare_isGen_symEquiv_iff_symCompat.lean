-- Prove2me | solution 1 for GlobalTheory.BoxCompare.isGen_symEquiv_iff_symCompat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:33.493601+00:00
-- url     : https://prove2.me/submissions/ae7e890d-8027-40ca-9690-7f5c78eb73d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
import Theorems.Thm_GlobalTheory_BoxCompare_restrict_lineBundleSymmetryUnitsEquivIso_apply
import Theorems.Thm_GlobalTheory_BoxCompare_res_dg_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxCompare
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LB
open GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum (PowerDatum IsNormSymm)
variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X)
namespace GlobalTheory.BoxCompare
theorem _root_.solution (sy : SymGen L f) :
    (symEquiv L f sy).IsGen ↔ SymCompat L f sy := by
  refine ⟨fun H a b a' b' W h₁ h₂ h₃ h₄ => ?_, fun H p q => ?_⟩
  · have k₃ := h₃.trans (ofIso_le L f _)
    have k₄ := h₄.trans (ofIso_le L f _)
    have key := congrArg (res (le_inf k₃ k₄)) (H (fun _ => a, b) (fun _ => a', b'))
    refine ((restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy (fun _ => a, b) k₃ h₃).symm.trans ?_)
    refine ((res_res _ _ _).symm.trans key).trans ((map_mul _ _ _).trans ?_)
    refine congrArg₂ (· * ·) (res_dg_pull L f (fun _ => a, b) (fun _ => a', b') _ h₁ h₂) ?_
    exact (res_res _ _ _).trans (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy (fun _ => a', b') k₄ h₄)
  · have h₃ := (inf_le_left (b := wchart L (fun _ : PUnit.{1} => f) q.1 ⊓ L.U q.2)).trans
      (toIso_le L f p)
    have h₄ := (inf_le_right (a := wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2)).trans
      (toIso_le L f q)
    have h₁ := (le_inf h₃ h₄).trans (wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] _ _ 0)
    have h₂ := (le_inf h₃ h₄).trans (wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] _ _ 1)
    refine (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy p _ h₃).trans ((H _ _ _ _ _ h₁ h₂ h₃ h₄).trans ?_)
    refine congrArg₂ (· * ·) ?_ (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy q _ h₄).symm
    exact (res_dg_pull L f p q le_rfl h₁ h₂).symm.trans (res_self _ _)
end GlobalTheory.BoxCompare

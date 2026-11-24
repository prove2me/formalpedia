-- Prove2me | solution 1 for GlobalTheory.BoxCompare.maps_iff_fixesRig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:34.710802+00:00
-- url     : https://prove2.me/submissions/0c206022-6938-42b9-b6aa-77b36ad48b6f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
import Theorems.Thm_GlobalTheory_BoxCompare_res_pullU_id
import Theorems.Thm_GlobalTheory_BoxCompare_prod_punit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_pullU_eq
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
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.BoxCompare
theorem _root_.solution (L : LB G.left) (r : LB.Gen (L.pull (eSec G)))
    (sy : SymGen L (ι[G]).left) :
    LB.Gen.Maps (LB.linCombIso (symEquiv L _ sy) (K := PUnit.{1}) (fun _ => eSec G) (fun _ => 1))
        r (rigPullOf (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L r) ↔
      FixesRig L (ι[G]).left (eSec G) sy r := by
  have he : eSec G ≫ (ι[G]).left = eSec G := GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv.trans (Category.id_comp _)

  have main : ∀ (a b : L.ι) (W : (𝟙_ (Over S)).left.Opens)
      (hW : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a) ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => b))
      (h : W ≤ eSec G ⁻¹ᵁ wchart L (K := Fin 2) ![(ι[G]).left, 𝟙 _] ![a, b]),
      res hW ((LB.linCombIso (symEquiv L _ sy) (K := PUnit.{1}) (fun _ => eSec G)
        (fun _ => 1)).s (fun _ _ => a, fun _ => b)) =
        res h (pullU (eSec G) _ (ts sy ![a, b])) := by
    intro a b W hW h
    refine (congrArg (res hW) ((prod_punit _).trans
      (zpow_one _))).trans ?_
    refine (res_res _ _ _).trans ?_
    exact (res_pullU_eq (eSec G) (toIso_le L _ (fun _ => a, b)) h _ _).symm
  have main₂ : ∀ (a : L.ι) (W : (𝟙_ (Over S)).left.Opens)
      (hW : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a))
      (ha : W ≤ wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => a)),
      res hW ((rigPullOf (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L r).s (fun _ _ => a)) =
        res ha (ts r (fun _ => a)) := fun a W hW ha =>
    (res_res _ _ _).trans (res_pullU_id _ _ _)
  refine ⟨fun H a b W ha hb h => ?_, fun H p => ?_⟩
  · have hW₁ : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a) :=
      fun y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (h hy) 0
    have key := congrArg (res (le_inf hW₁ hb)) (H (fun _ _ => a, fun _ => b))
    refine (main₂ a W hW₁ ha).symm.trans ((res_res _ _ _).symm.trans (key.trans ?_))
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (main a b W _ h) (res_res _ _ _))
  · obtain ⟨a, b⟩ := p
    have ha : wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) a ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) b ≤
        wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => a ⟨⟩ ⟨⟩) :=
      inf_le_left.trans (rigPull_le (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L a)
    have h : wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) a ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) b ≤
        eSec G ⁻¹ᵁ wchart L (K := Fin 2) ![(ι[G]).left, 𝟙 _] ![a ⟨⟩ ⟨⟩, b ⟨⟩] :=
      fun y hy => toIso_le L _ (a ⟨⟩, b ⟨⟩)
        ⟨Set.mem_iInter.1 hy.1 ⟨⟩, Set.mem_iInter.1 hy.2 ⟨⟩⟩
    refine (main₂ (a ⟨⟩ ⟨⟩) _ inf_le_left ha).trans
      ((H (a ⟨⟩ ⟨⟩) (b ⟨⟩) _ ha inf_le_right h).trans ?_)
    exact congrArg₂ (· * ·) ((main (a ⟨⟩ ⟨⟩) (b ⟨⟩) _ le_rfl h).symm.trans (res_self _ _)) rfl
end GlobalTheory.BoxCompare

-- Prove2me | solution 1 for GlobalTheory.BoxCompare.corr_iff_diagOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:38.347742+00:00
-- url     : https://prove2.me/submissions/11d95246-1b41-450a-ab32-bb9db3799624

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
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
variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : T ⟶ X)
namespace GlobalTheory.BoxCompare
theorem _root_.solution (he : e ≫ f = e) (sy : SymGen L f) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy e) (LB.oneGen L) ↔ DiagOne L f e sy := by
  refine ⟨fun H a W h => ?_, fun H j j' hj _ _ => ?_⟩
  · have key := H ![a, a] PEmpty.elim
      (fun k₁ k₂ _ => by fin_cases k₁ <;> fin_cases k₂ <;> rfl) (fun k => k.elim)
      (fun _ k => k.elim)
    have hW : W ≤ wchart L (fun k => e ≫ (![f, 𝟙 X] : Fin 2 → (X ⟶ X)) k) ![a, a] ⊓
        wchart L (Y := T) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun y hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k,
        Set.mem_iInter.2 fun k => k.elim⟩
    have key' := congrArg (res hW) key
    refine ((res_res _ _ _).trans (res_res _ _ _)).symm.trans (key'.trans ?_)
    exact (congrArg (res hW) (map_one _)).trans (map_one _)
  · have h01 : j 0 = j 1 := hj 0 1 (he.trans (Category.comp_id e).symm)
    obtain ⟨a, rfl⟩ : ∃ a, j = ![a, a] := ⟨j 0, by
      funext k
      fin_cases k
      · rfl
      · exact h01.symm⟩
    exact ((res_res _ _ _).trans (H a _ _)).trans (map_one _).symm
end GlobalTheory.BoxCompare

-- Prove2me | solution 1 for GlobalTheory.BoxCompare.diagOne_iff_fixesRig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:33.508856+00:00
-- url     : https://prove2.me/submissions/1d53b5be-7a28-4a18-a950-e81507a50422

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
import Theorems.Thm_GlobalTheory_BoxCompare_isGen_iff_symCompat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_g_self
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
theorem _root_.solution (hL : L.IsLB) (sy : SymGen L f) (hsy : sy.IsGen)
    (r : LB.Gen (L.pull e)) (hr : r.IsGen) : DiagOne L f e sy ↔ FixesRig L f e sy r := by
  refine ⟨fun H a b W ha hb h => ?_, fun H a W h => ?_⟩
  · have hc := (isGen_iff_symCompat L f sy).1 hsy
    set V := wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b] ⊓ L.U a with hV
    have v₁ : V ≤ f ⁻¹ᵁ L.U a := ((le_two L f ![a, b]).1 (inf_le_left : V ≤ _)).1
    have v₂ : V ≤ L.U b := ((le_two L f ![a, b]).1 (inf_le_left : V ≤ _)).2
    have v₃ : V ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, a] :=
      (le_two L f ![a, a]).2 ⟨v₁, inf_le_right⟩
    have hWV : W ≤ e ⁻¹ᵁ V := fun y hy => ⟨h hy, (le_one L e _).1 ha hy⟩
    have k := hc a b a a V (fun y hy => ⟨v₁ hy, v₁ hy⟩) (le_inf v₂ inf_le_right) inf_le_left v₃
    rw [pull_g_self hL f a (fun y hy => ⟨v₁ hy, v₁ hy⟩), _root_.one_mul] at k
    have k' := congrArg (fun x => res hWV (pullU e V x)) k
    simp only [map_mul, map_inv, pullU_res, res_res] at k'
    rw [H a W, _root_.mul_one] at k'
    have k₂ := congrArg (res (le_inf hb ha)) ((isGen_iff L r).1 hr (fun _ => b) (fun _ => a))
    rw [map_mul, res_res, res_res, lcg_pull, res_res] at k₂
    rw [k', k₂, inv_mul_cancel_left]
  · have ha : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => a) :=
      (le_one L e _).2 (h.trans (e.preimage_mono ((le_two L f ![a, a]).1 le_rfl).2))
    exact (mul_right_cancel ((_root_.one_mul _).trans (H a a W ha ha h))).symm
end GlobalTheory.BoxCompare

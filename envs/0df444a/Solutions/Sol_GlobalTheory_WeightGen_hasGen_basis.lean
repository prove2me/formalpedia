-- Prove2me | solution 1 for GlobalTheory.WeightGen.hasGen_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:15.492499+00:00
-- url     : https://prove2.me/submissions/2723b182-252a-45a0-be10-4ae6eeede3c9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_HasGen_of_local
import Theorems.Thm_GlobalTheory_WeightGen_gm_res_pull_top
import Theorems.Thm_GlobalTheory_WeightGen_act_q_left
import Theorems.Thm_GlobalTheory_WeightGen_exists_mem_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {S : Scheme.{0}}
variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)
attribute [local instance] SplitExt.free SplitExt.finite
namespace GlobalTheory.WeightGen
theorem _root_.solution (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    HasGen d.q.left (act d).left (snd (splitTorus S E.X) G).left (E.O (E.basis k)).L
      (wt E.X G (E.basis k)) := by
  have hL := (E.O (E.basis k)).isLB
  refine HasGen.of_local (act_q_left d) E.chart exists_mem_chart
    (fun j α Z r z => gm r z _ (d.u α k) * gm (r ≫ d.q.left) z _ ((E.O (E.basis k)).L.g (α k) j))
    (fun j α => ⟨res (V := d.q.left ⁻¹ᵁ (E.O (E.basis k)).L.U j ⊓ d.q.left ⁻¹ᵁ E.chart α)
      inf_le_right (d.u α k) * res (U := d.q.left ⁻¹ᵁ ((E.O (E.basis k)).L.U (α k) ⊓ (E.O (E.basis k)).L.U j))
        (le_inf (inf_le_right.trans (d.q.left.preimage_mono (E.chart_le α k))) inf_le_left)
        (pullU d.q.left _ ((E.O (E.basis k)).L.g (α k) j)), fun Z r z h₁ h₂ => ?_⟩)
    (fun Z r z j j' α α' h₁ h₂ h₃ h₄ => ?_) (fun Z r z j α h₁ h₂ => ?_)
  · have hm : r z ∈ d.q.left ⁻¹ᵁ (E.O (E.basis k)).L.U j ⊓ d.q.left ⁻¹ᵁ E.chart α := ⟨h₁, h₂⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
      ((gm_res r z _ hm _).trans (gm_pull r _ z (_ ⊓ _) ⟨E.chart_le α k h₂, h₁⟩ _)))
  · have hm : r z ∈ d.q.left ⁻¹ᵁ (E.chart α ⊓ E.chart α') := ⟨h₃, h₄⟩
    have e := (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (d.trans α α' k)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull r _ z _ hm _).trans
        (gm_res (r ≫ d.q.left) z _ hm _)) (gm_res r z _ hm _))))
    have c₁ := gm_cocycle hL (r ≫ d.q.left) z (E.chart_le α k h₃) (E.chart_le α' k h₄) h₂
    have c₂ := gm_cocycle hL (r ≫ d.q.left) z (E.chart_le α k h₃) h₁ h₂
    rw [e, mul_right_comm, c₁, ← c₂]
    ac_rfl
  · have hm : r z ∈ (snd (splitTorus S E.X) G).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart α) := h₂
    have e := congrArg (gm r z ((snd (splitTorus S E.X) G).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart α)))
      (d.equiv α k)
    rw [map_mul, gm_res r z _ hm,
      gm_pull r (act d).left z (d.q.left ⁻¹ᵁ E.chart α) (d.act_le α hm),
      gm_pull r (snd (splitTorus S E.X) G).left z (d.q.left ⁻¹ᵁ E.chart α) hm] at e
    have e' := e.trans (congrArg (· * _) (gm_res_pull_top r z _ hm _ _))
    rw [e', Category.assoc, Category.assoc, act_q_left, _root_.mul_assoc]
    rfl
end GlobalTheory.WeightGen

-- Prove2me | solution 1 for GlobalTheory.WeightGen.hasGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:39.24457+00:00
-- url     : https://prove2.me/submissions/cd441443-9477-44eb-b9cb-f976e102ac57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_HasGen_of_gen
import Theorems.Thm_GlobalTheory_WeightGen_HasGen_div
import Theorems.Thm_P2M_GlobalTheory_WeightGen_HasGen_iso__e42ac449ccba
import Theorems.Thm_GlobalTheory_WeightGen_wt_add
import Theorems.Thm_GlobalTheory_WeightGen_wt_zero
import Theorems.Thm_GlobalTheory_WeightGen_act_q_left
import Theorems.Thm_GlobalTheory_WeightGen_hasGen_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
theorem _root_.solution (χ : E.X) :
    HasGen d.q.left (act d).left (snd (splitTorus S E.X) G).left (E.O χ).L (wt E.X G χ) := by
  let Q : E.X → Prop := fun χ =>
    HasGen d.q.left (act d).left (snd (splitTorus S E.X) G).left (E.O χ).L (wt E.X G χ)
  have h0 : Q 0 := by
    obtain ⟨t, ht⟩ := E.zeroTriv
    simp only [Q, wt_zero]
    exact HasGen.of_gen (act_q_left d) t ht
  have hs : ∀ x y, Q (x + y) → Q x → Q y := by
    intro x y h₁ h₂
    obtain ⟨w, hw⟩ := E.addIso x y
    have := (HasGen.div (act_q_left d) h₁ h₂).iso' (act_q_left d) (fun b => by
      obtain ⟨i, hi⟩ := exists_chart (E.O (x + y)).isLB b
      obtain ⟨j, hj⟩ := exists_chart (E.O x).isLB b
      exact ⟨(i, j), hi, hj⟩) w hw
    have e : (fun Z r z => wt E.X G (x + y) Z r z * (wt E.X G x Z r z)⁻¹) = wt E.X G y := by
      funext Z r z
      rw [wt_add, mul_inv_cancel_comm]
    rwa [e] at this
  have hn : ∀ x, Q x → Q (-x) := fun x h => hs x (-x) (by rw [add_neg_cancel]; exact h0) h
  have hχ : χ ∈ AddSubgroup.closure (Set.range E.basis) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, E.basis.span_eq]; trivial
  refine AddSubgroup.closure_induction (p := fun x _ => Q x) ?_ h0 ?_ (fun x _ => hn x) hχ
  · rintro _ ⟨k, rfl⟩
    exact hasGen_basis d k
  · intro x y _ _ hx hy
    exact hs (-x) (x + y) (by rw [neg_add_cancel_left]; exact hy) (hn x hx)
end GlobalTheory.WeightGen

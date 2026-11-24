-- Prove2me | solution 1 for GlobalTheory.SecAff.isUnit_pa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:52.738512+00:00
-- url     : https://prove2.me/submissions/75f7c03c-7a0b-4de1-b97f-d181c05a2dd2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
namespace GlobalTheory.SecAff
theorem _root_.solution (h : T' ⟶ T) (r : Γ(T.left, ⊤)) (hr : ∀ x, h.left x ∈ T.left.basicOpen r) :
    IsUnit (pa h.left (V := ⊤) (le_pre_top _) r) := by
  have e := Scheme.basicOpen_appLE h.left ⊤ ⊤ (le_pre_top _) r
  refine T'.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => ?_
  have : x ∈ T'.left.basicOpen (pa h.left (V := ⊤) (le_pre_top _) r) := by
    change x ∈ T'.left.basicOpen (h.left.appLE ⊤ ⊤ (le_pre_top _) r)
    rw [e]
    exact ⟨trivial, hr x⟩
  exact (T'.left.mem_basicOpen _ x hx).1 this
end GlobalTheory.SecAff

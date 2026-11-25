-- Prove2me | solution 1 for GlobalTheory.WeilIsogeny.weilIs_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:31:53.044793+00:00
-- url     : https://prove2.me/submissions/f93d3163-228d-4bcb-a0ee-99ed120e3a23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenMovePow
import Theorems.Thm_GlobalTheory_CommutatorPairing_commIsOf_iff
import Theorems.Thm_GlobalTheory_CommutatorPairing_commVal_indep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilIsogeny
open CommutatorPairing
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
namespace GlobalTheory.WeilIsogeny
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θx θy : ThetaGrp A L k (overRes V),
      θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y ∧ CommIsOf A L k θx θy (unitRes V c)) :
    WeilIs A L k x y c := by
  intro p
  obtain ⟨V, hV, θx, θy, ex, ey, H⟩ := h p
  refine ⟨V, hV, ⟨θx, θy, ex, ey⟩, fun θ θ' e e' => (commIsOf_iff hL _ _ _).2 fun Z t b z J hJ => ?_⟩
  exact (commVal_indep hG hA hL θ θ' θx θy t t (by rw [e, ex]) (by rw [e', ey]) b z J hJ).trans
    ((commIsOf_iff hL _ _ _).1 H _ t b z J hJ)
end GlobalTheory.WeilIsogeny

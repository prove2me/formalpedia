-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.coaction_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:05.453815+00:00
-- url     : https://prove2.me/submissions/8bfdda8f-3d78-4f54-bd61-a4826d7e2943

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_comp_ev
import Theorems.Thm_GlobalTheory_TorsorUnit_univ_val
import Theorems.Thm_GlobalTheory_TorsorUnit_cst_apply
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_univ
import Theorems.Thm_GlobalTheory_TorsorUnit_coeff_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']
namespace GlobalTheory.TorsorUnit
theorem _root_.solution {α : A →+* C} {ρ : C →+* AddMonoidAlgebra C X}
    (h : IsTorsorOn (AddMonoidAlgebra (AddMonoidAlgebra C X) X) α ρ) (c : C) (x : X) :
    ρ ((ρ c).coeff x) = AddMonoidAlgebra.single x ((ρ c).coeff x) := by
  have h1 := RingHom.congr_fun (h.1 ((cst X _).comp (cst X C)) (univ X _)
    ((Units.map (cst X _).toMonoidHom).comp (univ X C))) c
  rw [← comp_ev, ev_univ, RingHom.comp_id] at h1
  have h2 := congrArg (fun f => AddMonoidAlgebra.coeff f x) h1
  have h3 := coeff_ev ρ 1 (ρ c) x
  simp only [RingHom.comp_apply] at h2
  rw [coeff_ev, univ_val, cst_apply, AddMonoidAlgebra.single_mul_single] at h2
  rw [MonoidHom.comp_one, _root_.mul_one, ← h2] at h3
  simpa using h3.symm
end GlobalTheory.TorsorUnit

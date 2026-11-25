-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.sval_cs_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:05.937118+00:00
-- url     : https://prove2.me/submissions/73ed68f2-ebdf-4771-a303-70176ffbe29f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
open GlobalTheory.UnifZero ReciprocityTheory.ChartRestriction.G.Out.Inh
variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.UU.RelModel
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (J) : sval (cs φ ε 1) r z J = 1 := by
  have hm : r z ∈ LB.wchart (trivLB X) φ (fun k => J (r ≫ φ k)) := by rw [GlobalTheory.ToricData.wchart_triv]; trivial
  refine (gs_eq r z _ hm _).trans ?_
  simp only [cs, resTop, map_one]
  erw [map_one, map_one]
end GlobalTheory.UU.RelModel

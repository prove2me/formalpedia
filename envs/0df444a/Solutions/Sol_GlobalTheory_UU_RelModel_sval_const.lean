-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.sval_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:24.640691+00:00
-- url     : https://prove2.me/submissions/2ae9e3a9-e342-42a2-a153-800f31d36e2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UnifZero_appTop_scal
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
namespace GlobalTheory.UU.RelModel
theorem _root_.solution {X Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb (trivLB X) φ ε)} {B : Type} [CommRing B] {p : Y ⟶ Spec (CommRingCat.of B)} {a : B}
    (h : SecConst s (scal p a)) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = gs (𝟙 Z) z ⊤ (scal (r ≫ p) a) := by
  have hm : r z ∈ LB.wchart (trivLB X) φ (fun k => J (r ≫ φ k)) := by rw [GlobalTheory.ToricData.wchart_triv]; trivial
  refine (congrArg (gs r z _) (h _)).trans ((gs_res r z le_top hm _).trans ?_)
  rw [← appTop_scal]
  exact ((gs_pull (𝟙 Z) r z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
end GlobalTheory.UU.RelModel

-- Prove2me | solution 1 for GlobalTheory.UnifPullRig.compatAlong_of_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:48:25.61239+00:00
-- url     : https://prove2.me/submissions/07b24bbb-056b-4ed1-b7bf-40fdcb0c3cb4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
import Theorems.Thm_GlobalTheory_UnifPullRig_gm_res_pull
import Theorems.Thm_GlobalTheory_UnifPullRig_pt_of_eq
import Theorems.Thm_GlobalTheory_UnifPullRig_RigAlong_stalk
import Theorems.Thm_GlobalTheory_UnifPullRig_CompatAlong_stalk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.UnifPullRig
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' B B' T T' T₁ T₁' G G' A A' : Scheme.{0}}
variable {L : LB G} {M : LB A} {L' : LB G'} {M' : LB A'} {F : G' ⟶ G} {E : A' ⟶ A}
    {f : T ⟶ G} {p : T ⟶ A} {f' : T' ⟶ G'} {p' : T' ⟶ A'}
    {f₁ : T₁ ⟶ G} {p₁ : T₁ ⟶ A} {f₁' : T₁' ⟶ G'} {p₁' : T₁' ⟶ A'}
namespace GlobalTheory.UnifPullRig
theorem _root_.solution (hL : L.IsLB) (hM : M.IsLB)
    {wL : LB.Iso L' (L.pull F)} {wM : LB.Iso M' (M.pull E)}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {h : T' ⟶ T}
    {w₁ : LB.Iso (L.pull f₁) (M.pull p₁)} {w₁' : LB.Iso (L'.pull f₁') (M'.pull p₁')} {h₁ : T₁' ⟶ T₁}
    {m : T ⟶ T₁} {m' : T' ⟶ T₁'} (Q : Square wL wM w w' h) (Q₁ : Square wL wM w₁ w₁' h₁)
    (H : CompatAlong w₁ w m) (hf : m ≫ f₁ = f) (hp : m ≫ p₁ = p) (hf' : m' ≫ f₁' = f')
    (hp' : m' ≫ p₁' = p') (hF : h ≫ f = f' ≫ F) (hE : p' ≫ E = h ≫ p) (hm : m' ≫ h₁ = h ≫ m) :
    CompatAlong w₁' w' m' := by
  rintro ⟨qM, qL⟩ V a₁ a₂
  refine unit_ext fun y hy => ?_
  obtain ⟨jM, hjM⟩ := exists_chart hM (E (p' y))
  obtain ⟨jL, hjL⟩ := exists_chart hL (F (f' y))
  have bM : p' y ∈ M'.U (qM ⟨⟩) := mem_pull.1 (a₂ hy).1
  have bL : f' y ∈ L'.U (qL ⟨⟩) := mem_pull.1 (a₂ hy).2
  have e₀ := Q _ (𝟙 T') y jM (qM ⟨⟩) jL (qL ⟨⟩) hjM bM hjL bL
  have e₂ := H.stalk hf hp (𝟙 T' ≫ h) y jM jL (pt_of_eq hE y ▸ hjM) ((pt_of_eq hF y).symm ▸ hjL)
  subst hf' hp'
  have e₁ := Q₁ _ (𝟙 T' ≫ m') y jM (qM ⟨⟩) jL (qL ⟨⟩) hjM bM hjL bL
  rw [Category.assoc, Category.assoc, Category.assoc, hm, ← Category.assoc _ h m, e₂, ← e₀] at e₁
  exact (gm_res_pull _ m' y a₁ hy _).trans ((mul_left_cancel e₁).trans (gm_res _ y a₂ hy _).symm)
end GlobalTheory.UnifPullRig

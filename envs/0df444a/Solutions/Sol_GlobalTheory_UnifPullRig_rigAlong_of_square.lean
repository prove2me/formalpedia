-- Prove2me | solution 1 for GlobalTheory.UnifPullRig.rigAlong_of_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:50:01.940944+00:00
-- url     : https://prove2.me/submissions/49e53fcf-8807-40a9-8525-1a474da977fb

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
    {ε : S ⟶ T} {i : S ⟶ B} {eG : B ⟶ G} {eA : B ⟶ A} {rL : LB.Gen (L.pull eG)}
    {rM : LB.Gen (M.pull eA)}
    {ε' : S' ⟶ T'} {i' : S' ⟶ B'} {eG' : B' ⟶ G'} {eA' : B' ⟶ A'} {rL' : LB.Gen (L'.pull eG')}
    {rM' : LB.Gen (M'.pull eA')} {b : B' ⟶ B} {σ : S' ⟶ S}
    (Q : Square wL wM w w' h) (H : RigAlong w ε i rL rM)
    (PL : PMaps wL (K := PUnit) (fun _ => eG') (fun _ => eG) (fun _ => 1) rL' rL b)
    (PM : PMaps wM (K := PUnit) (fun _ => eA') (fun _ => eA) (fun _ => 1) rM' rM b)
    (hf : ε ≫ f = i ≫ eG) (hp : ε ≫ p = i ≫ eA) (hf' : ε' ≫ f' = i' ≫ eG') (hp' : ε' ≫ p' = i' ≫ eA')
    (hF : h ≫ f = f' ≫ F) (hE : p' ≫ E = h ≫ p) (hε : ε' ≫ h = σ ≫ ε) (hσ : σ ≫ i = i' ≫ b) :
    RigAlong w' ε' i' rL' rM' := by
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  obtain ⟨jM, hjM⟩ := exists_chart hM (E (p' (ε' y)))
  obtain ⟨jL, hjL⟩ := exists_chart hL (F (f' (ε' y)))
  have bM : p' (ε' y) ∈ M'.U (qM ⟨⟩) := mem_pull.1 (a₁ hy).1
  have bL : f' (ε' y) ∈ L'.U (qL ⟨⟩) := mem_pull.1 (a₁ hy).2
  have e₀ := Q _ ε' y jM (qM ⟨⟩) jL (qL ⟨⟩) hjM bM hjL bL
  have e₁ := H.stalk hf hp σ y jM jL (by rw [← pt_of_eq hε y, ← pt_of_eq hE]; exact hjM)
    (by rw [← pt_of_eq hε y, pt_of_eq hF]; exact hjL)
  have e₂ := PL _ i' y (fun _ => jL) qL (fun _ => pt_of_eq hf' y ▸ hjL) (fun _ => pt_of_eq hf' y ▸ bL)
  have e₃ := PM _ i' y (fun _ => jM) qM (fun _ => pt_of_eq hp' y ▸ hjM) (fun _ => pt_of_eq hp' y ▸ bM)
  rw [Fintype.prod_unique, zpow_one] at e₂ e₃
  rw [hσ, ← hε] at e₁
  rw [hf', hp'] at e₀
  have e₄ := (congrArg (gw w (ε' ≫ h) y jM (fun _ => jL) * ·) e₂).symm.trans (e₁.trans e₃)
  rw [← _root_.mul_assoc] at e₄
  have e₅ := (congrArg (· * gm i' y (LB.wchart L' (fun _ => eG') qL) (rL'.s qL)) e₀).trans e₄
  have e₆ := mul_left_cancel ((_root_.mul_assoc _ _ _).symm.trans e₅)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ ε' y a₁ hy _)
    (gm_res_pull _ i' y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ i' y a₃ hy _).symm))
  rw [Category.id_comp, Category.id_comp]
  exact e₆
end GlobalTheory.UnifPullRig

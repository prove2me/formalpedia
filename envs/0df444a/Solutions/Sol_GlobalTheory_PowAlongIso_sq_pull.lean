-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.sq_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:45:13.136503+00:00
-- url     : https://prove2.me/submissions/1cf37603-8f45-4ca1-b6bd-b8fdc030e846

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_GlobalTheory_PowAlongIso_mem_wchart_comp
import Theorems.Thm_GlobalTheory_PowAlongIso_sq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open GlobalTheory GlobalTheory.PowAlongIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR (bw gm_linCombIso mem_finf)
variable {B B' X X' X'' T T' T'' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB X} {L' : LB X'} {L'' : LB X''} {j : ℕ}
  {prB : Fin j → (B' ⟶ B)} {pr : Fin j → (X' ⟶ X)} {p : T ⟶ B} {f : T ⟶ X} {p' : T' ⟶ B'} {f' : T' ⟶ X'}
namespace GlobalTheory.PowAlongIso
theorem _root_.solution (hL' : L'.IsLB) {E : X'' ⟶ X'} {pr' : Fin j → (X'' ⟶ X)} (hpr : ∀ i, pr' i = E ≫ pr i)
    {wD : LB.Iso M' (LB.LinComb M prB (fun _ => 1))} {wL : LB.Iso L' (LB.LinComb L pr (fun _ => 1))}
    {v : LB.Iso L'' (L'.pull E)} {wL' : LB.Iso L'' (LB.LinComb L pr' (fun _ => 1))}
    (hT : ∀ (Z : Scheme.{0}) (g : Z ⟶ X'') (z : Z)
      (a : Fin j → L.ι) (b : L'.ι) (c : L''.ι), g z ∈ LB.wchart L pr' a → E (g z) ∈ L'.U b → g z ∈ L''.U c →
      bw wL' g z a c = bw wL (g ≫ E) z a b * gw v g z b c)
    {p'' : T'' ⟶ B'} {f'' : T'' ⟶ X''} {h : T'' ⟶ T'} (hp : p'' = h ≫ p') (hf : h ≫ f' = f'' ≫ E)
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')}
    {w'' : LB.Iso (L''.pull f'') (M'.pull p'')} {ρ : Fin j → (T' ⟶ T)} {ρ' : Fin j → (T'' ⟶ T)}
    (hρ : ∀ i, ρ' i = h ≫ ρ i)
    (hw : ∀ (Z : Scheme.{0}) (r : Z ⟶ T'') (z : Z) (jM : M'.ι) (jL : L'.ι) (jL' : L''.ι), p'' (r z) ∈ M'.U jM →
      E (f'' (r z)) ∈ L'.U jL → f'' (r z) ∈ L''.U jL' →
      gw w'' r z jM (fun _ => jL') = gw w' (r ≫ h) z jM (fun _ => jL) * gw v (r ≫ f'') z jL jL')
    (H : Sq wD wL w w' ρ) : Sq wD wL' w w'' ρ' := by
  obtain rfl : pr' = fun i => E ≫ pr i := funext hpr
  obtain rfl : ρ' = fun i => h ≫ ρ i := funext hρ
  subst hp
  rw [sq_iff] at H ⊢
  intro Z r z jNM jM' jL' jNL h₁ h₂ h₃ h₄ h₅ h₆
  obtain ⟨k, hk⟩ := exists_chart hL' (E (f'' (r z)))
  have e : f' (h (r z)) = E (f'' (r z)) := congrArg (fun g : T'' ⟶ X' => g (r z)) hf
  have a := H Z (r ≫ h) z jNM jM' k jNL h₁ h₂ (show f' (h (r z)) ∈ _ from e ▸ hk) h₄ h₅
    (show f' (h (r z)) ∈ _ from e ▸ (mem_wchart_comp (E := E)).1 h₆)
  rw [hw Z r z jM' k jL' h₂ hk h₃, hT Z (r ≫ f'') z jNL k jL' h₆ hk h₃, ← _root_.mul_assoc, ← _root_.mul_assoc]
  simp only [Category.assoc, hf] at a ⊢
  rw [a]
end GlobalTheory.PowAlongIso

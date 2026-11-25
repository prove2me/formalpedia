-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.exists_box_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:41:34.067503+00:00
-- url     : https://prove2.me/submissions/15c7b464-a2be-4562-ab89-095f664e3c76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_GlobalTheory_PowAlongIso_isGen_box
import Theorems.Thm_GlobalTheory_PowAlongIso_mem_wchart_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
variable {X X' X'' Y Y' Y₀ Z : Scheme.{0}}
variable {M : LB X} {M' : LB X'} {M'' : LB X''} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
namespace GlobalTheory.PowAlongIso
theorem _root_.solution (hM : M.IsLB) (hM' : M'.IsLB) (hM'' : M''.IsLB) {E : X'' ⟶ X'} {pr' : Fin j → (X'' ⟶ X)}
    (hpr : ∀ i, pr' i = E ≫ pr i) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    (w' : LB.Iso M'' (M'.pull E)) (hw' : w'.IsGen) :
    ∃ w'' : LB.Iso M'' (LB.LinComb M pr' (fun _ => 1)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z)
      (a : Fin j → M.ι) (b : M'.ι) (c : M''.ι), f z ∈ LB.wchart M pr' a → E (f z) ∈ M'.U b → f z ∈ M''.U c →
      bw w'' f z a c = bw w (f ≫ E) z a b * gw w' f z b c := by
  obtain rfl : pr' = fun i => E ≫ pr i := funext hpr
  rw [isGen_box] at hw
  rw [isGen_iff] at hw'
  have glue : ∀ (a : Fin j → M.ι) (c : M''.ι), ∃ s : Γ(X'', LB.wchart M (fun i => E ≫ pr i) a ⊓ M''.U c)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z) (b : M'.ι), f z ∈ LB.wchart M (fun i => E ≫ pr i) a →
        E (f z) ∈ M'.U b → f z ∈ M''.U c → gm f z _ s = bw w (f ≫ E) z a b * gw w' f z b c := by
    intro a c
    obtain ⟨W, hW⟩ : ∃ W : M'.ι → X''.Opens, ∀ b x, x ∈ W b ↔
        x ∈ LB.wchart M (fun i => E ≫ pr i) a ∧ E x ∈ M'.U b ∧ x ∈ M''.U c :=
      ⟨fun b => LB.wchart M (fun i => E ≫ pr i) a ⊓ (E ⁻¹ᵁ M'.U b ⊓ M''.U c), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ b, W b ≤ LB.wchart M (fun i => E ≫ pr i) a ⊓ M''.U c := fun b x hx =>
      ⟨((hW b x).1 hx).1, ((hW b x).1 hx).2.2⟩
    have l₁ : ∀ b, W b ≤ E ⁻¹ᵁ (LB.wchart M pr a ⊓ M'.U b) := fun b x hx =>
      ⟨mem_wchart_comp.1 ((hW b x).1 hx).1, ((hW b x).1 hx).2.1⟩
    have l₂ : ∀ b, W b ≤ (M'.pull E).U (fun _ => b) ⊓ M''.U c := fun b x hx =>
      ⟨mem_pull.2 ((hW b x).1 hx).2.1, ((hW b x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ b, Γ(X'', W b)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z) (b : M'.ι), f z ∈ W b →
        gm f z (W b) (u b) = bw w (f ≫ E) z a b * gw w' f z b c :=
      ⟨fun b => res (l₁ b) (pullU E _ (w.s (a, b))) * res (l₂ b) (w'.s (fun _ => b, c)), fun Z f z b hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f z (l₁ b) hz _).trans (gm_pull f E z _ (l₁ b hz) _)) (gm_res f z (l₂ b) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨b, hb⟩ := exists_chart hM' (E x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, (hW b x).2 ⟨hx.1, hb, hx.2⟩⟩) u (fun b b' x hx => by
        have h₁ := (hW b x).1 hx.1
        have h₂ := (hW b' x).1 hx.2
        have ha := mem_wchart_comp.1 h₁.1
        have e₁ := hw _ (𝟙 X'' ≫ E) x a a b b' ha ha h₁.2.1 h₂.2.1
        have e₂ := hw' _ (𝟙 X'') x b b' c c h₁.2.1 h₂.2.1 h₁.2.2 h₁.2.2
        rw [Finset.prod_eq_one fun i _ => gm_self hM ((𝟙 X'' ≫ E) ≫ pr i) x (Set.mem_iInter.1 ha i)] at e₁
        rw [gm_self hM'' (𝟙 X'') x h₁.2.2] at e₂
        rw [hu _ (𝟙 X'') x b hx.1, hu _ (𝟙 X'') x b' hx.2, e₁, e₂, _root_.one_mul, inv_one, _root_.mul_one,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z f z b ha hb hc => ?_⟩
    have hz := (hW b (f z)).2 ⟨ha, hb, hc⟩
    exact (gm_res f z (l₀ b) hz s).symm.trans ((congrArg (gm f z (W b)) (hs b)).trans (hu Z f z b hz))
  choose s hs using glue
  let w'' : LB.Iso M'' (LB.LinComb M (fun i => E ≫ pr i) (fun _ => 1)) := ⟨fun p => s p.1 p.2⟩
  have T : ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z) (a : Fin j → M.ι) (b : M'.ι) (c : M''.ι),
      f z ∈ LB.wchart M (fun i => E ≫ pr i) a → E (f z) ∈ M'.U b → f z ∈ M''.U c →
      bw w'' f z a c = bw w (f ≫ E) z a b * gw w' f z b c := fun Z f z a b c ha hb hc => hs a c Z f z b ha hb hc
  refine ⟨w'', (isGen_box w'').2 fun Z f z a a' c c' ha ha' hc hc' => ?_, T⟩
  obtain ⟨b, hb⟩ := exists_chart hM' (E (f z))
  have e₁ := hw _ (f ≫ E) z a a' b b ((mem_wchart_comp (E := E)).1 ha) ((mem_wchart_comp (E := E)).1 ha') hb hb
  have e₂ := hw' _ f z b b c c' hb hb hc hc'
  rw [gm_self hM' (f ≫ E) z hb] at e₁ e₂
  rw [T Z f z a b c ha hb hc, T Z f z a' b c' ha' hb hc', e₁, e₂, inv_one, _root_.mul_one, _root_.one_mul,
    _root_.mul_mul_mul_comm]
  simp only [Category.assoc]
end GlobalTheory.PowAlongIso

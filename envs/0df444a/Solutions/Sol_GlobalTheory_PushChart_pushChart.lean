-- Prove2me | solution 1 for GlobalTheory.PushChart.pushChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:47.81221+00:00
-- url     : https://prove2.me/submissions/84eab816-c366-4f09-aaed-574ce9e0e881

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PushChart
import Theorems.Thm_GlobalTheory_PushChart_isCombAtG_comp
import Theorems.Thm_GlobalTheory_PushChart_isUnivJ_comp
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_GlobalTheory_T_exists_groupIso_cubicalIso_of_tripleMap_id


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.PushChart
namespace GlobalTheory.PushChart
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), ∃ x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G, (∀ m, (x' m).left = (x m).left ≫ n.φ) ∧ (GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x') ∧ (∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V), IsChartG t (𝟙 (Sp V)) d F act tg uv x → IsChartG t' (𝟙 (Sp V)) d F act (fun l => tg l ≫ n.φ) uv x') ∧ ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u (v ≫ n.φ) := by
  intro E _ _ _ H V _ t t' n d x
  obtain ⟨ψ, hl, hmon, hact, -⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  have hc : ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v →
      IsCombAtG t' (𝟙 (Sp V)) (dirs fun m => x m ≫ ψ.hom) u (v ≫ n.φ) := by
    intro u v h
    rw [← hl]
    refine isCombAtG_comp ψ.hom _ (fun i => ?_) h
    simp only [dirs, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  refine ⟨fun m => x m ≫ ψ.hom, fun m => ?_, fun h => isUnivJ_comp ψ h, ?_, hc⟩
  · rw [Over.comp_left, hl]
  · intro F act κ _ tg uv h
    refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun l => hc _ _ (h.tan l), h.basis⟩
    · rw [← Category.assoc, h.zero, MonObj.one_comp]
    · rw [← Category.assoc, h.trunc]
    · rw [← Category.assoc, h.law, MonObj.mul_comp]
      simp only [jptG, Category.assoc]
    · rw [Category.assoc, ← hact, ← Category.assoc, h.act, Category.assoc]
end GlobalTheory.PushChart

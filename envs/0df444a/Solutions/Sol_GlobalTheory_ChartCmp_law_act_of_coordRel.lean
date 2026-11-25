-- Prove2me | solution 1 for GlobalTheory.ChartCmp.law_act_of_coordRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:22:25.862403+00:00
-- url     : https://prove2.me/submissions/4159d0d2-5e76-4576-a7e8-715fb3661957

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_cc_ev
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_cc_comp1
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_eq_comp1_inv
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_jetSchemeMap_pointFamily_comp_singlePoint
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_jetSchemeMap_singlePoint_comp_singlePoint
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_eq_of_jetSchemeMap_singlePoint_universal
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_jptG_eq

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory.ChartCmp.CoordLaw
namespace GlobalTheory.ChartCmp
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by
  intro E _ _ _ H _ V _ t d B B' κ κ' _ _ tg tg' uv uv' x x' φ φi hc hc' hu hinv hrel
  have hφ := hinv.1
  have hr : ∀ m, x' m = sub1 m φ ≫ x m := hrel
  have hpt : ∀ (j : Fin 2) i, MvPowerSeries.constantCoeff (pt V d j i) = 0 := fun j i => MvPowerSeries.constantCoeff_X _
  refine ⟨?_, fun a => ?_⟩
  · let A : Fin 2 → Pt V 2 d := ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)]
    have hA : ∀ j i, MvPowerSeries.constantCoeff (A j i) = 0 := by
      intro j i
      fin_cases j <;> exact cc_comp1 hφ (hpt _) i
    have hX : ∀ j, (fun i => ev A (pt V d j i)) = A j := fun j => funext fun i =>
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 2 × Fin d => hA p.1 p.2) (j, i)
    have key : comp1 φ B'.G.F = addOf B.G.F (comp1 φ (pt V (n := 2) d 0)) (comp1 φ (pt V (n := 2) d 1)) := by
      refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ B'.G.const) (fun i => cc_ev A hA _ (B.G.const i)) fun m => ?_
      have l : sub1 m B.G.F ≫ x m = _ := hc.law m
      have l' : sub1 m B'.G.F ≫ x' m = _ := hc'.law m
      have l2 := congrArg (fun f => sub m A ≫ f) l
      simp only [jptG_eq, MonObj.comp_mul, ← Category.assoc, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA B.G.const, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA (hpt _),
        hX] at l2
      simp only [jptG_eq, hr m, ← Category.assoc, jetSchemeMap_singlePoint_comp_singlePoint m _ φ B'.G.const hφ, jetSchemeMap_singlePoint_comp_singlePoint m _ φ (hpt _) hφ] at l'
      exact l'.trans l2.symm
    exact fun i => congrFun (eq_comp1_inv hinv B'.G.const key) i
  · refine eq_comp1_inv hinv (B'.A.const a) ?_
    refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ (B'.A.const a)) (cc_comp1 (B.A.const a) hφ) fun m => ?_
    have l : x m ≫ t.act.act a = sub1 m (B.A.act a) ≫ x m := hc.act m a
    have l' : x' m ≫ t.act.act a = sub1 m (B'.A.act a) ≫ x' m := hc'.act m a
    rw [← jetSchemeMap_singlePoint_comp_singlePoint m _ φ (B'.A.const a) hφ, ← jetSchemeMap_singlePoint_comp_singlePoint m φ _ hφ (B.A.const a), Category.assoc, Category.assoc, ← hr m,
      ← l', ← l, hr m, Category.assoc]
end GlobalTheory.ChartCmp

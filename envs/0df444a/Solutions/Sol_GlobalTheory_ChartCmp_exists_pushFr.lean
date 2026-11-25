-- Prove2me | solution 1 for GlobalTheory.ChartCmp.exists_pushFr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:20.150158+00:00
-- url     : https://prove2.me/submissions/23b99125-08b8-4e9b-a12c-421e1b66f2f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CarriesLinCombGeneratorCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPushFr
import Theorems.Thm_GlobalTheory_ChartCmp_exists_corr_of_family_eq
import Theorems.Thm_GlobalTheory_T_carriesLinCombGenerator_calculus
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
open GlobalTheory GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), w.IsGen → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m, PushFr n w x x' e e' := by
  intro E _ _ _ H V _ t t' n w d x x' e hw hx he
  obtain ⟨ψ, hψ, hmon, -⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  haveI : IsIso n.φ := by
    rw [← hψ]
    exact inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have hcar := (GlobalTheory.T.carriesLinCombGenerator_calculus _ _ t.PP.L t'.PP.L n.φ w t.PP.isLB t'.PP.isLB hw).1
  have hx' : ∀ m, x' m = x m ≫ ψ.hom := fun m => by
    ext1
    rw [hx, Over.comp_left, hψ]
  have hfam : ∀ m, (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) =
      cφG t' ![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] := fun m => by
    funext J
    have hv : (![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] : Fin 2 → _) =
        fun k => (![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] : Fin 2 → _) k ≫ ψ.hom := by
      funext k
      fin_cases k <;> simp [jptG, hx']
    rw [hv]
    simp only [cφG, psum]
    rw [← hψ, ← Over.comp_left, foldr_padd_comp]
  have key : ∀ m, ∃ e' : FrTyG t' (𝟙 (Sp V)) d x' m, e'.IsGen ∧ ∃ c : LB.Gen (LB.LinComb t'.PP.L
      (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) (cε 2)),
      c.IsGen ∧ LB.Gen.Corr t'.PP.L _ _ _ _ c e' ∧
      Carries t'.PP.L n.φ w (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)])
        (cε 2) (e m) c := fun m => by
    obtain ⟨c, hc, hcc⟩ := hcar _ _
      (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)]) (cε 2) (e m) (he m)
    obtain ⟨e', he', hce⟩ := exists_corr_of_family_eq t'.PP.L (hfam m) (cε 2) c hc
    exact ⟨e', he', c, hc, hce, hcc⟩
  choose e' he' using key
  exact ⟨e', he'⟩
end GlobalTheory.ChartCmp

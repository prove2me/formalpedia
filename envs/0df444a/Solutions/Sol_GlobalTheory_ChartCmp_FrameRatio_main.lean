-- Prove2me | solution 1 for GlobalTheory.ChartCmp.FrameRatio.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:49.097417+00:00
-- url     : https://prove2.me/submissions/3886ea87-587e-44e2-8b24-7298caba85b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetFramesDifferByUnitEachOrder
import Theorems.Thm_GlobalTheory_ChartCmp_FrameRatio_exists_corr_scaled
import Theorems.Thm_P2M_GlobalTheory_ChartCmp_FrameRatio_comp_psum__249d30ba0974
import Theorems.Thm_P2M_GlobalTheory_ChartCmp_FrameRatio_unit__surj_a33959c60320
import Theorems.Thm_GlobalTheory_ChartCmp_FrameRatio_psJet_surj
import Theorems.Thm_GlobalTheory_ChartCmp_FrameRatio_copy_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_jetAug_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen


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
open Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.FrameRatio
namespace GlobalTheory.ChartCmp.FrameRatio
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → ∀ m, ∃ ε : PS V 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧ FrRel t x x' e e' φ m ε := by
  intro E _ _ _ H V _ t d x x' e e' φ _ hc he he' m
  let ψ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V :=
    ![fun j => psIn d m ![0] (φ j), fun j => psIn d m ![1] (φ j)]
  have hpt : ∀ i : Fin 2, (∀ j, ψ i j = psIn d m ![i] (φ j)) → jptG t (𝟙 (Sp V)) d x' m i =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2) ≫ jptG t (𝟙 (Sp V)) d x m i := by
    intro i hi
    rw [jptG, jptG, hc m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp,
      copy_subst d m φ ψ i hi]
  have hfam : cφG t ![jptG t (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x' m (1 : Fin 2)] =
      fun I => (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2)).left ≫
        cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I := by
    funext I
    rw [cφG, cφG, ← Over.comp_left, comp_psum']
    congr 2
    funext k
    fin_cases k
    · exact hpt 0 fun _ => rfl
    · exact hpt 1 fun _ => rfl
  obtain ⟨U, hU⟩ := exists_corr_scaled t.PP.L t.PP.isLB _ _ hfam (cε 2) (e' m)
    (peG t (𝟙 (Sp V)) d x e m ψ) (he' m) (DVR.pullGen_isGen _ _ _ _ (he m) _)
  obtain ⟨u, rfl⟩ := unitΓ_surj U
  obtain ⟨ε, hε⟩ := psJet_surj m (u : Jet V (Fin 2 × Fin d) m)
  refine ⟨ε, ?_, u, hε.symm, hU⟩
  rw [← GaugeR.jetAug_psJet m ε, hε]
  exact u.isUnit.map _
end GlobalTheory.ChartCmp.FrameRatio

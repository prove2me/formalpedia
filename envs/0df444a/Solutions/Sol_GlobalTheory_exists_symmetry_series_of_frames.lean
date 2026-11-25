-- Prove2me | solution 1 for GlobalTheory.exists_symmetry_series_of_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:00.182432+00:00
-- url     : https://prove2.me/submissions/f042710c-c0fd-4389-b819-11caed98a6b7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSymmetrySeriesOfFrames
import Theorems.Thm_GlobalTheory_FrameSymmetry_pt_sub
import Theorems.Thm_GlobalTheory_FrameSymmetry_pt_X
import Theorems.Thm_GlobalTheory_FrameSymmetry_pe_pt
import Theorems.Thm_GlobalTheory_FrameSymmetry_prod_cube2_swap
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_exists_series
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_pe_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameSymmetry
set_option maxHeartbeats 4000000
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ sy : PS S 2 d, ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (e m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])) := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ _ e he htr _
  have hBt : ∀ m y J, Good t.PP.L y J →
      val (peG t x0 d x e (m + 1) ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]) (ρn x0 d 2 m).left y J =
        val (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]) (𝟙 _) y J :=
    fun m y J hJ => pe_trunc t x0 d htr (fun _ => ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])
      (fun _ _ _ => by rw [sub_self]; exact zero_mem _) m y J hJ
  have hAt : ∀ m y J, Good t.PP.L y J → val (e (m + 1)) (ρn x0 d 2 m).left y J = val (e m) (𝟙 _) y J := by
    intro m y J hJ
    have h1 := val_corr hJ (htr m) (𝟙 _)
    have h2 := val_pull hJ (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left (𝟙 _)
    rw [Category.id_comp] at h2
    exact h2.symm.trans h1
  have hF : ∀ m, FormEq (fun I : ULift.{0} (Finset (Fin 2)) =>
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) (cε 2)
      (fun I => (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
          p.1 p.2)).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) (cε 2) := by
    intro m U _ h
    have hs0 : homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
          p.1 p.2) ≫ jptG t x0 d x m (0 : Fin 2) = jptG t x0 d x m (1 : Fin 2) :=
      (pt_sub m _ 0).trans (pt_X m 1)
    have hs1 : homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
          p.1 p.2) ≫ jptG t x0 d x m (1 : Fin 2) = jptG t x0 d x m (0 : Fin 2) :=
      (pt_sub m _ 1).trans (pt_X m 0)
    simp only [pe_pt]
    refine ((prod_cube2_swap (fun g : jOG x0 d m 2 ⟶ t.G => h g.left)
      ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]).trans ?_).trans
      (prod_cube2_swap (fun g : jOG x0 d m 2 ⟶ t.G => h g.left) _).symm
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hs0, hs1, _root_.mul_one]
    rw [_root_.mul_comm (jptG t x0 d x m 0) (jptG t x0 d x m 1)]
    ac_rfl
  obtain ⟨ph, hph⟩ := exists_series t x0 d _ (cε 2) _ (cε 2)
    (fun m => peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (he m) _) e he (fun m U _ h => (hF m U h).symm) hBt hAt
  refine ⟨ph, fun m => ?_⟩
  obtain ⟨u, hu, hc⟩ := hph m
  refine ⟨u, hu, corr_of_val t.PP.isLB fun y J hJ => ?_⟩
  rw [val_scale t _ _ _ _ _ _ _ hJ, val_corr hJ hc (𝟙 _)]
  have k1 := val_scale t _ _ (unitΓ u) (e m) (𝟙 (jOG x0 d m 2).left) y J hJ
  refine Eq.trans ?_ (congrArg (fun v => gm (𝟙 (jOG x0 d m 2).left) y ⊤ (unitΓ u⁻¹) * v) k1.symm)
  have k2 : unitΓ u⁻¹ * unitΓ u = 1 := by
    unfold unitΓ
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [← _root_.mul_assoc, ← map_mul]
  simp only [k2, map_one, _root_.one_mul]
end GlobalTheory

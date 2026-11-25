-- Prove2me | solution 1 for GlobalTheory.exists_firstPartialLaw_series_of_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:56.479801+00:00
-- url     : https://prove2.me/submissions/1b47e217-baf4-4234-9fa2-9f3ccb5d88e0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSymmetrySeriesOfFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFirstPartialLawSeriesOfFrames
import Theorems.Thm_GlobalTheory_FramePartialLaw_pt_law
import Theorems.Thm_GlobalTheory_FramePartialLaw_th_pt
import Theorems.Thm_GlobalTheory_FramePartialLaw_threePts_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_exists_series
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_pe_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_prod_cube2
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_prod_cube3
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_psIn_succ_sub
import Theorems.Thm_GlobalTheory_FrameSymmetry_ofMul_eq
import Theorems.Thm_GlobalTheory_FrameSymmetry_pe_pt
import Theorems.Thm_GlobalTheory_FrameSymmetry_pt_X
import Theorems.Thm_GlobalTheory_FrameSymmetry_pt_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameSymmetry GlobalTheory.FramePartialLaw
set_option maxHeartbeats 4000000
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ph1 : PS S 3 d, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))) := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch e heg htr _
  have hL := t.PP.isLB
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x e m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  have hB3 : ∀ (φ1 φ2 φ3 : ℕ → Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S),
      (∀ m i j, φ1 (m + 1) i j - φ1 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ2 (m + 1) i j - φ2 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ3 (m + 1) i j - φ3 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      ∀ m y J, Good t.PP.L y J →
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e (m + 1) (φ1 (m + 1)))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e (m + 1) (φ2 (m + 1))))
            (LB.invGen t.PP.L _ _ (peG t x0 d x e (m + 1) (φ3 (m + 1)))))) (ρn x0 d 3 m).left y J =
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m (φ1 m))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m (φ2 m)))
            (LB.invGen t.PP.L _ _ (peG t x0 d x e m (φ3 m))))) (𝟙 _) y J := by
    intro φ1 φ2 φ3 h1 h2 h3 m y J hJ
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, val_mul hJ, val_mul hJ, val_inv, val_inv,
      pe_trunc t x0 d htr φ1 h1 m y J hJ, pe_trunc t x0 d htr φ2 h2 m y J hJ, pe_trunc t x0 d htr φ3 h3 m y J hJ]
  obtain ⟨ph, hph⟩ := exists_series t x0 d (n := 3) _ _ _ _
    (fun m => LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (threePts (x := x) m 0 1 2).left)
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ t.cub.isGen _)
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (LB.mulGen t.PP.L _ _ _ _
        (LB.invGen t.PP.L _ _ (peG t x0 d x e m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))
        (LB.invGen t.PP.L _ _ (peG t x0 d x e m
          ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hpe m _) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _)) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _))))
    (fun m U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, th_pt, pe_pt, pt_sub, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_law hch, zpow_neg, Finset.prod_inv_distrib]
      erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      rw [prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
        prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      have ha : jptG t x0 d x m (0 : Fin 3) * jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) =
          jptG t x0 d x m (0 : Fin 3) * (jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3)) := _root_.mul_assoc _ _ _
      apply ofMul_eq
      simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
      erw [ha]
      abel!)
    (fun m y J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J) (threePts_trunc hch m 0 1 2)).trans
      (val_pull hJ _ _ _).symm))
    (fun m y J hJ => hB3 (fun m => ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX m _ j])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
  exact ⟨_, hph⟩
end GlobalTheory

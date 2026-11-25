-- Prove2me | solution 1 for GlobalTheory.ThetaLeast.nabValN_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:38.804403+00:00
-- url     : https://prove2.me/submissions/75a49be3-8a05-4672-9291-03dee9978d32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers
import Theorems.Thm_GlobalTheory_GaugeBaseChange_gp_actK
import Theorems.Thm_GlobalTheory_GaugeBaseChange_map_ev_two
import Theorems.Thm_GlobalTheory_GaugeBaseChange_map_expS
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_comp1
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_map_ev
import Theorems.Thm_GlobalTheory_dpolyN_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange
namespace GlobalTheory.ThetaLeast
theorem _root_.solution (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] [Algebra S S']
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (h : PS S 2 d)
    (hc : MvPowerSeries.constantCoeff h = 0) (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) :
    nabValN B S' (MvPowerSeries.map (algebraMap S S') h) w0 m (MvPowerSeries.map (algebraMap S S') f) cp
      (fun l j => algebraMap S S' (u l j)) (MvPolynomial.map (algebraMap S S') P) =
      algebraMap S S' (nabValN B S h w0 m f cp u P) := by
  set ψ := algebraMap S S' with hψ
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S S') (B.G.F i)
    ext e
    simp [coeff_map, hψ]
  have eA : mapP ψ (B.actK S w0) = B.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S S') (B.A.act w0 i)
    ext e
    simp [coeff_map, hψ]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN
  rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
    map_expS _ _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
    Finset.sum_congr rfl fun b _ => eb b]
end GlobalTheory.ThetaLeast

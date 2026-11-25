-- Prove2me | solution 1 for GlobalTheory.TwistCheck.additive_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:49.60886+00:00
-- url     : https://prove2.me/submissions/b6d9ab46-cb95-4226-ab9a-39042c09bac3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_BilLActRight
import Theorems.Thm_GlobalTheory_TwistCheck_cc_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czFF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czSw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_d_evF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_d_evY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_eq_C_of_pderiv_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ez_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_mul_om
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_logOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_second_ev_first_point_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply


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
open GlobalTheory GlobalTheory.TwistCheck
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace GlobalTheory.TwistCheck
theorem _root_.solution (G : FGLaw S d) (g : PS S 1 d)
    (hg : ev (n := 2) ![G.F] g = ev (n := 2) ![pt S d 0] g + ev (n := 2) ![pt S d 1] g) :
    g = ∑ j, C (constantCoeff (pderiv S ((0 : Fin 1), j) g)) * logOf G j := by
  have hx : ∀ h : PS S 1 d, ev (n := 1) ![pt S d 0, 0] (ev (n := 2) ![G.F] h) = h := by
    intro h
    rw [ev_ev cz1 (czFF G)]
    have : (fun j i => ev (n := 1) ![pt S d 0, 0] ((![G.F] : Fin 1 → Pt S 2 d) j i)) = fun j => pt S (n := 1) d j := by
      funext j i
      fin_cases j
      show ev (n := 1) ![pt S d 0, 0] (G.F i) = X ((0 : Fin 1), i)
      rw [← G.unit i]
      conv_lhs => rw [← G.comm i, ev_ev cz1 czSw]
      congr 1
      funext j c
      fin_cases j <;> simp [pt_apply, ev_X cz1]
    rw [this, ev_pt]
  have h1 : ∀ b, ∑ e, pderiv S ((0 : Fin 1), e) g * Jac G e b = C (constantCoeff (pderiv S ((0 : Fin 1), b) g)) := by
    intro b
    have := congrArg (fun f => ev (n := 1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), b) f)) hg
    simp only [map_add, d_evF, pderiv_second_ev_first_point_eq_zero, d_evY, zero_add, ez_y, ev_sum cz1, ev_mul cz1, hx] at this
    exact this
  have h2 : ∀ a, pderiv S ((0 : Fin 1), a) g =
      ∑ b, C (constantCoeff (pderiv S ((0 : Fin 1), b) g)) * Om G b a := by
    intro a
    have e1 : pderiv S ((0 : Fin 1), a) g = ∑ e, pderiv S ((0 : Fin 1), e) g * (JM G * Om G) e a := by
      rw [mul_om]; simp [Matrix.one_apply]
    rw [e1]
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← h1 b, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [JM, Matrix.of_apply]; ring
  have h0 : constantCoeff g = 0 := by
    have := congrArg constantCoeff hg
    rw [map_add, cc_ev (czFF G), cc_ev czX, cc_ev czY] at this
    simpa using this
  rw [← sub_eq_zero]
  have hd : ∀ v, pderiv S v (g - ∑ j, C (constantCoeff (pderiv S ((0 : Fin 1), j) g)) * logOf G j) = 0 := by
    rintro ⟨j, c⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [map_sub, map_sum, h2 c, sub_eq_zero]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul, pderiv_logOf]
  rw [eq_C_of_pderiv_zero hd]
  simp [h0, cc_log]
end GlobalTheory.TwistCheck

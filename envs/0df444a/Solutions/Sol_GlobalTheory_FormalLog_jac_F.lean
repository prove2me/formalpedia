-- Prove2me | solution 1 for GlobalTheory.FormalLog.jac_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:12.856945+00:00
-- url     : https://prove2.me/submissions/d1d29fd3-0a0e-43d6-b3de-70539119b325

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Theorems.Thm_GlobalTheory_FormalLog_cc_pt
import Theorems.Thm_GlobalTheory_FormalLog_CZ_nil
import Theorems.Thm_GlobalTheory_FormalLog_CZ_cons
import Theorems.Thm_GlobalTheory_FormalLog_pt_apply
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev_zero
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_pt
import Theorems.Thm_GlobalTheory_FormalLog_cz1
import Theorems.Thm_GlobalTheory_FormalLog_czZ
import Theorems.Thm_GlobalTheory_FormalLog_czFF
import Theorems.Thm_GlobalTheory_FormalLog_cz01
import Theorems.Thm_GlobalTheory_FormalLog_cz12
import Theorems.Thm_GlobalTheory_FormalLog_formal_ev_second_point_of_x_zero
import Theorems.Thm_GlobalTheory_FormalLog_ev_z_yz
import Theorems.Thm_GlobalTheory_FormalLog_formalGroupLaw_ev_y_zero
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_ev_X
import Theorems.Thm_GlobalTheory_FormalLog_ev_ev
import Theorems.Thm_GlobalTheory_FormalLog_ev_mul
import Theorems.Thm_GlobalTheory_FormalLog_ev_pt
import Theorems.Thm_GlobalTheory_FormalLog_ev_sum
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev
import Theorems.Thm_P2M_GlobalTheory_FormalLog_ev_zero__96b7e70e62c8


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution (i b : Fin d) :
    ev (n := 2) ![G.F] (Jac G i b) = ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  set aL : Fin 2 → Pt k 3 d := ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] with haL
  set aR : Fin 2 → Pt k 3 d := ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] with haR
  have hL : CZ aL := CZ.cons (fun l => constantCoeff_ev cz01 (G.const l)) (CZ.cons (cc_pt 2) CZ.nil)
  have hR : CZ aR := CZ.cons (cc_pt 0) (CZ.cons (fun l => constantCoeff_ev cz12 (G.const l)) CZ.nil)
  have dL : pderiv k ((2 : Fin 3), b) (ev aL (G.F i)) = ev aL (pderiv k ((1 : Fin 2), b) (G.F i)) := by
    rw [pderiv_ev hL, Fintype.sum_prod_type, Fin.sum_univ_two]
    have h0 : ∀ c, pderiv k ((2 : Fin 3), b) (aL 0 c) = 0 := fun c =>
      pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
    simp only [h0, mul_zero, Finset.sum_const_zero, zero_add]
    simp [haL, pderiv_pt]
  have dR : pderiv k ((2 : Fin 3), b) (ev aR (G.F i)) = ∑ c, ev aR (pderiv k ((1 : Fin 2), c) (G.F i)) *
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (G.F c)) := by
    rw [pderiv_ev hR, Fintype.sum_prod_type, Fin.sum_univ_two]
    have h0 : ∀ c, pderiv k ((2 : Fin 3), b) (aR 0 c) = 0 := fun c => by simp [haR, pderiv_pt]
    have h1 : ∀ c, pderiv k ((2 : Fin 3), b) (aR 1 c) =
        ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (G.F c)) := fun c => by
      simp only [haR, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
      simp [pderiv_pt]
    simp only [h0, h1, mul_zero, Finset.sum_const_zero, zero_add]
  have h := congrArg (fun g => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b) g)) (G.assoc i)
  beta_reduce at h
  rw [dL, dR, ev_sum czZ] at h
  have eL : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev aL g) = ev (n := 2) ![G.F, 0] g := by
    intro g
    rw [ev_ev czZ hL]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 0, pt k d 1] (G.F c)) = G.F c
      rw [ev_ev czZ cz01]
      have : (fun j c => ev (n := 2) ![pt k d 0, pt k d 1, 0] ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j c)) =
          fun j => pt k (n := 2) d j := by
        funext j c; fin_cases j <;> simp [pt_apply, ev_X czZ]
      rw [this, ev_pt]
    · simp [haL, pt_apply, ev_X czZ]
  have eR : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev aR g) = g := by
    intro g
    rw [ev_ev czZ hR]
    conv_rhs => rw [← ev_pt g]
    congr 1
    funext j c
    fin_cases j
    · simp [haR, pt_apply, ev_X czZ]
    · show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (G.F c)) = X ((1 : Fin 2), c)
      rw [ev_z_yz, formalGroupLaw_ev_y_zero]
  have eJ : ev (n := 2) ![G.F] (Jac G i b) = ev (n := 2) ![G.F, 0] (pderiv k ((1 : Fin 2), b) (G.F i)) := by
    rw [Jac, ev_ev (czFF G) cz1]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X (czFF G), ev_zero' (czFF G)]
  rw [eL, ← eJ] at h
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ev_mul czZ, eR, ev_z_yz, ← formal_ev_second_point_of_x_zero]
  rfl
end GlobalTheory.FormalLog

-- Prove2me | solution 1 for GlobalTheory.AnArc.perFactor_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:13:24.274693+00:00
-- url     : https://prove2.me/submissions/d1f3baea-bce1-4ba3-bd25-42ec74533065

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_ah_cocycle
import Theorems.Thm_GlobalTheory_AnArc_ah_add
import Theorems.Thm_GlobalTheory_AnArc_e_neg_div
import Theorems.Thm_GlobalTheory_AnArc_q_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (la la' : A.La) (v : A.V) :
    A.perFactor w (la + la') v = A.perFactor w la (v + A.Pw w la') * A.perFactor w la' v := by
  have h1 : (v + A.Pw w la').1 la.y = v.1 la.y + A.T la.y la'.y + la'.n la.y +
      -(A.H (A.ct la.y) la'.l / (2 * Complex.I)) + w * A.be la.y la'.y := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, Pw_fst_apply, A.T_symm, A.be_symm]; ring
  have h2 : (v + A.Pw w la').2 + A.ct la.y = v.2 + A.ct (la.y + la'.y) + la'.l := by
    simp only [Prod.snd_add, Pw_snd, map_add]; abel
  have h3 : v.2 + A.ct (la.y + la'.y) = v.2 + A.ct la'.y + A.ct la.y := by rw [map_add]; abel
  have h4 : A.ah la'.l (v.2 + A.ct (la.y + la'.y)) =
      A.ah la'.l (v.2 + A.ct la'.y) * Complex.exp (Real.pi * A.H (A.ct la.y) la'.l) := by rw [h3, ah_add]
  rw [perFactor, perFactor, perFactor, ← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, h1, h2, La.add_l, La.add_y, ah_cocycle, h4, psi_add, q_add, map_add v.1]
  push_cast
  simp only [mul_add, e_add, e_intCast, e_neg_div, Complex.exp_neg]
  have := e_ne_zero
  have := Complex.exp_ne_zero (Real.pi * A.H (A.ct la.y) la'.l)
  have := (A.psi la.y).ne_zero
  have := (A.psi la'.y).ne_zero
  field_simp
end GlobalTheory.AnArc

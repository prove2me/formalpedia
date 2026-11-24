-- Prove2me | solution 1 for GlobalTheory.FormalLog.cc_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:07:54.918782+00:00
-- url     : https://prove2.me/submissions/eafd67a9-0c03-4db0-9967-97d2717f777b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_cc_ev
import Theorems.Thm_GlobalTheory_FormalLog_formalFamilyConstantCoeffZero_zero_secondVar
import Theorems.Thm_GlobalTheory_FormalLog_cz1
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_pt


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
theorem _root_.solution (i b : Fin d) : constantCoeff (Jac G i b) = if i = b then 1 else 0 := by
  rw [Jac, cc_ev cz1, ← cc_ev formalFamilyConstantCoeffZero_zero_secondVar]
  have h := congrArg (pderiv k ((0 : Fin 1), b)) (G.unit i)
  rw [pderiv_ev formalFamilyConstantCoeffZero_zero_secondVar, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, zero_add, pderiv_pt] at h
  simp only [Fin.isValue, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  rw [h, pderiv_X]
  simp [Pi.single_apply, eq_comm]
end GlobalTheory.FormalLog

-- Prove2me | solution 1 for GlobalTheory.FormalLog.om_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:50.177797+00:00
-- url     : https://prove2.me/submissions/c017d450-ed8f-4456-a1a1-2470b83caa77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_mul_om
import Theorems.Thm_GlobalTheory_FormalLog_om_key


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution (i a c : Fin d) :
    pderiv k ((0 : Fin 1), c) (Om G i a) = pderiv k ((0 : Fin 1), a) (Om G i c) := by
  set M : Fin d → PS k 1 d := fun e => pderiv k ((0 : Fin 1), e) (Om G i a) - pderiv k ((0 : Fin 1), a) (Om G i e)
    with hMdef
  have hM : ∀ b, ∑ e, M e * Jac G e b = 0 := by
    intro b
    simp only [hMdef, sub_mul, Finset.sum_sub_distrib]
    rw [← om_key G i a b]
    simp only [mul_comm, sub_self]
  have h1 : M c = ∑ e, M e * (JM G * Om G) e c := by
    rw [mul_om]
    simp [Matrix.one_apply]
  have h2 : ∑ e, M e * (JM G * Om G) e c = 0 := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hM b
    simp only [JM, Matrix.of_apply]
    rw [show ∑ x, M x * (Jac G x b * Om G b c) = (∑ x, M x * Jac G x b) * Om G b c by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring, this, zero_mul]
  have h3 : M c = 0 := h1.trans h2
  exact sub_eq_zero.1 h3
end GlobalTheory.FormalLog

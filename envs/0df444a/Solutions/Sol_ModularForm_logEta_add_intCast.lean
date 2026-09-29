-- Prove2me | solution 1 for ModularForm.logEta_add_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6e5843fe-3277-5e94-abad-a4de35729541

import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_logEta_add_intCast

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

theorem logEta_add_int (z : ℂ) (m : ℤ) : logEta (z + m) = logEta z + π * I * m / 12 := by
  have hq : ∀ n : ℕ, ModularForm.eta_q n (z + m) = ModularForm.eta_q n z := by
    intro n
    rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp,
      show 2 * π * I * (n + 1) * (z + m) = 2 * π * I * (n + 1) * z + ((n + 1) * m : ℤ) * (2 * π * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [logEta, hq]
  ring

end DedekindEtaLog

end

theorem solution (z : ℂ) (m : ℤ) : (Real.pi * Complex.I * (z + m) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z + m))) = (Real.pi * Complex.I * z / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n z)) + Real.pi * Complex.I * m / 12 :=
  DedekindEtaLog.logEta_add_int z m

end S_ModularForm_logEta_add_intCast
end P2MW
export P2MW.S_ModularForm_logEta_add_intCast (solution)

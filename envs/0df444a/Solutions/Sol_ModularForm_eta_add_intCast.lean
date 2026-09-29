-- Prove2me | solution 1 for ModularForm.eta_add_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/effe6a10-1fb6-53c9-b70b-5096d9a13982

import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_eta_add_intCast

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real

namespace DedekindEtaLaw

lemma eta_add_int (z : ℂ) (m : ℤ) : η (z + m) = cexp (π * I * m / 12) * η z := by
  unfold ModularForm.eta
  have hq : Function.Periodic.qParam 24 (z + m) = cexp (π * I * m / 12) * Function.Periodic.qParam 24 z := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp : (fun n => 1 - ModularForm.eta_q n (z + m)) = fun n => 1 - ModularForm.eta_q n z := by
    funext n
    rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp]
    congr 1
    rw [show 2 * π * I * (n + 1) * (z + m) = 2 * π * I * (n + 1) * z + ((n + 1) * m : ℤ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  rw [hq, hp]
  ring

end DedekindEtaLaw

end

theorem solution (z : ℂ) (m : ℤ) : ModularForm.eta (z + m) = Complex.exp (Real.pi * Complex.I * m / 12) * ModularForm.eta z :=
  DedekindEtaLaw.eta_add_int z m

end S_ModularForm_eta_add_intCast
end P2MW
export P2MW.S_ModularForm_eta_add_intCast (solution)

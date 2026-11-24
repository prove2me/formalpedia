-- Prove2me | solution 1 for NFOne.cols_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:01:28.528476+00:00
-- url     : https://prove2.me/submissions/8e505669-30f5-4be5-aa2b-91353f913223

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Theorems.Thm_NFOne_P_colX
import Theorems.Thm_NFOne_sg_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] NFOne.sg_val



set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (1 + Pm k r j V) *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  funext p
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  have h : (Pm k r j V *ᵥ bvec (eI k r a)) p = 0 := by
    rw [show (Pm k r j V *ᵥ bvec (eI k r a)) p = ∑ q, Pm k r j V p q * bvec (eI k r a) q from rfl]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : q = eI k r a
    · subst hq
      rw [P_colX k r j V p _ a.isLt, zero_mul]
    · simp [bvec, Pi.single_apply, hq]
  rw [h, add_zero]
end NFOne

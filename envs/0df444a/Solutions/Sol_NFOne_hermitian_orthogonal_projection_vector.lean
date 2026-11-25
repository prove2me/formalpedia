-- Prove2me | solution 1 for NFOne.hermitian_orthogonal_projection_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:43.878202+00:00
-- url     : https://prove2.me/submissions/8435d7f2-737e-4fb1-92c3-f7b7f1bc315a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Theorems.Thm_NFOne_herm_Hpk_of_inWb_eq_sum_wI
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
theorem _root_.solution (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ)
    (z' : Fin (2 * r + k + 1) → ℂ) (hzy : ∀ a, herm (Hpk k r) z' (y a) = 0) (c : ℕ) :
    herm (Hpk k r) z' (Vv y N c) = 0 := by
  unfold Vv
  split_ifs with h
  · exact herm_Hpk_of_inWb_eq_sum_wI k r j y z' hzy _
  · simp [herm]
end NFOne

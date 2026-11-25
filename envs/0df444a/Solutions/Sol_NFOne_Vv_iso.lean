-- Prove2me | solution 1 for NFOne.Vv_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:41.810802+00:00
-- url     : https://prove2.me/submissions/ffdb5f93-b0c2-4cdf-b385-b5089a8a5456

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Theorems.Thm_NFOne_herm_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ)
    (hyy : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (b c : ℕ) (hb : b < j) (hc : c < j) :
    herm (Hpk k r) (Vv y N b) (Vv y N c) = 0 := by
  unfold Vv
  rw [dif_pos hb, dif_pos hc]
  exact herm_comb k r j y hyy _ _
end NFOne

-- Prove2me | solution 1 for NFOne.nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:12.356841+00:00
-- url     : https://prove2.me/submissions/c215ad4a-f2de-4887-967d-8e507458def3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Theorems.Thm_NFOne_nf_sum
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
theorem _root_.solution (k r j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (N : Matrix (Fin j) (Fin j) ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hMN : (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) * N = 1) (a : Fin j) :
    (1 + Pm k r j (Vv y N)) *ᵥ (fun q => if r + k < q.val then y a q else 0) = y a := by
  funext p
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, nf_sum k r j hj y N hy2 hMN a p]
  split_ifs <;> simp
end NFOne

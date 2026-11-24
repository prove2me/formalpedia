-- Prove2me | solution 1 for NFOne.y_esI_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:49:44.086005+00:00
-- url     : https://prove2.me/submissions/19b5f7cb-e917-4753-83e8-1f8ed24eb345

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
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
theorem _root_.solution (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (a : Fin j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) (hb : ¬ (sg k r q).val < j) :
    y a q = 0 := by
  have hq2 := q.isLt
  have hb' : (sg k r q).val < r := by simp only [sg_val]; omega
  have h := hy2 a ⟨(sg k r q).val, hb'⟩ (Nat.le_of_not_lt hb)
  have he : esI k r ⟨(sg k r q).val, hb'⟩ = q := by
    apply Fin.ext
    simp only [esI, sg_val]
    omega
  rw [he] at h
  exact h
end NFOne

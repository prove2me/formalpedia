-- Prove2me | solution 1 for NFOne.herm_Hpk_of_inWb_eq_sum_wI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:49:30.500897+00:00
-- url     : https://prove2.me/submissions/a8e01958-7dc1-45a6-ba0f-5ac7ed9a9ae1

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


section
open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
noncomputable section
namespace NFOne
private theorem herm_sum_smul_right' {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} [Fintype ι]
    (β : ι → ℂ) (v : Fin n → ℂ) (w : ι → Fin n → ℂ) :
    herm H v (∑ a, β a • w a) = ∑ a, star (β a) * herm H v (w a) := by
  unfold herm
  simp only [dotProduct, Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring
end NFOne
end
end

set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r + k + 1) → ℂ)
    (hzy : ∀ a, herm (Hpk k r) z' (y a) = 0) (β : Fin j → ℂ) :
    herm (Hpk k r) z' (∑ a, β a • y a) = 0 := by
  rw [herm_sum_smul_right']
  simp [hzy]
end NFOne

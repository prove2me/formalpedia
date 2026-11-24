-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.mem_GLint_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:37:42.875563+00:00
-- url     : https://prove2.me/submissions/65897a58-f79e-4d68-bfd8-bf2880487626

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_cartan_entries_of_mem
import Theorems.Thm_Formalism_UG_P_cartan_mem_of_entries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L)) {k : GL (Fin n) L} (hk : k ∈ UJ σ (J : Matrix (Fin n) (Fin n) L))
    (hi : ∀ i j, (k : Matrix (Fin n) (Fin n) L) i j ∈ intL L) : k ∈ GLint (Fin n) (intL L) := by
  refine P.cartan_mem_of_entries _ k hi ?_
  have hk' : cT σ (k : Matrix (Fin n) (Fin n) L) * J * k = J := hk
  have : ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ (k : Matrix (Fin n) (Fin n) L) * J) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [Matrix.mul_assoc, hk', Units.inv_mul]
  rw [this]
  intro i j
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun a _ => mul_mem (P.cartan_entries_of_mem _ _ (inv_mem hJ) _ _) ?_
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun b _ => mul_mem ?_ (P.cartan_entries_of_mem _ _ hJ _ _)
  show σ _ ∈ _
  rw [mem_int, hσ]; exact hi _ _
end GlobalTheory.UnitarySwap

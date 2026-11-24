-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.selfDual_intVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:30:47.292406+00:00
-- url     : https://prove2.me/submissions/7b6ccca0-7479-483c-8953-9a86df85396a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
import Theorems.Thm_GlobalTheory_UnitarySwap_form_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_mulVec_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_single_mem
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_cartan_entries_of_mem


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
    (hJ : J ∈ GLint (Fin n) (intL L)) :
    SelfDual (form σ (J : Matrix (Fin n) (Fin n) L)) ⊤ (intVec L n) := by
  intro v
  constructor
  · intro hv
    refine ⟨trivial, fun w hw => ?_⟩
    rw [form_apply]
    refine Subring.sum_mem _ fun i _ => mul_mem ?_ (mulVec_mem (P.cartan_entries_of_mem _ J hJ) hw i)
    rw [Function.comp_apply, mem_int, hσ]; exact hv i
  · rintro ⟨-, hv⟩ i
    have := hv _ (mulVec_mem (P.cartan_entries_of_mem _ J⁻¹ (inv_mem hJ)) (single_mem i))
    rw [form_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, dotProduct_single, mul_one,
      Function.comp_apply, mem_int, hσ] at this
    exact this
end GlobalTheory.UnitarySwap

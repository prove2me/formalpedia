-- Prove2me | solution 1 for GlobalTheory.BorelUMod.Cayley.cay_sub_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:58.985511+00:00
-- url     : https://prove2.me/submissions/0441433b-dddd-4232-b039-9343f7e45af7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_unit_mul_mem_iff
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_cay_eq
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.Cayley
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod.Cayley
theorem _root_.solution {c C : Fin n → Fin n → ℤ} (hc : IsWeight c) (hI : IsIdealWeight c C) {t : L}
    (ht : Valued.v t ≤ 1) {u u' : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) (hu' : u' - 1 ∈ upLat L c) :
    -cay t u + cay t u' ∈ upLat L C ↔ u' - u ∈ upLat L C := by
  obtain ⟨z, hz, e1, e2, e⟩ := cay_eq hc ht hu
  obtain ⟨z', hz', e1', e2', e'⟩ := cay_eq hc ht hu'
  rw [← unit_mul_mem_iff hc hI hz hz' (x := u' - u)]
  have hcomm : (1 + z') * (u' - 1) = (u' - 1) * (1 + z') := by
    have : (u' - 1) * (1 + t • (u' - 1)) = (1 + t • (u' - 1)) * (u' - 1) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    calc (1 + z') * (u' - 1) = (1 + z') * ((u' - 1) * (1 + t • (u' - 1))) * (1 + z') := by
          rw [mul_assoc, mul_assoc, e1', mul_one]
      _ = _ := by rw [this, ← mul_assoc, e2', one_mul]
  have key : u' - u = (1 + t • (u - 1)) * (u' - 1) - (u - 1) * (1 + t • (u' - 1)) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  have : (1 + z) * (u' - u) * (1 + z') = -cay t u + cay t u' := by
    rw [key, mul_sub, sub_mul, ← mul_assoc, e2, one_mul, mul_assoc, mul_assoc, e1', mul_one, e, e', hcomm]
    abel
  rw [this]
end GlobalTheory.BorelUMod.Cayley

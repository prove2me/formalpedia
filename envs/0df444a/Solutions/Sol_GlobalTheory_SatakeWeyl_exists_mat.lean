-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.exists_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:17:58.015974+00:00
-- url     : https://prove2.me/submissions/578d4014-d23b-4afc-96ce-c0db32d70be7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (M : Matrix (Fin n) (Fin n) L) (hM : cT σ M * antiJ L n * M = antiJ L n) :
    ∃ g : GU σ n, mat g = M := by
  have h : (antiJ L n * (cT σ M * antiJ L n)) * M = 1 := by
    rw [Matrix.mul_assoc, hM, GlobalTheory.UnitarySwap.antiJ_mul_self]
  exact ⟨⟨⟨M, _, mul_eq_one_comm.1 h, h⟩, hM⟩, rfl⟩
end GlobalTheory.SatakeWeyl

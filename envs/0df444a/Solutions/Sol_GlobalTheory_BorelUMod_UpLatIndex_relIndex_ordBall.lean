-- Prove2me | solution 1 for GlobalTheory.BorelUMod.UpLatIndex.relIndex_ordBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:53.946639+00:00
-- url     : https://prove2.me/submissions/688f99b3-9b10-4316-8f33-9bc2d7eb90aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_ordBall_mono
import Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_relIndex_ordBall_succ
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
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
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.UpLatIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod.UpLatIndex
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {k K : ℤ} (hk : k ≤ K) :
    (ordBall L K).relIndex (ordBall L k) = (q ^ 2) ^ (K - k).toNat := by
  obtain ⟨-, -, -, hϖ, -, -, hq⟩ := h
  obtain ⟨m, rfl⟩ := Int.le.dest hk
  have e : ∀ m : ℕ, (k + m - k).toNat = m := fun m => by omega
  rw [e]
  clear hk
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (ordBall L (k + m + 1)).relIndex (ordBall L (k + m)) = q ^ 2 :=
      (relIndex_ordBall_succ hϖ (k + m)).trans hq
    have h2 := AddSubgroup.relIndex_mul_relIndex (ordBall L (k + m + 1)) (ordBall L (k + m)) (ordBall L k)
      (ordBall_mono (by omega)) (ordBall_mono (by omega))
    rw [Nat.cast_succ, ← add_assoc, ← h2, h1, ih, pow_succ' (q ^ 2)]
end GlobalTheory.BorelUMod.UpLatIndex

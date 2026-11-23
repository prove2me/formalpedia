-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.LocIn.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:44.081164+00:00
-- url     : https://prove2.me/submissions/9154694a-3437-4354-80bd-9d1093ab8434

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
namespace LocIn
theorem _root_.solution {m n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E} (h : LocIn n v z) (hm : m ≤ n) : LocIn m v z := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun P hP => (ha P hP).trans (WithZero.exp_le_exp.2 (by omega))⟩
end LocIn
end GlobalTheory.CMVal.Euler

-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.IntAt.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:32.144689+00:00
-- url     : https://prove2.me/submissions/1bd86e53-c803-4383-a84c-38c8ff147a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
namespace GlobalTheory.CMVal.Model
namespace IntAt
theorem _root_.solution {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a + b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have := ((isIntegral_natCast (R := ℤ) m).mul ha).add ((isIntegral_natCast (R := ℤ) n).mul hb)
  have e : ((n * m : ℕ) : ℂ) * (a + b) = m * (n * a) + n * (m * b) := by push_cast; ring
  rw [e]; exact this
end IntAt
end GlobalTheory.CMVal.Model

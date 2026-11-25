-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.unitAt_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:29:14.470729+00:00
-- url     : https://prove2.me/submissions/20da7acf-12c1-4204-aa45-6a3a023026dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
namespace GlobalTheory.CMVal.Model
theorem _root_.solution {l m : ℕ} (hm : m ≠ 0) (h : m.Coprime l) : UnitAt l (m : ℂ) := by
  have h0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  refine ⟨h0, ⟨1, by simp, by simpa using isIntegral_natCast (R := ℤ) m⟩, ⟨m, h, ?_⟩⟩
  rw [mul_inv_cancel₀ h0]; exact isIntegral_one
end GlobalTheory.CMVal.Model

-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.shift_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:23:38.860802+00:00
-- url     : https://prove2.me/submissions/d44919f4-179d-41fe-b91b-84356cfb9471

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_inv_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {π : (Af E)ˣ} (y : (Af E)ˣ) {w : HeightOneSpectrum (𝓞 E)} (h : (π : Af E) w = 1) :
    ((π⁻¹ * y : (Af E)ˣ) : Af E) w = (y : Af E) w := by
  rw [Units.val_mul, mul_coord, inv_coord, h, inv_one, one_mul]
end GlobalTheory.CMVal.Euler

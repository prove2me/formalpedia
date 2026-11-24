-- Prove2me | solution 1 for GlobalTheory.CMVal.IdeleIdeal.val_eq_of_idealOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:20:25.685498+00:00
-- url     : https://prove2.me/submissions/3103ea5a-0a90-4db6-b56f-be8bb590df52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_ordAt_cast
import Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_count_idealOf
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_coord_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleIdeal
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.IdeleIdeal
theorem _root_.solution {y y' : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1)
    (h' : ∀ w, Valued.v ((y' : Af E) w) ≤ 1) (e : idealOf y = idealOf y') (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) w) = Valued.v ((y' : Af E) w) := by
  have h1 := count_idealOf y w
  rw [e, count_idealOf, ordAt_cast (h w), ordAt_cast (h' w), neg_inj] at h1
  rw [← WithZero.exp_log (IdeleModule.coord_ne y w), ← h1, WithZero.exp_log (IdeleModule.coord_ne y' w)]
end GlobalTheory.CMVal.IdeleIdeal

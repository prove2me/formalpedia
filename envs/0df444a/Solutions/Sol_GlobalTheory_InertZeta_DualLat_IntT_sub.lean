-- Prove2me | solution 1 for GlobalTheory.InertZeta.DualLat.IntT.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:26.961282+00:00
-- url     : https://prove2.me/submissions/a969870a-4dff-47a1-babf-401e666a3582

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSum
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_add
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_neg
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_add
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.DualLat
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.DualLat
namespace IntT
theorem _root_.solution {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg
end IntT
end GlobalTheory.InertZeta.DualLat

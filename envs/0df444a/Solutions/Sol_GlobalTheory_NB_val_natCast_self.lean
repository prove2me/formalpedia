-- Prove2me | solution 1 for GlobalTheory.NB.val_natCast_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:42.469808+00:00
-- url     : https://prove2.me/submissions/11c9586f-99f0-4b28-b6ce-2fcd2d9a3c5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow
namespace GlobalTheory.NB
theorem _root_.solution (l : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (h0 : (l : O) ≠ 0) (h1 : ¬ IsUnit (l : O)) : val l (l : O) = 1 := by
  refine div_self ?_
  rw [Nat.cast_ne_zero, Ne, ENat.toNat_eq_zero, not_or, IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsDiscreteValuationRing.addVal_eq_top_iff]
  exact ⟨h1, h0⟩
end GlobalTheory.NB

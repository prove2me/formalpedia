-- Prove2me | solution 1 for GlobalTheory.CMFormBound.val_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:04:00.561601+00:00
-- url     : https://prove2.me/submissions/443bb5ed-6b8f-4fb0-86f2-166ade2bb9f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
import Theorems.Thm_GlobalTheory_CMFormBound_ord_mul
import Theorems.Thm_GlobalTheory_CMFormBound_val_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
namespace GlobalTheory.CMFormBound
theorem _root_.solution (l : ℕ) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    val_vp O l (x * y) = val_vp O l x + val_vp O l y := by
  rw [val_of_ne O l hx, val_of_ne O l hy, val_of_ne O l (mul_ne_zero hx hy), ord_mul O hx hy,
    ← WithTop.coe_add]
  congr 1
  push_cast
  ring
end GlobalTheory.CMFormBound

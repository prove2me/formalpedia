-- Prove2me | solution 1 for GlobalTheory.CMFormBound.val_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:35.718198+00:00
-- url     : https://prove2.me/submissions/5167f4d4-5630-436a-9595-0e762100b744

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral

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
theorem _root_.solution (l : ℕ) {x : K} (hx : x ≠ 0) :
    val_vp O l x = (((ord_vw O x : ℚ) / (ord_vw O (l : K) : ℚ) : ℚ) : WithTop ℚ) := by
  rw [val_vp, if_neg hx]
end GlobalTheory.CMFormBound

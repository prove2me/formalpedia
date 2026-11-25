-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.det_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:58.265972+00:00
-- url     : https://prove2.me/submissions/5328fdf9-ce09-4a7e-b01a-8cc70c2d2938

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_GlobalTheory_OrbitDenom_det_low
import Theorems.Thm_GlobalTheory_OrbitDenom_det_up
import Theorems.Thm_GlobalTheory_OrbitDenom_sub_three

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]
namespace GlobalTheory.OrbitDenom
theorem _root_.solution {n l : ℕ} (h : l ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1) :
    ((A * W * B).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (W.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  rw [sub_three h A W B hA hB, Matrix.det_mul, Matrix.det_mul, det_low h A hA hA1, det_up h B hB hB1,
    one_mul, mul_one]
end GlobalTheory.OrbitDenom

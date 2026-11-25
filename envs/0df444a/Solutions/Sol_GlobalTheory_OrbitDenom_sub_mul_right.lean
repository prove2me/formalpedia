-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.sub_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:24.853361+00:00
-- url     : https://prove2.me/submissions/6a429c03-86e3-4116-8ab0-f61fed380153

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_GlobalTheory_OrbitDenom_sum_castLE
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]
namespace GlobalTheory.OrbitDenom
theorem _root_.solution {n l : ℕ} (h : l ≤ n) {α : Type} (p : α → Fin n) (M N : Matrix (Fin n) (Fin n) E)
    (hN : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → N k b = 0) :
    (M * N).submatrix p (Fin.castLE h) =
      M.submatrix p (Fin.castLE h) * N.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_castLE h (fun k => M (p a) k * N k (Fin.castLE h b)) ?_
  intro k hk
  rw [hN k _ hk (by simp), mul_zero]
end GlobalTheory.OrbitDenom

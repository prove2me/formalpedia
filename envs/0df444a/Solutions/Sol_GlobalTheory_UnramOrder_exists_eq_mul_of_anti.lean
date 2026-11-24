-- Prove2me | solution 1 for GlobalTheory.UnramOrder.exists_eq_mul_of_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:23.068348+00:00
-- url     : https://prove2.me/submissions/8b4b656b-f860-4e47-97c8-01339570aaf4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
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
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.UnramOrder
theorem _root_.solution (L : LocE F E) {y z : E} (hy : L.cj y = -y) (hz : L.cj z = -z)
    (hz0 : z ≠ 0) : ∃ c : F, y = algebraMap F E c * z := by
  have := L.reduced
  obtain ⟨d, hd⟩ := (L.cj_fix (z ^ 2)).1 (by simp [hz])
  obtain ⟨s, hs⟩ := (L.cj_fix (y * z)).1 (by simp [hz, hy])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hz0 (IsReduced.eq_zero z ⟨2, by rw [← hd, map_zero]⟩)
  have h1 : algebraMap F E d⁻¹ * z ^ 2 = 1 := by
    rw [← hd, ← map_mul, inv_mul_cancel₀ hd0, map_one]
  refine ⟨s * d⁻¹, ?_⟩
  rw [map_mul, hs]
  linear_combination (-y) * h1
end GlobalTheory.UnramOrder

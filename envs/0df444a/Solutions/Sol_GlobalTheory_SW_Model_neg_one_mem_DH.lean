-- Prove2me | solution 1 for GlobalTheory.SW.Model.neg_one_mem_DH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:08.350255+00:00
-- url     : https://prove2.me/submissions/badaa4ee-5602-4333-b7c9-1b092974fafc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution (n : ℕ) : (-1 : Matrix (Fin n) (Fin n) E) ∈ DH E n 2 := by
  refine ⟨?_, 1, one_pos, by norm_num, -1, fun i j => ?_, ?_⟩
  · have : ccT (-1 : Matrix (Fin n) (Fin n) E) = -1 := by
      ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
    rw [this]; simp
  · by_cases h : i = j <;> simp [Matrix.one_apply, h, isIntegral_zero, isIntegral_one.neg]
  · ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]; norm_num
end GlobalTheory.SW.Model

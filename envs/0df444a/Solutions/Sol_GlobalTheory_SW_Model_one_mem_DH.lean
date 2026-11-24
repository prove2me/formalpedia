-- Prove2me | solution 1 for GlobalTheory.SW.Model.one_mem_DH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:22.737644+00:00
-- url     : https://prove2.me/submissions/7f005423-6318-4be4-8b51-c0a98bc13634

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
theorem _root_.solution (n M : ℕ) : (1 : Matrix (Fin n) (Fin n) E) ∈ DH E n M := by
  refine ⟨?_, 1, one_pos, Nat.coprime_one_left M, 0, fun _ _ => isIntegral_zero, by simp⟩
  have : ccT (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
  rw [this, one_mul]
end GlobalTheory.SW.Model

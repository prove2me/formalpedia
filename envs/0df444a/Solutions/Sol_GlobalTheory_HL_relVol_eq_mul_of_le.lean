-- Prove2me | solution 1 for GlobalTheory.HL.relVol_eq_mul_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:48:52.294504+00:00
-- url     : https://prove2.me/submissions/8b9c9176-dbab-41b2-b3ed-4b4424512564

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonneg

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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W}
    (h1 : A.relIndex W0 ≠ 0) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    relVol W0 A = (A'.relIndex A : ℝ) * relVol W0 A' := by
  have h1' : A'.relIndex W0 ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hi h1
  have e1 : W0.relIndex A' * A'.relIndex A = (W0 ⊓ A').relIndex A := by
    have := AddSubgroup.relIndex_inf_mul_relIndex W0 A' A
    rwa [inf_eq_left.2 hle] at this
  have e2 : A'.relIndex (W0 ⊓ A) * W0.relIndex A = (A' ⊓ W0).relIndex A :=
    AddSubgroup.relIndex_inf_mul_relIndex A' W0 A
  have e3 : A'.relIndex (A ⊓ W0) * A.relIndex W0 = A'.relIndex W0 := by
    have := AddSubgroup.relIndex_inf_mul_relIndex A' A W0
    rwa [inf_eq_left.2 hle] at this
  rw [inf_comm A' W0, ← e1, inf_comm W0 A] at e2
  have e2' : (A'.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = W0.relIndex A' * A'.relIndex A := by
    exact_mod_cast e2
  have e3' : (A'.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = A'.relIndex W0 := by
    exact_mod_cast e3
  have n1 : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast h1
  have n2 : (A'.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast h1'
  unfold relVol
  rw [← mul_div_assoc, div_eq_div_iff n1 n2, ← e3']
  linear_combination (A.relIndex W0 : ℝ) * e2'
end GlobalTheory.HL

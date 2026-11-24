-- Prove2me | solution 1 for GlobalTheory.Lin.exists_dvd_mul_add_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:57.65894+00:00
-- url     : https://prove2.me/submissions/b67d47da-5f0b-4fe3-b0b4-6f395abb5cf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ArithmeticLargeSieveOneResidueClassPerPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin
namespace GlobalTheory.Lin
theorem _root_.solution (l q r : ℕ) (hl : l.Prime) (hq : ¬ l ∣ q) : ∃ c : ℕ, l ∣ q * c + r := by
  haveI := Fact.mk hl
  have hq' : (q : ZMod l) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q l).1 h)
  refine ⟨(-(r : ZMod l) * (q : ZMod l)⁻¹).val, (ZMod.natCast_eq_zero_iff _ l).1 ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring
end GlobalTheory.Lin

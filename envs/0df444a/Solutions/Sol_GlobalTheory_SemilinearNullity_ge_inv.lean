-- Prove2me | solution 1 for GlobalTheory.SemilinearNullity.ge_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:51.250809+00:00
-- url     : https://prove2.me/submissions/45ef73db-c91b-49be-8dc9-1f99e27a94e6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal
import Theorems.Thm_GlobalTheory_SemilinearNullity_mm_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.SemilinearNullity
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.SemilinearNullity
theorem _root_.solution {a : C} (h : ¬ V.MM a) : V.Ge 0 a⁻¹ := by
  have h0 : a ≠ 0 := by rintro rfl; exact h mm_zero
  show (0 : WithTop ℝ) ≤ V.v a⁻¹
  have e : V.v a⁻¹ + V.v a = 0 := by rw [← V.v.map_mul, inv_mul_cancel₀ h0, V.v.map_one]
  have h1 : V.v a ≤ 0 := not_lt.mp h
  calc (0 : WithTop ℝ) = V.v a⁻¹ + V.v a := e.symm
    _ ≤ V.v a⁻¹ := add_le_of_nonpos_right h1
end GlobalTheory.SemilinearNullity

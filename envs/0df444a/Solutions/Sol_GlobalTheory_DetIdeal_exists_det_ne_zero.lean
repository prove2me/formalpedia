-- Prove2me | solution 1 for GlobalTheory.DetIdeal.exists_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:39.165264+00:00
-- url     : https://prove2.me/submissions/57a552a8-3167-4d9a-8d44-d9d7b028f3c9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution (S : Set (Fin r → K)) (hS : Submodule.span K S = ⊤) :
    ∃ Y : Matrix (Fin r) (Fin r) K, (∀ i, Y i ∈ S) ∧ Y.det ≠ 0 := by
  obtain ⟨f, hf, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq K S
  have e : r = Module.finrank K (Submodule.span K S) := by rw [hS]; simp
  refine ⟨Matrix.of fun i => f (Fin.cast e i), fun i => hf _, ?_⟩
  apply IsUnit.ne_zero
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
  exact hli.comp _ (Fin.cast_injective e)
end GlobalTheory.DetIdeal

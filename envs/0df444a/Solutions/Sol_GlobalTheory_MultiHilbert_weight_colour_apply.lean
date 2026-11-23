-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.weight_colour_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:35.170884+00:00
-- url     : https://prove2.me/submissions/88dd0f57-dadb-458a-abdf-411226bfcb00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution (d : σ →₀ ℕ) (k : Fin r) :
    Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d k =
      ∑ i ∈ d.support, if col i = k then d i else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : col i = k
  · subst h
    simp
  · simp [h, Ne.symm h]
end GlobalTheory.MultiHilbert

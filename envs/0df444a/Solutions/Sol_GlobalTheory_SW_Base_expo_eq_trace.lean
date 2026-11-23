-- Prove2me | solution 1 for GlobalTheory.SW.Base.expo_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:53.448639+00:00
-- url     : https://prove2.me/submissions/7f4f5e1b-b521-48f9-a2b7-2662faf4ed66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible

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
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
omit [IsCMField E]
namespace GlobalTheory.SW.Base
theorem _root_.solution (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    expo Ψ x Z z z' = ∑ τ : Ψ, ((x.map τ.1 * Z τ * (x.map τ.1)ᴴ).trace +
      (x.map τ.1 * (z τ)ᵀ).trace + (z' τ * (x.map τ.1)ᴴ).trace) := by
  unfold expo
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.trace, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_assoc]
  rfl
end GlobalTheory.SW.Base

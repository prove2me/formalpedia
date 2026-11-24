-- Prove2me | solution 1 for GlobalTheory.SW.Base.expo_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:36.199517+00:00
-- url     : https://prove2.me/submissions/83226d5f-9de6-48a9-8920-71940d59b656

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_ccT_map
import Theorems.Thm_GlobalTheory_SW_Base_expo_eq_trace

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
namespace GlobalTheory.SW.Base
theorem _root_.solution {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    expo Ψ (h * x) Z z z' =
      expo Ψ x Z (fun τ => (h.map τ.1)ᵀ * z τ) (fun τ => (h.map τ.1)ᴴ * z' τ) := by
  rw [expo_eq_trace, expo_eq_trace]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : (h.map τ.1)ᴴ * h.map τ.1 = 1 := by
    rw [← ccT_map, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_mul, Matrix.conjTranspose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  generalize h.map τ.1 = H at e ⊢
  generalize x.map τ.1 = X
  congr 1
  · congr 1
    · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, e, Matrix.one_mul]
    · rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
end GlobalTheory.SW.Base

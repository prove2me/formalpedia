-- Prove2me | solution 1 for GlobalTheory.SW.GaussDict.zetaOf_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:05.311288+00:00
-- url     : https://prove2.me/submissions/ce45e663-8240-48f8-951c-d9465c305fd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_GaussianQuadFormRationalCoordsHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.GaussDict
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.GaussDict
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (z z' : CM Ψ n N) (k : Fin n) (u : QI E N → ℂ) :
    zetaOf Ψ z z' k ⬝ᵥ u = ∑ τ : Ψ,
      (z τ k ⬝ᵥ (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) +
      z' τ k ⬝ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) := by
  simp only [dotProduct, zetaOf, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring
end GlobalTheory.SW.GaussDict

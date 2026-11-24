-- Prove2me | solution 1 for GlobalTheory.SW.GaussDict.tauOf_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:04.400783+00:00
-- url     : https://prove2.me/submissions/2497eff7-b4a9-4340-a006-ae3e403fef6c

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
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (Y : CM Ψ N N) (u : QI E N → ℂ) (p : QI E N) :
    (tauOf Ψ Y *ᵥ u) p = ∑ τ : Ψ, (τ.1 (Module.finBasis ℚ E p.2) *
      (Y τ *ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) p.1 +
      conj (τ.1 (Module.finBasis ℚ E p.2)) *
      ((Y τ)ᵀ *ᵥ fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) p.1) := by
  simp only [Matrix.mulVec, dotProduct, tauOf, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring
end GlobalTheory.SW.GaussDict

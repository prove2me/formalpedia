-- Prove2me | solution 1 for GlobalTheory.SW.GaussDict.im_tauOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:03.663896+00:00
-- url     : https://prove2.me/submissions/c8f49367-905c-4351-9ce1-f8ff6be20717

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
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (Z : CM Ψ N N) :
    ((tauOf Ψ Z).map fun t => (t.im : ℂ)) = tauOf Ψ (fun τ => imH (Z τ)) := by
  ext p q
  simp only [Matrix.map_apply, tauOf, Matrix.of_apply]
  rw [Complex.im_eq_sub_conj, map_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [imH, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
    Complex.star_def, smul_eq_mul, map_add, map_mul, Complex.conj_conj]
  ring
end GlobalTheory.SW.GaussDict

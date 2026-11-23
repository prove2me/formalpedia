-- Prove2me | solution 1 for GlobalTheory.CMLattice.im_mul_conj_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:36.040056+00:00
-- url     : https://prove2.me/submissions/b40fe531-833e-4530-89bc-76c269330c42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.CMLattice
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.CMLattice
theorem _root_.solution (σ : K →+* ℂ) (b : Basis (Fin 2) ℚ K) (v : Fin 2 → K) :
    (σ (v 0) * starRingEnd ℂ (σ (v 1))).im =
      (b.det v : ℚ) * (σ (b 0) * starRingEnd ℂ (σ (b 1))).im := by
  have hv : ∀ j, σ (v j) = ∑ i, ((b.toMatrix v i j : ℚ) : ℂ) * σ (b i) := by
    intro j
    conv_lhs => rw [← b.sum_toMatrix_smul_self v j]
    simp [Rat.smul_def, map_mul, map_ratCast]
  rw [hv 0, hv 1, Basis.det_apply, Matrix.det_fin_two]
  simp only [Fin.sum_univ_two, map_add, map_mul, map_ratCast, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ratCast_re,
    Complex.ratCast_im]
  push_cast
  ring
end GlobalTheory.CMLattice

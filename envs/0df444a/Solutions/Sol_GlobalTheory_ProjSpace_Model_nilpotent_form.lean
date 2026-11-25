-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.nilpotent_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:30.264031+00:00
-- url     : https://prove2.me/submissions/c8150b57-dcc5-44d1-9379-35df6f1f552e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_formSec_inj
import Theorems.Thm_GlobalTheory_ProjSpace_nonzeroLocus_formSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}
namespace GlobalTheory.ProjSpace.Model
theorem _root_.solution (h : (C 2 * X 0 : MvPolynomial (Fin 2) (ZMod 4)).IsHomogeneous 1) :
    formSec 1 _ h ≠ formSec 1 0 (isHomogeneous_zero _ _ 1) ∧ nonzeroLocus (formSec 1 _ h) = ⊥ := by
  refine ⟨fun e => ?_, ?_⟩
  · have := congrArg (coeff (Finsupp.single 0 1)) ((formSec_inj _ _).1 e)
    rw [coeff_C_mul, coeff_X, if_pos rfl, coeff_zero] at this
    exact absurd this (by decide)
  · rw [nonzeroLocus_formSec]
    refine le_bot_iff.1 fun x hx => hx (x.isPrime.mem_of_pow_mem 2 ?_)
    have : (C 2 * X 0 : MvPolynomial (Fin 2) (ZMod 4)) ^ 2 = 0 := by
      rw [mul_pow, ← map_pow, show (2 : ZMod 4) ^ 2 = 0 by decide, map_zero, zero_mul]
    rw [this]; exact zero_mem _
end GlobalTheory.ProjSpace.Model

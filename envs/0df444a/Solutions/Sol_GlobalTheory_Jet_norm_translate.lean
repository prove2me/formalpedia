-- Prove2me | solution 1 for GlobalTheory.Jet.norm_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:54.030245+00:00
-- url     : https://prove2.me/submissions/f818c511-5a48-4551-b3f1-0740179683e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_GlobalTheory_Jet_Hf_eq_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.Jet
theorem _root_.solution (q : ℕ) (y : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ)
    (v : EuclideanSpace ℂ ι) :
    ‖cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y)‖ ^ 2 *
        Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) =
      ‖F (v - y)‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v - y‖ ^ 2) := by
  have hre : (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2 : ℂ).re =
      q * Real.pi * (inner ℂ y v : ℂ).re - q * Real.pi * ‖y‖ ^ 2 / 2 := by
    rw [Hf_eq_inner, Hf_eq_inner, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hn : ‖v - y‖ ^ 2 = ‖y‖ ^ 2 - 2 * (inner ℂ y v : ℂ).re + ‖v‖ ^ 2 := by
    rw [norm_sub_rev, @norm_sub_sq ℂ]
    rfl
  rw [norm_mul, Complex.norm_exp, hre, hn, mul_pow, mul_comm _ (‖F (v - y)‖ ^ 2), mul_assoc,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  push_cast
  ring
end GlobalTheory.Jet

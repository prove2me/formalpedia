-- Prove2me | solution 1 for GlobalTheory.SharpObj.hermForm_real_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:47:05.971624+00:00
-- url     : https://prove2.me/submissions/8baaf63a-c29a-4cd9-8fd9-c46ed96c4331

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}
namespace GlobalTheory.SharpObj
theorem _root_.solution (M : Matrix (Fin h) (Fin h) ℝ) (z w : Fin h → ℂ) :
    (hermForm (M.map fun x : ℝ => (x : ℂ)) z w).re =
      (fun i => (z i).re) ⬝ᵥ M.mulVec (fun i => (w i).re) + (fun i => (z i).im) ⬝ᵥ M.mulVec (fun i => (w i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring
end GlobalTheory.SharpObj

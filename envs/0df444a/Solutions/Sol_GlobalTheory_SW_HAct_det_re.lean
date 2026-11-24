-- Prove2me | solution 1 for GlobalTheory.SW.HAct.det_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:06.121395+00:00
-- url     : https://prove2.me/submissions/d9b55307-fd46-4f7c-ac49-7a7d1d5ace48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution {Q Y X : Matrix (Fin N) (Fin N) ℂ} (h : Qᴴ * Y * Q = X) :
    Y.det.re * ‖Q.det‖ ^ 2 = X.det.re := by
  have e : X.det = Y.det * ((‖Q.det‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h, det_mul, det_mul, det_conjTranspose]
    push_cast
    rw [← Complex.conj_mul', Complex.star_def]
    ring
  rw [e, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring
end GlobalTheory.SW.HAct

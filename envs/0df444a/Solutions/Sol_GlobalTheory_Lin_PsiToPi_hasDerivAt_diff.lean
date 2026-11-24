-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.hasDerivAt_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:59:26.921298+00:00
-- url     : https://prove2.me/submissions/6e21d642-3583-48b6-acc3-81280f19f7df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_hasDerivAt_Li

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution (θ : ℤ) {β u : ℝ} (hβ : 0 < β) (hu : 1 < u) :
    HasDerivAt (fun u => Emain θ β u - mainPsi θ β u / Real.log u) (mainPsi θ β u / (u * Real.log u ^ 2)) u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos hu
  have h1 : HasDerivAt (fun u : ℝ => u ^ β) (β * u ^ (β - 1)) u := Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
  have h2 := (hasDerivAt_Li (Real.one_lt_rpow hu hβ)).comp u h1
  have h3 := (hasDerivAt_Li hu).sub (h2.const_mul (θ : ℝ))
  have h4 := ((hasDerivAt_id u).sub ((h1.div_const β).const_mul (θ : ℝ))).div (Real.hasDerivAt_log hu0.ne') hl.ne'
  have h5 := h3.sub h4
  refine HasDerivAt.congr_deriv (f := fun u => Emain θ β u - mainPsi θ β u / Real.log u) h5 ?_
  simp only [mainPsi, id, Pi.sub_apply]
  rw [Real.log_rpow hu0]
  field_simp
  ring
end GlobalTheory.Lin.PsiToPi

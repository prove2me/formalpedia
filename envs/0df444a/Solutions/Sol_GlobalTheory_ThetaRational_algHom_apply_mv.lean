-- Prove2me | solution 1 for GlobalTheory.ThetaRational.algHom_apply_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:59.129809+00:00
-- url     : https://prove2.me/submissions/0fb3a16e-22ba-4a55-929a-4cce8bd5c3db

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_P2M_GlobalTheory_ThetaRational_algHom_eval__435c3be33efa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {A : Type*} [CommRing A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.ThetaRational
theorem _root_.solution (j : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (χ : A →ₐ[ℂ] ℂ)
    (q : MvPolynomial (Fin n) ℂ) :
    χ (j q) = MvPolynomial.eval (fun i => χ (j (MvPolynomial.X i))) q := by
  simpa using algHom_eval₂ j χ (Polynomial.C q) 0
end GlobalTheory.ThetaRational

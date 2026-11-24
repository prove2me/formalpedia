-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:24.419801+00:00
-- url     : https://prove2.me/submissions/a10f2309-4371-4830-995d-1f9a8eb4d833

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsInvOne
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_StandardBasisDerivatives_ArchimedeanBasisDerivatives_StBasDeriv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtTwistHomotopyKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistHomotopy
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwistHomotopy
theorem _root_.solution (p : Fin n × Fin n) : (hb p)ᴴ = hb p := by
  unfold hb
  split_ifs with h1 h2
  · simp
  · simp [conjTranspose_smul, conjTranspose_add, add_comm]
  · have e : star (((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) = -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) := by
      simp
    rw [conjTranspose_smul, conjTranspose_sub, e]
    simp [neg_smul, smul_sub]
    abel
end GlobalTheory.CompanionTheory.TwistHomotopy

-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.phi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:23.362977+00:00
-- url     : https://prove2.me/submissions/800cf2f1-f0a3-49b6-bc87-a90ba916f77e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.PhiConjugateTranspose
variable {n : ℕ} {R : Type} [CommRing R]
namespace GlobalTheory.Tw.PhiConjugateTranspose
theorem _root_.solution (i k : Fin n) : Phi n R i k = if k = i.rev then (-1 : R) ^ (i : ℕ) else 0 := by
  simp only [Phi, of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  omega
end GlobalTheory.Tw.PhiConjugateTranspose

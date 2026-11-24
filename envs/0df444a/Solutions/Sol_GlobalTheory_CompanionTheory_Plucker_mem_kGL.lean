-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.mem_kGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:14.443785+00:00
-- url     : https://prove2.me/submissions/c13cbcac-d5ee-4949-95b0-a75b24162e28

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (A : Ad E R) {k : GL ι R} : k ∈ A.kGL ι ↔
    (∀ r c, (k : Matrix ι ι R) r c ∈ A.O ∧ ((k⁻¹ : GL ι R) : Matrix ι ι R) r c ∈ A.O) ∧
    ∀ w, (k : Matrix ι ι R).map (A.φ w) ∈ Matrix.unitaryGroup ι ℂ := Iff.rfl
end GlobalTheory.CompanionTheory.Plucker

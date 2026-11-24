-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.mem_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:08:43.04602+00:00
-- url     : https://prove2.me/submissions/d4578335-51de-414c-ab64-059c2b125354

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
theorem _root_.solution {s : Set ι} {g : GL ι R} : g ∈ stab R s ↔
    ∀ r ∉ s, ∀ c ∈ s, (g : Matrix ι ι R) r c = 0 ∧ ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0 := Iff.rfl
end GlobalTheory.CompanionTheory.Plucker

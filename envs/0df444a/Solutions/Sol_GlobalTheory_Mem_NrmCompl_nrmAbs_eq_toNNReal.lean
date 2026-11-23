-- Prove2me | solution 1 for GlobalTheory.Mem.NrmCompl.nrmAbs_eq_toNNReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:01.798693+00:00
-- url     : https://prove2.me/submissions/fa3027e4-1883-4fb9-a3c4-8f8214ddf5df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NrmAbsOfValuationEqExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.NrmCompl
open NumberField IsDedekindDomain
variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
namespace GlobalTheory.Mem.NrmCompl
theorem _root_.solution (x : P.adicCompletion L) :
    nrmAbs P x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P) (Valued.v x) :=
  FinitePlace.norm_def (v := P) x
end GlobalTheory.Mem.NrmCompl

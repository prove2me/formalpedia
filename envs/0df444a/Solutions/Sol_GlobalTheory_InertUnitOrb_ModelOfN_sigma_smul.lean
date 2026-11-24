-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.sigma_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:43.976533+00:00
-- url     : https://prove2.me/submissions/3cd1659f-2ebc-4c4a-a158-1b0a23bfd49e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution {K : UQ} (B : InvAlg K) (e : K.E) (y : B.A) : B.σ (e • y) = K.c e • B.σ y := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
end GlobalTheory.InertUnitOrb.ModelOfN

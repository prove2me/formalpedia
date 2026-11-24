-- Prove2me | solution 1 for GlobalTheory.GaloisDescentLattice.sigma_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:46.884191+00:00
-- url     : https://prove2.me/submissions/02d842e5-e34b-4df7-b953-04a9cd3315a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.GaloisDescentLattice
namespace GlobalTheory.GaloisDescentLattice
theorem _root_.solution {K : UQ} (B : InvAlg K) {a b : K.O}
    (hab : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E b) (y : B.A) :
    B.σ (a • y) = b • B.σ y := by
  rw [← algebraMap_smul K.E a y, ← algebraMap_smul K.E b (B.σ y), Algebra.smul_def, Algebra.smul_def,
    map_mul, B.σ_alg, hab]
end GlobalTheory.GaloisDescentLattice

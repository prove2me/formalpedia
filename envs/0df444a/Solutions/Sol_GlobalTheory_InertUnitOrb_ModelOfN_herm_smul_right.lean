-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:34.073241+00:00
-- url     : https://prove2.me/submissions/32eca99b-bc8e-4bdd-afb4-244c57cc59fd

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
variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution (h : V → V → K.E)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) (hsym : ∀ y z, h z y = K.c (h y z))
    (a : K.E) (y z : V) : h y (a • z) = K.c a * h y z := by
  rw [hsym (a • z) y, hsmul, map_mul, ← hsym z y]
end GlobalTheory.InertUnitOrb.ModelOfN

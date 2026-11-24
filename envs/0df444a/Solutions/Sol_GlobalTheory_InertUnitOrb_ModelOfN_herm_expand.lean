-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.herm_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:42.004059+00:00
-- url     : https://prove2.me/submissions/f0bfd334-156d-4574-b3a8-0e3a55af7d47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_herm_smul_right
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_herm_add_right

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
theorem _root_.solution (h : V → V → K.E) (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) (hsym : ∀ y z, h z y = K.c (h y z))
    (e : K.E) (y z : V) :
    h (e • y + z) (e • y + z) = e * K.c e * h y y + e * h y z + K.c e * h z y + h z z := by
  rw [hadd, herm_add_right h hadd hsym, herm_add_right h hadd hsym, hsmul, hsmul,
    herm_smul_right h hsmul hsym, herm_smul_right h hsmul hsym]
  ring
end GlobalTheory.InertUnitOrb.ModelOfN

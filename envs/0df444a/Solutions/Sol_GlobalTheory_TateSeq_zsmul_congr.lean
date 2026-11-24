-- Prove2me | solution 1 for GlobalTheory.TateSeq.zsmul_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:39.5684+00:00
-- url     : https://prove2.me/submissions/aa618038-e4e9-40fc-8e2d-fe24fc8411aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TateSeq
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.TateSeq
theorem _root_.solution {N : ℕ} {m : M} (hm : N • m = 0) {a b : ℤ}
    (h : (a : ZMod N) = (b : ZMod N)) : a • m = b • m := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨c, hc⟩ := h
  have : b = a + c * N := by linarith
  rw [this, add_smul, mul_smul, natCast_zsmul, hm, smul_zero, add_zero]
end GlobalTheory.TateSeq

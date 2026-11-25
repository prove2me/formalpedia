-- Prove2me | solution 1 for GlobalTheory.FrobRoot.mm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:55.129148+00:00
-- url     : https://prove2.me/submissions/54abab3d-9ec2-4e53-87b4-be5651de2ad9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds GlobalTheory.LeafTerm
open GlobalTheory GlobalTheory.FrobRoot
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.FrobRoot
theorem _root_.solution {a : C} (ha : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  unfold VF.MM at *
  rw [V.v.map_pow]
  exact nsmul_pos ha hn
end GlobalTheory.FrobRoot

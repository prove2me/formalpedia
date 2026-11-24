-- Prove2me | solution 1 for GlobalTheory.SympMod.card_torsion_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:00:09.250533+00:00
-- url     : https://prove2.me/submissions/856c46e2-bcc5-4b34-ad08-a09e31a26c42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SympMod
namespace GlobalTheory.SympMod
theorem _root_.solution {M d : ℕ} [NeZero M] (hd : d ∣ M) :
    Nat.card {a : ZMod M // d • a = 0} = d := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod M) d
  rw [Nat.card_zmod, Nat.gcd_eq_right hd] at h
  exact h
end GlobalTheory.SympMod

-- Prove2me | solution 1 for GlobalTheory.Prism.FCrys.unit_effective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:23.078458+00:00
-- url     : https://prove2.me/submissions/cb83f9fe-ae4e-482b-a657-e546a2859d7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Prism
attribute [instance] Obj.ring
variable {l : ℕ} {R : Type} [CommRing R]
attribute [instance] FCrys.acg FCrys.mod
attribute [instance] VBun.acg VBun.mod
namespace GlobalTheory.Prism
namespace FCrys
theorem _root_.solution (l : ℕ) (R : Type) [CommRing R] : (FCrys.unit l R).Effective := by
  intro P x
  refine ⟨P.D.φ x, fun d => ?_⟩
  change LocalizedModule.mk (P.D.φ x) (1 : Submonoid.powers (d : P.A)) = LocalizedModule.mk _ _
  congr 1
  ext; simp
end FCrys
end GlobalTheory.Prism

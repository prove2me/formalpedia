-- Prove2me | solution 1 for GlobalTheory.InertiaEigenvalues.exists_isActC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:59.864469+00:00
-- url     : https://prove2.me/submissions/d48bb905-9009-4401-93ac-111bbb29d456

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GalExtCContinuous
import Theorems.Thm_GlobalTheory_InertiaEigenvalues_isActC_galActC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.InertiaEigenvalues
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.InertiaEigenvalues
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime], ∃ act : GQ l →* (PadicComplex l ≃+* PadicComplex l), IsActC act :=
  fun l _ => ⟨galActC l, isActC_galActC l⟩
end GlobalTheory.InertiaEigenvalues

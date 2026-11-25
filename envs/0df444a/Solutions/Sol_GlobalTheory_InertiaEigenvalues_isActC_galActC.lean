-- Prove2me | solution 1 for GlobalTheory.InertiaEigenvalues.isActC_galActC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:45:34.595626+00:00
-- url     : https://prove2.me/submissions/45cde159-6068-4202-92fe-24ab81d00f2e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GalExtCContinuous
import Theorems.Thm_GlobalTheory_InertiaEigenvalues_norm_galExtC

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] : IsActC (galActC l) :=
  ⟨galExtC_coe, norm_galExtC⟩
end GlobalTheory.InertiaEigenvalues

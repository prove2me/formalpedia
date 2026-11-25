-- Prove2me | solution 1 for GlobalTheory.TateDecomp.Xsum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:53.609049+00:00
-- url     : https://prove2.me/submissions/edb45a2b-a99a-49f3-977b-3169e96896c4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_subC_mono
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_TateDecomp_Xlev_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution (K : FinExt l) (j : ℕ) : Xsum K j ≤ intA (Kinf K) := by
  refine iSup₂_le fun i _ x hx => ?_
  have := Xlev_le K i hx
  exact ⟨subC_mono (Ks_le_Kinf K i) (intC_iff.1 this).1, this.2⟩
end GlobalTheory.TateDecomp

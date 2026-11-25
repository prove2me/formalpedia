-- Prove2me | solution 1 for GlobalTheory.TateDecomp.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:17.030249+00:00
-- url     : https://prove2.me/submissions/2a7e22e3-cf33-4414-9947-f5e82be0658f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono
import Theorems.Thm_GlobalTheory_TateDecomp_exists_level
import Theorems.Thm_GlobalTheory_TateDecomp_Xlev_le_Xsum
import Theorems.Thm_GlobalTheory_TateDecomp_step

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
theorem _root_.solution (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {z : PadicComplex l} (hz : z ∈ intC (Kinf K)) :
    ∃ y ∈ intC (Ks K j), z - y ∈ Xsum K j := by
  have key : ∀ n, ∀ z ∈ intC (Ks K (j + n)), ∃ y ∈ intC (Ks K j), z - y ∈ Xsum K j := by
    intro n
    induction n with
    | zero => exact fun z hz => ⟨z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨w, hw, h⟩ := step K (i := j + (n + 1)) (by omega) hz
      obtain ⟨y, hy, h'⟩ := ih w hw
      refine ⟨y, hy, ?_⟩
      have := add_mem (Xlev_le_Xsum K (show j < j + (n + 1) by omega) h) h'
      simpa using this
  obtain ⟨⟨w, hw, rfl⟩, hn⟩ := intC_iff.1 hz
  obtain ⟨i, hi⟩ := exists_level K hw
  exact key i _ ⟨⟨w, Ks_mono K (by omega) hi, rfl⟩, hn⟩
end GlobalTheory.TateDecomp

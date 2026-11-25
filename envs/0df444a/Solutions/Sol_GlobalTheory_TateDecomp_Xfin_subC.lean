-- Prove2me | solution 1 for GlobalTheory.TateDecomp.Xfin_subC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:30.94526+00:00
-- url     : https://prove2.me/submissions/50fb430c-cd69-41b7-ac6f-a96d51b88d58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_subC_mono
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono
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
theorem _root_.solution (K : FinExt l) (j n : ℕ) : ∀ x ∈ Xfin K j n, x ∈ subC (Ks K (j + n)) := by
  induction n with
  | zero => intro x hx; rw [AddSubgroup.mem_bot.1 hx]; exact zero_mem _
  | succ n ih =>
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hx
    exact add_mem (subC_mono (Ks_mono K (by omega)) (ih a ha)) (intC_iff.1 (Xlev_le K _ hb)).1
end GlobalTheory.TateDecomp

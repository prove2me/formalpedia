-- Prove2me | solution 1 for GlobalTheory.TateDecomp.Xsum_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:36.049791+00:00
-- url     : https://prove2.me/submissions/4ca94277-d258-473d-bc16-0ba350414d01

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_subC_mono
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono
import Theorems.Thm_GlobalTheory_TateDecomp_Xlev_inter
import Theorems.Thm_GlobalTheory_TateDecomp_Xfin_subC

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
theorem _root_.solution (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {x : PadicComplex l} (hx : x ∈ Xsum K j)
    (hx' : x ∈ subC (Ks K j)) : x = 0 := by
  have hm : Monotone (Xfin K j) := monotone_nat_of_le_succ fun n => le_sup_left
  have h1 : Xsum K j ≤ ⨆ n, Xfin K j n := by
    refine iSup₂_le fun i hi => ?_
    obtain ⟨n, rfl⟩ : ∃ n, i = j + (n + 1) := ⟨i - j - 1, by omega⟩
    exact le_trans (le_sup_right : _ ≤ Xfin K j (n + 1)) (le_iSup (Xfin K j) (n + 1))
  obtain ⟨n, hn⟩ := (AddSubgroup.mem_iSup_of_directed hm.directed_le).1 (h1 hx)
  clear hx
  induction n with
  | zero => exact AddSubgroup.mem_bot.1 hn
  | succ n ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hn
    have hb0 : b = 0 := by
      refine Xlev_inter K (by omega) hb ?_
      have := sub_mem (subC_mono (Ks_mono K (show j ≤ j + n by omega)) hx') (Xfin_subC K j n a ha)
      simpa using this
    subst hb0
    exact ih (by rw [add_zero]; exact ha)
end GlobalTheory.TateDecomp

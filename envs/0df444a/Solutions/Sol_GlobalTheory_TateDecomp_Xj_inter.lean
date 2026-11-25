-- Prove2me | solution 1 for GlobalTheory.TateDecomp.Xj_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:57.242699+00:00
-- url     : https://prove2.me/submissions/34be5af4-bf3a-4730-82c9-4bf0e16a05c8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_mem_Xj
import Theorems.Thm_GlobalTheory_TateDecomp_norm_le_of_close
import Theorems.Thm_GlobalTheory_TateDecomp_norm_l_lt

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
theorem _root_.solution (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {x : PadicComplex l} (hx : x ∈ Xj K j)
    (hx' : x ∈ subC (Ks K j)) : x = 0 := by
  have hl : 0 < ‖(l : PadicComplex l)‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  by_contra h0
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 h0) (norm_l_lt (l := l))
  obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.1 (mem_Xj.1 hx) _ (pow_pos hl m)
  rw [dist_eq_norm] at hd
  exact absurd (norm_le_of_close K hj hx' hw m hd.le) (not_le.2 hm)
end GlobalTheory.TateDecomp

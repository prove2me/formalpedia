-- Prove2me | solution 1 for GlobalTheory.TateDecomp.Xlev_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:53.858066+00:00
-- url     : https://prove2.me/submissions/8bc06805-62ca-4e90-9302-fac905e9c62f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_subC_mono
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono
import Theorems.Thm_GlobalTheory_TateDecomp_root_mem_subC
import Theorems.Thm_GlobalTheory_TateDecomp_norm_root

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
theorem _root_.solution (K : FinExt l) (i : ℕ) : Xlev K i ≤ intA (Ks K i) := by
  rw [Xlev, AddSubgroup.closure_le]
  rintro z ⟨ζ, y, hζ, hy, rfl⟩
  refine ⟨mul_mem (root_mem_subC K hζ.pow_eq_one)
    (subC_mono (Ks_mono K (Nat.sub_le i 1)) (intC_iff.1 hy).1), ?_⟩
  rw [norm_mul, norm_root hζ.pow_eq_one, one_mul]
  exact hy.2
end GlobalTheory.TateDecomp

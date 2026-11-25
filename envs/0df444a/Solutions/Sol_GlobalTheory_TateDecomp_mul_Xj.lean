-- Prove2me | solution 1 for GlobalTheory.TateDecomp.mul_Xj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:05.035218+00:00
-- url     : https://prove2.me/submissions/0685a4b2-f7f7-4fb8-aee1-4438c2fd9650

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_subC_mono
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono
import Theorems.Thm_GlobalTheory_TateDecomp_map_Xj

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
theorem _root_.solution {K : FinExt l} {j : ℕ} {y x : PadicComplex l} (hy : y ∈ intC (Ks K j))
    (hx : x ∈ Xj K j) : y * x ∈ Xj K j := by
  refine map_Xj (AddMonoidHom.mulLeft y) (continuous_const.mul continuous_id) ?_ hx
  intro i hi ζ w hζ hw
  refine AddSubgroup.subset_closure ⟨ζ, y * w, hζ, ⟨mul_mem
    (subC_mono (Ks_mono K (by omega)) (intC_iff.1 hy).1) (intC_iff.1 hw).1, ?_⟩, ?_⟩
  · rw [norm_mul]; exact mul_le_one₀ hy.2 (norm_nonneg _) hw.2
  · simp only [AddMonoidHom.coe_mulLeft]; ring
end GlobalTheory.TateDecomp

-- Prove2me | solution 1 for GlobalTheory.CycSeries.mul_mem_intC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:22:29.080236+00:00
-- url     : https://prove2.me/submissions/a6d244aa-711a-4266-ae63-d95834c3262f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Theorems.Thm_GlobalTheory_CycSeries_mem_inC_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycSeries
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycSeries
theorem _root_.solution {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ intC F)
    (hy : y ∈ intC F) : x * y ∈ intC F :=
  ⟨(mem_inC_iff _ _).2 (mul_mem ((mem_inC_iff _ _).1 hx.1) ((mem_inC_iff _ _).1 hy.1)),
    by rw [norm_mul]; exact mul_le_one₀ hx.2 (norm_nonneg _) hy.2⟩
end GlobalTheory.CycSeries

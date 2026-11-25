-- Prove2me | solution 1 for GlobalTheory.CycPerturb.mul_mem_intC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:48:36.654507+00:00
-- url     : https://prove2.me/submissions/0451e051-ddb6-4681-b0b6-429b92fffd65

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
import Theorems.Thm_GlobalTheory_CycPerturb_mem_inC_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycPerturb
theorem _root_.solution {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l}
    (hx : x ∈ intC F) (hy : y ∈ intC F) : x * y ∈ intC F :=
  ⟨(mem_inC_iff _ _).2 (mul_mem ((mem_inC_iff _ _).1 hx.1) ((mem_inC_iff _ _).1 hy.1)), by
    rw [norm_mul]; exact mul_le_one₀ hx.2 (norm_nonneg _) hy.2⟩
end GlobalTheory.CycPerturb

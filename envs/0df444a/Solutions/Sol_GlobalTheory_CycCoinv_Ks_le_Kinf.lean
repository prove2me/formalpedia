-- Prove2me | solution 1 for GlobalTheory.CycCoinv.Ks_le_Kinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:56:59.656206+00:00
-- url     : https://prove2.me/submissions/51492571-dc17-4f4d-95ae-5876ec0aedd0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.CycCoinv
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycCoinv
theorem _root_.solution (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] _ _ fun (x : Om l) hx =>
    (show ∃ j : ℕ, x ^ (l ^ j) = 1 from ⟨j, hx⟩)) _
end GlobalTheory.CycCoinv

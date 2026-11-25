-- Prove2me | solution 1 for GlobalTheory.CycCoinv.add_mem_Ohat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:08:50.490172+00:00
-- url     : https://prove2.me/submissions/520a8efc-a384-479f-970b-beeb33de7a40

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
import Theorems.Thm_GlobalTheory_CycCoinv_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_le_Kinf


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
theorem _root_.solution (K : FinExt l) (j : ℕ) {y x : PadicComplex l} (hy : y ∈ intC (Ks K j))
    (hx : x ∈ Ohat K) : y + x ∈ Ohat K := by
  have hy' : y ∈ (intR (Kinf K)).topologicalClosure :=
    (intR (Kinf K)).le_topologicalClosure
      (show y ∈ intC (Kinf K) from ⟨Set.image_mono (Ks_le_Kinf K j) hy.1, hy.2⟩)
  have hx' : x ∈ (intR (Kinf K)).topologicalClosure := hx
  exact add_mem hy' hx'
end GlobalTheory.CycCoinv

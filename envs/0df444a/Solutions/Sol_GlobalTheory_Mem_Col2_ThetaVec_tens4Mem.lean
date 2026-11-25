-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.tens4Mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:43.975951+00:00
-- url     : https://prove2.me/submissions/7a865f73-12c5-449c-8b42-61271746bb70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_matrixForm_fourfoldBlock
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_analyticAt_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)
variable {n : Type} [Fintype n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution : Tens4Mem := by
  intro n _ h Λ α θ hθ
  refine ⟨fun z _ => ?_, fun x hx z => ?_⟩
  · exact Finset.analyticAt_fun_prod (f := fun a (v : Fin 4 × n → ℂ) => θ a (slice a v)) _ fun a _ =>
      ((hθ a).1 _ trivial).comp (analyticAt_slice a z)
  · rw [opU, matrixForm_fourfoldBlock, matrixForm_fourfoldBlock, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib, Complex.exp_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => (hθ a).2 _ (hx a) (slice a z)
end GlobalTheory.Mem.Col2.ThetaVec

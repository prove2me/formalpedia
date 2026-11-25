-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.ins_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:43.342274+00:00
-- url     : https://prove2.me/submissions/eee5e030-cda0-4cf2-be87-eab54a6c02c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_matrixForm_fourfoldBlock
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_slice_ins

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
theorem _root_.solution {h : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)} {α : (n → ℂ) → ℂ} (h0 : α 0 = 1)
    {P : (Fin 4 × n → ℂ) → ℂ} (hP : P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ))
    (z : Fin 4 × n → ℂ) : (fun x => P (ins z x)) ∈ Th (matH h) α Λ := by
  have hs : ∀ a, slice a (0 : Fin 4 × n → ℂ) = 0 := fun _ => rfl
  refine ⟨fun x _ => ?_, fun y hy x => ?_⟩
  · refine (hP.1 _ trivial).comp (f := ins z) (analyticAt_pi_iff.2 fun w => ?_)
    by_cases hw : w.1 = 0
    · simp only [ins, hw, if_true]
      exact (ContinuousLinearMap.proj w.2 : (n → ℂ) →L[ℂ] ℂ).analyticAt x
    · simp only [ins, hw, if_false]
      exact analyticAt_const
  · have h1 := hP.2 (ins 0 y) (fun a => by rw [slice_ins]; split_ifs; exacts [hy, Λ.zero_mem]) (ins z x)
    have h2 : ins z x + ins 0 y = ins z (x + y) := by
      funext w
      by_cases hw : w.1 = 0 <;> simp [ins, hw]
    rw [opU, h2, matrixForm_fourfoldBlock, matrixForm_fourfoldBlock] at h1
    simpa [opU, slice_ins, Fin.sum_univ_four, Fin.prod_univ_four, hs, h0] using h1
end GlobalTheory.Mem.Col2.ThetaVec

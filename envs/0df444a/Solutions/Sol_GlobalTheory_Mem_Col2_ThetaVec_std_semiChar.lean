-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.std_semiChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:25.359806+00:00
-- url     : https://prove2.me/submissions/f3f3af7e-d08c-4742-b6ee-8684b721a323

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_th0Char_sq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_th0Char_add
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_altE_stdH
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_mem_stdLat

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
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) {α : (n → ℂ) → ℂ}
    (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) : IsSemiChar (stdH L n) (stdLat L n) α := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [← mul_self_eq_one_iff, hα x hx, stdChar, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => th0Char_sq L h0 ((mem_stdLat L).1 hx i)
  · rw [hα x hx, hα y hy, hα _ (add_mem hx hy), stdChar, stdChar, stdChar, altE_stdH, Complex.ofReal_sum,
      Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => th0Char_add L ω₀ ((mem_stdLat L).1 hx i) ((mem_stdLat L).1 hy i)
end GlobalTheory.Mem.Col2.ThetaVec

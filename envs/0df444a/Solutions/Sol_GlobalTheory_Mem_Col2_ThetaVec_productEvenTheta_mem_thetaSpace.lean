-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.productEvenTheta_mem_thetaSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:51.666104+00:00
-- url     : https://prove2.me/submissions/c37f0c77-b4e8-4958-935c-3632604011e1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_differentiable_evenTheta
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_evenTheta_translation_law
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_stdH_apply
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
theorem _root_.solution (ω₀ : ℂ) {α : (n → ℂ) → ℂ} (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) :
    F0 L ω₀ n ∈ Th (stdH L n) α (stdLat L n) := by
  refine ⟨fun z _ => ?_, fun x hx z => ?_⟩
  · refine Finset.analyticAt_fun_prod (f := fun i (z : n → ℂ) => F.th0 L (ω₀ / 2) (z i)) _ fun i _ => ?_
    exact ((differentiable_evenTheta L _).analyticAt _).comp (f := fun z : n → ℂ => z i)
      ((ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ).analyticAt z)
  · rw [hα x hx, stdChar, opU, stdH_apply, stdH_apply, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib, Complex.exp_sum, F0, prodFn, prodFn, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => evenTheta_translation_law L ω₀ ((mem_stdLat L).1 hx i) (z i)
end GlobalTheory.Mem.Col2.ThetaVec

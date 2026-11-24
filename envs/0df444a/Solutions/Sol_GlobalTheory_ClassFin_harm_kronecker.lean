-- Prove2me | solution 1 for GlobalTheory.ClassFin.harm_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:41.901776+00:00
-- url     : https://prove2.me/submissions/7fa3d424-3d87-4e02-9083-b73cb95a84e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsLogKronecker
import Theorems.Thm_GlobalTheory_ClassFin_isLog_kronecker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ) (g' : σ → Matrix κ κ ℂ), Harm g → Harm g' → Harm (fun s => g s ⊗ₖ g' s) := by
  intro ι _ _ κ _ _ σ _ g g' ⟨H, hH, hs⟩ ⟨H', hH', hs'⟩
  refine ⟨fun s => H s ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H' s, fun s => ?_, ?_⟩
  · have := isLog_kronecker (hH s) (hH' s)
    simpa only [conjTranspose_kronecker, ← mul_kronecker_mul] using this
  · ext ⟨i, k⟩ ⟨j, l⟩
    have h1 : ∑ s, H s i j = 0 := by
      have := congrFun (congrFun hs i) j
      simpa [Matrix.sum_apply] using this
    have h2 : ∑ s, H' s k l = 0 := by
      have := congrFun (congrFun hs' k) l
      simpa [Matrix.sum_apply] using this
    simp only [Matrix.sum_apply, Matrix.add_apply, kroneckerMap_apply, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, h1, h2, Matrix.zero_apply]
    simp
end GlobalTheory.ClassFin

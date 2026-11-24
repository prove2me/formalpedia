-- Prove2me | solution 1 for GlobalTheory.HasTriangularWeight.of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:16.339822+00:00
-- url     : https://prove2.me/submissions/cd6f3168-522f-4821-b735-b9999db6cb32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
import Theorems.Thm_GlobalTheory_HasTriangularWeight_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
namespace GlobalTheory
namespace HasTriangularWeight
theorem _root_.solution [∀ s, AddCommGroup (V s)] [∀ s, Module 𝕜 (V s)]
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W} (hP : HasTriangularWeight 𝕜 a P)
    (x : ∀ s, Fin (r s) → V s)
    (hc : Continuous fun b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜 => P (frameMul x b))
    (b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜) (hb : ∀ s, (b s).IsUpperTriangular) :
    P (frameMul x b) = (∏ s, ∏ i, b s i i ^ a s i) • P x := by
  let c : 𝕜 → ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜 := fun t s => b s + Matrix.diagonal fun _ => t
  have hcc : Continuous c := by
    refine continuous_pi fun s => continuous_const.add ?_
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  have hfin : (Set.range fun k : Σ s, Fin (r s) => -b k.1 k.2 k.2).Finite := Set.finite_range _
  have hd : Dense (Set.range fun k : Σ s, Fin (r s) => -b k.1 k.2 k.2)ᶜ := hfin.countable.dense_compl 𝕜
  have h1 : Continuous fun t => P (frameMul x (c t)) := hc.comp hcc
  have h2 : Continuous fun t => (∏ s, ∏ i, c t s i i ^ a s i) • P x := by
    refine Continuous.smul ?_ continuous_const
    refine continuous_finset_prod _ fun s _ => continuous_finset_prod _ fun i _ => ?_
    exact (((continuous_apply s).comp hcc).matrix_elem i i).pow _
  have h3 := Continuous.ext_on hd h1 h2 (fun t ht => by
    refine hP x (c t) (fun s => (hb s).add (Matrix.blockTriangular_diagonal _)) fun s i h => ht ?_
    refine ⟨⟨s, i⟩, ?_⟩
    simp only [c, Matrix.add_apply, Matrix.diagonal_apply_eq] at h
    exact neg_eq_of_add_eq_zero_right h)
  simpa [c] using congrFun h3 0
end HasTriangularWeight
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdProj.entryMul_poly_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:19.016269+00:00
-- url     : https://prove2.me/submissions/9074f6c9-8f31-4f2b-8b1d-ae82a5543991

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
import Theorems.Thm_GlobalTheory_CompanionTheory_AdProj_entryMul_pow_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdProj
namespace GlobalTheory.CompanionTheory.AdProj
theorem _root_.solution {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (p : Polynomial ℝ) :
    entryMul h (fun t => p.eval t) X ∈ 𝔤 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hs : entryMul h (fun t => (p + q).eval t) X =
        entryMul h (fun t => p.eval t) X + entryMul h (fun t => q.eval t) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.add_apply, Polynomial.eval_add]
      push_cast
      ring
    rw [hs]
    exact 𝔤.add_mem hp hq
  | monomial m a =>
    have hs : entryMul h (fun t => (Polynomial.monomial m a).eval t) X =
        a • entryMul h (fun t => t ^ m) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.smul_apply, Polynomial.eval_monomial,
        Complex.real_smul]
      push_cast
      ring
    rw [hs]
    exact 𝔤.smul_mem a (entryMul_pow_mem 𝔤 h hD hbr hX m)
end GlobalTheory.CompanionTheory.AdProj

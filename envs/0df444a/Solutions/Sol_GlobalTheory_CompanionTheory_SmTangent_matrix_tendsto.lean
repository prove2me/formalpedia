-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmTangent.matrix_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:45.387182+00:00
-- url     : https://prove2.me/submissions/36adf2f8-0b32-4d8d-b2bf-cb8376dfcf48

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
import Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_tendsto_pow_of_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmTangent
namespace GlobalTheory.CompanionTheory.SmTangent
theorem _root_.solution (n : ℕ) (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : γ 0 = 1) (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp ((t : ℂ) • Y))) := by
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  letI R : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI Al : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.linfty_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hd' : HasDerivAt γ Y 0 := hasDerivAt_iff_tendsto_slope.2 hs
  have key := @tendsto_pow_of_hasDerivAt _ R Al this h1 γ Y h0 hd' t
  have e : (t : ℂ) • Y = t • Y := by
    ext i j
    simp
  rw [e]
  exact key
end GlobalTheory.CompanionTheory.SmTangent

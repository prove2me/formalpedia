-- Prove2me | solution 1 for GlobalTheory.dbar_symbol_elliptic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:49.896857+00:00
-- url     : https://prove2.me/submissions/f0da32dd-f7f8-469f-89a6-c21bfd95bf28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DbarSolveComplexTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n g : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)) (ξ : Fin n → ℝ)
    (h : ∀ a, ∑ k, ((T.symm (Pi.single a 1) k : ℂ) +
      I * (T.symm (I • (Pi.single a 1 : Fin g → ℂ)) k : ℂ)) * (ξ k : ℂ) = 0) : ξ = 0 := by
  have h1 : ∀ a, T.symm (Pi.single a 1) ⬝ᵥ ξ = 0 := fun a => by
    have := congrArg Complex.re (h a)
    simpa [Complex.re_sum, dotProduct] using this
  have h2 : ∀ a, T.symm (I • (Pi.single a 1 : Fin g → ℂ)) ⬝ᵥ ξ = 0 := fun a => by
    have := congrArg Complex.im (h a)
    simpa [Complex.im_sum, dotProduct] using this
  have h3 : ∀ z : Fin g → ℂ, T.symm z ⬝ᵥ ξ = 0 := fun z => by
    have hz : z = ∑ a, ((z a).re • (Pi.single a 1 : Fin g → ℂ) +
        (z a).im • (I • (Pi.single a 1 : Fin g → ℂ))) := by
      conv_lhs => rw [← Finset.univ_sum_single z]
      refine Finset.sum_congr rfl fun a _ => ?_
      funext c
      by_cases hc : c = a
      · subst hc; simp
      · simp [hc]
    rw [hz, map_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_add, map_smul, map_smul, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2]
    simp
  have := h3 (T ξ)
  rw [T.symm_apply_apply] at this
  exact dotProduct_self_eq_zero.mp this
end GlobalTheory

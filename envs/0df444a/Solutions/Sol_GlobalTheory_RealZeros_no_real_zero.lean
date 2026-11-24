-- Prove2me | solution 1 for GlobalTheory.RealZeros.no_real_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:14.746392+00:00
-- url     : https://prove2.me/submissions/b7f09b53-fe80-4244-8d60-1069c180c518

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
import Theorems.Thm_GlobalTheory_RealZeros_riemannZeta_ne_zero_of_mem_Ioo
import Theorems.Thm_GlobalTheory_RealZeros_LFunction_chi8_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution :
    (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta σ ≠ 0) ∧
    ∀ (χ : DirichletCharacter ℂ 8), (∀ a : ZMod 8, χ a = ((ZMod.χ₈ a : ℤ) : ℂ)) →
      ∀ σ : ℝ, 0 < σ → DirichletCharacter.LFunction χ σ ≠ 0 :=
  ⟨riemannZeta_ne_zero_of_mem_Ioo, LFunction_chi8_ne_zero⟩
end GlobalTheory.RealZeros

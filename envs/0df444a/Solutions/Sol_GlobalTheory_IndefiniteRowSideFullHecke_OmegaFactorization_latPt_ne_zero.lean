-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:31.689744+00:00
-- url     : https://prove2.me/submissions/a4a71d31-a33c-4038-8e0b-4307fd7a5e91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}
open NumberField Complex
open scoped nonZeroDivisors ContDiff
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
theorem _root_.solution {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) {p : F × F} (hp : p ≠ 0) (τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z p τ ≠ 0 := by
  intro h
  have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rcases mul_eq_zero.mp h with h' | h'
  · exact h2 h'
  · by_cases hb : p.2 = 0
    · have ha : p.1 ≠ 0 := fun ha => hp (Prod.ext ha hb)
      rw [hb, map_zero] at h'
      simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_eq_zero,
        map_eq_zero] at h'
      exact ha h'
    · have him := congrArg Complex.im h'
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        zero_mul, add_zero, zero_add, Complex.zero_im] at him
      rcases mul_eq_zero.mp him with h1 | h1
      · exact hb ((map_eq_zero τ).mp h1)
      · exact (hz τ).ne' h1
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

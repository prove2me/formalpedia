-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_intT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:51.361989+00:00
-- url     : https://prove2.me/submissions/bce6cfdc-9dbd-4be2-a157-15f4e701c6c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_hasDerivAt_intT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth
namespace GlobalTheory.HeckeTwo.TermSmooth
theorem _root_.solution (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ∀ n : ℕ, ∀ a b m : ℕ, 2 ≤ a + 2 * b → ContDiffOn ℝ n (intT σ ν a b m) {y | y ≠ 0} := by
  intro n
  induction n with
  | zero =>
    intro a b m hab
    exact contDiffOn_zero.2 fun y hy => (hasDerivAt_intT σ hσ ν m hab hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro a b m hab
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_ne]
    refine ⟨fun y hy => (hasDerivAt_intT σ hσ ν m hab hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have c1 := (contDiffOn_const (c := -(a : ℂ) * I)).mul (ih (a + 1) b m (by omega))
    have c2 := (contDiffOn_const (c := 2 * (-σ - (b : ℂ)))).mul (ih a (b + 1) (m + 1) (by omega))
    have c3 := (contDiffOn_const (c := (m : ℂ))).mul (ih a b (m - 1) hab)
    refine ((c1.add c2).add c3).congr fun y hy => ?_
    exact (hasDerivAt_intT σ hσ ν m hab hy).deriv
end GlobalTheory.HeckeTwo.TermSmooth

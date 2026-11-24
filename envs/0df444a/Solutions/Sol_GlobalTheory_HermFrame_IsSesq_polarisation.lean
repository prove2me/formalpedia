-- Prove2me | solution 1 for GlobalTheory.HermFrame.IsSesq.polarisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:48.120406+00:00
-- url     : https://prove2.me/submissions/5b7380c5-3f07-4395-b29e-6e8a935e09b1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.HermFrame
namespace IsSesq
theorem _root_.solution {F : V → V → M} (hF : IsSesq F) (x y : V) :
    F x y = (1 / 4 : ℂ) • ((F (x + y) (x + y) + (-1 : ℂ) • F (x - y) (x - y)) +
      (I • F (x + I • y) (x + I • y) + (-I) • F (x - I • y) (x - I • y))) := by
  have h : ∀ v : V, -v = (-1 : ℂ) • v := fun v => by simp
  simp only [sub_eq_add_neg, h, hF.add_left, hF.add_right, hF.smul_left, hF.smul_right, conj_I,
    map_neg, map_one]
  match_scalars <;> (ring_nf; try simp only [I_sq, I_pow_three]; try ring_nf)
end IsSesq
end GlobalTheory.HermFrame

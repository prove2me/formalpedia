-- Prove2me | solution 1 for GlobalTheory.ThetaInter.chi_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:55.635795+00:00
-- url     : https://prove2.me/submissions/4abff600-f2d5-4d2a-9e2e-5517d52c469d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
namespace GlobalTheory.ThetaInter
theorem _root_.solution (x y : V) : chi H x y = 1 ↔ ∃ m : ℤ, altE H x y = m := by
  rw [chi, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have : (altE H x y : ℂ) = -k := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      linear_combination -hk
    exact_mod_cast this
  · rintro ⟨m, hm⟩
    exact ⟨-m, by rw [hm]; push_cast; ring⟩
end GlobalTheory.ThetaInter

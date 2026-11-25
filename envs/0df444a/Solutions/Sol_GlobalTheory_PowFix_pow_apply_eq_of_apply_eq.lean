-- Prove2me | solution 1 for GlobalTheory.PowFix.pow_apply_eq_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:28:08.068936+00:00
-- url     : https://prove2.me/submissions/578df9e6-28da-4f52-a8f1-5dd623d2f2c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPosPowGaloisFixingFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.PowFix
namespace GlobalTheory.PowFix
theorem _root_.solution {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (τ : Ω ≃ₐ[E] Ω) (x : Ω) (h : τ x = x) (j : ℕ) : (τ ^ j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
end GlobalTheory.PowFix

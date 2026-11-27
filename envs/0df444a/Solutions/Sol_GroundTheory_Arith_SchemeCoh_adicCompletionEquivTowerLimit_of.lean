-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.adicCompletionEquivTowerLimit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:40.657551+00:00
-- url     : https://prove2.me/submissions/c50a636c-eb56-4079-8b47-cdf5c866adaf

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {A : Type u} [CommRing A] (I : Ideal A) {H : Type u} [AddCommGroup H] [Module A H]
  (K : ℕ → Submodule A H) (hK : Antitone K)
variable {I K}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (h₁ : ∀ n, I ^ (n + 1) • (⊤ : Submodule A H) ≤ K n)
    {c : ℕ} (h₂ : ∀ n, K (n + c) ≤ I ^ n • (⊤ : Submodule A H)) (h : H) (n : ℕ) :
    (adicCompletionEquivTowerLimit hK h₁ h₂ (AdicCompletion.of I H h)).1 n =
      Submodule.Quotient.mk h := rfl
end GroundTheory.Arith.SchemeCoh

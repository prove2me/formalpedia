-- Prove2me | solution 1 for GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:49.994013+00:00
-- url     : https://prove2.me/submissions/12af3755-ad99-4f51-8725-162f1c7ef8e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSmoothAtOfSmoothQuotientPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSmoothAtOfSmoothModIdealPowers
import Theorems.Thm_GlobalTheory_SmoothLimit_isSmoothAt_of_smooth_quotient_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmoothAdic
open TensorProduct IsLocalRing
namespace GlobalTheory.SmoothAdic
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], (∀ e : ℕ, Algebra.Smooth (R ⧸ I ^ (e + 1)) (TensorProduct R (R ⧸ I ^ (e + 1)) C)) → ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap R C) = IsLocalRing.maximalIdeal R → Algebra.IsSmoothAt R q := by
  intro R _ _ _ I hI C _ _ _ h q _ hq
  refine GlobalTheory.SmoothLimit.isSmoothAt_of_smooth_quotient_pow (V := R) (A := C) (fun e => ?_) q hq
  have hle : I ^ (e + 1) ≤ maximalIdeal R ^ (e + 1) :=
    Ideal.pow_right_mono (le_maximalIdeal hI) (e + 1)
  let _ : Algebra (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1)) :=
    (Ideal.Quotient.factor hle).toAlgebra
  have : IsScalarTower R (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := h e
  exact Algebra.Smooth.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1))
      (R ⧸ maximalIdeal R ^ (e + 1)) C)
end GlobalTheory.SmoothAdic

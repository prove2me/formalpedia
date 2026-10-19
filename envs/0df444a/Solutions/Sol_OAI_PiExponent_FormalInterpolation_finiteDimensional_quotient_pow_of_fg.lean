-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_pow_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:28:02.573987+00:00
-- url     : https://prove2.me/submissions/26974994-2ff7-474a-ba49-7cf1a7324277

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.NilpotentKer

open TensorProduct

-- The induction is adapted from Andrew Yang's proof of
-- Module.finite_of_surjective_of_ker_le_nilradical in Mathlib.
theorem solution
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (I : Ideal A) (hI : I.FG)
    (hfinite : FiniteDimensional K (A ⧸ I)) (s : Nat) :
    FiniteDimensional K (A ⧸ I ^ s) := by
  letI : Module.Finite K (A ⧸ I) := hfinite
  induction s with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
  | succ n IH =>
      let φ : (A ⧸ I ^ (n + 1)) →ₐ[A] A ⧸ I ^ n :=
        Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right n.le_succ)
      have hφ : Function.Surjective φ :=
        Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
      have hφ' : φ.toLinearMap ∘ₗ (I ^ (n + 1)).mkQ = (I ^ n).mkQ := rfl
      refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker
        (φ.toLinearMap.restrictScalars K) ?_ ?_⟩
      · simpa [LinearMap.range_eq_top_of_surjective
          (φ.toLinearMap.restrictScalars K) hφ] using Module.Finite.fg_top
      · have : Module.Finite K ((A ⧸ I) ⊗[A] ↑(I ^ n)) := by
          have : Module.Finite A ↑(I ^ n) := .of_fg (Ideal.FG.pow hI)
          exact .trans (A ⧸ I) _
        let ψ : (A ⧸ I) ⊗[A] ↑(I ^ n) →ₗ[A] (A ⧸ I ^ (n + 1)) := by
          refine ?_ ∘ₗ (TensorProduct.quotTensorEquivQuotSMul _ I).toLinearMap
          refine Submodule.liftQ _ ((Submodule.mkQ _).comp (I ^ n).subtype) ?_
          rw [LinearMap.ker_comp,
            ← Submodule.map_le_map_iff_of_injective (I ^ n).subtype_injective,
            Submodule.map_smul'', Submodule.map_comap_eq]
          simpa [pow_succ'] using Ideal.mul_le_right (I := I) (J := I ^ n)
        convert! Module.Finite.fg_top.map (ψ.restrictScalars K) using 1
        suffices LinearMap.ker φ.toLinearMap =
            Submodule.map (I ^ (n + 1)).mkQ (I ^ n) by
          simpa [LinearMap.range_restrictScalars, ψ, LinearMap.range_comp,
            Submodule.range_liftQ]
        apply Submodule.comap_injective_of_surjective (I ^ (n + 1)).mkQ_surjective
        simpa [← LinearMap.ker_comp, hφ'] using Ideal.pow_le_pow_right n.le_succ
-- Prove2me | solution 1 for IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2734967a-a06a-5859-a81f-4b6f2abc59aa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
set_option autoImplicit false
universe u v

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution
    (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] (x : L) (hx : Transcendental K x) :
    ∃ e : ↥(IntermediateField.adjoin K ({x} : Set L)) ≃ₐ[K] RatFunc K,
      e ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ = RatFunc.X := by
  classical

  have hinj0 : Function.Injective (Polynomial.aeval (R := K) x) := transcendental_iff_injective.mp hx
  have hφ : nonZeroDivisors (Polynomial K) ≤
      Submonoid.comap (Polynomial.aeval x : Polynomial K →ₐ[K] L) (nonZeroDivisors L) := by
    intro p hp
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hp (hinj0 (h.trans (map_zero _).symm)))
  let ψ : RatFunc K →ₐ[K] L := RatFunc.liftAlgHom (Polynomial.aeval x) hφ
  have hψ : ∀ p q : Polynomial K,
      ψ (algebraMap _ (RatFunc K) p / algebraMap _ (RatFunc K) q) = Polynomial.aeval x p / Polynomial.aeval x q :=
    RatFunc.liftAlgHom_apply_div _ hφ

  have hmemA : ∀ p : Polynomial K, Polynomial.aeval x p ∈ IntermediateField.adjoin K ({x} : Set L) := fun p =>
    IntermediateField.algebra_adjoin_le_adjoin K _
      (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩)
  have hrange : ∀ r : RatFunc K, ψ r ∈ IntermediateField.adjoin K ({x} : Set L) := by
    intro r
    rw [← RatFunc.num_div_denom r, hψ]
    exact div_mem (hmemA _) (hmemA _)
  let f : RatFunc K →ₐ[K] ↥(IntermediateField.adjoin K ({x} : Set L)) :=
    ψ.codRestrict (IntermediateField.adjoin K ({x} : Set L)).toSubalgebra hrange

  have hf : Function.Bijective f := by
    refine ⟨fun a b h => (ψ : RatFunc K →+* L).injective
      (congrArg (fun z : ↥(IntermediateField.adjoin K ({x} : Set L)) => (z : L)) h), fun y => ?_⟩
    obtain ⟨r, hr, s, hs, hy⟩ := IntermediateField.mem_adjoin_iff_div.mp y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hr
    obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).mp hs
    refine ⟨algebraMap _ (RatFunc K) p / algebraMap _ (RatFunc K) q, Subtype.ext ?_⟩
    show ψ _ = (y : L)
    rw [hψ, ← hy]
  refine ⟨(AlgEquiv.ofBijective f hf).symm, ?_⟩
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.ofBijective_apply]
  apply Subtype.ext
  show x = ψ RatFunc.X
  rw [← RatFunc.algebraMap_X, ← div_one (algebraMap (Polynomial K) (RatFunc K) Polynomial.X),
    ← map_one (algebraMap (Polynomial K) (RatFunc K)), hψ, map_one, div_one, Polynomial.aeval_X]

end S_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
end P2MW
export P2MW.S_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental (solution)

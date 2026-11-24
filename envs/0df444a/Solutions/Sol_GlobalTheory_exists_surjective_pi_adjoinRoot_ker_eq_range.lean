-- Prove2me | solution 1 for GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:59.493337+00:00
-- url     : https://prove2.me/submissions/54bf22e2-8709-4f81-a1e6-2f4fe44296a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRange
import Theorems.Thm_GlobalTheory_exists_equiv_pi_adjoinRoot_of_aeval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [Field F] (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X])
    [Fact (Irreducible f)] :
    ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧
      (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧
      LinearMap.ker π = LinearMap.range (aeval g f) ∧
      Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by
  set N : Submodule F V := LinearMap.range (aeval g f) with hN
  have hg : N ≤ N.comap g := by
    rintro _ ⟨v, rfl⟩
    refine ⟨g v, ?_⟩
    have h1 : aeval g f * g = g * aeval g f := by
      have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using this
    exact congrArg (fun u : Module.End F V => u v) h1
  let gq : Module.End F (V ⧸ N) := N.mapQ N g hg
  have hq : ∀ v, gq (N.mkQ v) = N.mkQ (g v) := fun v => rfl
  have hp : ∀ (p : F[X]) (v : V), aeval gq p (N.mkQ v) = N.mkQ (aeval g p v) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => intro v; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro v; simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial n a ih =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply, hq, ih]
  have h0 : aeval gq f = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := N.mkQ_surjective x
    rw [hp]
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨v, rfl⟩
  obtain ⟨t, e, he, hd⟩ := exists_equiv_pi_adjoinRoot_of_aeval_eq_zero F (V ⧸ N) gq f h0
  refine ⟨t, e.toLinearMap ∘ₗ N.mkQ, e.surjective.comp N.mkQ_surjective, fun v => ?_, ?_, ?_⟩
  · have := he (N.mkQ v)
    rw [hq] at this
    exact this
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]
  · have h1 := LinearMap.finrank_range_add_finrank_ker (aeval g f)
    have h2 := Submodule.finrank_quotient_add_finrank N
    rw [← hN] at h1
    omega
end GlobalTheory

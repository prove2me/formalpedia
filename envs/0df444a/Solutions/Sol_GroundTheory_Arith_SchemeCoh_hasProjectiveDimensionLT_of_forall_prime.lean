-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_forall_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:11.99621+00:00
-- url     : https://prove2.me/submissions/7d15d52c-3f4f-44b6-ab5e-63669c5a5d66

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre

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
open IsLocalRing Ideal RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R]
open CategoryTheory Abelian
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsNoetherianRing R] (n : ℕ) (I : Ideal R)
    (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ q)) n)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ a ∈ I, ∀ m : M, a • m = 0) :
    HasProjectiveDimensionLT (ModuleCat.of R M) n := by
  revert hM
  induction ‹Module.Finite R M› using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    with
  | subsingleton N =>
    intro _
    have : Limits.IsZero (ModuleCat.of R N) := ModuleCat.isZero_of_subsingleton _
    have := this.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 n (Nat.zero_le _)
  | quotient N p e =>
    intro hN
    have hle : I ≤ p.1 := by
      intro a ha
      have h := congrArg e (hN a ha (e.symm 1))
      rw [map_smul, LinearEquiv.apply_symm_apply, map_zero, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h
      exact h
    have := hI p.1 p.2 hle
    exact hasProjectiveDimensionLT_of_iso e.symm.toModuleIso n
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hN
    have k₁ : ∀ a ∈ I, ∀ m : N₁, a • m = 0 := fun a ha m ↦ hf (by rw [map_smul, hN a ha, map_zero])
    have k₃ : ∀ a ∈ I, ∀ m : N₃, a • m = 0 := fun a ha m ↦ by
      obtain ⟨m, rfl⟩ := hg m
      rw [← map_smul, hN a ha, map_zero]
    have hS := ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero f g (LinearMap.ext fun x ↦ hfg.apply_apply_eq_zero x))
      hfg hf hg
    exact hS.hasProjectiveDimensionLT_X₂ n (h₁ k₁) (h₃ k₃)
end GroundTheory.Arith.SchemeCoh

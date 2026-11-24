-- Prove2me | solution 1 for GlobalTheory.MinkDiv.prime_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:17:29.929018+00:00
-- url     : https://prove2.me/submissions/3a13565f-0df9-4bf0-8916-56270cbe3dbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MinkowskiDivisible
import Theorems.Thm_GlobalTheory_MinkDiv_iterate_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.MinkDiv
variable {A : Type} [AddCommGroup A]
namespace GlobalTheory.MinkDiv
theorem _root_.solution (l p : ℕ) (hl : l.Prime) (ho : Odd l) (hp : p.Prime) (f : A →+ A)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x)
    (hord : ∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[p] x = x)
    (hfix : ∀ x : A, l • x = 0 → f x = x) :
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by
  set g : A →+ A := f - AddMonoidHom.id A with hg
  have hfg : ∀ z, f z = z + g z := fun z => by simp [hg]
  have key : ∀ k : ℕ, ∀ x : A, l ^ (k + 1) • x = 0 → g x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have := hfix x (by simpa using hx)
      simp [hg, this]
    | succ k ih =>
      intro x hx
      have h1 : ∀ z : A, l • z = 0 → g z = 0 := fun z hz =>
        ih z (by rw [pow_succ, mul_smul, hz, smul_zero])
      have h2 : ∀ z : A, l ^ (k + 1 + 1) • z = 0 → l • g z = 0 := fun z hz => by
        rw [← map_nsmul]
        exact ih _ (by rw [← mul_smul, ← pow_succ]; exact hz)
      by_cases hpl : p = l
      · subst hpl
        obtain ⟨y, rfl⟩ := hdiv x
        have hy : p ^ (k + 1 + 1 + 1) • y = 0 := by rw [pow_succ, mul_smul]; exact hx
        have e1 : p • p • g y = 0 := by
          rw [← map_nsmul g p y]; exact h2 _ hx
        have e2 : p • g (g y) = 0 := by
          apply h2
          rw [pow_succ, pow_succ, mul_smul, mul_smul, e1, smul_zero]
        have e3 : g (g (g y)) = 0 := h1 _ e2
        have e4 := iterate_eq f g hfg y e3 p
        rw [hord y _ hy] at e4
        have h3 : 2 < p := by
          rcases hp.two_le.lt_or_eq with h | h
          · exact h
          · subst h; exact absurd ho (by decide)
        obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := 2) (by norm_num) h3
        rw [hc, mul_comm, mul_smul, e2, smul_zero, add_zero] at e4
        rw [map_nsmul]
        exact (add_eq_left.mp e4.symm)
      · have e1 : l • g x = 0 := h2 x hx
        have e2 : g (g x) = 0 := h1 _ e1
        have e4 := iterate_eq f g hfg x (by rw [e2, map_zero]) p
        rw [hord x _ hx, e2, smul_zero, add_zero] at e4
        have e5 : p • g x = 0 := add_eq_left.mp e4.symm
        have hc : Nat.Coprime p l := (Nat.coprime_primes hp hl).mpr hpl
        have d1 := addOrderOf_dvd_of_nsmul_eq_zero e5
        have d2 := addOrderOf_dvd_of_nsmul_eq_zero e1
        have d3 := Nat.dvd_gcd d1 d2
        rw [hc, Nat.dvd_one] at d3
        exact AddMonoid.addOrderOf_eq_one_iff.mp d3
  intro a x hx
  have := key a x (by rw [pow_succ', mul_smul, hx, smul_zero])
  rw [hfg, this, add_zero]
end GlobalTheory.MinkDiv

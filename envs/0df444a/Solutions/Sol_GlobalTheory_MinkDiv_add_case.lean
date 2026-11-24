-- Prove2me | solution 1 for GlobalTheory.MinkDiv.add_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:34:01.749467+00:00
-- url     : https://prove2.me/submissions/e65ac00c-a2a8-4a90-99c1-f48c17b71253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MinkowskiDivisible
import Theorems.Thm_GlobalTheory_MinkDiv_prime_case

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
theorem _root_.solution (l : ℕ) (hl : l.Prime) (ho : Odd l)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x) (r : ℕ) (hr : r ≠ 0) :
    ∀ f : AddMonoid.End A, (∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[r] x = x) →
    (∀ x : A, l • x = 0 → f x = x) →
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by
  induction r using induction_on_primes with
  | zero => exact absurd rfl hr
  | one => intro f h _ a x hx; exact h x a hx
  | prime_mul p b hp ih =>
    intro f hord hfix
    have hb : b ≠ 0 := by rintro rfl; simp at hr
    have hc : ((f ^ p : AddMonoid.End A) : A → A) = f^[p] := AddMonoid.End.coe_pow _ _ _
    have := ih hb (f ^ p)
      (fun x a hx => by rw [hc, ← Function.iterate_mul]; exact hord x a hx)
      (fun x hx => by rw [hc]; exact Function.iterate_fixed (hfix x hx) p)
    exact prime_case l p hl ho hp f hdiv
      (fun x a hx => by have h := this a x hx; rw [hc] at h; exact h) hfix
end GlobalTheory.MinkDiv

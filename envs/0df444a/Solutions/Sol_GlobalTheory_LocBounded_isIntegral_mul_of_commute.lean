-- Prove2me | solution 1 for GlobalTheory.LocBounded.isIntegral_mul_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:46:43.807519+00:00
-- url     : https://prove2.me/submissions/acdc13b6-ade8-4472-a995-10a65092bff6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded
namespace GlobalTheory.LocBounded
theorem _root_.solution {R A : Type} [CommRing R] [Ring A] [Algebra R A] {x y : A}
    (hc : Commute x y) (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x * y) := by
  let S := Algebra.adjoin R ({x, y} : Set A)
  letI : CommRing S := Algebra.adjoinCommRingOfComm R (by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [rfl, hc.eq, hc.eq.symm, rfl])
  have hx' : x ∈ S := Algebra.subset_adjoin (by simp)
  have hy' : y ∈ S := Algebra.subset_adjoin (by simp)
  have h1 : IsIntegral R (⟨x, hx'⟩ : S) :=
    (isIntegral_algHom_iff S.val Subtype.val_injective).1 hx
  have h2 : IsIntegral R (⟨y, hy'⟩ : S) :=
    (isIntegral_algHom_iff S.val Subtype.val_injective).1 hy
  exact (h1.mul h2).map S.val
end GlobalTheory.LocBounded

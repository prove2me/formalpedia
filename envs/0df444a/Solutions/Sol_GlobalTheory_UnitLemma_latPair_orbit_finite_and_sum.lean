-- Prove2me | solution 1 for GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:10.489004+00:00
-- url     : https://prove2.me/submissions/fdffe948-7411-4df9-aeb3-68ba2df80523

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticePairOrbitsFiniteAndCardProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
namespace GlobalTheory.UnitLemma
theorem _root_.solution : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂), Finite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) → Finite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) → Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) ∧ ∀ (f₁ : stLat O E g₁ → ℚ) (f₂ : stLat O E g₂ → ℚ), (∀ (t : A₁ˣ) (y : stLat O E g₁), f₁ (t • y) = f₁ y) → (∀ (t : A₂ˣ) (y : stLat O E g₂), f₂ (t • y) = f₂ y) → ∑ᶠ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂), f₁ (Quotient.out o).1 * f₂ (Quotient.out o).2 = (∑ᶠ o : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁), f₁ (Quotient.out o)) * (∑ᶠ o : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂), f₂ (Quotient.out o)) := by
  intro O E A₁ A₂ _ _ _ _ _ _ _ _ g₁ g₂ h₁ h₂
  let e := latPairOrbitEquiv O E A₁ A₂ g₁ g₂
  haveI hfin : Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) := Finite.of_equiv _ e.symm
  refine ⟨hfin, ?_⟩
  intro f₁ f₂ hf₁ hf₂

  have inv₁ : ∀ a b : stLat O E g₁, (MulAction.orbitRel A₁ˣ (stLat O E g₁)) a b → f₁ a = f₁ b := by
    intro a b h
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact hf₁ t b
  have inv₂ : ∀ a b : stLat O E g₂, (MulAction.orbitRel A₂ˣ (stLat O E g₂)) a b → f₂ a = f₂ b := by
    intro a b h
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact hf₂ t b
  have key : ∀ x : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁) × MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂),
      f₁ (Quotient.out (e.symm x)).1 * f₂ (Quotient.out (e.symm x)).2 = f₁ (Quotient.out x.1) * f₂ (Quotient.out x.2) := by
    intro x
    have hx : e (e.symm x) = x := e.apply_symm_apply x
    set o := e.symm x
    have h1 : (Quotient.mk _ (Quotient.out o).1 : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) = x.1 := by
      rw [← hx]
      conv_rhs => rw [← Quotient.out_eq o]
      rfl
    have h2 : (Quotient.mk _ (Quotient.out o).2 : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) = x.2 := by
      rw [← hx]
      conv_rhs => rw [← Quotient.out_eq o]
      rfl
    rw [inv₁ _ _ (Quotient.exact (h1.trans (Quotient.out_eq x.1).symm)),
      inv₂ _ _ (Quotient.exact (h2.trans (Quotient.out_eq x.2).symm))]
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁))
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂))
  rw [← finsum_comp_equiv e.symm]
  simp_rw [key]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
end GlobalTheory.UnitLemma

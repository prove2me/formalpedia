-- Prove2me | solution 1 for GlobalTheory.UnitCase.coeff_mul_mfact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:34.636573+00:00
-- url     : https://prove2.me/submissions/2bb4ee20-dcd7-437e-9110-4e4b120ace5f

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_mfact_int
import Theorems.Thm_GlobalTheory_UnitCase_coeff_pow_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution [Fintype κ] {l : ℕ} (hl : l.Prime) (q : MvPolynomial κ ℤ) (A β : κ →₀ ℕ)
    (h : ∀ j, l * β j ≤ A j) (hne : A ≠ l • β) :
    ∃ z : ℤ, MvPolynomial.coeff A (q ^ l) * (mfact A : ℤ) = (-(l : ℤ)) ^ (∑ j, β j) * (l * z) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, A j ≠ l * β j := by
    by_contra hc
    push Not at hc
    exact hne (Finsupp.ext fun j => by simpa using hc j)
  by_cases hd : l ∣ A j
  · obtain ⟨z, hz⟩ := mfact_int hl A (β + Finsupp.single j 1) fun i => by
      by_cases hi : j = i
      · subst hi
        obtain ⟨t, ht⟩ := hd
        have h1 := h j
        rw [ht] at h1 hj ⊢
        have h2 : β j ≤ t := Nat.le_of_mul_le_mul_left h1 hl.pos
        have h3 : t ≠ β j := fun e => hj (by rw [e])
        refine Nat.mul_le_mul_left _ ?_
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        omega
      · simpa [Finsupp.single_apply, hi] using h i
    have hs : ∑ i, (β + Finsupp.single j 1 : κ →₀ ℕ) i = ∑ i, β i + 1 := by
      simp [Finset.sum_add_distrib, Finsupp.single_apply]
    refine ⟨-(MvPolynomial.coeff A (q ^ l) * z), ?_⟩
    rw [hz, hs]
    ring
  · obtain ⟨z, hz⟩ := mfact_int hl A β h
    have h0 := coeff_pow_zmod hl q A
    rw [MvPolynomial.coeff_expand_of_not_dvd _ hd, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    obtain ⟨t, ht⟩ := h0
    refine ⟨t * z, ?_⟩
    rw [hz, ht]
    ring
end GlobalTheory.UnitCase

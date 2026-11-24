-- Prove2me | solution 1 for GlobalTheory.natCard_le_of_forall_pow_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:51.14586+00:00
-- url     : https://prove2.me/submissions/3f292553-50b5-4dae-9eb1-d4e470ac835c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardPrimesOverEqFinrankOfTrivialFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type*) [CommRing F] [IsDomain F] [Finite F]
    (q : ℕ) (hq : 1 < q) (h : ∀ x : F, x ^ q = x) : Nat.card F ≤ q := by
  classical
  haveI := Fintype.ofFinite F
  have hne : (X ^ q - X : F[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
    rw [natDegree_X_pow, natDegree_X] at h1
    omega
  have hdeg : (X ^ q - X : F[X]).natDegree ≤ q := by
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_X_pow, natDegree_X]
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans ?_ hdeg
  refine Polynomial.card_le_degree_of_subset_roots ?_
  intro x _
  rw [mem_roots hne]
  simp [h x]
end GlobalTheory

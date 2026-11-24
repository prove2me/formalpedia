-- Prove2me | solution 1 for GlobalTheory.Published.dn_eq_of_action_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:01.199053+00:00
-- url     : https://prove2.me/submissions/8755cce6-44de-4733-86a0-b55c7e0d7dd2

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.Published
variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {M : Type*} [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M]
omit [TopologicalSpace Γ] [TopologicalSpace M] [IsTopologicalAddGroup M]
namespace GlobalTheory.Published
theorem _root_.solution {R R' : Type*} [CommRing R] [CommRing R'] [Module R M] [Module R' M]
    (rho : Representation R Γ M) (rho' : Representation R' Γ M)
    (h : ∀ g m, rho g m = rho' g m) (n : ℕ) (f : (Fin n → Γ) → M) :
    dn rho n f = dn rho' n f := by
  funext g
  show rho (g 0) (f fun i => g i.succ) + (Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
    rho' (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R') ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases Nat.even_or_odd ((j : ℕ) + 1) with hj | hj <;> simp [hj.neg_one_pow]
end GlobalTheory.Published

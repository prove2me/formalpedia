-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_eq_algebraMap_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:03.133911+00:00
-- url     : https://prove2.me/submissions/cb1421ff-d8c0-4a47-a77d-3c2dda53e2b5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Theorems.Thm_GroundTheory_Automorphic_exists_ne_zero_of_isIrreducible
import Theorems.Thm_GroundTheory_Automorphic_injective_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Polynomial Cardinal
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution [ρ.IsIrreducible]
    (φ : Representation.IntertwiningMap ρ ρ) {p : ℂ[X]} (hp : p ≠ 0) (hφ : aeval φ p = 0) :
    ∃ c : ℂ, φ = algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  induction hn : p.natDegree generalizing p with
  | zero =>
    rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨a, rfl⟩ := hn
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hp
    rw [aeval_C] at hφ
    have h1 : a • v = 0 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hφ
    exact absurd h1 (smul_ne_zero ha hv)
  | succ n ih =>
    have hdeg : p.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hp, hn]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg
    set q := p /ₘ (X - C r)
    have hpq : (X - C r) * q = p := mul_divByMonic_eq_iff_isRoot.2 hr
    have hq : q ≠ 0 := by
      intro hq
      rw [hq, mul_zero] at hpq
      exact hp hpq.symm
    have hqdeg : q.natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]
      rfl
    by_cases hφr : φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r = 0
    · exact ⟨r, sub_eq_zero.1 hφr⟩
    · refine ih hq ?_ hqdeg
      have hinj := injective_of_ne_zero hφr
      rw [← hpq, map_mul, map_sub, aeval_X, aeval_C] at hφ
      refine DFunLike.ext _ _ fun w => hinj ?_
      have h1 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f w) hφ
      change (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r) ((aeval φ q) w) =
        (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r) 0
      rw [map_zero]
      exact h1
end GroundTheory.Automorphic

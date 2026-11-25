-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.esymm_mem_adjoin_psum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:51.518461+00:00
-- url     : https://prove2.me/submissions/5ae20a83-7add-4e39-b2e7-f21c5f317cd7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (k : ℕ) (hk : k ≤ n) :
    esymm (Fin n) ℂ k ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set A := Algebra.adjoin ℂ (Set.range (psumFin (n := n)))
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [esymm_zero]; exact A.one_mem
  have hps : ∀ j, 1 ≤ j → j ≤ n → psum (Fin n) ℂ j ∈ A := by
    intro j hj1 hjn
    refine Algebra.subset_adjoin ⟨⟨j - 1, by omega⟩, ?_⟩
    show psum (Fin n) ℂ (j - 1 + 1) = psum (Fin n) ℂ j
    rw [Nat.sub_add_cancel hj1]
  have hsum : (k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k ∈ A := by
    rw [mul_esymm_eq_sum]
    refine A.mul_mem (A.pow_mem (A.neg_mem A.one_mem) _) (A.sum_mem fun a ha => ?_)
    rw [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    exact A.mul_mem (A.mul_mem (A.pow_mem (A.neg_mem A.one_mem) _) (ih a.1 ha.2 (by omega)))
      (hps a.2 (by omega) (by omega))
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have e : esymm (Fin n) ℂ k =
      (k : ℂ)⁻¹ • ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) := by
    rw [← map_natCast (C : ℂ →+* MvPolynomial (Fin n) ℂ) k, smul_eq_C_mul, ← mul_assoc, ← C_mul,
      inv_mul_cancel₀ hk', C_1, one_mul]
  rw [e]
  exact A.smul_mem hsum _
end GroundTheory.Automorphic.HarishChandra

-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_self_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:55.930802+00:00
-- url     : https://prove2.me/submissions/27b3837a-2d54-478b-87d3-c7cab015a284

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mfact_pos
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {σ : Type*}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (f : MvPolynomial σ ℂ) : fischer f f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [fischer_self, Complex.ofReal_eq_zero] at h
  have hnn : ∀ m ∈ f.support, 0 ≤ (mfact m : ℝ) * Complex.normSq (coeff m f) :=
    fun m _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext m
  by_contra hm
  have hm' : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have := hz m hm'
  rcases mul_eq_zero.1 this with h1 | h1
  · exact (Nat.cast_ne_zero.2 (mfact_pos m).ne') h1
  · exact hm (Complex.normSq_eq_zero.1 h1)
end GroundTheory.Automorphic.HarishChandra

-- Prove2me | solution 1 for GroundTheory.Automorphic.finite_latticeDual_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:02.03972+00:00
-- url     : https://prove2.me/submissions/60777b9e-1604-4bde-be86-a6ee0b579079

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
import Theorems.Thm_GroundTheory_Automorphic_eq_zero_of_forall_inner_eq_zero

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
open Module Submodule
open scoped RealInnerProductSpace
universe u
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
namespace GroundTheory.Automorphic
theorem _root_.solution [FiniteDimensional ℝ X] {L : AddSubgroup X}
    (hL : span ℝ (L : Set X) = ⊤) (C : ℝ) :
    ({y | y ∈ latticeDual L ∧ ‖y‖ ≤ C} : Set X).Finite := by
  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent ℝ (L : Set X)
  rw [hL] at hspan
  have hsfin : s.Finite := hli.setFinite
  have : Finite s := hsfin.to_subtype
  let Φ : X → s → ℝ := fun y x => ⟪y, (x : X)⟫
  have hinj : Set.InjOn Φ {y | y ∈ latticeDual L ∧ ‖y‖ ≤ C} := by
    intro y _ y' _ h
    have : y - y' = 0 := eq_zero_of_forall_inner_eq_zero hspan fun x hx => by
      have := congrFun h ⟨x, hx⟩
      simp only [Φ] at this
      rw [inner_sub_left, this, sub_self]
    exact sub_eq_zero.1 this
  refine Set.Finite.of_finite_image (Set.Finite.subset (Set.Finite.pi (t := fun x : s =>
    (Int.cast '' Set.Icc (-⌈C * ‖(x : X)‖⌉) ⌈C * ‖(x : X)‖⌉ : Set ℝ))
    fun x => (Set.finite_Icc _ _).image _) ?_) hinj
  rintro _ ⟨y, ⟨hyD, hyC⟩, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro x
  obtain ⟨n, hn⟩ := hyD x (hsL x.2)
  refine ⟨n, ⟨?_, ?_⟩, hn.symm⟩
  all_goals
    have h1 : |(n : ℝ)| ≤ C * ‖(x : X)‖ := by
      rw [← hn]
      exact (abs_real_inner_le_norm y x).trans
        (mul_le_mul_of_nonneg_right hyC (norm_nonneg _))
    have h2 : C * ‖(x : X)‖ ≤ ⌈C * ‖(x : X)‖⌉ := Int.le_ceil _
  · have : -((⌈C * ‖(x : X)‖⌉ : ℤ) : ℝ) ≤ n := by linarith [neg_abs_le (n : ℝ)]
    exact_mod_cast this
  · have : (n : ℝ) ≤ ((⌈C * ‖(x : X)‖⌉ : ℤ) : ℝ) := by linarith [le_abs_self (n : ℝ)]
    exact_mod_cast this
end GroundTheory.Automorphic

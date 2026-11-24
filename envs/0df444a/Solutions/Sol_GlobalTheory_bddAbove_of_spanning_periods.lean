-- Prove2me | solution 1 for GlobalTheory.bddAbove_of_spanning_periods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:17.048259+00:00
-- url     : https://prove2.me/submissions/55595066-be37-4d9f-9ba0-1dbd875b89c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BddAboveOfSpanningPeriods

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (g : R → ℝ) (hg : Continuous g) (S : Set R)
    (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) :
    ∃ C : ℝ, ∀ x, g x ≤ C := by
  classical
  let P : AddSubgroup R :=
    { carrier := {p | ∀ x, g (x + p) = g x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by
        rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by
        have := ha (x + -a)
        rw [← this]; simp }
  have hP : Submodule.span ℝ (P : Set R) = ⊤ := by
    rw [eq_top_iff, ← hS, Submodule.span_le]
    intro s hs
    obtain ⟨N, hN, h⟩ := hper s hs
    have h1 : (N : ℝ) • s ∈ Submodule.span ℝ (P : Set R) := Submodule.subset_span h
    have h2 := Submodule.smul_mem _ ((N : ℝ)⁻¹) h1
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at h2
  obtain ⟨t, htP, hspan, hli⟩ := exists_linearIndependent ℝ (P : Set R)
  have hfin : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b : Module.Basis t ℝ R := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, hP])
  have hb : Submodule.span ℤ (Set.range b) ≤ AddSubgroup.toIntSubmodule P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i = (i : R) := by simp [b]
    rw [this]
    exact htP i.2
  have hK : IsCompact (Metric.closedBall (0 : R) (∑ i, ‖b i‖)) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.bddAbove_image hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hfl : ((ZSpan.floor b x : R)) ∈ P := hb (ZSpan.floor b x).2
  have hx : g x = g (ZSpan.fract b x) := by
    have := hfl (ZSpan.fract b x)
    rw [← this, ZSpan.fract_apply]; simp
  rw [hx]
  apply hC
  exact ⟨_, by simpa using ZSpan.norm_fract_le b x, rfl⟩
end GlobalTheory

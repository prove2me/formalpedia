-- Prove2me | solution 1 for OAI.Problem310.ScaleDiscretization.exists_affine_floor_representatives
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T05:48:25.376515+00:00
-- url     : https://prove2.me/submissions/786887d7-4f37-41ae-85e5-52f4568211b7

-- Adapted from OpenAI/math contributors, MonotoneRepresentatives.lean lines 65–104,
-- commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a. Mathematical proof credited upstream.
-- Alexander Richard Towell (queelius) directed the contribution; Codex adapted
-- and verified the Lean proof and its actual accepted dependency.
import Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_monotone_representatives

universe u_ι
open scoped BigOperators
open OAI.Problem310.ScaleDiscretization

/-- An integer floor can increase by at most the ceiling of the displacement. -/
private lemma floor_sub_floor_le_ceil (x y : ℝ) : ⌊y⌋ - ⌊x⌋ ≤ ⌈y - x⌉ := by
  have hy := Int.floor_le y
  have hx := Int.lt_floor_add_one x
  have hc := Int.le_ceil (y - x)
  have h : ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) < (⌈y - x⌉ : ℝ) + 1 := by
    push_cast
    linarith
  have hi : ⌊y⌋ - ⌊x⌋ < ⌈y - x⌉ + 1 := by exact_mod_cast h
  omega

/-- Simultaneous floor keys on an affine path admit at most one plus the sum of
their (rounded-up) displacements many representatives. -/
theorem solution {ι : Type u_ι} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (u v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ (1 + ∑ i, ⌈v i * (b - a)⌉).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by
  classical
  let f : ℝ → ι → ℤ := fun t i => ⌊u i + v i * t⌋
  have hf : MonotoneOn f (Set.Icc a b) := by
    intro x hx y hy hxy i
    apply Int.floor_le_floor
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (hv i))
  obtain ⟨R, hR, hcard, hrep⟩ := exists_monotone_representatives a b hab f hf
  refine ⟨R, hR, hcard.trans ?_, ?_⟩
  · apply Int.toNat_le_toNat
    have hi (i : ι) : f b i - f a i ≤ ⌈v i * (b - a)⌉ := by
      have h := floor_sub_floor_le_ceil (u i + v i * a) (u i + v i * b)
      convert h using 1
      congr 1
      ring
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_sub_distrib] at hs
    linarith
  · intro t ht
    obtain ⟨t', ht', heq⟩ := hrep t ht
    exact ⟨t', ht', fun i => congrFun heq i⟩

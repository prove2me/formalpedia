-- Prove2me | solution 1 for LenstraIP.Hyperplanes.exists_lattice_point_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:48:05.055286+00:00
-- url     : https://prove2.me/submissions/af49fe45-a102-45c7-911e-164160f3fb88

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

set_option autoImplicit false

open KannanLattice.Core

open LenstraIP.Hyperplanes

/-- Averaging step: one of the two roundings `v + f w`, `v + (f - 1) w` is short. -/
private lemma round_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    ‖v + f • w‖ ^ 2 ≤ ‖v‖ ^ 2 + (1 / 4 : ℝ) * ‖w‖ ^ 2 ∨
      ‖v + (f - 1) • w‖ ^ 2 ≤ ‖v‖ ^ 2 + (1 / 4 : ℝ) * ‖w‖ ^ 2 := by
  have key : ∀ c : ℝ, ‖v + c • w‖ ^ 2 = ‖v‖ ^ 2 + 2 * c * inner ℝ v w + c ^ 2 * ‖w‖ ^ 2 := by
    intro c
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [key, key]
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hw : 0 ≤ ‖w‖ ^ 2 := by positivity
  nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hf1.le), sq_nonneg (f - 1 / 2),
    mul_nonneg (sq_nonneg (f - 1 / 2)) hw]

/-- Babai rounding over a finite index set, with arbitrary real coefficients. -/
private lemma round_finset {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : ι → E) (t : ι → ℝ) (s : Finset ι) :
    ∃ z : ι → ℤ, ‖∑ i ∈ s, (t i - z i) • b i‖ ^ 2 ≤ (1 / 4 : ℝ) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨z, hz⟩ := ih
    set v := ∑ i ∈ s, (t i - z i) • b i with hv
    have hsplit : ∀ c : ℤ,
        ∑ i ∈ insert a s, (t i - ((fun j => if j = a then c else z j) i : ℤ)) • b i
          = v + (t a - c) • b a := by
      intro c
      rw [Finset.sum_insert ha, add_comm]
      simp only
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≠ a := fun h => ha (h ▸ hi)
      simp [this]
    have hfr : t a - (⌊t a⌋ : ℝ) = Int.fract (t a) := rfl
    have hfr' : t a - ((⌊t a⌋ + 1 : ℤ) : ℝ) = Int.fract (t a) - 1 := by
      push_cast; rw [← hfr]; ring
    rw [Finset.sum_insert ha]
    rcases round_step v (b a) (Int.fract (t a)) (Int.fract_nonneg _) (Int.fract_lt_one _) with
      h | h
    · refine ⟨fun j => if j = a then ⌊t a⌋ else z j, ?_⟩
      rw [hsplit, hfr]
      linarith
    · refine ⟨fun j => if j = a then ⌊t a⌋ + 1 else z j, ?_⟩
      rw [hsplit, hfr']
      linarith

theorem solution (n : ℕ) (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ y ∈ lattice b, ‖x - y‖ ^ 2 ≤ (1 / 4 : ℝ) * ∑ i, ‖b i‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    have hx0 : x = 0 := by
      ext i
      exact isEmptyElim i
    simp [hx0]
  let B := basisOfLinearIndependentOfCardEqFinrank hb (by simp)
  have hB : ∀ i, B i = b i := fun i => by
    simp [B]
  set t : Fin n → ℝ := fun i => B.repr x i
  have hx : x = ∑ i, t i • b i := by
    conv_lhs => rw [← B.sum_repr x]
    simp [t, hB]
  obtain ⟨z, hz⟩ := round_finset b t Finset.univ
  refine ⟨∑ i, (z i : ℝ) • b i, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have : x - ∑ i, (z i : ℝ) • b i = ∑ i, (t i - z i) • b i := by
      rw [hx, ← Finset.sum_sub_distrib]
      simp [sub_smul]
    rw [this]
    exact hz

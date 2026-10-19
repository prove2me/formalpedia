-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.finiteMatrix_injective_of_rank_triangular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T08:06:13.175705+00:00
-- url     : https://prove2.me/submissions/ec1c94bd-d9fe-4699-a017-fa7255cb3829

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Mathlib.Data.Matrix.Mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

/-!
A vector in the kernel cannot have a nonzero coordinate of maximal rank:
the triangularity hypothesis makes all off-diagonal contributions vanish.
-/
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (rank : ι → ℕ) (M : Matrix ι ι ℂ)
    (hdiag : ∀ i, M i i = 1)
    (htri : ∀ i j, i ≠ j → M i j ≠ 0 → rank i < rank j) :
    Function.Injective M.mulVecLin := by
  intro x y hxy
  have hsub : M.mulVecLin (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzero : x - y = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, (x - y) i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    let s : Finset ι := Finset.univ.filter fun j => (x - y) j ≠ 0
    have hs : s.Nonempty := by
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image s rank hs
    have hrow : (∑ j : ι, M i₀ j * (x - y) j) = 0 := by
      simpa [Matrix.mulVec_eq_sum] using congrFun hsub i₀
    have hsum : (∑ j : ι, M i₀ j * (x - y) j) =
        M i₀ i₀ * (x - y) i₀ := by
      rw [Finset.sum_eq_single i₀]
      · intro j hj hji
        by_cases hjz : (x - y) j = 0
        · simp [hjz]
        · have hjmem : j ∈ s :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjz⟩
          have hle := hmax j hjmem
          by_cases hm : M i₀ j = 0
          · simp [hm]
          · exact False.elim (not_lt_of_ge hle (htri i₀ j hji.symm hm))
      · simp
    rw [hsum, hdiag i₀] at hrow
    have hz : (x - y) i₀ = 0 := by simpa using hrow
    exact (Finset.mem_filter.mp hi₀).2 hz
  exact sub_eq_zero.mp hzero

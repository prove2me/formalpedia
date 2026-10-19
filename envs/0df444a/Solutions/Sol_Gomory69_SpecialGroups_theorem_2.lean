-- Prove2me | solution 1 for Gomory69.SpecialGroups.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T09:41:24.92012+00:00
-- url     : https://prove2.me/submissions/cee88b3a-22c9-4145-81d5-9753f79d0e9e

-- Direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Mathematical argument: Ralph E. Gomory (1969), Theorem 2, p.460.
-- Platform formulation and nonzero-right-hand-side qualification: mikedeng1; review: Shuze Chen.
import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron
set_option autoImplicit false
open Gomory69.SpecialGroups
open scoped Pointwise
namespace GomoryResearch
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
lemma shift_sum (t r s : {g : G // g ≠ 0} → ℕ) (hr : r ≤ t)
    (he : groupSum s = groupSum r) :
    groupSum (fun g => t g - r g + s g) = groupSum t := by
  unfold groupSum at *
  simp_rw [add_nsmul, sub_nsmul _ (hr _)]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, he]
  abel
end GomoryResearch

theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (hg₀ : g₀ ≠ 0) (x : {g : G // g ≠ 0} → ℝ)
    (hx : x ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) :
    ∃ t ∈ solutionSet g₀, toReal t = x ∧ IsIrreducible t := by
  classical
  obtain ⟨t, ht, rfl⟩ := extremePoints_convexHull_subset hx
  refine ⟨t, ht, rfl, ?_⟩
  intro r s hr hs he
  let u := fun g => t g - r g + s g
  let v := fun g => t g - s g + r g
  have hu : u ∈ solutionSet g₀ := ⟨(GomoryResearch.shift_sum t r s hr he).trans ht.1,
    fun h => (hg₀ h).elim⟩
  have hv : v ∈ solutionSet g₀ := ⟨(GomoryResearch.shift_sum t s r hs he.symm).trans ht.1,
    fun h => (hg₀ h).elim⟩
  have huc : toReal u ∈ masterPolyhedron g₀ := subset_convexHull ℝ _ ⟨u, hu, rfl⟩
  have hvc : toReal v ∈ masterPolyhedron g₀ := subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  have hmid : toReal t ∈ openSegment ℝ (toReal u) (toReal v) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toReal, u, v, Nat.cast_add,
      Nat.cast_sub (hr g), Nat.cast_sub (hs g)]
    ring
  have eq := hx.2 huc hvc hmid
  funext g
  have hg := congrFun eq g
  simp only [toReal, u, Nat.cast_add, Nat.cast_sub (hr g)] at hg
  exact_mod_cast (show (r g : ℝ) = (s g : ℝ) by linarith)

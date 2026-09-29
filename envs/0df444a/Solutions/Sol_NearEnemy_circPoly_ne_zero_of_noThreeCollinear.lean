-- Prove2me | solution 1 for NearEnemy.circPoly_ne_zero_of_noThreeCollinear
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:08:35.170816+00:00
-- url     : https://prove2.me/submissions/bb88007b-6b05-4d2f-a91c-fd5832638fe6

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_circPoly_ne_zero_of_affineIndependent
import Theorems.Thm_NearEnemy_circPoly_ne_zero_of_coplanar

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

/-- A difference proportionality `c - a = t • (b - a)` puts the triple on
the line through `a` with direction `b - a`. -/
 theorem collinear_triple_of_smul
    {a b c : EuclideanSpace ℝ ι} {t : ℝ}
    (ht : c - a = t • (b - a)) :
    Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)) := by
  rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
  refine ⟨b - a, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by rw [vadd_eq_add]; module⟩
  · exact ⟨t, by rw [vadd_eq_add]; linear_combination (norm := module) ht⟩

end NearEnemy

open NearEnemy in
theorem solution {a b c e : EuclideanSpace ℝ ι}
    (hab : a ≠ b) (hae : a ≠ e)
    (habc : ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)))
    (hbce : ¬ Collinear ℝ ({b, c, e} : Set (EuclideanSpace ℝ ι))) :
    circPoly a b c e ≠ 0 := by
  by_cases hind : AffineIndependent ℝ ![a, b, c, e]
  · exact circPoly_ne_zero_of_affineIndependent hind
  · refine circPoly_ne_zero_of_coplanar hab hae habc hbce ?_
    -- Extract a planar dependence from the failure of affine independence.
    rw [affineIndependent_iff] at hind
    push Not at hind
    obtain ⟨sf, w, hw0, hwp, i, his, hwi⟩ := hind
    classical
    set W : Fin 4 → ℝ := fun j => if j ∈ sf then w j else 0 with hW
    have hWs : ∀ j ∈ sf, W j = w j := fun j hj => if_pos hj
    have hW0 : ∑ j, W j = 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ sf)
        (fun j _ hj => if_neg hj)]
      exact (Finset.sum_congr rfl hWs).trans hw0
    have hWp : ∑ j, W j • ![a, b, c, e] j = 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ sf)
        (fun j _ hj => by rw [hW]; simp only [if_neg hj, zero_smul])]
      exact (Finset.sum_congr rfl fun j hj => by rw [hWs j hj]).trans hwp
    have hWi : W i ≠ 0 := by rw [hWs i his]; exact hwi
    have h4 : W 0 + W 1 + W 2 + W 3 = 0 := by
      simpa [Fin.sum_univ_four] using hW0
    have hp4 : W 0 • a + W 1 • b + W 2 • c + W 3 • e = 0 := by
      simpa [Fin.sum_univ_four] using hWp
    have hW0' : W 0 = -(W 1) - W 2 - W 3 := by linarith
    rw [hW0'] at hp4
    have hcomb : W 1 • (b - a) + W 2 • (c - a) + W 3 • (e - a) = 0 := by
      linear_combination (norm := module) hp4
    by_cases h3 : W 3 = 0
    · exfalso
      rw [h3, zero_smul, add_zero] at hcomb
      by_cases h2 : W 2 = 0
      · rw [h2, zero_smul, add_zero] at hcomb
        have h1 : W 1 = 0 := by
          rcases smul_eq_zero.mp hcomb with h | h
          · exact h
          · exact absurd (sub_eq_zero.mp h).symm hab
        have h0' : W 0 = 0 := by rw [hW0', h1, h2, h3]; ring
        have : W i = 0 := by fin_cases i <;> assumption
        exact hWi this
      · apply habc
        have key : W 2 • (c - a) = (-(W 1)) • (b - a) := by
          linear_combination (norm := module) hcomb
        refine collinear_triple_of_smul (t := (W 2)⁻¹ * (-(W 1))) ?_
        have hkey := congrArg (fun z : EuclideanSpace ℝ ι => (W 2)⁻¹ • z) key
        simp only [smul_smul] at hkey
        rwa [inv_mul_cancel₀ h2, one_smul] at hkey
    · have key : W 3 • (e - a) =
          (-(W 1)) • (b - a) + (-(W 2)) • (c - a) := by
        linear_combination (norm := module) hcomb
      have hsol : e - a = ((W 3)⁻¹ * (-(W 1))) • (b - a) +
          ((W 3)⁻¹ * (-(W 2))) • (c - a) := by
        have hkey := congrArg (fun z : EuclideanSpace ℝ ι => (W 3)⁻¹ • z) key
        simp only [smul_add, smul_smul] at hkey
        rwa [inv_mul_cancel₀ h3, one_smul] at hkey
      rw [hsol]
      exact add_mem
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))

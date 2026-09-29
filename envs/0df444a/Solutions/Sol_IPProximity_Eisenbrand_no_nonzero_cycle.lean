-- Prove2me | solution 1 for IPProximity.Eisenbrand.no_nonzero_cycle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:30:50.498993+00:00
-- url     : https://prove2.me/submissions/5439c225-b95c-4b85-804f-78663ee3b6a1

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsCycle

namespace IPProximity.Eisenbrand

lemma aux_nnc_coord (d y : ℝ) (h1 : |y| ≤ |d|) (h2 : 0 ≤ y * d) :
    (0 ≤ y ∧ y ≤ d) ∨ (d ≤ y ∧ y ≤ 0) := by
  rcases le_total 0 d with hd | hd <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hd, abs_of_nonneg hy] at h1
    exact Or.inl ⟨hy, h1⟩
  · rw [abs_of_nonneg hd, abs_of_nonpos hy] at h1
    left
    constructor <;> nlinarith
  · rw [abs_of_nonpos hd, abs_of_nonneg hy] at h1
    right
    constructor <;> nlinarith
  · rw [abs_of_nonpos hd, abs_of_nonpos hy] at h1
    exact Or.inr ⟨by linarith, hy⟩

lemma aux_nnc_abs (d y : ℝ) (h : (0 ≤ y ∧ y ≤ d) ∨ (d ≤ y ∧ y ≤ 0)) :
    |d - y| = |d| - |y| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d - y), abs_of_nonneg (by linarith : (0:ℝ) ≤ d),
      abs_of_nonneg h1]
  · rw [abs_of_nonpos (by linarith : d - y ≤ 0), abs_of_nonpos (by linarith : d ≤ 0),
      abs_of_nonpos h2]
    ring

end IPProximity.Eisenbrand

open IPProximity.Eisenbrand

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (x : Fin n → ℝ) (z : Fin n → ℤ)
    (hx : IsLPOptimal A b c u x) (hz : IsIPOptimal A b c u z)
    (hmin : ∀ z' : Fin n → ℤ, IsIPOptimal A b c u z' →
      ∑ i, |(z i : ℝ) - x i| ≤ ∑ i, |(z' i : ℝ) - x i|) :
    ¬ ∃ y : Fin n → ℤ, y ≠ 0 ∧ IsCycle A z x y := by
  rintro ⟨y, hy0, hAy, hyc⟩
  have hcoord : ∀ i, (0 ≤ (y i : ℝ) ∧ (y i : ℝ) ≤ (z i : ℝ) - x i) ∨
      ((z i : ℝ) - x i ≤ y i ∧ (y i : ℝ) ≤ 0) :=
    fun i => aux_nnc_coord _ _ (hyc i).1 (hyc i).2
  obtain ⟨⟨hxA, hxb⟩, hxopt⟩ := hx
  obtain ⟨⟨hzA, hzb⟩, hzopt⟩ := hz
  set yR : Fin n → ℝ := fun i => (y i : ℝ) with hyR
  have hAyR : (A.map (Int.cast : ℤ → ℝ)).mulVec yR = 0 := by
    funext j
    have := congrFun hAy j
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this ⊢
    simp only [Matrix.map_apply, hyR]
    exact_mod_cast this
  have hfeasLP : x + yR ∈ lpPolytope A b u := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.mulVec_add, hxA, hAyR, add_zero]
    · intro i
      have hz1 : (0 : ℝ) ≤ z i := by exact_mod_cast (hzb i).1
      have hz2 : (z i : ℝ) ≤ (u i : ℝ) := by exact_mod_cast (hzb i).2
      have := hxb i
      simp only [Pi.add_apply, hyR]
      rcases hcoord i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have hcyR : dotProduct (fun i => (c i : ℝ)) yR ≤ 0 := by
    have := hxopt _ hfeasLP
    rw [dotProduct_add] at this
    linarith
  have hcy : dotProduct c y ≤ 0 := by
    have : ((dotProduct c y : ℤ) : ℝ) = dotProduct (fun i => (c i : ℝ)) yR := by
      simp [dotProduct, hyR]
    exact_mod_cast (this ▸ hcyR)
  have hfeasIP : z - y ∈ ipFeasible A b u := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.mulVec_sub, hzA, hAy, sub_zero]
    · intro i
      have hz1 : (0 : ℝ) ≤ z i := by exact_mod_cast (hzb i).1
      have hz2 : (z i : ℝ) ≤ (u i : ℝ) := by exact_mod_cast (hzb i).2
      have := hxb i
      have key : (0 : ℝ) ≤ (z i : ℝ) - y i ∧ (z i : ℝ) - y i ≤ (u i : ℝ) := by
        rcases hcoord i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
      simp only [Pi.sub_apply]
      constructor
      · exact_mod_cast key.1
      · exact_mod_cast key.2
  have hopt : IsIPOptimal A b c u (z - y) := by
    refine ⟨hfeasIP, fun z' hz' => ?_⟩
    have := hzopt z' hz'
    rw [dotProduct_sub]
    linarith
  have hle := hmin (z - y) hopt
  have hrw : ∀ i, |(((z - y) i : ℤ) : ℝ) - x i| = |(z i : ℝ) - x i| - |(y i : ℝ)| := by
    intro i
    have : (((z - y) i : ℤ) : ℝ) - x i = ((z i : ℝ) - x i) - (y i : ℝ) := by
      simp only [Pi.sub_apply]; push_cast; ring
    rw [this]
    exact aux_nnc_abs _ _ (hcoord i)
  simp only [hrw, Finset.sum_sub_distrib] at hle
  have hpos : 0 < ∑ i, |(y i : ℝ)| := by
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra h
      push Not at h
      exact hy0 (funext h)
    have hj' : 0 < |(y j : ℝ)| := by
      rw [abs_pos]; exact_mod_cast hj
    exact lt_of_lt_of_le hj'
      (Finset.single_le_sum (f := fun i => |(y i : ℝ)|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ j))
  linarith

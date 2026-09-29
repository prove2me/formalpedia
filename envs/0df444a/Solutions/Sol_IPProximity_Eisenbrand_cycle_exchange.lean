-- Prove2me | solution 1 for IPProximity.Eisenbrand.cycle_exchange
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:04:02.803996+00:00
-- url     : https://prove2.me/submissions/5f990693-da15-4a49-a3a1-ddb6c7eed624

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope
import Definitions.Def_IPProximity_Eisenbrand_ipFeasible
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsCycle

namespace IPProximity.Eisenbrand

/-- Coordinatewise bounds: if `Y` lies between `0` and `Z - X`, then `Z - Y` and `X + Y` lie
between `X` and `Z`, hence in `[0, U]`. -/
theorem aux_ce_bounds (X Y Z U : ℝ) (hX0 : 0 ≤ X) (hXU : X ≤ U) (hZ0 : 0 ≤ Z) (hZU : Z ≤ U)
    (habs : |Y| ≤ |Z - X|) (hmul : 0 ≤ Y * (Z - X)) :
    (0 ≤ Z - Y ∧ Z - Y ≤ U) ∧ (0 ≤ X + Y ∧ X + Y ≤ U) := by
  have h1 := le_abs_self Y
  have h2 := neg_abs_le Y
  rcases le_or_gt 0 (Z - X) with h | h
  · rw [abs_of_nonneg h] at habs
    have hY : 0 ≤ Y := by
      rcases h.eq_or_lt with h' | h'
      · linarith
      · by_contra hY
        push Not at hY
        nlinarith [mul_neg_of_neg_of_pos hY h']
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rw [abs_of_neg h] at habs
    have hY : Y ≤ 0 := by
      by_contra hY
      push Not at hY
      nlinarith [mul_neg_of_pos_of_neg hY h]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

end IPProximity.Eisenbrand

open IPProximity.Eisenbrand

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (x : Fin n → ℝ) (z : Fin n → ℤ)
    (hx : IsLPOptimal A b c u x) (hz : IsIPOptimal A b c u z)
    (y : Fin n → ℤ) (hy : IsCycle A z x y) :
    z - y ∈ ipFeasible A b u ∧
      (x + fun i => (y i : ℝ)) ∈ lpPolytope A b u ∧
      dotProduct c y ≤ 0 := by
  obtain ⟨⟨hxA, hxb⟩, hxopt⟩ := hx
  obtain ⟨⟨hzA, hzb⟩, hzopt⟩ := hz
  obtain ⟨hyA, hyc⟩ := hy
  have key : ∀ i, ((0 : ℝ) ≤ (z i : ℝ) - (y i : ℝ) ∧ (z i : ℝ) - (y i : ℝ) ≤ (u i : ℝ)) ∧
      (0 ≤ x i + (y i : ℝ) ∧ x i + (y i : ℝ) ≤ (u i : ℝ)) := by
    intro i
    have hz0 : (0 : ℝ) ≤ (z i : ℝ) := by exact_mod_cast (hzb i).1
    have hzu : (z i : ℝ) ≤ (u i : ℝ) := by exact_mod_cast (hzb i).2
    exact aux_ce_bounds (x i) (y i) (z i) (u i) (hxb i).1 (hxb i).2 hz0 hzu (hyc i).1 (hyc i).2
  have hfeas : z - y ∈ ipFeasible A b u := by
    refine ⟨?_, fun i => ?_⟩
    · rw [Matrix.mulVec_sub, hzA, hyA, sub_zero]
    · obtain ⟨⟨h1, h2⟩, -⟩ := key i
      simp only [Pi.sub_apply]
      constructor
      · have : ((0 : ℤ) : ℝ) ≤ ((z i - y i : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      · have : ((z i - y i : ℤ) : ℝ) ≤ (((u i : ℤ)) : ℝ) := by push_cast; linarith
        exact_mod_cast this
  have hlp : (x + fun i => (y i : ℝ)) ∈ lpPolytope A b u := by
    refine ⟨?_, fun i => ?_⟩
    · rw [Matrix.mulVec_add, hxA]
      have hy0 : Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) (fun i => (y i : ℝ)) = 0 := by
        funext j
        have := RingHom.map_mulVec (Int.castRingHom ℝ) A y j
        rw [hyA] at this
        simp only [Pi.zero_apply, map_zero] at this
        simpa [Function.comp_def] using this.symm
      rw [hy0, add_zero]
    · obtain ⟨-, h1, h2⟩ := key i
      simp only [Pi.add_apply]
      exact ⟨h1, h2⟩
  refine ⟨hfeas, hlp, ?_⟩
  have h := hxopt _ hlp
  rw [dotProduct_add] at h
  have hcast : dotProduct (fun i => (c i : ℝ)) (fun i => (y i : ℝ)) = ((dotProduct c y : ℤ) : ℝ) := by
    simp [dotProduct]
  have : ((dotProduct c y : ℤ) : ℝ) ≤ 0 := by linarith
  exact_mod_cast this

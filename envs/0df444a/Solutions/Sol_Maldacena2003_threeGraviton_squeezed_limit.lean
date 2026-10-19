-- Prove2me | solution 1 for Maldacena2003.threeGraviton_squeezed_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:10:47.963343+00:00
-- url     : https://prove2.me/submissions/45cf98d6-bbb1-4af1-a959-be6fcf51ecdf

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

lemma T0 (k₂ : EuclideanSpace ℝ (Fin 3)) (ε₁ ε₂ ε₃ : Matrix (Fin 3) (Fin 3) ℝ)
    (hε₂symm : ∀ i j, ε₂ i j = ε₂ j i)
    (hε₂tv : ∀ i, ∑ j, ε₂ i j * k₂ j = 0) :
    (∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ l',
        ε₁ i i' * ε₂ j j' * ε₃ l l' * tTensor 0 k₂ (-k₂) i j l * tTensor 0 k₂ (-k₂) i' j' l')
      = (∑ i, ∑ j, ε₂ i j * ε₃ i j) * ∑ i, ∑ j, ε₁ i j * k₂ i * k₂ j := by
  have hε₂tv' : ∀ j', ∑ j, ε₂ j j' * k₂ j = 0 := fun j' => by
    simpa [hε₂symm] using hε₂tv j'
  simp only [tTensor, PiLp.zero_apply, PiLp.neg_apply, zero_mul, add_zero]
  simp only [mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have z3 : ∑ x, ∑ x_1, ∑ x_2, ∑ x_3, ε₁ x x_1 * ε₂ x_2 x_3 * ε₃ x_2 x_1 * k₂ x * -k₂ x_3 = 0 := by
    refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun x1 _ => Finset.sum_eq_zero (fun x2 _ => ?_)))
    have : ∑ x_3, ε₁ x x1 * ε₂ x2 x_3 * ε₃ x2 x1 * k₂ x * -k₂ x_3
        = -(ε₁ x x1 * ε₃ x2 x1 * k₂ x) * ∑ x_3, ε₂ x2 x_3 * k₂ x_3 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [this, hε₂tv, mul_zero]
  have z4 : ∑ x, ∑ x_1, ∑ x_2, ∑ x_3, ε₁ x x_1 * ε₂ x_2 x_3 * ε₃ x x_1 * -k₂ x_2 * -k₂ x_3 = 0 := by
    refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun x1 _ => Finset.sum_eq_zero (fun x2 _ => ?_)))
    have : ∑ x_3, ε₁ x x1 * ε₂ x2 x_3 * ε₃ x x1 * -k₂ x2 * -k₂ x_3
        = (ε₁ x x1 * ε₃ x x1 * k₂ x2) * ∑ x_3, ε₂ x2 x_3 * k₂ x_3 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [this, hε₂tv, mul_zero]
  have z2 : ∑ x, ∑ x_1, ∑ x_2, ∑ x_3, ε₁ x x_1 * ε₂ x_2 x_3 * ε₃ x x_3 * -k₂ x_2 * k₂ x_1 = 0 := by
    refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun x1 _ => ?_))
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (x2 x3 : Fin 3) => ε₁ x x1 * ε₂ x2 x3 * ε₃ x x3 * -k₂ x2 * k₂ x1)]
    refine Finset.sum_eq_zero (fun x3 _ => ?_)
    have : ∑ x_2, ε₁ x x1 * ε₂ x_2 x3 * ε₃ x x3 * -k₂ x_2 * k₂ x1
        = -(ε₁ x x1 * ε₃ x x3 * k₂ x1) * ∑ x_2, ε₂ x_2 x3 * k₂ x_2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [this, hε₂tv', mul_zero]
  rw [z2, z3, z4, add_zero, add_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x3 _ => ?_)
  ring

theorem solution (ρd : ℝ) (n k₂ : EuclideanSpace ℝ (Fin 3))
    (hn : ‖n‖ = 1) (hk₂ : k₂ ≠ 0) (ε₁ ε₂ ε₃ : Matrix (Fin 3) (Fin 3) ℝ)
    (hε₁symm : ∀ i j, ε₁ i j = ε₁ j i) (hε₁tr : Matrix.trace ε₁ = 0)
    (hε₁tv : ∀ i, ∑ j, ε₁ i j * n j = 0)
    (hε₂symm : ∀ i j, ε₂ i j = ε₂ j i) (hε₂tr : Matrix.trace ε₂ = 0)
    (hε₂tv : ∀ i, ∑ j, ε₂ i j * k₂ j = 0)
    (hε₃symm : ∀ i j, ε₃ i j = ε₃ j i) (hε₃tr : Matrix.trace ε₃ = 0)
    (hε₃tv : ∀ i, ∑ j, ε₃ i j * k₂ j = 0) :
    Tendsto
      (fun t : ℝ => 2 * t ^ 3 * threeGravitonBispectrum ρd ε₁ ε₂ ε₃ (t • n) k₂ (-(t • n) - k₂))
      (𝓝[>] 0)
      (𝓝 ((∑ i, ∑ j, ε₂ i j * ε₃ i j) * ρd ^ 2 * (1 / (2 * ‖k₂‖ ^ 5)) * (2 * ρd ^ 2) * (3 / 2)
        * ∑ i, ∑ j, ε₁ i j * k₂ i * k₂ j)) := by
  set K := ‖k₂‖ with hK
  have hK0 : 0 < K := norm_pos_iff.2 hk₂
  set T : ℝ → ℝ := fun t => ∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ l',
        ε₁ i i' * ε₂ j j' * ε₃ l l' * tTensor (t • n) k₂ (-(t • n) - k₂) i j l
          * tTensor (t • n) k₂ (-(t • n) - k₂) i' j' l' with hT
  have hTc : ContinuousAt T 0 := by
    simp only [hT, tTensor]
    fun_prop
  have hT0 : T 0 = (∑ i, ∑ j, ε₂ i j * ε₃ i j) * ∑ i, ∑ j, ε₁ i j * k₂ i * k₂ j := by
    simp only [hT, zero_smul, neg_zero, zero_sub]
    exact T0 k₂ ε₁ ε₂ ε₃ hε₂symm hε₂tv
  set h : ℝ → ℝ := fun t => ρd ^ 4 * (1 / ((2 * K ^ 3) * (2 * ‖-(t • n) - k₂‖ ^ 3))) * (-4) * T t
      * integralI ‖t • n‖ K ‖-(t • n) - k₂‖ with hh
  have hv3 : ‖-((0:ℝ) • n) - k₂‖ = K := by simp [hK]
  have hc : ContinuousAt h 0 := by
    simp only [hh, integralI]
    have := hTc
    fun_prop (disch := (simp [← hK]; first | positivity | (constructor <;> positivity)))
  have hv : h 0 = (∑ i, ∑ j, ε₂ i j * ε₃ i j) * ρd ^ 2 * (1 / (2 * K ^ 5)) * (2 * ρd ^ 2) * (3 / 2)
        * ∑ i, ∑ j, ε₁ i j * k₂ i * k₂ j := by
    have hv3' : ‖-(0:EuclideanSpace ℝ (Fin 3)) - k₂‖ = K := by simp [hK]
    simp only [hh, integralI, zero_smul, norm_zero, hv3']
    rw [hT0]
    field_simp
    ring
  have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  rw [hv] at h1
  apply h1.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hnt : ‖t • n‖ = t := by rw [norm_smul, hn, Real.norm_of_nonneg ht.le, mul_one]
  simp only [hh, threeGravitonBispectrum, hnt, ← hK]
  rcases (norm_nonneg (-(t • n) - k₂)).lt_or_eq with h3 | h3
  · field_simp
    simp only [hT]; ring
  · simp [← h3]

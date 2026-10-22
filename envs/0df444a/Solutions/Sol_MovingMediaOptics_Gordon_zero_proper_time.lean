-- Prove2me | solution 1 for MovingMediaOptics.Gordon.zero_proper_time
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:47:25.377499+00:00
-- url     : https://prove2.me/submissions/0d45c1be-1bb4-4204-9a2f-4100b58a0173

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

open QAlgorithms.Papers.Independent.Renew46.P42
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

lemma pdX (F : EuclideanSpace ℝ (Fin 3) → ℝ) (x v : EuclideanSpace ℝ (Fin 3))
    (hF : DifferentiableAt ℝ F x) (d : ℝ) (hd : HasDerivAt (fun t : ℝ => F (x + t • v)) d 0) :
    fderiv ℝ F x v = d := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have h2 := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) h1 (by simp)
  exact h2.unique hd

lemma lineX (s A a b q0 m l : ℝ) (hq : 0 < q0) :
    HasDerivAt (fun t => s * Real.sqrt (q0 + b * t + a * t ^ 2) + A * (l + m * t))
      (s * (b / (2 * Real.sqrt q0)) + A * m) 0 := by
  have hp : HasDerivAt (fun t : ℝ => q0 + b * t + a * t ^ 2) b 0 := by
    have := (((hasDerivAt_id (0:ℝ)).const_mul b).const_add q0).fun_add
      (((hasDerivAt_id (0:ℝ)).pow 2).const_mul a)
    simpa using this
  have hs := (hp.sqrt (by simp; exact hq.ne')).const_mul s
  have hl : HasDerivAt (fun t : ℝ => A * (l + m * t)) (A * m) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul m).const_add l).const_mul A
  simpa using hs.fun_add hl

lemma dotsX (u k : V3) (i : Fin 3) (t : ℝ) :
    dot3 u (k + t • Pi.single i 1) = dot3 u k + t * u i ∧
    dot3 (k + t • Pi.single i 1) (k + t • Pi.single i 1) = dot3 k k + 2 * k i * t + t ^ 2 := by
  constructor
  · fin_cases i <;> simp [dot3, Fin.sum_univ_three, Pi.single_apply] <;> ring
  · fin_cases i <;> simp [dot3, Fin.sum_univ_three, Pi.single_apply] <;> ring

lemma velX (c n : ℝ) (u k : V3) (i : Fin 3)
    (hq : 0 < c ^ 2 * dot3 k k - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2) :
    rayVelocity c n u k i =
      Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) *
        ((2 * c ^ 2 * k i - 2 * ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * dot3 u k * u i) /
          (2 * Real.sqrt (c ^ 2 * dot3 k k - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2)))
      + ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * u i := by
  set A := (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u) with hA
  set s := Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) with hs
  unfold rayVelocity QAlgorithms.Papers.Independent.Renew46.P42.gradient cartesianPartial
    QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial
  apply pdX
  · have hdot : ∀ w : V3, Differentiable ℝ (fun y : EuclideanSpace ℝ (Fin 3) => dot3 w (WithLp.ofLp y)) := by
      intro w; unfold dot3; fun_prop
    have hdd : Differentiable ℝ (fun y : EuclideanSpace ℝ (Fin 3) => dot3 (WithLp.ofLp y) (WithLp.ofLp y)) := by
      unfold dot3; fun_prop
    unfold rayHamiltonian
    rw [← hA, ← hs]
    apply DifferentiableAt.add
    · apply DifferentiableAt.const_mul
      apply DifferentiableAt.sqrt
      · exact ((hdd _).const_mul _).sub (((hdot u _).pow 2).const_mul _)
      · simpa using hq.ne'
    · exact ((hdot u _).const_mul _)
  · have hf : (fun t : ℝ => rayHamiltonian c n u
        (WithLp.ofLp (WithLp.toLp 2 k + t • EuclideanSpace.single i 1))) =
        fun t => s * Real.sqrt ((c ^ 2 * dot3 k k - A * dot3 u k ^ 2) +
          (2 * c ^ 2 * k i - 2 * A * dot3 u k * u i) * t + (c ^ 2 - A * u i ^ 2) * t ^ 2) +
          A * (dot3 u k + u i * t) := by
      funext t
      have e : WithLp.ofLp (WithLp.toLp 2 k + t • EuclideanSpace.single i (1:ℝ)) = k + t • Pi.single i 1 := by
        ext j; simp [Pi.single_apply]
      rw [e]
      obtain ⟨h1, h2⟩ := dotsX u k i t
      unfold rayHamiltonian
      rw [h1, h2, ← hA, ← hs]
      congr 2
      · congr 1; ring
      · ring
    rw [hf]
    convert lineX s A _ _ _ (u i) (dot3 u k) hq using 1

lemma quadX (c n : ℝ) (u : V3) (p : V4) :
    quadratic (gDown c n u) p =
      (p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) + (1 / n ^ 2 - 1) *
        (lorentzFactor c u * p 0 - lorentzFactor c u * u 0 / c * p 1
          - lorentzFactor c u * u 1 / c * p 2 - lorentzFactor c u * u 2 / c * p 3) ^ 2 := by
  simp only [quadratic, gDown, apply4, minkowskiMetric, fourFlow, Fin.sum_univ_four]
  simp
  ring

lemma posX (w : V3) (hw : w ≠ 0) : 0 < dot3 w w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h; push Not at h; exact hw (funext h)
  unfold dot3
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

lemma csX (u k : V3) : dot3 u k ^ 2 ≤ dot3 u u * dot3 k k := by
  simp only [dot3, Fin.sum_univ_three]
  nlinarith [sq_nonneg (u 0 * k 1 - u 1 * k 0), sq_nonneg (u 0 * k 2 - u 2 * k 0),
    sq_nonneg (u 1 * k 2 - u 2 * k 1)]

lemma gammaX (c : ℝ) (u : V3) (hc : 0 < c) (hu : dot3 u u < c ^ 2) :
    lorentzFactor c u ^ 2 * (c ^ 2 - dot3 u u) = c ^ 2 := by
  have h1 : 0 < 1 - dot3 u u / c ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]; exact hu
  have hs := Real.sq_sqrt h1.le
  have e : c ^ 2 - dot3 u u = (1 - dot3 u u / c ^ 2) * c ^ 2 := by field_simp
  unfold lorentzFactor
  rw [div_pow, one_pow, hs, e, ← mul_assoc, one_div_mul_cancel h1.ne', one_mul]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
theorem solution (c n : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) (hk : k ≠ 0) :
    quadratic (gDown c n u)
      ![c, rayVelocity c n u k 0, rayVelocity c n u k 1, rayVelocity c n u k 2] = 0 := by
  have hc0 : c ≠ 0 := hc.ne'
  have hn0 : n ≠ 0 := by linarith
  have hDn : 0 ≤ dot3 u u := by unfold dot3; exact Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  have hKK := posX k hk
  have hcs := csX u k
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hM : 0 < n ^ 2 * c ^ 2 - dot3 u u := by nlinarith
  have hq : 0 < c ^ 2 * dot3 k k - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2 := by
    have e : c ^ 2 * dot3 k k - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2
        = (c ^ 2 * dot3 k k * (n ^ 2 * c ^ 2 - dot3 u u) - (n ^ 2 * c ^ 2 - c ^ 2) * (dot3 u k) ^ 2) /
          (n ^ 2 * c ^ 2 - dot3 u u) := by
      have h0 := hM.ne'
      have h6 : (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u) * (dot3 u k) ^ 2 * (n ^ 2 * c ^ 2 - dot3 u u)
          = (n ^ 2 * c ^ 2 - c ^ 2) * (dot3 u k) ^ 2 := by
        rw [mul_right_comm, div_mul_cancel₀ _ h0]
      rw [eq_div_iff h0, sub_mul, h6]
    rw [e]
    apply div_pos _ hM
    have h3 : 0 ≤ (n ^ 2 * c ^ 2 - c ^ 2) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left hcs h3
    have h5 : 0 < c ^ 2 * dot3 k k * n ^ 2 * (c ^ 2 - dot3 u u) := by
      have : 0 < c ^ 2 - dot3 u u := by linarith
      positivity
    nlinarith
  have hR := gammaX c u hc hu
  have hs2 : Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) ^ 2 =
      (c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u) :=
    Real.sq_sqrt (div_nonneg (by linarith) hM.le)
  have hr2 := Real.sq_sqrt hq.le
  have hr0 := (Real.sqrt_pos.mpr hq).ne'
  rw [quadX]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  rw [velX c n u k 0 hq, velX c n u k 1 hq, velX c n u k 2 hq]
  generalize Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) = s at hs2 ⊢
  generalize Real.sqrt (c ^ 2 * dot3 k k - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2) = r at hr2 hr0 ⊢
  generalize lorentzFactor c u = g at hR ⊢
  have hM0 := hM.ne'
  set D := dot3 u u with hDd
  clear_value D
  simp only [dot3, Fin.sum_univ_three] at hr2 ⊢
  linear_combination (norm := skip) ((-c^4*(k 0)^2*n^6*s^2*(u 0)^2 + c^4*(k 0)^2*n^4*s^2*(u 0)^2 - 2*c^4*(k 0)*(k 1)*n^6*s^2*(u 0)*(u 1) + 2*c^4*(k 0)*(k 1)*n^4*s^2*(u 0)*(u 1) - 2*c^4*(k 0)*(k 2)*n^6*s^2*(u 0)*(u 2) + 2*c^4*(k 0)*(k 2)*n^4*s^2*(u 0)*(u 2) + 2*c^4*(k 0)*n^6*r*s*(u 0) - 2*c^4*(k 0)*n^4*r*s*(u 0) - c^4*(k 1)^2*n^6*s^2*(u 1)^2 + c^4*(k 1)^2*n^4*s^2*(u 1)^2 - 2*c^4*(k 1)*(k 2)*n^6*s^2*(u 1)*(u 2) + 2*c^4*(k 1)*(k 2)*n^4*s^2*(u 1)*(u 2) + 2*c^4*(k 1)*n^6*r*s*(u 1) - 2*c^4*(k 1)*n^4*r*s*(u 1) - c^4*(k 2)^2*n^6*s^2*(u 2)^2 + c^4*(k 2)^2*n^4*s^2*(u 2)^2 + 2*c^4*(k 2)*n^6*r*s*(u 2) - 2*c^4*(k 2)*n^4*r*s*(u 2) - c^4*n^6*r^2 + c^4*n^4*r^2 + c^2*(k 0)^2*n^6*s^2*(u 0)^4 + c^2*(k 0)^2*n^6*s^2*(u 0)^2*(u 1)^2 + c^2*(k 0)^2*n^6*s^2*(u 0)^2*(u 2)^2 - c^2*(k 0)^2*n^4*s^2*(u 0)^4 - c^2*(k 0)^2*n^4*s^2*(u 0)^2*(u 1)^2 - c^2*(k 0)^2*n^4*s^2*(u 0)^2*(u 2)^2 + 2*c^2*(k 0)*(k 1)*n^6*s^2*(u 0)^3*(u 1) + 2*c^2*(k 0)*(k 1)*n^6*s^2*(u 0)*(u 1)^3 + 2*c^2*(k 0)*(k 1)*n^6*s^2*(u 0)*(u 1)*(u 2)^2 - 2*c^2*(k 0)*(k 1)*n^4*s^2*(u 0)^3*(u 1) - 2*c^2*(k 0)*(k 1)*n^4*s^2*(u 0)*(u 1)^3 - 2*c^2*(k 0)*(k 1)*n^4*s^2*(u 0)*(u 1)*(u 2)^2 + 2*c^2*(k 0)*(k 2)*n^6*s^2*(u 0)^3*(u 2) + 2*c^2*(k 0)*(k 2)*n^6*s^2*(u 0)*(u 1)^2*(u 2) + 2*c^2*(k 0)*(k 2)*n^6*s^2*(u 0)*(u 2)^3 - 2*c^2*(k 0)*(k 2)*n^4*s^2*(u 0)^3*(u 2) - 2*c^2*(k 0)*(k 2)*n^4*s^2*(u 0)*(u 1)^2*(u 2) - 2*c^2*(k 0)*(k 2)*n^4*s^2*(u 0)*(u 2)^3 - 2*c^2*(k 0)*n^6*r*s*(u 0)^3 - 2*c^2*(k 0)*n^6*r*s*(u 0)*(u 1)^2 - 2*c^2*(k 0)*n^6*r*s*(u 0)*(u 2)^2 + 2*c^2*(k 0)*n^4*r*s*(u 0)^3 + 2*c^2*(k 0)*n^4*r*s*(u 0)*(u 1)^2 + 2*c^2*(k 0)*n^4*r*s*(u 0)*(u 2)^2 + c^2*(k 1)^2*n^6*s^2*(u 0)^2*(u 1)^2 + c^2*(k 1)^2*n^6*s^2*(u 1)^4 + c^2*(k 1)^2*n^6*s^2*(u 1)^2*(u 2)^2 - c^2*(k 1)^2*n^4*s^2*(u 0)^2*(u 1)^2 - c^2*(k 1)^2*n^4*s^2*(u 1)^4 - c^2*(k 1)^2*n^4*s^2*(u 1)^2*(u 2)^2 + 2*c^2*(k 1)*(k 2)*n^6*s^2*(u 0)^2*(u 1)*(u 2) + 2*c^2*(k 1)*(k 2)*n^6*s^2*(u 1)^3*(u 2) + 2*c^2*(k 1)*(k 2)*n^6*s^2*(u 1)*(u 2)^3 - 2*c^2*(k 1)*(k 2)*n^4*s^2*(u 0)^2*(u 1)*(u 2) - 2*c^2*(k 1)*(k 2)*n^4*s^2*(u 1)^3*(u 2) - 2*c^2*(k 1)*(k 2)*n^4*s^2*(u 1)*(u 2)^3 - 2*c^2*(k 1)*n^6*r*s*(u 0)^2*(u 1) - 2*c^2*(k 1)*n^6*r*s*(u 1)^3 - 2*c^2*(k 1)*n^6*r*s*(u 1)*(u 2)^2 + 2*c^2*(k 1)*n^4*r*s*(u 0)^2*(u 1) + 2*c^2*(k 1)*n^4*r*s*(u 1)^3 + 2*c^2*(k 1)*n^4*r*s*(u 1)*(u 2)^2 + c^2*(k 2)^2*n^6*s^2*(u 0)^2*(u 2)^2 + c^2*(k 2)^2*n^6*s^2*(u 1)^2*(u 2)^2 + c^2*(k 2)^2*n^6*s^2*(u 2)^4 - c^2*(k 2)^2*n^4*s^2*(u 0)^2*(u 2)^2 - c^2*(k 2)^2*n^4*s^2*(u 1)^2*(u 2)^2 - c^2*(k 2)^2*n^4*s^2*(u 2)^4 - 2*c^2*(k 2)*n^6*r*s*(u 0)^2*(u 2) - 2*c^2*(k 2)*n^6*r*s*(u 1)^2*(u 2) - 2*c^2*(k 2)*n^6*r*s*(u 2)^3 + 2*c^2*(k 2)*n^4*r*s*(u 0)^2*(u 2) + 2*c^2*(k 2)*n^4*r*s*(u 1)^2*(u 2) + 2*c^2*(k 2)*n^4*r*s*(u 2)^3 + c^2*n^6*r^2*(u 0)^2 + c^2*n^6*r^2*(u 1)^2 + c^2*n^6*r^2*(u 2)^2 - c^2*n^4*r^2*(u 0)^2 - c^2*n^4*r^2*(u 1)^2 - c^2*n^4*r^2*(u 2)^2) / (n^2*r^2*(n^2*c^2 - D)^2)) * hR + ((-c^6*(k 0)^2*n^4 - c^6*(k 1)^2*n^4 - c^6*(k 2)^2*n^4 + c^4*(k 0)^2*n^4*(u 0)^2 + c^4*(k 0)^2*n^2*(u 1)^2 + c^4*(k 0)^2*n^2*(u 2)^2 + 2*c^4*(k 0)*(k 1)*n^4*(u 0)*(u 1) - 2*c^4*(k 0)*(k 1)*n^2*(u 0)*(u 1) + 2*c^4*(k 0)*(k 2)*n^4*(u 0)*(u 2) - 2*c^4*(k 0)*(k 2)*n^2*(u 0)*(u 2) + c^4*(k 1)^2*n^4*(u 1)^2 + c^4*(k 1)^2*n^2*(u 0)^2 + c^4*(k 1)^2*n^2*(u 2)^2 + 2*c^4*(k 1)*(k 2)*n^4*(u 1)*(u 2) - 2*c^4*(k 1)*(k 2)*n^2*(u 1)*(u 2) + c^4*(k 2)^2*n^4*(u 2)^2 + c^4*(k 2)^2*n^2*(u 0)^2 + c^4*(k 2)^2*n^2*(u 1)^2) * (n^2*c^2 - D) / (n^2*r^2*(n^2*c^2 - D)^2)) * hs2 + ((c^4*n^2 - c^2*n^2*(u 0)^2 - c^2*n^2*(u 1)^2 - c^2*n^2*(u 2)^2) * (n^2*c^2 - D) / (n^2*r^2*(n^2*c^2 - D)^2)) * hr2
  have hM1 : c ^ 2 * n ^ 2 - D ≠ 0 := by rw [mul_comm]; exact hM0
  field_simp
  subst hDd
  simp only [dot3, Fin.sum_univ_three]
  ring

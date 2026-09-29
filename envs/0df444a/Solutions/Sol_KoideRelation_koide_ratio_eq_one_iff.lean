-- Prove2me | solution 1 for KoideRelation.koide_ratio_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T20:19:55.328836+00:00
-- url     : https://prove2.me/submissions/43e44b0c-0641-40a2-bb7b-90d1786b1ca5

import Definitions.Def_KoideRelation_defs

open KoideRelation

theorem W2p_KoideRelation_koide_ratio_bounds {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hpos : ∃ i, 0 < m i) :
    1 / (n : ℝ) ≤ koideRatio m ∧ koideRatio m ≤ 1 := by
  unfold koideRatio
  obtain ⟨i0, hi0⟩ := hpos
  have hQ : ∑ i, m i = ∑ i, Real.sqrt (m i) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => (Real.sq_sqrt (hm i)).symm)
  have hS : 0 < ∑ i, Real.sqrt (m i) :=
    Finset.sum_pos' (fun i _ => Real.sqrt_nonneg _)
      ⟨i0, Finset.mem_univ _, Real.sqrt_pos.mpr hi0⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i0
  have hCS : (∑ i, Real.sqrt (m i)) ^ 2 ≤ n * ∑ i, Real.sqrt (m i) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => Real.sqrt (m i))
    simpa using this
  have hle : ∑ i, Real.sqrt (m i) ^ 2 ≤ (∑ i, Real.sqrt (m i)) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Real.sqrt_nonneg _)
  rw [hQ]
  constructor
  · rw [div_le_div_iff₀ hn (by positivity)]
    linarith
  · rw [div_le_one (by positivity)]
    exact hle

theorem W2p_KoideRelation_koide_cos_eq {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hpos : ∃ i, 0 < m i) :
    koideCos m = 1 / Real.sqrt ((n : ℝ) * koideRatio m) := by
  obtain ⟨i0, hi0⟩ := hpos
  have hQ : ∑ i, Real.sqrt (m i) ^ 2 = ∑ i, m i :=
    Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hm i))
  have hS : 0 < ∑ i, Real.sqrt (m i) :=
    Finset.sum_pos' (fun i _ => Real.sqrt_nonneg _)
      ⟨i0, Finset.mem_univ _, Real.sqrt_pos.mpr hi0⟩
  have hQp : 0 < ∑ i, m i :=
    Finset.sum_pos' (fun i _ => hm i) ⟨i0, Finset.mem_univ _, hi0⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i0
  unfold koideCos koideRatio
  rw [hQ, ← mul_div_assoc, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hS.le,
    Real.sqrt_mul hn.le, one_div_div]
  ring

theorem W2p_KoideRelation_koide_angle_eq_pi_div_four_iff (m : Fin 3 → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hpos : ∃ i, 0 < m i) :
    koideAngle m = Real.pi / 4 ↔ koideRatio m = 2 / 3 := by
  have hb := W2p_KoideRelation_koide_ratio_bounds m hm hpos
  have hc := W2p_KoideRelation_koide_cos_eq m hm hpos
  simp only [Nat.cast_ofNat] at hb hc
  unfold koideAngle
  rw [hc]
  have h3q : 1 ≤ 3 * koideRatio m := by
    have := hb.1
    rw [div_le_iff₀ (by norm_num)] at this
    linarith
  have hsq : 1 ≤ Real.sqrt (3 * koideRatio m) := Real.one_le_sqrt.mpr h3q
  have hsq0 : 0 < Real.sqrt (3 * koideRatio m) := by linarith
  have hy1 : 1 / Real.sqrt (3 * koideRatio m) ≤ 1 := by
    rw [div_le_one hsq0]; exact hsq
  have hy0 : 0 < 1 / Real.sqrt (3 * koideRatio m) := by positivity
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hcos := congrArg Real.cos h
    rw [Real.cos_arccos (by linarith) hy1, Real.cos_pi_div_four] at hcos
    have h2 : (1 / Real.sqrt (3 * koideRatio m)) ^ 2 = (Real.sqrt 2 / 2) ^ 2 := by rw [hcos]
    rw [div_pow, one_pow, Real.sq_sqrt (by linarith), div_pow, h22] at h2
    rw [show (2 : ℝ) / 2 ^ 2 = 1 / 2 by norm_num,
      div_eq_div_iff (by linarith : (0 : ℝ) < 3 * koideRatio m).ne' (by norm_num)] at h2
    have h4 : 3 * koideRatio m = 2 := by linarith
    linarith
  · intro hq
    rw [hq, show (3 : ℝ) * (2 / 3) = 2 by norm_num]
    have e : 1 / Real.sqrt 2 = Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      have : 0 < Real.sqrt 2 := by positivity
      field_simp
      nlinarith [h22]
    rw [e, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

theorem W2p_KoideRelation_pseudoMass_one_eq_mass (m : Fin 3 → ℝ) (hm : ∀ i, 0 ≤ m i) :
    pseudoMass 1 m = m ∧ koideRatio (pseudoMass 1 m) = koideRatio m := by
  have h1 : pseudoMass 1 m = m := by
    funext i
    simp [pseudoMass, Matrix.one_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hm i)]
  exact ⟨h1, by rw [h1]⟩

theorem W2p_KoideRelation_koide_imp_sqrt_free (m₁ m₂ m₃ : ℝ) (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂)
    (h₃ : 0 ≤ m₃)
    (hq : koideRatio ![m₁, m₂, m₃] = 2 / 3) :
    ((m₁ + m₂ + m₃) ^ 2 - 16 * (m₁ * m₂ + m₂ * m₃ + m₁ * m₃)) ^ 2
      = 3 / 2 * 32 ^ 2 * (m₁ * m₂ * m₃) * (m₁ + m₂ + m₃) := by
  unfold koideRatio at hq
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hq
  have e1 := Real.sq_sqrt h₁
  have e2 := Real.sq_sqrt h₂
  have e3 := Real.sq_sqrt h₃
  generalize Real.sqrt m₁ = x1 at hq e1
  generalize Real.sqrt m₂ = x2 at hq e2
  generalize Real.sqrt m₃ = x3 at hq e3
  subst e1 e2 e3
  have hS : (x1 + x2 + x3) ^ 2 ≠ 0 := by
    intro h
    rw [h, div_zero] at hq
    norm_num at hq
  rw [div_eq_iff hS] at hq
  linear_combination (3 * ((x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - 4 * (x1 * x2 + x2 * x3 + x1 * x3)) *
      (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + 4 * (x1 * x2 + x2 * x3 + x1 * x3)) ^ 2 +
    64 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + 4 * (x1 * x2 + x2 * x3 + x1 * x3)) * (x1 * x2 * x3) *
      (x1 + x2 + x3) - 512 * (x1 * x2 * x3) ^ 2)) * hq

theorem W2p_KoideRelation_sqrt_free_not_imp_koide :
    ∃ m : Fin 3 → ℝ, (∀ i, 0 < m i) ∧
      ((m 0 + m 1 + m 2) ^ 2 - 16 * (m 0 * m 1 + m 1 * m 2 + m 0 * m 2)) ^ 2
        = 3 / 2 * 32 ^ 2 * (m 0 * m 1 * m 2) * (m 0 + m 1 + m 2) ∧
      koideRatio m ≠ 2 / 3 := by
  obtain ⟨t, ht, htpos⟩ : ∃ t : ℝ, t ^ 2 + 8 * t - 2 = 0 ∧ 0 < t := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h0 := Real.sqrt_nonneg 2
    refine ⟨3 * Real.sqrt 2 - 4, by linear_combination 9 * h2, ?_⟩
    nlinarith
  refine ⟨![1, 1, t ^ 2], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;> first | exact htpos.ne' | positivity | exact pow_pos htpos 2
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination (t ^ 6 - 8 * t ^ 5 + 10 * t ^ 4 - 96 * t ^ 3 + 12 * t ^ 2 - 288 * t - 72) * ht
  · unfold koideRatio
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.sqrt_one,
      Real.sqrt_sq htpos.le]
    intro h
    rw [div_eq_iff (by positivity)] at h
    nlinarith

theorem W2p_KoideRelation_koide_iff_sum_z_eq_zero (E : ℝ) (hE : 0 < E) (z : Fin 3 → ℝ)
    (hz : ∑ i, z i ^ 2 = 1) (hnn : ∀ i, 0 ≤ z i + 1 / Real.sqrt 3)
    (m : Fin 3 → ℝ) (hm : ∀ i, m i = E * (z i + 1 / Real.sqrt 3) ^ 2)
    (hne : ∃ i, m i ≠ 0) :
    koideRatio m = 2 / 3 ↔ ∑ i, z i = 0 := by
  set a := 1 / Real.sqrt 3 with ha
  have ha2 : a ^ 2 = 1 / 3 := by
    rw [ha, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  simp only [Fin.sum_univ_three] at hz ⊢
  have hw0 := hnn 0
  have hw1 := hnn 1
  have hw2 := hnn 2
  have hW : 0 < (z 0 + a) + (z 1 + a) + (z 2 + a) := by
    by_contra hcon
    push_neg at hcon
    have e0 : z 0 + a = 0 := by linarith
    have e1 : z 1 + a = 0 := by linarith
    have e2 : z 2 + a = 0 := by linarith
    obtain ⟨i, hi⟩ := hne
    apply hi
    rw [hm i]
    have : z i + a = 0 := by
      match i with
      | 0 => exact e0
      | 1 => exact e1
      | 2 => exact e2
    rw [this]; ring
  unfold koideRatio
  simp only [Fin.sum_univ_three]
  rw [hm 0, hm 1, hm 2, Real.sqrt_mul hE.le, Real.sqrt_mul hE.le, Real.sqrt_mul hE.le,
    Real.sqrt_sq hw0, Real.sqrt_sq hw1, Real.sqrt_sq hw2]
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
  have hE2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE.le
  have hden : (Real.sqrt E * (z 0 + a) + Real.sqrt E * (z 1 + a) + Real.sqrt E * (z 2 + a)) ^ 2
      ≠ 0 := by
    apply pow_ne_zero
    rw [← mul_add, ← mul_add]
    exact (mul_pos hsE hW).ne'
  rw [div_eq_iff hden]
  constructor
  · intro h
    have h' : (z 0 + a) ^ 2 + (z 1 + a) ^ 2 + (z 2 + a) ^ 2 =
        2 / 3 * ((z 0 + a) + (z 1 + a) + (z 2 + a)) ^ 2 := by
      apply mul_left_cancel₀ hE.ne'
      linear_combination h + (2 / 3 * ((z 0 + a) + (z 1 + a) + (z 2 + a)) ^ 2) * hE2
    have hZW : (z 0 + z 1 + z 2) * ((z 0 + a) + (z 1 + a) + (z 2 + a)) = 0 := by
      linear_combination (-3 / 2) * h' + (3 / 2) * hz - (9 / 2) * ha2
    rcases mul_eq_zero.mp hZW with h0 | h0
    · exact h0
    · linarith
  · intro hZ
    linear_combination E * hz - 3 * E * ha2 -
      (2 / 3) * E * ((z 0 + a) + (z 1 + a) + (z 2 + a)) * hZ -
      (2 / 3) * ((z 0 + a) + (z 1 + a) + (z 2 + a)) ^ 2 * hE2

theorem W2p_KoideRelation_koide_ratio_eq_inv_card_iff {n : ℕ} (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i)
    (hpos : ∃ i, 0 < m i) :
    koideRatio m = 1 / (n : ℝ) ↔ ∀ i j, m i = m j := by
  obtain ⟨i0, hi0⟩ := hpos
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i0
  have hS : 0 < ∑ i, Real.sqrt (m i) :=
    Finset.sum_pos' (fun i _ => Real.sqrt_nonneg _)
      ⟨i0, Finset.mem_univ _, Real.sqrt_pos.mpr hi0⟩
  have hQ' : ∑ i, Real.sqrt (m i) ^ 2 = ∑ i, m i :=
    Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hm i))
  constructor
  · intro h
    unfold koideRatio at h
    rw [div_eq_div_iff (by positivity) hn.ne'] at h
    have hvar : ∑ i, (Real.sqrt (m i) - (∑ j, Real.sqrt (m j)) / n) ^ 2 =
        (∑ i, Real.sqrt (m i) ^ 2) + (-2 * ((∑ j, Real.sqrt (m j)) / n)) *
          (∑ i, Real.sqrt (m i)) + n * ((∑ j, Real.sqrt (m j)) / n) ^ 2 := by
      rw [Finset.sum_congr rfl (fun i _ => show (Real.sqrt (m i) - (∑ j, Real.sqrt (m j)) / n) ^ 2
          = Real.sqrt (m i) ^ 2 + (-2 * ((∑ j, Real.sqrt (m j)) / n)) * Real.sqrt (m i)
            + ((∑ j, Real.sqrt (m j)) / n) ^ 2 by ring),
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hzero : ∑ i, (Real.sqrt (m i) - (∑ j, Real.sqrt (m j)) / n) ^ 2 = 0 := by
      rw [hvar, hQ']
      have e : (∑ i, m i) + (-2 * ((∑ j, Real.sqrt (m j)) / n)) * (∑ i, Real.sqrt (m i))
          + n * ((∑ j, Real.sqrt (m j)) / n) ^ 2
          = ((∑ i, m i) * n - (∑ j, Real.sqrt (m j)) ^ 2) / n := by
        have := hn.ne'
        field_simp <;> ring
      rw [e, h, one_mul, sub_self, zero_div]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hzero
    have heq : ∀ i, Real.sqrt (m i) = (∑ j, Real.sqrt (m j)) / n := by
      intro i
      have := hall i (Finset.mem_univ i)
      have := pow_eq_zero_iff two_ne_zero |>.mp this
      linarith
    intro i j
    rw [← Real.sq_sqrt (hm i), ← Real.sq_sqrt (hm j), heq i, heq j]
  · intro h
    have hfun : m = fun _ => m i0 := funext (fun i => h i i0)
    rw [hfun]
    unfold koideRatio
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_pow, Real.sq_sqrt (hm i0)]
    have := hi0.ne'
    have := hn.ne'
    field_simp <;> ring

theorem solution {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hpos : ∃ i, 0 < m i) :
    koideRatio m = 1 ↔ ∃ i, ∀ j, j ≠ i → m j = 0 := by
  obtain ⟨i0, hi0⟩ := hpos
  have hS : 0 < ∑ i, Real.sqrt (m i) :=
    Finset.sum_pos' (fun i _ => Real.sqrt_nonneg _)
      ⟨i0, Finset.mem_univ _, Real.sqrt_pos.mpr hi0⟩
  constructor
  · intro h
    unfold koideRatio at h
    rw [div_eq_one_iff_eq (by positivity)] at h
    refine ⟨i0, fun j hj => ?_⟩
    have hQ' : ∑ i, Real.sqrt (m i) * Real.sqrt (m i) = ∑ i, m i :=
      Finset.sum_congr rfl (fun i _ => Real.mul_self_sqrt (hm i))
    have hsum : ∑ i, Real.sqrt (m i) * ((∑ k, Real.sqrt (m k)) - Real.sqrt (m i)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hQ', h]
      ring
    have hle : ∀ i, Real.sqrt (m i) ≤ ∑ k, Real.sqrt (m k) := fun i =>
      Finset.single_le_sum (fun k _ => Real.sqrt_nonneg (m k)) (Finset.mem_univ i)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (hle i)))).mp hsum
    have h0 := hall i0 (Finset.mem_univ _)
    have hx0 : 0 < Real.sqrt (m i0) := Real.sqrt_pos.mpr hi0
    have hSx : ∑ k, Real.sqrt (m k) = Real.sqrt (m i0) := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · linarith
      · linarith
    have hpair : Real.sqrt (m i0) + Real.sqrt (m j) ≤ ∑ k, Real.sqrt (m k) := by
      have e : ∑ k ∈ ({i0, j} : Finset (Fin n)), Real.sqrt (m k) =
          Real.sqrt (m i0) + Real.sqrt (m j) := Finset.sum_pair (Ne.symm hj)
      rw [← e]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => Real.sqrt_nonneg _)
    have hxj : Real.sqrt (m j) = 0 := by
      have := Real.sqrt_nonneg (m j)
      linarith
    rw [← Real.sq_sqrt (hm j), hxj]
    ring
  · rintro ⟨i, hi⟩
    have hmi : 0 < m i := by
      by_cases hk : i0 = i
      · rw [← hk]; exact hi0
      · exact absurd (hi i0 hk) hi0.ne'
    unfold koideRatio
    rw [Finset.sum_eq_single (f := fun k => m k) i (fun j _ hj => hi j hj) (fun h => absurd (Finset.mem_univ i) h),
      Finset.sum_eq_single (f := fun k => Real.sqrt (m k)) i (fun j _ hj => by rw [hi j hj, Real.sqrt_zero])
        (fun h => absurd (Finset.mem_univ i) h),
      Real.sq_sqrt hmi.le, div_self hmi.ne']

theorem W2p_KoideRelation_koide_third_mass_solutions (m₁ m₂ m₃ : ℝ) (h₁ : 0 < m₁)
    (h₂ : 0 < m₂) (h₃ : 0 < m₃) :
    koideRatio ![m₁, m₂, m₃] = 2 / 3 ↔
      m₃ = 7 * (m₁ + m₂) + 20 * Real.sqrt (m₁ * m₂)
            + 4 * Real.sqrt 3 * (Real.sqrt m₁ + Real.sqrt m₂)
              * Real.sqrt (m₁ + 4 * Real.sqrt (m₁ * m₂) + m₂) ∨
      (4 * Real.sqrt (m₁ * m₂) < m₁ + m₂ ∧
        m₃ = 7 * (m₁ + m₂) + 20 * Real.sqrt (m₁ * m₂)
              - 4 * Real.sqrt 3 * (Real.sqrt m₁ + Real.sqrt m₂)
                * Real.sqrt (m₁ + 4 * Real.sqrt (m₁ * m₂) + m₂)) := by
  unfold koideRatio
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [Real.sqrt_mul h₁.le]
  have e1 := Real.sq_sqrt h₁.le
  have e2 := Real.sq_sqrt h₂.le
  have e3 := Real.sq_sqrt h₃.le
  have p1 : 0 < Real.sqrt m₁ := Real.sqrt_pos.mpr h₁
  have p2 : 0 < Real.sqrt m₂ := Real.sqrt_pos.mpr h₂
  have p3 : 0 < Real.sqrt m₃ := Real.sqrt_pos.mpr h₃
  generalize Real.sqrt m₁ = x1 at e1 p1 ⊢
  generalize Real.sqrt m₂ = x2 at e2 p2 ⊢
  generalize Real.sqrt m₃ = x3 at e3 p3 ⊢
  subst e1 e2 e3
  have hR2 : Real.sqrt (x1 ^ 2 + 4 * (x1 * x2) + x2 ^ 2) ^ 2 = x1 ^ 2 + 4 * (x1 * x2) + x2 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hR0 := Real.sqrt_nonneg (x1 ^ 2 + 4 * (x1 * x2) + x2 ^ 2)
  generalize Real.sqrt (x1 ^ 2 + 4 * (x1 * x2) + x2 ^ 2) = R at hR2 hR0 ⊢
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs30 : 0 < Real.sqrt 3 := by positivity
  have hK : (Real.sqrt 3 * R) ^ 2 = 3 * (x1 ^ 2 + 4 * (x1 * x2) + x2 ^ 2) := by
    rw [mul_pow, hs3, hR2]
  have hK0 : 0 ≤ Real.sqrt 3 * R := by positivity
  rw [div_eq_iff (by positivity)]
  constructor
  · intro h
    have hsq : (x3 - 2 * (x1 + x2)) ^ 2 = (Real.sqrt 3 * R) ^ 2 := by
      linear_combination 3 * h - hK
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
    · left
      have hx3 : x3 = 2 * (x1 + x2) + Real.sqrt 3 * R := by linarith
      rw [hx3]
      linear_combination hK
    · right
      have hx3 : x3 = 2 * (x1 + x2) - Real.sqrt 3 * R := by linarith
      refine ⟨?_, by rw [hx3]; linear_combination hK⟩
      have h4 : 0 < 2 * (x1 + x2) - Real.sqrt 3 * R := by linarith
      nlinarith [mul_pos h4 (by positivity : (0 : ℝ) < 2 * (x1 + x2) + Real.sqrt 3 * R)]
  · intro h
    rcases h with h | ⟨hc, h⟩
    · have hfac : (x3 - (2 * (x1 + x2) + Real.sqrt 3 * R)) *
          (x3 + (2 * (x1 + x2) + Real.sqrt 3 * R)) = 0 := by
        linear_combination h - hK
      rcases mul_eq_zero.mp hfac with h' | h'
      · have hx3 : x3 = 2 * (x1 + x2) + Real.sqrt 3 * R := by linarith
        linear_combination (1 / 3) * (x3 - 2 * (x1 + x2) + Real.sqrt 3 * R) * hx3 + (1 / 3) * hK
      · exfalso
        linarith
    · have h4 : 0 < 2 * (x1 + x2) - Real.sqrt 3 * R := by
        by_contra hneg
        push_neg at hneg
        nlinarith [mul_le_mul_of_nonneg_right hneg
          (by positivity : (0 : ℝ) ≤ 2 * (x1 + x2) + Real.sqrt 3 * R)]
      have hfac : (x3 - (2 * (x1 + x2) - Real.sqrt 3 * R)) *
          (x3 + (2 * (x1 + x2) - Real.sqrt 3 * R)) = 0 := by
        linear_combination h - hK
      rcases mul_eq_zero.mp hfac with h' | h'
      · have hx3 : x3 = 2 * (x1 + x2) - Real.sqrt 3 * R := by linarith
        linear_combination (1 / 3) * (x3 - 2 * (x1 + x2) - Real.sqrt 3 * R) * hx3 + (1 / 3) * hK
      · exfalso
        linarith

theorem W2p_KoideRelation_tau_mass_prediction (mtau : ℝ) (hbig : 105.6583663 < mtau)
    (hq : koideRatio ![0.510998910, 105.6583663, mtau] = 2 / 3) :
    |mtau - 1776.968874| < 0.000001 := by
  have hme : (0 : ℝ) ≤ 0.510998910 := by norm_num
  have hmm : (0 : ℝ) ≤ 105.6583663 := by norm_num
  have hmt : 0 ≤ mtau := by linarith
  unfold koideRatio at hq
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hq
  have ea := Real.sq_sqrt hme
  have eb := Real.sq_sqrt hmm
  have ex := Real.sq_sqrt hmt
  have ha0 : 0 < Real.sqrt (0.510998910 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hb0 : 0 < Real.sqrt (105.6583663 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have ha1 : (71484187762049 / 100000000000000 : ℝ) < Real.sqrt 0.510998910 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have ha2 : Real.sqrt 0.510998910 < (71484187762050 / 100000000000000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hb1 : (1027902555206474 / 100000000000000 : ℝ) < Real.sqrt 105.6583663 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hb2 : Real.sqrt 105.6583663 < (1027902555206475 / 100000000000000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hx0 : 0 ≤ Real.sqrt mtau := Real.sqrt_nonneg _
  generalize Real.sqrt (0.510998910 : ℝ) = a at ea ha0 ha1 ha2 hq
  generalize Real.sqrt (105.6583663 : ℝ) = b at eb hb0 hb1 hb2 hq
  generalize Real.sqrt mtau = x at ex hx0 hq
  subst ex
  have hS : (a + b + x) ^ 2 ≠ 0 := by positivity
  rw [div_eq_iff hS] at hq
  have hy2 : (x - 2 * a - 2 * b) ^ 2 = 3 * a ^ 2 + 3 * b ^ 2 + 12 * (a * b) := by
    linear_combination 3 * hq + 3 * ea + 3 * eb
  norm_num at ea eb hbig
  have hab1 := mul_lt_mul'' ha1 hb1 (by norm_num) (by norm_num)
  have hab2 := mul_lt_mul'' ha2 hb2 ha0.le hb0.le
  norm_num at hab1 hab2
  have hxb : b < x := by nlinarith
  generalize hy : x - 2 * a - 2 * b = y at hy2
  have hy0 : 0 < y := by
    by_contra h
    push_neg at h
    have h1 : -y < 2 * a + b := by linarith
    have h2 := mul_self_lt_mul_self (neg_nonneg.mpr h) h1
    nlinarith
  have hyL : (2016637376275078 / 100000000000000 : ℝ) < y := by
    by_contra h
    push_neg at h
    have := pow_le_pow_left₀ hy0.le h 2
    norm_num at this
    nlinarith
  have hyU : y < (2016637376275083 / 100000000000000 : ℝ) := by
    by_contra h
    push_neg at h
    have := pow_le_pow_left₀ (by norm_num) h 2
    norm_num at this
    nlinarith
  have hxL : (4215410862212124 / 100000000000000 : ℝ) < x := by linarith
  have hxU : x < (4215410862212133 / 100000000000000 : ℝ) := by linarith
  have hx2L := pow_lt_pow_left₀ hxL (by norm_num) two_ne_zero
  have hx2U := pow_lt_pow_left₀ hxU hx0 two_ne_zero
  norm_num at hx2L hx2U
  refine abs_lt.mpr ⟨?_, ?_⟩ <;> norm_num <;> linarith

theorem W2p_KoideRelation_koide_matrix_form (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M.IsHermitian)
    (hpos : ∀ i, 0 ≤ hM.eigenvalues i) (hq : koideRatio hM.eigenvalues = 2 / 3) :
    (7 * M.trace ^ 2 - 8 * (M * M).trace) ^ 2 = 3 / 2 * 32 ^ 2 * M.det * M.trace := by
  have hv : hM.eigenvalues = ![hM.eigenvalues 0, hM.eigenvalues 1, hM.eigenvalues 2] := by
    funext i; fin_cases i <;> rfl
  have key := W2p_KoideRelation_koide_imp_sqrt_free (hM.eigenvalues 0) (hM.eigenvalues 1)
    (hM.eigenvalues 2) (hpos 0) (hpos 1) (hpos 2) (by rw [← hv]; exact hq)
  have hreal : (7 * (hM.eigenvalues 0 + hM.eigenvalues 1 + hM.eigenvalues 2) ^ 2 -
      8 * (hM.eigenvalues 0 * hM.eigenvalues 0 + hM.eigenvalues 1 * hM.eigenvalues 1 +
        hM.eigenvalues 2 * hM.eigenvalues 2)) ^ 2 =
      3 / 2 * 32 ^ 2 * (hM.eigenvalues 0 * hM.eigenvalues 1 * hM.eigenvalues 2) *
        (hM.eigenvalues 0 + hM.eigenvalues 1 + hM.eigenvalues 2) := by
    linear_combination key
  have hc := congrArg (RCLike.ofReal : ℝ → ℂ) hreal
  simp only [RCLike.ofReal_mul, RCLike.ofReal_add, RCLike.ofReal_sub, RCLike.ofReal_pow,
    RCLike.ofReal_div, RCLike.ofReal_ofNat] at hc
  obtain ⟨U, D, hU, hMeq, hD⟩ : ∃ U D : Matrix (Fin 3) (Fin 3) ℂ, star U * U = 1 ∧
      M = U * D * star U ∧ D = Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) :=
    ⟨_, _, Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.prop, hM.spectral_theorem, rfl⟩
  have hdet := hM.det_eq_prod_eigenvalues
  have htr : M.trace = D.trace := by
    rw [hMeq, Matrix.trace_mul_cycle, hU, one_mul]
  have hMM : (M * M).trace = (D * D).trace := by
    have e : M * M = U * (D * D) * star U := by
      rw [hMeq]
      simp only [mul_assoc]
      rw [← mul_assoc (star U) U, hU, one_mul]
    rw [e, Matrix.trace_mul_cycle, hU, one_mul]
  rw [htr, hMM, hdet, hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Matrix.trace_diagonal]
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, Function.comp_apply]
  linear_combination hc

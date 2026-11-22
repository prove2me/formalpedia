-- Prove2me | solution 1 for MasulloAudit.edge_state_trace_limits
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-22T01:34:48.610127+00:00
-- url     : https://prove2.me/submissions/3bb6c78a-21c7-4628-a942-52967511d5f4

import Definitions.Def_MasulloAudit_EdgeLattice

set_option autoImplicit false

open Filter Topology BigOperators

namespace MasulloAudit


lemma term_eq (α : ℝ) (c : ℂ) (hc0 : c ≠ 0) (φ : ℤ → ℂ) (m n : ℤ) :
    φ (n - m) * c ^ (-n) * (starRingEnd ℂ c) ^ (-m) / (edgeWeight α m : ℂ)
      = (φ (n - m) * c ^ (-(n - m))) * (edgeMass α c m : ℂ) := by
  have h1 : c ^ (-n) = c ^ (-(n - m)) * c ^ (-m) := by
    rw [← zpow_add₀ hc0]; congr 1; ring
  have h2 : c ^ (-m) * (starRingEnd ℂ c) ^ (-m) = ((‖c‖ ^ (-2 * m) : ℝ) : ℂ) := by
    rw [← mul_zpow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [← zpow_natCast, ← zpow_mul]
    congr 1; push_cast; ring
  unfold edgeMass
  rw [h1, Complex.ofReal_div]
  rw [show φ (n - m) * (c ^ (-(n - m)) * c ^ (-m)) * (starRingEnd ℂ) c ^ (-m) / (edgeWeight α m : ℂ)
      = φ (n - m) * c ^ (-(n - m)) * (c ^ (-m) * (starRingEnd ℂ) c ^ (-m)) / (edgeWeight α m : ℂ) by ring]
  rw [h2]; ring

lemma edgeWeight_pos (α : ℝ) (m : ℤ) : 0 < edgeWeight α m := Real.exp_pos _

lemma edgeMass_nonneg (α : ℝ) (c : ℂ) (m : ℤ) : 0 ≤ edgeMass α c m :=
  div_nonneg (zpow_nonneg (norm_nonneg _) _) (edgeWeight_pos α m).le

lemma edgeMass_le_one (α : ℝ) (c : ℂ) (hα : 0 ≤ α) (hc1 : 1 ≤ ‖c‖) (m : ℤ) (hm : 0 ≤ m) :
    edgeMass α c m ≤ 1 := by
  unfold edgeMass
  have hw : 1 ≤ edgeWeight α m := by
    unfold edgeWeight; apply Real.one_le_exp; positivity
  have hz : ‖c‖ ^ (-2 * m) ≤ 1 := zpow_le_one_of_nonpos₀ hc1 (by omega)
  rw [div_le_one (by linarith)]; linarith

lemma edgeMass_neg (α : ℝ) (c : ℂ) (hc0 : c ≠ 0) (R : ℕ) :
    edgeMass α c (-(R : ℤ)) = (‖c‖ / Real.exp α) ^ (2 * R) := by
  unfold edgeMass edgeWeight
  have hn : (0:ℝ) < ‖c‖ := norm_pos_iff.mpr hc0
  rw [div_pow, ← Real.exp_nat_mul]
  congr 1
  · rw [show (-2 * -(R:ℤ)) = ((2 * R : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  · congr 1; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring

/-- reindex -/
lemma sum_shift (f : ℤ → ℂ) (a b m : ℤ) :
    ∑ n ∈ Finset.Icc a b, f (n - m) = ∑ d ∈ Finset.Icc (a - m) (b - m), f d := by
  apply Finset.sum_nbij' (fun n => n - m) (fun d => d + m)
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro n _; ring
  · intro d _; ring
  · intro n _; rfl


section support
variable (φ : ℤ → ℂ) (D : ℕ) (hφ : ∀ d : ℤ, d ≤ 0 ∨ (D : ℤ) < d → φ d = 0)
include hφ

lemma sum_eq_T0 (c : ℂ) (lo hi : ℤ) (hlo : lo ≤ 1) (hhi : (D : ℤ) ≤ hi) :
    ∑ d ∈ Finset.Icc lo hi, φ d * c ^ (-d) = ∑ d ∈ Finset.Icc (1 : ℤ) D, φ d * c ^ (-d) := by
  symm
  apply Finset.sum_subset
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d hd hd'
    simp only [Finset.mem_Icc, not_and_or, not_le] at hd'
    rw [hφ d (by omega)]; ring

lemma norm_sum_le_C (c : ℂ) (s : Finset ℤ) :
    ‖∑ d ∈ s, φ d * c ^ (-d)‖ ≤ ∑ d ∈ Finset.Icc (1 : ℤ) D, ‖φ d * c ^ (-d)‖ := by
  have : ∑ d ∈ s, φ d * c ^ (-d) = ∑ d ∈ s ∩ Finset.Icc (1 : ℤ) D, φ d * c ^ (-d) := by
    symm; apply Finset.sum_subset Finset.inter_subset_left
    intro d hd hd'
    have : d ∉ Finset.Icc (1:ℤ) D := fun h => hd' (Finset.mem_inter.mpr ⟨hd, h⟩)
    simp only [Finset.mem_Icc, not_and_or, not_le] at this
    rw [hφ d (by omega)]; ring
  rw [this]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => norm_nonneg _))

lemma sum_zero_off (c : ℂ) (lo hi : ℤ) (h : hi < 1 ∨ (D : ℤ) < lo) :
    ∑ d ∈ Finset.Icc lo hi, φ d * c ^ (-d) = 0 := by
  apply Finset.sum_eq_zero
  intro d hd; simp only [Finset.mem_Icc] at hd
  rw [hφ d (by omega)]; ring
end support

theorem solution_aux (α : ℝ) (c : ℂ) (hα : 0 ≤ α) (hc : Real.exp α < ‖c‖)
    (φ : ℤ → ℂ) (D : ℕ) (hφ : ∀ d : ℤ, d ≤ 0 ∨ (D : ℤ) < d → φ d = 0) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), ∑ n ∈ Finset.Icc (-(R : ℤ)) (R + 1),
            φ (n - m) * c ^ (-n) * (starRingEnd ℂ c) ^ (-m) / (edgeWeight α m : ℂ)) /
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ)))
      atTop (𝓝 (∑ d ∈ Finset.Icc (1 : ℤ) D, φ d * c ^ (-d))) ∧
    ∀ Λ : ℕ, Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), ∑ n ∈ Finset.Icc (-(Λ : ℤ)) Λ,
            φ (n - m) * c ^ (-n) * (starRingEnd ℂ c) ^ (-m) / (edgeWeight α m : ℂ)) /
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ)))
      atTop (𝓝 0) := by
  have hc1 : 1 < ‖c‖ := lt_of_le_of_lt (Real.one_le_exp hα) hc
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc1; linarith
  set f : ℤ → ℂ := fun d => φ d * c ^ (-d) with hf
  set T0 : ℂ := ∑ d ∈ Finset.Icc (1 : ℤ) D, f d with hT0
  set C : ℝ := ∑ d ∈ Finset.Icc (1 : ℤ) D, ‖f d‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  set Den : ℕ → ℝ := fun R => ∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), edgeMass α c m with hDen
  have hq : 1 < (‖c‖ / Real.exp α) ^ 2 := by
    have : 1 < ‖c‖ / Real.exp α := by rw [one_lt_div (Real.exp_pos _)]; exact hc
    nlinarith
  have hDen_ge : ∀ R : ℕ, ((‖c‖ / Real.exp α) ^ 2) ^ R ≤ Den R := by
    intro R
    rw [← pow_mul, ← edgeMass_neg α c hc0 R]
    exact Finset.single_le_sum (f := fun m => edgeMass α c m)
      (fun m _ => edgeMass_nonneg α c m) (Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩)
  have hDen_pos : ∀ R : ℕ, 0 < Den R := fun R =>
    lt_of_lt_of_le (pow_pos (by linarith) R) (hDen_ge R)
  have hDen_top : Tendsto Den atTop atTop :=
    tendsto_atTop_mono hDen_ge (tendsto_pow_atTop_atTop_of_one_lt hq)
  have hDenC : ∀ R : ℕ, (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ)) = (Den R : ℂ) := by
    intro R; simp [hDen]
  -- numerator rewriting
  have hNum : ∀ (R : ℕ) (s : Finset ℤ),
      (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), ∑ n ∈ s,
          φ (n - m) * c ^ (-n) * (starRingEnd ℂ c) ^ (-m) / (edgeWeight α m : ℂ))
        = ∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ) * ∑ n ∈ s, f (n - m) := by
    intro R s
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [term_eq α c hc0 φ m n]; simp only [hf]; ring
  -- generic bound: ‖Num/Den - L‖ ≤ B/Den  ⇒ limit
  have key : ∀ (N : ℕ → ℂ) (L : ℂ) (B : ℝ),
      (∀ᶠ R in atTop, ‖N R - L * (Den R : ℂ)‖ ≤ B) →
      Tendsto (fun R => N R / (Den R : ℂ)) atTop (𝓝 L) := by
    intro N L B hB
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun R => B / Den R) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hDen_top
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
    filter_upwards [hB] with R hR
    have hD : (Den R : ℂ) ≠ 0 := by exact_mod_cast (hDen_pos R).ne'
    have : N R / (Den R : ℂ) - L = (N R - L * (Den R : ℂ)) / (Den R : ℂ) := by
      field_simp
    rw [this, norm_div, Complex.norm_real, Real.norm_of_nonneg (hDen_pos R).le]
    exact div_le_div_of_nonneg_right hR (hDen_pos R).le
  constructor
  · -- part 1
    refine (key _ T0 (2 * C * D) ?_).congr (fun R => by rw [hDenC R])
    filter_upwards [eventually_ge_atTop D] with R hR
    rw [hNum R]
    have hexp : (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ) *
          ∑ n ∈ Finset.Icc (-(R : ℤ)) (R + 1), f (n - m)) - T0 * (Den R : ℂ)
        = ∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ) *
          ((∑ n ∈ Finset.Icc (-(R : ℤ)) (R + 1), f (n - m)) - T0) := by
      rw [← hDenC R, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m _ => by ring)
    rw [hexp]
    have hterm : ∀ m ∈ Finset.Icc (-(R : ℤ)) (R + 1),
        ‖(edgeMass α c m : ℂ) * ((∑ n ∈ Finset.Icc (-(R : ℤ)) (R + 1), f (n - m)) - T0)‖
          ≤ if m ∈ Finset.Icc ((R : ℤ) + 2 - D) (R + 1) then 2 * C else 0 := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      rw [sum_shift f]
      split_ifs with h
      · simp only [Finset.mem_Icc] at h
        have hm0 : 0 ≤ m := by omega
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (edgeMass_nonneg α c m)]
        have h1 := edgeMass_le_one α c hα hc1.le m hm0
        have h2 : ‖(∑ d ∈ Finset.Icc (-(R : ℤ) - m) (R + 1 - m), f d) - T0‖ ≤ 2 * C := by
          refine (norm_sub_le _ _).trans ?_
          have a1 := norm_sum_le_C φ D hφ c (Finset.Icc (-(R : ℤ) - m) (R + 1 - m))
          have a2 := norm_sum_le_C φ D hφ c (Finset.Icc (1 : ℤ) D)
          simp only [hf, hC, hT0] at a1 a2 ⊢
          linarith
        calc edgeMass α c m * ‖(∑ d ∈ Finset.Icc (-(R : ℤ) - m) (R + 1 - m), f d) - T0‖
            ≤ 1 * (2 * C) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
          _ = 2 * C := by ring
      · simp only [Finset.mem_Icc, not_and_or, not_le] at h
        have heq : (∑ d ∈ Finset.Icc (-(R : ℤ) - m) (R + 1 - m), f d) = T0 := by
          simp only [hf, hT0]
          exact sum_eq_T0 φ D hφ c _ _ (by omega) (by omega)
        rw [heq, sub_self, mul_zero, norm_zero]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_ite_mem]
    refine (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => by positivity)).trans ?_
    rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
    have : ((R : ℤ) + 1 + 1 - ((R : ℤ) + 2 - D)).toNat = D := by omega
    rw [this]; linarith
  · -- part 2
    intro Λ
    set K : ℝ := ∑ m ∈ Finset.Icc (-(Λ : ℤ) - D) Λ, edgeMass α c m * C with hK
    refine (key _ 0 K ?_).congr (fun R => by rw [hDenC R])
    refine Eventually.of_forall (fun R => ?_)
    rw [hNum R, zero_mul, sub_zero]
    have hterm : ∀ m ∈ Finset.Icc (-(R : ℤ)) (R + 1),
        ‖(edgeMass α c m : ℂ) * ∑ n ∈ Finset.Icc (-(Λ : ℤ)) Λ, f (n - m)‖
          ≤ if m ∈ Finset.Icc (-(Λ : ℤ) - D) Λ then edgeMass α c m * C else 0 := by
      intro m _
      rw [sum_shift f, norm_mul, Complex.norm_real, Real.norm_of_nonneg (edgeMass_nonneg α c m)]
      split_ifs with h
      · refine mul_le_mul_of_nonneg_left ?_ (edgeMass_nonneg α c m)
        have a1 := norm_sum_le_C φ D hφ c (Finset.Icc (-(Λ : ℤ) - m) (Λ - m))
        simpa only [hf, hC] using a1
      · simp only [Finset.mem_Icc, not_and_or, not_le] at h
        have : (∑ d ∈ Finset.Icc (-(Λ : ℤ) - m) (Λ - m), f d) = 0 := by
          simp only [hf]
          exact sum_zero_off φ D hφ c _ _ (by omega)
        rw [this, norm_zero, mul_zero]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_ite_mem]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun m _ _ => mul_nonneg (edgeMass_nonneg α c m) hC0)

end MasulloAudit

open MasulloAudit in
theorem solution (α : ℝ) (c : ℂ) (hα : 0 ≤ α) (hc : Real.exp α < ‖c‖)
    (φ : ℤ → ℂ) (D : ℕ) (hφ : ∀ d : ℤ, d ≤ 0 ∨ (D : ℤ) < d → φ d = 0) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), ∑ n ∈ Finset.Icc (-(R : ℤ)) (R + 1),
            φ (n - m) * c ^ (-n) * (starRingEnd ℂ c) ^ (-m) / (edgeWeight α m : ℂ)) /
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ)))
      atTop (𝓝 (∑ d ∈ Finset.Icc (1 : ℤ) D, φ d * c ^ (-d))) ∧
    ∀ Λ : ℕ, Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), ∑ n ∈ Finset.Icc (-(Λ : ℤ)) Λ,
            φ (n - m) * c ^ (-n) * (starRingEnd ℂ c) ^ (-m) / (edgeWeight α m : ℂ)) /
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ)))
      atTop (𝓝 0) :=
  solution_aux α c hα hc φ D hφ

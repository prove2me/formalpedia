-- Prove2me | solution 1 for GlobalTheory.summable_and_tsum_le_of_box_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:47.136783+00:00
-- url     : https://prove2.me/submissions/5700e049-e1e2-473d-a758-7aa6c4472ec3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SummableAndTsumLeOfBoxCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ι Γ : Type) [Fintype ι] (D : Γ → ι → ℝ) (t : Γ → ℝ)
    (a A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (ha : Real.exp (-a) ≤ 1 / 2) (_hD : ∀ γ v, 0 ≤ D γ v)
    (ht : ∀ γ, 0 ≤ t γ ∧ t γ ≤ c * ∏ v, Real.exp (-(2 * a * (⌊D γ v⌋₊ : ℝ))))
    (hN : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (a * ∑ v, r v)) :
    Summable t ∧ ∑' γ, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
  classical
  set q := Real.exp (-a) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by linarith
  have hgeom : ∀ M : ℕ, ∑ k ∈ Finset.range M, q ^ k ≤ 2 := by
    intro M
    calc ∑ k ∈ Finset.range M, q ^ k ≤ ∑' k, q ^ k :=
          (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun k _ => pow_nonneg hq0 k)
      _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
      _ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
  have hprod : ∀ F : Finset (ι → ℕ), ∑ n ∈ F, ∏ v, q ^ (n v) ≤ 2 ^ Fintype.card ι := by
    intro F
    set M := F.sup (fun n => ∑ v, n v) + 1 with hM
    have hsub : F ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
      intro n hn
      rw [Fintype.mem_piFinset]
      intro v
      rw [Finset.mem_range]
      have h1 : n v ≤ ∑ w, n w :=
        Finset.single_le_sum (fun w _ => Nat.zero_le (n w)) (Finset.mem_univ v)
      have h2 : ∑ w, n w ≤ F.sup (fun n => ∑ v, n v) := Finset.le_sup (f := fun n => ∑ v, n v) hn
      omega
    calc ∑ n ∈ F, ∏ v, q ^ (n v)
        ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => Finset.range M), ∏ v, q ^ (n v) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => Finset.prod_nonneg (fun v _ => pow_nonneg hq0 _))
      _ = ∏ _v : ι, ∑ k ∈ Finset.range M, q ^ k :=
          (Finset.prod_univ_sum (fun _ => Finset.range M) (fun _ k => q ^ k)).symm
      _ ≤ ∏ _v : ι, (2 : ℝ) :=
          Finset.prod_le_prod (fun v _ => Finset.sum_nonneg (fun k _ => pow_nonneg hq0 k))
            (fun v _ => hgeom M)
      _ = 2 ^ Fintype.card ι := by simp
  have hB : 0 ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by positivity
  have hfin : ∀ s : Finset Γ, ∑ γ ∈ s, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
    intro s
    set φ : Γ → ι → ℕ := fun γ v => ⌊D γ v⌋₊ with hφ
    set s' := s.filter (fun γ => t γ ≠ 0) with hs'
    rw [← Finset.sum_filter_ne_zero]
    rw [← Finset.sum_fiberwise_of_maps_to (t := s'.image φ) (g := φ)
      (fun γ hγ => Finset.mem_image_of_mem φ hγ)]
    have hfib : ∀ n : ι → ℕ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ ≤
        c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
      intro n
      set Fn := s'.filter (fun γ => φ γ = n) with hFn
      set e : ℝ := c * ∏ v, Real.exp (-(2 * a * (n v : ℝ))) with he_def
      have he : 0 ≤ e := by positivity
      have h1 : ∑ γ ∈ Fn, t γ ≤ Fn.card * e := by
        calc ∑ γ ∈ Fn, t γ ≤ ∑ _γ ∈ Fn, e := by
              apply Finset.sum_le_sum
              intro γ hγ
              have hn : φ γ = n := (Finset.mem_filter.1 hγ).2
              have hfl : ∀ v, ⌊D γ v⌋₊ = n v := fun v => congrFun hn v
              have h := (ht γ).2
              simp only [hfl] at h
              exact h
          _ = Fn.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
      set r : ι → ℝ := fun v => (n v : ℝ) + 1 with hr_def
      have hr : ∀ v, 0 ≤ r v := fun v => by positivity
      obtain ⟨hSf, hSc⟩ := hN r hr
      have hsub : (↑Fn : Set Γ) ⊆ {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v} := by
        intro γ hγ
        have hm := Finset.mem_filter.1 (Finset.mem_coe.1 hγ)
        have hm' := Finset.mem_filter.1 hm.1
        refine ⟨hm'.2, fun v => ?_⟩
        have hfl : ⌊D γ v⌋₊ = n v := congrFun hm.2 v
        have hl := Nat.lt_floor_add_one (D γ v)
        rw [hfl] at hl
        exact hl.le
      have hcard : (Fn.card : ℝ) ≤ A * Real.exp (a * ∑ v, r v) := by
        have hc' := Set.ncard_le_ncard hsub hSf
        rw [Set.ncard_coe_finset] at hc'
        exact le_trans (by exact_mod_cast hc') hSc
      have hS2 : ∑ v, 2 * a * (n v : ℝ) = 2 * a * ∑ v, (n v : ℝ) := by rw [Finset.mul_sum]
      have hS3 : ∑ v, (n v : ℝ) * -a = (∑ v, (n v : ℝ)) * -a := by rw [Finset.sum_mul]
      have hS1 : ∑ v, r v = ∑ v, (n v : ℝ) + Fintype.card ι := by
        simp only [hr_def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
      calc ∑ γ ∈ Fn, t γ ≤ Fn.card * e := h1
        _ ≤ A * Real.exp (a * ∑ v, r v) * e := mul_le_mul_of_nonneg_right hcard he
        _ = c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
            rw [he_def, hq]
            simp_rw [← Real.exp_nat_mul]
            rw [← Real.exp_sum, ← Real.exp_sum, Finset.sum_neg_distrib, hS2, hS3, hS1]
            rw [show A * Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
                  (c * Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) =
                c * A * (Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
                  Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) by ring,
              show c * A * Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a) =
                c * A * (Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a)) by ring,
              ← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
    calc ∑ n ∈ s'.image φ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ
        ≤ ∑ n ∈ s'.image φ, c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) :=
          Finset.sum_le_sum (fun n _ => hfib n)
      _ = c * A * Real.exp (a * Fintype.card ι) * ∑ n ∈ s'.image φ, ∏ v, q ^ (n v) := by
          rw [Finset.mul_sum]
      _ ≤ c * A * Real.exp (a * Fintype.card ι) * 2 ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_left (hprod _) (by positivity)
      _ = c * A * (2 * Real.exp a) ^ Fintype.card ι := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_comm (Fintype.card ι : ℝ) a]
          ring
  exact ⟨summable_of_sum_le (fun γ => (ht γ).1) hfin, tsum_le_of_sum_le' hB hfin⟩
end GlobalTheory

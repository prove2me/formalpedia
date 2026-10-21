-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.row_count_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:35:19.077894+00:00
-- url     : https://prove2.me/submissions/9afadb67-ca2e-4b05-bcb4-167fb4706e1c

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_volume_bounds

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto (fun H : ℝ => (actualRowCount d H : ℝ) / H ^ (d.m + 1)) atTop
      (𝓝 (((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m) /
        ((Nat.factorial (d.m + 1) : ℝ) * (d.v0 : ℝ) * ∏ i : Fin d.m, d.x (i.val + 1)))) := by
  classical
  let q : Fin d.m → ℕ := finiteDenominators d
  let w : Fin (d.m + 1) → ℝ :=
    InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ) (MatrixArithmetic.logWeights q)
  have hθpos : (0 : ℝ) < (d.base.theta : ℝ) := d.base.theta_pos
  have hv0pos : (0 : ℝ) < (d.v0 : ℝ) := d.v0_pos
  have hq2 : ∀ i : Fin d.m, 2 ≤ q i := fun i => (d.approximations i.val).1
  have hlogpos : ∀ i : Fin d.m, 0 < MatrixArithmetic.logWeights q i := by
    intro i
    simp only [MatrixArithmetic.logWeights]
    have h1 : (1 : ℝ) < (q i : ℝ) := by
      have h2 : (1 : ℕ) < q i := by have := hq2 i; omega
      exact_mod_cast h2
    have h3 : (0 : ℕ) < ⌈Real.log (q i)⌉₊ := Nat.ceil_pos.mpr (Real.log_pos h1)
    exact_mod_cast h3
  have hw : ∀ i : Fin (d.m + 1), 0 < w i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · show 0 < w 0
      simp only [w, InterpolationMatrix.rowWeights]
      exact hv0pos
    · intro j
      show 0 < w j.succ
      simp only [w, InterpolationMatrix.rowWeights]
      exact div_pos (hlogpos j) hθpos
  -- The row count is `K` times the strict weighted-simplex count.
  have hcard : ∀ H : ℝ, (actualRowCount d H : ℝ) =
      (d.K : ℝ) * ((strictWeightedSimplex w H).card : ℝ) := by
    intro H
    have hNat : actualRowCount d H = d.K * (strictWeightedSimplex w H).card := by
      rw [actualRowCount]
      change Fintype.card (Fin d.K × ↥(strictWeightedSimplex w H)) =
        d.K * (strictWeightedSimplex w H).card
      simp
    rw [hNat]
    push_cast
    ring
  -- Membership relations between the strict and non-strict weighted simplices.
  have hsub : ∀ H : ℝ, strictWeightedSimplex w H ⊆ realWeightedSimplex w H := by
    intro H a ha
    simp only [strictWeightedSimplex, Finset.mem_filter] at ha
    exact ha.1
  have hshift : ∀ H : ℝ, 1 ≤ H → realWeightedSimplex w (H - 1) ⊆ strictWeightedSimplex w H := by
    intro H hH a ha
    simp only [realWeightedSimplex, strictWeightedSimplex, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_range] at ha ⊢
    obtain ⟨hbox, hsum⟩ := ha
    refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
    · have hsub' : H - 1 ≤ H := by linarith
      have hdiv : (H - 1) / w i ≤ H / w i :=
        div_le_div_of_nonneg_right hsub' (le_of_lt (hw i))
      have hfloor : ⌊(H - 1) / w i⌋₊ ≤ ⌊H / w i⌋₊ := Nat.floor_mono hdiv
      have := hbox i
      omega
    · linarith
    · linarith
  -- Two-sided volume bound for the strict count.
  have hstrict : Tendsto (fun H : ℝ =>
      ((strictWeightedSimplex w H).card : ℝ) / H ^ (d.m + 1)) atTop
      (𝓝 (1 / ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i))) := by
    have hDpos : (0 : ℝ) < (Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i :=
      mul_pos (by positivity) (Finset.prod_pos (fun i _ => hw i))
    have hlowerlim : Tendsto (fun H : ℝ =>
        ((H - 1) / H) ^ (d.m + 1) /
          ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i)) atTop
        (𝓝 (1 / ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i))) := by
      have h1 : Tendsto (fun H : ℝ => (H - 1) / H) atTop (𝓝 1) := by
        have hbase : Tendsto (fun H : ℝ => 1 - H⁻¹) atTop (𝓝 1) := by
          have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
          have h := hc.sub (tendsto_inv_atTop_zero (𝕜 := ℝ))
          simpa using h
        refine hbase.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
        field_simp
      have h2 : Tendsto (fun H : ℝ => ((H - 1) / H) ^ (d.m + 1)) atTop (𝓝 1) := by
        simpa using h1.pow (d.m + 1)
      simpa using h2.div_const ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i)
    have hupperlim : Tendsto (fun H : ℝ =>
        ((H + ∑ i : Fin (d.m + 1), w i) / H) ^ (d.m + 1) /
          ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i)) atTop
        (𝓝 (1 / ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i))) := by
      have h1 : Tendsto (fun H : ℝ => (H + ∑ i : Fin (d.m + 1), w i) / H) atTop (𝓝 1) := by
        have hbase : Tendsto (fun H : ℝ => 1 + (∑ i : Fin (d.m + 1), w i) * H⁻¹) atTop (𝓝 1) := by
          have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
          have h := hc.add
            ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (∑ i : Fin (d.m + 1), w i))
          simpa using h
        refine hbase.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
        field_simp
      have h2 : Tendsto (fun H : ℝ => ((H + ∑ i : Fin (d.m + 1), w i) / H) ^ (d.m + 1))
          atTop (𝓝 1) := by
        simpa using h1.pow (d.m + 1)
      simpa using h2.div_const ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerlim hupperlim ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      have hHpos : (0 : ℝ) < H := by linarith
      have hHpowpos : (0 : ℝ) < H ^ (d.m + 1) := pow_pos hHpos _
      have hb := (weighted_simplex_volume_bounds (d.m + 1) w (H - 1) hw (by linarith)).1
      have hle : (H - 1) ^ (d.m + 1) /
          ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i) ≤
          ((strictWeightedSimplex w H).card : ℝ) := by
        calc (H - 1) ^ (d.m + 1) /
              ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i)
            ≤ ((realWeightedSimplex w (H - 1)).card : ℝ) := hb
          _ ≤ ((strictWeightedSimplex w H).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (hshift H hH)
      calc ((H - 1) / H) ^ (d.m + 1) /
            ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i)
          = ((H - 1) ^ (d.m + 1) /
              ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i)) / H ^ (d.m + 1) := by
            rw [div_pow]
            field_simp
        _ ≤ ((strictWeightedSimplex w H).card : ℝ) / H ^ (d.m + 1) :=
            div_le_div_of_nonneg_right hle hHpowpos.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      have hHpos : (0 : ℝ) < H := by linarith
      have hHpowpos : (0 : ℝ) < H ^ (d.m + 1) := pow_pos hHpos _
      have hb := (weighted_simplex_volume_bounds (d.m + 1) w H hw hHpos.le).2
      have hle : ((strictWeightedSimplex w H).card : ℝ) ≤
          (H + ∑ i : Fin (d.m + 1), w i) ^ (d.m + 1) /
            ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i) := by
        calc ((strictWeightedSimplex w H).card : ℝ)
            ≤ ((realWeightedSimplex w H).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (hsub H)
          _ ≤ _ := hb
      calc ((strictWeightedSimplex w H).card : ℝ) / H ^ (d.m + 1)
          ≤ ((H + ∑ i : Fin (d.m + 1), w i) ^ (d.m + 1) /
              ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i)) / H ^ (d.m + 1) :=
            div_le_div_of_nonneg_right hle hHpowpos.le
        _ = ((H + ∑ i : Fin (d.m + 1), w i) / H) ^ (d.m + 1) /
              ((Nat.factorial (d.m + 1) : ℝ) * ∏ i : Fin (d.m + 1), w i) := by
            rw [div_pow]
            field_simp
  -- Product identity converting `∏ w` into the target constant.
  have hxlog : ∀ i : Fin d.m, MatrixArithmetic.logWeights q i = d.x (i.val + 1) := by
    intro i
    simp only [MatrixArithmetic.logWeights, q, finiteDenominators]
    rw [d.x_log i.val]
  have hprod : ∀ f : Fin d.m → ℝ, (∏ i : Fin d.m, f i / (d.base.theta : ℝ)) =
      (∏ i : Fin d.m, f i) / (d.base.theta : ℝ) ^ d.m := by
    intro f
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hP : (∏ i : Fin (d.m + 1), w i) =
      (d.v0 : ℝ) * (∏ i : Fin d.m, d.x (i.val + 1)) / (d.base.theta : ℝ) ^ d.m := by
    rw [Fin.prod_univ_succ]
    have hw0 : w 0 = (d.v0 : ℝ) := by
      simp [w, InterpolationMatrix.rowWeights]
    have hws : ∀ i : Fin d.m, w i.succ =
        MatrixArithmetic.logWeights q i / (d.base.theta : ℝ) := by
      intro i
      simp [w, InterpolationMatrix.rowWeights]
    rw [hw0]
    conv_lhs => rw [show (∏ i : Fin d.m, w i.succ) =
        ∏ i : Fin d.m, (MatrixArithmetic.logWeights q i / (d.base.theta : ℝ)) from
      Finset.prod_congr rfl (fun i _ => hws i)]
    rw [hprod]
    rw [show (∏ i : Fin d.m, MatrixArithmetic.logWeights q i) =
        ∏ i : Fin d.m, d.x (i.val + 1) from
      Finset.prod_congr rfl (fun i _ => hxlog i)]
    ring
  -- Assemble.
  have hmain : Tendsto (fun H : ℝ => (actualRowCount d H : ℝ) / H ^ (d.m + 1)) atTop
      (𝓝 ((d.K : ℝ) * (1 / ((Nat.factorial (d.m + 1) : ℝ) *
        ∏ i : Fin (d.m + 1), w i)))) := by
    have h := hstrict.const_mul (d.K : ℝ)
    refine h.congr' ?_
    filter_upwards with H
    rw [hcard H]
    ring
  have hval : (d.K : ℝ) * (1 / ((Nat.factorial (d.m + 1) : ℝ) *
        ∏ i : Fin (d.m + 1), w i)) =
      ((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m) /
        ((Nat.factorial (d.m + 1) : ℝ) * (d.v0 : ℝ) *
          ∏ i : Fin d.m, d.x (i.val + 1)) := by
    rw [hP]
    have hθne : (d.base.theta : ℝ) ≠ 0 := hθpos.ne'
    have hv0ne : (d.v0 : ℝ) ≠ 0 := hv0pos.ne'
    have hfacne : ((Nat.factorial (d.m + 1) : ℝ)) ≠ 0 := by positivity
    have hxne : (∏ i : Fin d.m, d.x (i.val + 1)) ≠ 0 :=
      (Finset.prod_pos (fun i _ => by
        rw [← hxlog i]
        exact hlogpos i)).ne'
    field_simp
  rw [hval] at hmain
  exact hmain

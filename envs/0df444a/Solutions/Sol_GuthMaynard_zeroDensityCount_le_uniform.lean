-- Prove2me | solution 1 for GuthMaynard.zeroDensityCount_le_uniform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:33:22.570244+00:00
-- url     : https://prove2.me/submissions/60f708a6-3dae-4b80-a0d5-e55a31d8a735
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GuthMaynard_huxley_density_estimate_uniform
import Theorems.Thm_LindelofHypothesis_guth_maynard_density_estimate

open Filter Topology Asymptotics
open scoped ENNReal

namespace GuthMaynard.CitedZeros

/-! ## Monotonicity of `N(σ, T)` -/

lemma enat_summable {β : Type*} (f : β → ℕ∞) : Summable f :=
  ⟨_, hasSum_of_isLUB _ (isLUB_sSup _)⟩

lemma enat_tsum_mono {f : ℂ → ℕ∞} {s t : Set ℂ} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  Summable.tsum_le_tsum_of_inj (Set.inclusion h) (Set.inclusion_injective h)
    (fun _ _ => zero_le) (fun _ => le_rfl) (enat_summable _) (enat_summable _)

lemma N_mono {σ σ' T T' : ℝ} (hσ : σ ≤ σ') (hT : T' ≤ T) :
    (LindelofHypothesis.zeroDensityCount σ' T' : ℝ≥0∞) ≤
      LindelofHypothesis.zeroDensityCount σ T := by
  rw [ENat.toENNReal_le]
  unfold LindelofHypothesis.zeroDensityCount
  exact enat_tsum_mono (fun s hs => ⟨hs.1, hσ.trans hs.2.1, hs.2.2.trans hT⟩)

/-! ## Goal 1 -/

/-! ## Goal 2 -/

/-- The constant used in the uniform bound. -/
noncomputable def Cst (CH : ℝ) : ℝ := max CH 0 + (Real.log 2 ^ 44)⁻¹

lemma Cst_L {CH T : ℝ} (hT : 2 ≤ T) : 1 ≤ Cst CH * Real.log T ^ (44 : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hL : Real.log T ^ (44 : ℝ) = Real.log T ^ (44 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rw [hL]
  have h44 : Real.log 2 ^ 44 ≤ Real.log T ^ 44 := pow_le_pow_left₀ hl2.le hle 44
  have hp : 0 < Real.log 2 ^ 44 := by positivity
  have h1 : 1 ≤ (Real.log 2 ^ 44)⁻¹ * Real.log T ^ 44 := by
    rw [inv_mul_eq_div, one_le_div hp]; exact h44
  have hm : 0 ≤ max CH 0 * Real.log T ^ 44 := by
    have := le_max_right CH 0; positivity
  unfold Cst; rw [add_mul]; linarith

lemma Cst_nonneg (CH : ℝ) : 0 ≤ Cst CH := by
  unfold Cst; have := le_max_right CH 0; positivity

/-- Huxley range `σ ∈ [4/5, 1]`. -/
lemma hux_part {CH : ℝ}
    (hCH : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44))
    {T σ δ : ℝ} (hT : 2 ≤ T) (hσ₀ : 4 / 5 ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 ≤ δ) :
    (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
      ENNReal.ofReal (Cst CH * T ^ ((30 / 13 + δ) * (1 - σ)) * Real.log T ^ (44 : ℝ)) := by
  refine (hCH T hT σ (by linarith) hσ₁).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL : Real.log T ^ (44 : ℝ) = Real.log T ^ (44 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rw [hL]
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hexp : 3 * (1 - σ) / (3 * σ - 1) ≤ (30 / 13 + δ) * (1 - σ) := by
    rw [div_le_iff₀ (by linarith)]
    have a1 : 0 ≤ 1 - σ := by linarith
    nlinarith [mul_nonneg a1 (by linarith : (0 : ℝ) ≤ σ - 4 / 5),
      mul_nonneg (mul_nonneg a1 hδ) (by linarith : (0 : ℝ) ≤ 3 * σ - 1)]
  have hpow : T ^ (3 * (1 - σ) / (3 * σ - 1)) ≤ T ^ ((30 / 13 + δ) * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
  have hm : max CH 0 ≤ Cst CH := by
    unfold Cst; have : 0 ≤ (Real.log 2 ^ 44)⁻¹ := by positivity
    linarith
  have h0 : 0 ≤ T ^ (3 * (1 - σ) / (3 * σ - 1)) := by positivity
  calc CH * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44
      ≤ max CH 0 * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44 := by
        gcongr; exact le_max_left _ _
    _ ≤ Cst CH * T ^ ((30 / 13 + δ) * (1 - σ)) * Real.log T ^ 44 := by
        have := le_max_right CH 0
        have := Cst_nonneg CH
        gcongr

/-- Single-point Guth–Maynard bound with the constant absorbed. -/
lemma pt {s : ℝ} (hs₀ : 1 / 2 ≤ s) (hs₁ : s ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (LindelofHypothesis.zeroDensityCount s T : ℝ≥0∞) ≤
      ENNReal.ofReal (T ^ (30 / 13 * (1 - s) + ε)) := by
  obtain ⟨C, hC⟩ := LindelofHypothesis.guth_maynard_density_estimate s hs₀ hs₁ (ε / 2)
    (half_pos hε)
  filter_upwards [hC, (tendsto_rpow_atTop (half_pos hε)).eventually_ge_atTop C,
    eventually_gt_atTop 0] with T h1 h2 h3
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have : T ^ (30 / 13 * (1 - s) + ε) = T ^ (ε / 2) * T ^ (30 / 13 * (1 - s) + ε / 2) := by
    rw [← Real.rpow_add h3]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- Range `σ ∈ [1/2, 4/5]` via a finite grid. -/
lemma low_part {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T in atTop, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 4 / 5 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (T ^ ((30 / 13 + δ) * (1 - σ))) := by
  set h : ℝ := δ / 40 with hh
  have hpos : 0 < h := by positivity
  set n : ℕ := ⌊(3 / 10) / h⌋₊ with hn
  let g : Fin (n + 1) → ℝ := fun i => 1 / 2 + (i : ℕ) * h
  have hg : ∀ i : Fin (n + 1), 1 / 2 ≤ g i ∧ g i ≤ 1 := by
    intro i
    have hi : ((i : ℕ) : ℝ) ≤ (3 / 10) / h := by
      have : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.2
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by positivity))
    have : ((i : ℕ) : ℝ) * h ≤ 3 / 10 := (le_div_iff₀ hpos).mp hi
    have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) * h := by positivity
    constructor <;> simp only [g] <;> linarith
  have hall : ∀ᶠ T in atTop, ∀ i : Fin (n + 1),
      (LindelofHypothesis.zeroDensityCount (g i) T : ℝ≥0∞) ≤
        ENNReal.ofReal (T ^ (30 / 13 * (1 - g i) + δ / 10)) :=
    eventually_all.mpr fun i => pt (hg i).1 (hg i).2 (by positivity)
  filter_upwards [hall, eventually_ge_atTop 1] with T hT h1 σ hσ₀ hσ₁
  have hq : 0 ≤ (σ - 1 / 2) / h := div_nonneg (by linarith) hpos.le
  set j : ℕ := ⌊(σ - 1 / 2) / h⌋₊ with hj
  have hjn : j ≤ n := Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hpos.le)
  let i : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hjn⟩
  have hgi : g i = 1 / 2 + (j : ℝ) * h := rfl
  have hlo : (j : ℝ) * h ≤ σ - 1 / 2 := (le_div_iff₀ hpos).mp (Nat.floor_le hq)
  have hhi : σ - 1 / 2 < ((j : ℝ) + 1) * h := (div_lt_iff₀ hpos).mp (Nat.lt_floor_add_one _)
  refine (N_mono (by rw [hgi]; linarith) le_rfl).trans ((hT i).trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le h1 ?_)))
  rw [hgi]
  have : δ * (1 / 5) ≤ δ * (1 - σ) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
  nlinarith

/-- Eventual uniform bound for every `δ > 0`. -/
lemma part_i {CH : ℝ}
    (hCH : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T in atTop, ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (Cst CH * T ^ ((30 / 13 + δ) * (1 - σ)) * Real.log T ^ (44 : ℝ)) := by
  filter_upwards [low_part hδ, eventually_ge_atTop 2] with T hT h2 σ hσ
  rcases le_or_gt σ (4 / 5) with hs | hs
  · refine (hT σ hσ.1 hs).trans (ENNReal.ofReal_le_ofReal ?_)
    have := Cst_L (CH := CH) h2
    have h0 : 0 ≤ T ^ ((30 / 13 + δ) * (1 - σ)) := by positivity
    rw [mul_comm (Cst CH), mul_assoc]
    nlinarith
  · exact hux_part hCH h2 hs.le hσ.2 hδ.le

/-- Bounded range of `T`. -/
lemma part_ii {CH : ℝ}
    (hCH : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44))
    (U : ℝ) : ∃ B : ℝ, ∀ T : ℝ, 2 ≤ T → T ≤ U → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (Cst CH * T ^ ((30 / 13 + B) * (1 - σ)) * Real.log T ^ (44 : ℝ)) := by
  obtain ⟨T', hT', hUT'⟩ :=
    ((pt (s := 1 / 2) le_rfl (by norm_num) one_pos).and (eventually_ge_atTop U)).exists
  obtain ⟨M, hT'⟩ : ∃ M : ℝ, (LindelofHypothesis.zeroDensityCount (1 / 2) T' : ℝ≥0∞) ≤
      ENNReal.ofReal M := ⟨_, hT'⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨5 * |M| / Real.log 2, fun T h2 hTU σ hσ => ?_⟩
  have hB : 0 ≤ 5 * |M| / Real.log 2 := by positivity
  rcases le_or_gt σ (4 / 5) with hs | hs
  · refine (N_mono hσ.1 (hTU.trans hUT')).trans (hT'.trans (ENNReal.ofReal_le_ofReal ?_))
    set x := (30 / 13 + 5 * |M| / Real.log 2) * (1 - σ)
    have hx : 5 * |M| / Real.log 2 / 5 ≤ x := by
      have : 5 * |M| / Real.log 2 * (1 / 5) ≤ 5 * |M| / Real.log 2 * (1 - σ) :=
        mul_le_mul_of_nonneg_left (by linarith) hB
      have : 0 ≤ 30 / 13 * (1 - σ) := by linarith
      simp only [x]; nlinarith
    have hx0 : 0 ≤ x := le_trans (by positivity) hx
    have hle : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) h2
    have hTx : M ≤ T ^ x := by
      rw [Real.rpow_def_of_pos (by linarith)]
      have e1 := Real.add_one_le_exp (Real.log T * x)
      have e2 : Real.log 2 * x ≤ Real.log T * x := mul_le_mul_of_nonneg_right hle hx0
      have e3 : |M| ≤ Real.log 2 * x := by
        have : Real.log 2 * (5 * |M| / Real.log 2 / 5) = |M| := by field_simp
        rw [← this]; exact mul_le_mul_of_nonneg_left hx hl2.le
      linarith [le_abs_self M]
    have := Cst_L (CH := CH) h2
    have h0 : 0 ≤ T ^ x := by positivity
    rw [mul_comm (Cst CH), mul_assoc]
    nlinarith
  · exact hux_part hCH h2 hs.le hσ.2 hB

/-- Abstract diagonal construction of the error function `e`. -/
lemma exists_e (P : ℝ → ℝ → Prop) (h1 : ∀ k : ℕ, ∃ U : ℝ, ∀ T ≥ U, P (1 / ((k : ℝ) + 1)) T)
    (h2 : ∀ U : ℝ, ∃ B : ℝ, ∀ T, 2 ≤ T → T ≤ U → P B T) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ T, 2 ≤ T → P (e T) T := by
  classical
  choose U hU using h1
  let V : ℕ → ℝ := fun k => (k : ℝ) + ∑ j ∈ Finset.range (k + 1), |U j|
  have hUV : ∀ k, U k ≤ V k := fun k => by
    have : |U k| ≤ ∑ j ∈ Finset.range (k + 1), |U j| :=
      Finset.single_le_sum (f := fun j => |U j|) (fun j _ => abs_nonneg _)
        (Finset.self_mem_range_succ k)
    have := le_abs_self (U k)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    simp only [V]; linarith
  have hkV : ∀ k : ℕ, (k : ℝ) ≤ V k := fun k => by
    have : 0 ≤ ∑ j ∈ Finset.range (k + 1), |U j| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    simp only [V]; linarith
  obtain ⟨B, hB⟩ := h2 (V 1)
  let kf : ℝ → ℕ := fun T => Nat.findGreatest (fun k => V k ≤ T) ⌊T⌋₊
  let e : ℝ → ℝ := fun T => if kf T = 0 then B else 1 / ((kf T : ℝ) + 1)
  have key : ∀ n : ℕ, ∀ T, V n ≤ T → n ≤ kf T := fun n T hT =>
    Nat.le_findGreatest (Nat.le_floor ((hkV n).trans hT)) hT
  refine ⟨e, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨V (n + 1), fun T hT => ?_⟩
    have hk := key (n + 1) T hT
    have hk0 : kf T ≠ 0 := by omega
    simp only [e, if_neg hk0, Real.dist_eq, sub_zero]
    rw [abs_of_pos (by positivity)]
    calc 1 / ((kf T : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast (by omega : n + 1 ≤ kf T + 1)
      _ < ε := hn
  · intro T hT
    by_cases hk0 : kf T = 0
    · simp only [e, if_pos hk0]
      apply hB T hT
      by_contra hlt
      push Not at hlt
      have := key 1 T hlt.le
      omega
    · simp only [e, if_neg hk0]
      apply hU
      have : V (kf T) ≤ T := Nat.findGreatest_of_ne_zero rfl hk0
      exact (hUV _).trans this

theorem uniform_dev :
    ∃ (C A : ℝ) (e : ℝ → ℝ), Tendsto e atTop (𝓝 0) ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ,
      σ ∈ Set.Icc (1 / 2 : ℝ) 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ A) := by
  obtain ⟨CH, hCH⟩ := GuthMaynard.huxley_density_estimate_uniform
  obtain ⟨e, he, hP⟩ := exists_e (fun δ T => ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (Cst CH * T ^ ((30 / 13 + δ) * (1 - σ)) * Real.log T ^ (44 : ℝ)))
    (fun k => eventually_atTop.mp (part_i hCH (by positivity)))
    (part_ii hCH)
  exact ⟨Cst CH, 44, e, he, hP⟩

end GuthMaynard.CitedZeros

open LindelofHypothesis in
theorem solution :
    ∃ (C A : ℝ) (e : ℝ → ℝ), Tendsto e atTop (𝓝 0) ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ A) :=
  GuthMaynard.CitedZeros.uniform_dev

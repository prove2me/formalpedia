-- Prove2me | solution 1 for KingmanSubadditive.PositiveMatrices.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:59:02.568195+00:00
-- url     : https://prove2.me/submissions/873c5709-74ef-4ccf-8b68-4b05f9c25a1f

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
import Theorems.Thm_KingmanSubadditive_PositiveMatrices_limit_11
import Theorems.Thm_KingmanSubadditive_PositiveMatrices_liminf_ge
import Theorems.Thm_KingmanSubadditive_PositiveMatrices_limsup_le
open MeasureTheory Filter Topology

namespace FKAux
open KingmanSubadditive.PositiveMatrices

/-- `s(A) = log k + Σ_{a,b} |log A_ab|`. -/
noncomputable def hfun (k : ℕ) (A : Fin k → Fin k → ℝ) : ℝ :=
  Real.log k + ∑ a, ∑ b, |Real.log (A a b)|

lemma measurable_hfun (k : ℕ) : Measurable (hfun k) := by
  unfold hfun
  refine measurable_const.add ?_
  refine Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun b _ => ?_))
  exact (Real.measurable_log.comp ((measurable_pi_apply b).comp (measurable_pi_apply a))).abs

lemma abs_log_le_sum {k : ℕ} (A : Fin k → Fin k → ℝ) (a b : Fin k) :
    |Real.log (A a b)| ≤ ∑ a, ∑ b, |Real.log (A a b)| := by
  calc |Real.log (A a b)| ≤ ∑ b, |Real.log (A a b)| :=
        Finset.single_le_sum (f := fun b => |Real.log (A a b)|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ b)
    _ ≤ ∑ a, ∑ b, |Real.log (A a b)| :=
        Finset.single_le_sum (f := fun a => ∑ b, |Real.log (A a b)|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ a)

lemma X_succ {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (n : ℕ) (ω : Ω) :
    X Y (n + 1) ω = X Y n ω * Y (n + 1) ω := by
  unfold X blockProd
  simp only [Nat.sub_zero, zero_add]
  rw [List.range'_concat, List.map_append, List.prod_append]
  simp [add_comm]

lemma X_one {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (ω : Ω) :
    X Y 1 ω = Y 1 ω := by
  unfold X blockProd
  simp

/-- Two-sided bounds on the entries of `X_{n+1}`. -/
lemma bounds {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (ω : Ω)
    (hpos : ∀ r, 1 ≤ r → ∀ i j, 0 < Y r ω i j) (n : ℕ) :
    ∀ i j, 0 < X Y (n + 1) ω i j ∧
      -(∑ r ∈ Finset.range (n + 1), ∑ a, ∑ b, |Real.log (Y (r + 1) ω a b)|)
        ≤ Real.log (X Y (n + 1) ω i j) ∧
      Real.log (X Y (n + 1) ω i j) ≤ (n + 1 : ℝ) * Real.log k +
        ∑ r ∈ Finset.range (n + 1), ∑ a, ∑ b, |Real.log (Y (r + 1) ω a b)| := by
  have hk : (0 : ℝ) ≤ Real.log k := Real.log_nonneg (by
    have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
    exact_mod_cast this)
  induction n with
  | zero =>
    intro i j
    rw [X_one]
    have hp := hpos 1 le_rfl i j
    have h1 := abs_log_le_sum (fun a b => Y 1 ω a b) i j
    simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.cast_zero, one_mul]
    refine ⟨hp, ?_, ?_⟩
    · have := neg_abs_le (Real.log (Y 1 ω i j)); linarith
    · have := le_abs_self (Real.log (Y 1 ω i j)); linarith
  | succ n ih =>
    intro i j
    set S := ∑ r ∈ Finset.range (n + 1), ∑ a, ∑ b, |Real.log (Y (r + 1) ω a b)| with hS
    set sB := ∑ a, ∑ b, |Real.log (Y (n + 2) ω a b)| with hsB
    have hsum : ∑ r ∈ Finset.range (n + 1 + 1), ∑ a, ∑ b, |Real.log (Y (r + 1) ω a b)| = S + sB :=
      Finset.sum_range_succ _ _
    rw [hsum, X_succ, Matrix.mul_apply]
    have hBpos : ∀ a b, 0 < Y (n + 1 + 1) ω a b := fun a b => hpos _ (by omega) a b
    have hterm : ∀ l, 0 < X Y (n + 1) ω i l * Y (n + 1 + 1) ω l j :=
      fun l => mul_pos (ih i l).1 (hBpos l j)
    have hsumpos : 0 < ∑ l, X Y (n + 1) ω i l * Y (n + 1 + 1) ω l j :=
      Finset.sum_pos (fun l _ => hterm l) Finset.univ_nonempty
    refine ⟨hsumpos, ?_, ?_⟩
    · -- lower bound via the single term l = 0
      have hsingle : X Y (n + 1) ω i 0 * Y (n + 1 + 1) ω 0 j ≤
          ∑ l, X Y (n + 1) ω i l * Y (n + 1 + 1) ω l j :=
        Finset.single_le_sum (f := fun l => X Y (n + 1) ω i l * Y (n + 1 + 1) ω l j)
          (fun l _ => (hterm l).le) (Finset.mem_univ 0)
      have hlog := Real.log_le_log (hterm 0) hsingle
      rw [Real.log_mul (ih i 0).1.ne' (hBpos 0 j).ne'] at hlog
      have h1 := (ih i 0).2.1
      have h2 := abs_log_le_sum (fun a b => Y (n + 2) ω a b) 0 j
      have h3 := neg_abs_le (Real.log (Y (n + 1 + 1) ω 0 j))
      try simp only at h2
      linarith
    · -- upper bound: every term ≤ exp(U) exp(sB)
      set U := (n + 1 : ℝ) * Real.log k + S
      have hle : ∀ l, X Y (n + 1) ω i l * Y (n + 1 + 1) ω l j ≤ Real.exp U * Real.exp sB := by
        intro l
        have hA : X Y (n + 1) ω i l ≤ Real.exp U := by
          rw [← Real.exp_log (ih i l).1]
          exact Real.exp_le_exp.mpr (ih i l).2.2
        have hB : Y (n + 1 + 1) ω l j ≤ Real.exp sB := by
          rw [← Real.exp_log (hBpos l j)]
          refine Real.exp_le_exp.mpr ?_
          have h2 := abs_log_le_sum (fun a b => Y (n + 2) ω a b) l j
          have h3 := le_abs_self (Real.log (Y (n + 1 + 1) ω l j))
          try simp only at h2
          linarith
        exact mul_le_mul hA hB (hBpos l j).le (Real.exp_pos _).le
      have htot : ∑ l, X Y (n + 1) ω i l * Y (n + 1 + 1) ω l j ≤
          (k : ℝ) * (Real.exp U * Real.exp sB) := by
        calc ∑ l, X Y (n + 1) ω i l * Y (n + 1 + 1) ω l j
            ≤ ∑ _l : Fin k, Real.exp U * Real.exp sB := Finset.sum_le_sum (fun l _ => hle l)
          _ = (k : ℝ) * (Real.exp U * Real.exp sB) := by simp
      have hkpos : (0 : ℝ) < k := by
        have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
        exact_mod_cast this
      have hlog := Real.log_le_log hsumpos htot
      rw [Real.log_mul hkpos.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_exp, Real.log_exp] at hlog
      push_cast
      linarith

lemma measurable_X {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (hm : ∀ n : ℕ, 1 ≤ n → Measurable (fun ω (i j : Fin k) => Y n ω i j)) (n : ℕ) :
    ∀ i j, Measurable (fun ω => X Y (n + 1) ω i j) := by
  have hY : ∀ r, 1 ≤ r → ∀ i j, Measurable (fun ω => Y r ω i j) := fun r hr i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hm r hr))
  induction n with
  | zero =>
    intro i j
    have he : (fun ω => X Y (0 + 1) ω i j) = fun ω => Y 1 ω i j := by
      funext ω; exact congrFun (congrFun (X_one Y ω) i) j
    rw [he]; exact hY 1 le_rfl i j
  | succ n ih =>
    intro i j
    have he : (fun ω => X Y (n + 1 + 1) ω i j) =
        fun ω => ∑ l, X Y (n + 1) ω i l * Y (n + 1 + 1) ω l j := by
      funext ω; rw [X_succ, Matrix.mul_apply]
    rw [he]
    exact Finset.measurable_sum _ (fun l _ => (ih i l).mul (hY _ (by omega) l j))

lemma identDistrib_Y {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) (r : ℕ) :
    ProbabilityTheory.IdentDistrib (fun ω (i j : Fin k) => Y (r + 1) ω i j)
      (fun ω (i j : Fin k) => Y 1 ω i j) P P := by
  obtain ⟨hm, -, -, hst⟩ := hY
  have hS : ProbabilityTheory.IdentDistrib (fun ω (n : ℕ) (i j : Fin k) => Y (n + 2) ω i j)
      (fun ω (n : ℕ) (i j : Fin k) => Y (n + 1) ω i j) P P :=
    { aemeasurable_fst := (measurable_pi_lambda _ (fun n => hm (n + 2) (by omega))).aemeasurable
      aemeasurable_snd := (measurable_pi_lambda _ (fun n => hm (n + 1) (by omega))).aemeasurable
      map_eq := hst }
  induction r with
  | zero => exact ProbabilityTheory.IdentDistrib.refl (hm 1 le_rfl).aemeasurable
  | succ r ih =>
    have := hS.comp (measurable_pi_apply r)
    exact this.trans ih

end FKAux

open KingmanSubadditive.PositiveMatrices FKAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    ∃ lam : Ω → ℝ, Integrable lam P ∧ ∀ i j : Fin k,
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.log (X Y n ω i j) / n) atTop (𝓝 (lam ω))) ∧
      Tendsto (fun n : ℕ => ∫ ω, |Real.log (X Y n ω i j) / n - lam ω| ∂P) atTop (𝓝 0) := by
  obtain ⟨lam, hli, hae, -⟩ := limit_11 P Y hY
  refine ⟨lam, hli, fun i j => ?_⟩
  have hlo := liminf_ge P Y hY lam hae i j
  have hhi := limsup_le P Y hY lam hae i j
  -- almost-sure convergence from the liminf / limsup bounds
  have hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => Real.log (X Y n ω i j) / n) atTop (𝓝 (lam ω)) := by
    filter_upwards [hlo, hhi] with ω h1 h2
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · filter_upwards [h1 ((lam ω - a) / 2) (by linarith)] with n hn
      linarith
    · filter_upwards [h2 ((b - lam ω) / 2) (by linarith)] with n hn
      linarith
  refine ⟨hconv, ?_⟩
  -- convergence in mean via uniform integrability
  set f : ℕ → Ω → ℝ := fun n ω => Real.log (X Y n ω i j) / n with hf
  set H : ℕ → Ω → ℝ := fun r ω => hfun k (fun a b => Y (r + 1) ω a b) with hH
  have hXmeas : ∀ n a b, Measurable (fun ω => X Y n ω a b) := by
    intro n a b
    cases n with
    | zero =>
      have he : (fun ω => X Y 0 ω a b) = fun _ => (1 : Matrix (Fin k) (Fin k) ℝ) a b := by
        funext ω; simp [X, blockProd]
      rw [he]; exact measurable_const
    | succ n => exact measurable_X Y hY.1 n a b
  have hfmeas : ∀ n, AEStronglyMeasurable (f n) P := fun n =>
    ((Real.measurable_log.comp (hXmeas n i j)).div_const _).aestronglyMeasurable
  have hHid : ∀ r, ProbabilityTheory.IdentDistrib (H r) (H 0) P P := fun r =>
    ((identDistrib_Y P Y hY r).comp (measurable_hfun k)).trans
      ((identDistrib_Y P Y hY 0).comp (measurable_hfun k)).symm
  have hH0 : MemLp (H 0) 1 P := by
    rw [memLp_one_iff_integrable]
    simp only [hH, hfun]
    exact (integrable_const _).add (integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun b _ => (hY.2.2.1 1 le_rfl a b).abs)
  have hHUI : UniformIntegrable H 1 P :=
    ProbabilityTheory.MemLp.uniformIntegrable_of_identDistrib le_rfl ENNReal.one_ne_top hH0 hHid
  have hGUI := (uniformIntegrable_average le_rfl hHUI).2.1
  have hk : (0 : ℝ) ≤ Real.log k := Real.log_nonneg (by
    have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
    exact_mod_cast this)
  -- domination |f n| ≤ n⁻¹ Σ_{r<n} H r
  have hdom : ∀ n ω, |f n ω| ≤ (n : ℝ)⁻¹ * ∑ r ∈ Finset.range n, H r ω := by
    intro n ω
    cases n with
    | zero => simp [hf]
    | succ m =>
      have hb := bounds Y ω (fun r hr => hY.2.1 r hr ω) m i j
      have hsum : ∑ r ∈ Finset.range (m + 1), H r ω = (m + 1 : ℝ) * Real.log k +
          ∑ r ∈ Finset.range (m + 1), ∑ a, ∑ b, |Real.log (Y (r + 1) ω a b)| := by
        simp only [hH, hfun, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        push_cast; ring
      have habs : |Real.log (X Y (m + 1) ω i j)| ≤ ∑ r ∈ Finset.range (m + 1), H r ω := by
        rw [hsum, abs_le]
        constructor
        · have : 0 ≤ (m + 1 : ℝ) * Real.log k := by positivity
          linarith [hb.2.1]
        · exact hb.2.2
      have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      simp only [hf]
      rw [abs_div, abs_of_pos hpos, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr hpos.le)
  have hfUI : UnifIntegrable f 1 P := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hGUI hε
    refine ⟨δ, hδ, fun n s hs hle => le_trans (eLpNorm_mono (fun ω => ?_)) (hδ' n s hs hle)⟩
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Real.norm_eq_abs]
      exact (hdom n ω).trans (le_abs_self _)
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  have hL := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hfmeas
    (memLp_one_iff_integrable.mpr hli) hfUI hconv
  have hL' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL
  rw [ENNReal.toReal_zero] at hL'
  refine hL'.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
    ((hfmeas n).sub hli.aestronglyMeasurable)]
  simp [Real.norm_eq_abs, hf]

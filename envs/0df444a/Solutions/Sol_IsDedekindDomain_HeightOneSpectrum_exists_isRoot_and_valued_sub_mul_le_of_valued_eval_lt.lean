-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/31eef776-f1ce-5b73-9063-7e831cac78a0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
set_option autoImplicit false
p2m_open "NumberField IsDedekindDomain P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt.IsDedekindDomain Topology"

set_option linter.unusedSectionVars false

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "adicCompletion under adicCompletionIntegers"
namespace HenselStrong
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

theorem norm_le_iff' (x y : (v.adicCompletion K)) : ‖x‖ ≤ ‖y‖ ↔ Valued.v x ≤ Valued.v y := Valued.toNormedField.norm_le_iff
theorem norm_lt_iff' (x y : (v.adicCompletion K)) : ‖x‖ < ‖y‖ ↔ Valued.v x < Valued.v y := Valued.toNormedField.norm_lt_iff

theorem norm_coe_le_one (x : (v.adicCompletionIntegers K)) : ‖(x : (v.adicCompletion K))‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr x.2

theorem mem_integers_of_norm_le_one {x : (v.adicCompletion K)} (hx : ‖x‖ ≤ 1) : x ∈ v.adicCompletionIntegers K :=
  Valued.toNormedField.norm_le_one_iff.mp hx

theorem coe_eval (f : Polynomial (v.adicCompletionIntegers K)) (x : (v.adicCompletionIntegers K)) :
    ((f.eval x : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) = (f.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).eval (x : (v.adicCompletion K)) := by
  show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (f.eval x) =
    (f.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).eval (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x)
  rw [Polynomial.eval_map, Polynomial.eval₂_hom]

theorem norm_coe_sub_eval_le (g : Polynomial (v.adicCompletionIntegers K)) (x y : (v.adicCompletionIntegers K)) :
    ‖((g.eval x : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - ((g.eval y : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ ‖(x : (v.adicCompletion K)) - (y : (v.adicCompletion K))‖ := by
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub x y g
  have : ((g.eval x : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - ((g.eval y : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) = ((x : (v.adicCompletion K)) - (y : (v.adicCompletion K))) * (c : (v.adicCompletion K)) := by
    have := congrArg (fun z : (v.adicCompletionIntegers K) => (z : (v.adicCompletion K))) hc
    simpa using this
  rw [this, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_coe_le_one c)

section newton
variable (f : Polynomial (v.adicCompletionIntegers K)) (a₀ : (v.adicCompletionIntegers K))

open Classical in

noncomputable def step (b : (v.adicCompletionIntegers K)) : (v.adicCompletionIntegers K) :=
  if h : ((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) ≠ 0 ∧ ‖((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ ‖((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ then
    b - ⟨((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) / ((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)), mem_integers_of_norm_le_one (by
      rw [norm_div]; exact div_le_one_of_le₀ h.2 (norm_nonneg _))⟩
  else b

noncomputable def seq (k : ℕ) : (v.adicCompletionIntegers K) := (step f)^[k] a₀

theorem seq_zero : seq f a₀ 0 = a₀ := rfl
theorem seq_succ (k : ℕ) : seq f a₀ (k + 1) = step f (seq f a₀ k) := by
  rw [seq, Function.iterate_succ', Function.comp_apply]; rfl

variable {f a₀}

theorem step_spec (h0 : ‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ < ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ^ 2) (b : (v.adicCompletionIntegers K))
    (hb1 : ‖(b : (v.adicCompletion K)) - (a₀ : (v.adicCompletion K))‖ < ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖) (hb2 : ‖((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ ‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖) :
    ‖((step f b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (b : (v.adicCompletion K))‖ = ‖((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ / ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ∧
    ‖((f.eval (step f b) : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ ‖((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ^ 2 / ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ^ 2 := by
  set D : ℝ := ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ with hD
  have hD0 : 0 < D := by
    have : 0 < D ^ 2 := lt_of_le_of_lt (norm_nonneg _) h0
    nlinarith [norm_nonneg ((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))]
  have hD1 : D ≤ 1 := norm_coe_le_one _

  have hder : ‖((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ = D := by
    have hdiff := norm_coe_sub_eval_le f.derivative b a₀
    have hlt : ‖((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - ((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ < ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ :=
      lt_of_le_of_lt hdiff hb1
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hlt)
    rw [sub_add_cancel, max_eq_right (le_of_lt hlt)] at this
    exact this
  have hder0 : ((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) ≠ 0 := by
    rw [← norm_pos_iff, hder]; exact hD0
  have hle : ‖((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ ‖((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ := by
    rw [hder]
    calc ‖((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ ‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ := hb2
      _ ≤ D ^ 2 := le_of_lt h0
      _ ≤ D := by nlinarith

  set y : (v.adicCompletionIntegers K) := ⟨((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) / ((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)), mem_integers_of_norm_le_one (by
      rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _))⟩ with hy
  have hstep : step f b = b - y := by
    rw [step, dif_pos ⟨hder0, hle⟩]
  have hycoe : (y : (v.adicCompletion K)) = ((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) / ((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) := rfl
  have hynorm : ‖(y : (v.adicCompletion K))‖ = ‖((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ / D := by rw [hycoe, norm_div, hder]
  constructor
  · rw [hstep]
    show ‖((b - y : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (b : (v.adicCompletion K))‖ = _
    rw [show ((b - y : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) = (b : (v.adicCompletion K)) - (y : (v.adicCompletion K)) from rfl, sub_sub_cancel_left, norm_neg, hynorm]
  ·
    obtain ⟨k, hk⟩ := Polynomial.binomExpansion f b (-y)
    have hcancel : f.derivative.eval b * (-y) = -f.eval b := by
      apply Subtype.ext
      show ((f.derivative.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) * (-(y : (v.adicCompletion K))) = -((f.eval b : (v.adicCompletionIntegers K)) : (v.adicCompletion K))
      rw [hycoe, mul_neg, mul_div_cancel₀ _ hder0]
    rw [hcancel, add_neg_cancel, zero_add, ← sub_eq_add_neg] at hk
    rw [hstep, hk]
    show ‖((k * (-y) ^ 2 : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ _
    rw [show ((k * (-y) ^ 2 : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) = (k : (v.adicCompletion K)) * (-(y : (v.adicCompletion K))) ^ 2 from rfl, norm_mul, norm_pow, norm_neg, hynorm, div_pow]
    exact mul_le_of_le_one_left (by positivity) (norm_coe_le_one k)

theorem seq_spec (h0 : ‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ < ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ^ 2) (k : ℕ) :
    ‖((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (a₀ : (v.adicCompletion K))‖ ≤ ‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ / ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ∧
    ‖((f.eval (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤
      ‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ * (‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ / ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ^ 2) ^ k ∧
    ‖((seq f a₀ (k + 1) : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - ((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤
      (‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ / ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖) * (‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ / ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ^ 2) ^ k := by
  set D : ℝ := ‖((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ with hD
  set A : ℝ := ‖((f.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hD0 : 0 < D := by
    have : 0 < D ^ 2 := lt_of_le_of_lt (norm_nonneg _) h0
    nlinarith [norm_nonneg ((f.derivative.eval a₀ : (v.adicCompletionIntegers K)) : (v.adicCompletion K))]
  set t : ℝ := A / D ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := (div_lt_one (by positivity)).mpr h0
  have hAD : A / D < D := by
    rw [div_lt_iff₀ hD0]; nlinarith

  have main : ∀ k, ‖((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (a₀ : (v.adicCompletion K))‖ ≤ A / D ∧ ‖((f.eval (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ A * t ^ k := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [seq_zero, sub_self, norm_zero]; positivity
      · rw [seq_zero, pow_zero, mul_one]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hb1 : ‖((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (a₀ : (v.adicCompletion K))‖ < D := lt_of_le_of_lt ih1 hAD
      have hb2 : ‖((f.eval (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ A :=
        ih2.trans (mul_le_of_le_one_right hA0 (pow_le_one₀ ht0 ht1.le))
      obtain ⟨hs1, hs2⟩ := step_spec h0 (seq f a₀ k) hb1 hb2
      rw [seq_succ]
      refine ⟨?_, ?_⟩
      · have hy : ‖((step f (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - ((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ A / D := by
          rw [hs1]; exact div_le_div_of_nonneg_right hb2 hD0.le
        calc ‖((step f (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (a₀ : (v.adicCompletion K))‖
            = ‖(((step f (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - ((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K))) + (((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (a₀ : (v.adicCompletion K)))‖ := by
              rw [sub_add_sub_cancel]
          _ ≤ max ‖((step f (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - ((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ‖((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (a₀ : (v.adicCompletion K))‖ :=
              IsUltrametricDist.norm_add_le_max _ _
          _ ≤ A / D := max_le hy ih1
      · calc ‖((f.eval (step f (seq f a₀ k)) : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖
            ≤ ‖((f.eval (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ^ 2 / D ^ 2 := hs2
          _ ≤ (A * t ^ k) * (A * t ^ k) / D ^ 2 := by
              rw [sq]; exact div_le_div_of_nonneg_right (mul_le_mul ih2 ih2 (norm_nonneg _) (by positivity)) (by positivity)
          _ = A * t ^ k * (t * t ^ k) := by rw [ht]; ring
          _ ≤ A * t ^ k * (t * 1) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1.le) ht0
          _ = A * t ^ (k + 1) := by ring
  obtain ⟨m1, m2⟩ := main k
  refine ⟨m1, m2, ?_⟩
  have hb1 : ‖((seq f a₀ k : (v.adicCompletionIntegers K)) : (v.adicCompletion K)) - (a₀ : (v.adicCompletion K))‖ < D := lt_of_le_of_lt m1 hAD
  have hb2 : ‖((f.eval (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ ≤ A := m2.trans (mul_le_of_le_one_right hA0 (pow_le_one₀ ht0 ht1.le))
  obtain ⟨hs1, -⟩ := step_spec h0 (seq f a₀ k) hb1 hb2
  rw [seq_succ, hs1, div_eq_mul_inv, div_eq_mul_inv A D]
  calc ‖((f.eval (seq f a₀ k) : (v.adicCompletionIntegers K)) : (v.adicCompletion K))‖ * D⁻¹ ≤ (A * t ^ k) * D⁻¹ := mul_le_mul_of_nonneg_right m2 (by positivity)
    _ = A * D⁻¹ * t ^ k := by ring

end newton

end IsDedekindDomain.HeightOneSpectrum.HenselStrong

open IsDedekindDomain.HeightOneSpectrum.HenselStrong in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : Polynomial ↥(v.adicCompletionIntegers K)) (a₀ : ↥(v.adicCompletionIntegers K))
    (h : Valued.v ((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) <
      Valued.v ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ^ 2) :
    ∃ a : ↥(v.adicCompletionIntegers K), f.IsRoot a ∧
      Valued.v ((a : v.adicCompletion K) - (a₀ : v.adicCompletion K)) *
          Valued.v ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ≤
        Valued.v ((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) := by

  have h0 : ‖((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)‖ <
      ‖((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)‖ ^ 2 := by
    rw [← norm_pow, norm_lt_iff', map_pow]; exact h
  set D : ℝ := ‖((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)‖ with hD
  set A : ℝ := ‖((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)‖ with hA
  have hD0 : 0 < D := by
    have : 0 < D ^ 2 := lt_of_le_of_lt (norm_nonneg _) h0
    nlinarith [norm_nonneg ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)]
  have ht1 : A / D ^ 2 < 1 := (div_lt_one (by positivity)).mpr h0

  let u : ℕ → v.adicCompletion K := fun k => ((seq f a₀ k : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric (A / D ^ 2) (A / D) ht1 fun k => ?_
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    exact (seq_spec h0 k).2.2
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcau

  have ha1 : ‖a‖ ≤ 1 :=
    le_of_tendsto' (tendsto_norm.comp ha) fun k => norm_coe_le_one _
  refine ⟨⟨a, mem_integers_of_norm_le_one ha1⟩, ?_, ?_⟩
  ·
    have hcont : Filter.Tendsto (fun k => ((f.eval (seq f a₀ k) : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)) Filter.atTop
        (𝓝 ((f.map (algebraMap ↥(v.adicCompletionIntegers K) (v.adicCompletion K))).eval a)) := by
      have := ((f.map (algebraMap ↥(v.adicCompletionIntegers K) (v.adicCompletion K))).continuous.tendsto a).comp ha
      refine this.congr fun k => ?_
      show (f.map _).eval (u k) = _
      exact (coe_eval f _).symm
    have hzero : Filter.Tendsto (fun k => ((f.eval (seq f a₀ k) : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)) Filter.atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => (seq_spec h0 k).2.1) ?_
      rw [show (0 : ℝ) = A * 0 by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ht1).const_mul A
    have heq := tendsto_nhds_unique hcont hzero
    show f.eval ⟨a, _⟩ = 0
    apply Subtype.ext
    rw [coe_eval]
    exact heq
  ·
    have hbound : ‖a - (a₀ : v.adicCompletion K)‖ ≤ A / D :=
      le_of_tendsto' ((tendsto_norm.comp (ha.sub_const _))) fun k => (seq_spec h0 k).1
    have hnorm : ‖(a - (a₀ : v.adicCompletion K)) * ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)‖ ≤
        ‖((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K)‖ := by
      rw [norm_mul]
      calc ‖a - (a₀ : v.adicCompletion K)‖ * D ≤ A / D * D := mul_le_mul_of_nonneg_right hbound hD0.le
        _ = A := div_mul_cancel₀ A hD0.ne'
    have := (norm_le_iff' _ _).mp hnorm
    rwa [map_mul] at this

end S_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt (solution)

-- Prove2me | solution 1 for HighConfRobust.fact_3_3_iv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:56:46.707712+00:00
-- url     : https://prove2.me/submissions/4b9f256b-2e93-42f3-8732-71d411d5967d

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

open MeasureTheory

namespace FactIV

/-- Clause 1: change of measure for `q > 1`. -/
lemma clause1 {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (E : Set X) (hE : MeasurableSet E)
    (q D : ℝ) (hq : 1 < q) (hD : HighConfRobust.renyiDivergence q P Q ≤ (D : EReal)) :
    (P E).toReal ≤ (Q E).toReal ^ ((q - 1) / q) * Real.exp ((q - 1) / q * D) := by
  have hq1 : q ≠ 1 := ne_of_gt hq
  unfold HighConfRobust.renyiDivergence PADMPriv.renyiDiv at hD
  rw [if_neg hq1] at hD
  by_cases hac : P ≪ Q
  swap
  · rw [if_neg hac] at hD; exact absurd hD (by simp)
  rw [if_pos hac] at hD
  set I : ENNReal := ∫⁻ z, (P.rnDeriv Q z) ^ q ∂Q with hI
  -- bound on I
  have hlogI : ENNReal.log I ≤ (((q - 1) * D : ℝ) : EReal) := by
    have hc : (0 : EReal) ≤ ((q - 1 : ℝ) : EReal) := by
      exact_mod_cast (by linarith : (0:ℝ) ≤ q - 1)
    have := mul_le_mul_of_nonneg_left hD hc
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ (by linarith : (q - 1 : ℝ) ≠ 0),
      EReal.coe_one, one_mul, ← EReal.coe_mul] at this
    exact this
  have hIle : I ≤ ENNReal.ofReal (Real.exp ((q - 1) * D)) := by
    rw [← ENNReal.log_strictMono.le_iff_le, ENNReal.log_ofReal_of_pos (Real.exp_pos _),
      Real.log_exp]
    exact hlogI
  -- Hölder
  set p' : ℝ := q.conjExponent
  have hpq : q.HolderConjugate p' := Real.HolderConjugate.conjExponent hq
  have hp' : 1 / p' = (q - 1) / q := by
    simp only [p', Real.conjExponent]; field_simp
  have hp'pos : 0 < p' := hpq.symm.pos
  have hPE : P E = ∫⁻ z, ((fun z => P.rnDeriv Q z) * E.indicator (1 : X → ENNReal)) z ∂Q := by
    rw [← Measure.setLIntegral_rnDeriv' hac hE, ← lintegral_indicator hE]
    congr 1; ext z
    by_cases hz : z ∈ E <;> simp [hz, Set.indicator]
  have hind : ∫⁻ z, (E.indicator (1 : X → ENNReal) z) ^ p' ∂Q = Q E := by
    rw [← lintegral_indicator_one hE]
    congr 1; ext z
    by_cases hz : z ∈ E <;> simp [hz, Set.indicator, hp'pos]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq Q hpq
    (Measure.measurable_rnDeriv P Q).aemeasurable
    ((measurable_one.indicator hE).aemeasurable)
  rw [← hPE, hind, ← hI, hp'] at hH
  have hH2 : P E ≤ ENNReal.ofReal (Real.exp ((q - 1) * D)) ^ (1 / q) * Q E ^ ((q - 1) / q) :=
    hH.trans (by gcongr)
  have hfin : ENNReal.ofReal (Real.exp ((q - 1) * D)) ^ (1 / q) * Q E ^ ((q - 1) / q) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by
        have : 0 < q := by linarith
        exact div_nonneg (by linarith) this.le) (measure_ne_top _ _)
  have := ENNReal.toReal_mono hfin hH2
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ← Real.exp_mul] at this
  have he : (q - 1) * D * (1 / q) = (q - 1) / q * D := by ring
  rw [he, mul_comm] at this
  exact this


open InformationTheory in
/-- Restricted Gibbs inequality: `P(S) log(P(S)/Q(S)) ≤ ∫_S log(dP/dQ) dP`. -/
lemma restrict_mul_log_le {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hac : P ≪ Q) (hint : Integrable (llr P Q) P)
    (S : Set X) (hS : MeasurableSet S) :
    P.real S * Real.log (P.real S / Q.real S) ≤ ∫ x in S, llr P Q x ∂P := by
  have hres : P.restrict S = (Q.restrict S).withDensity (P.rnDeriv Q) := by
    rw [← restrict_withDensity hS, Measure.withDensity_rnDeriv_eq _ _ hac]
  have hac' : P.restrict S ≪ Q.restrict S := hac.restrict S
  have hrn : (P.restrict S).rnDeriv (Q.restrict S) =ᵐ[Q.restrict S] P.rnDeriv Q := by
    rw [hres]; exact Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  have hllr : llr (P.restrict S) (Q.restrict S) =ᵐ[P.restrict S] llr P Q := by
    filter_upwards [hac'.ae_le hrn] with x hx
    simp only [llr, hx]
  have hint' : Integrable (llr (P.restrict S) (Q.restrict S)) (P.restrict S) :=
    (hint.restrict).congr hllr.symm
  have h1 := mul_log_le_toReal_klDiv hac' hint'
  rw [toReal_klDiv hac' hint', integral_congr_ae hllr] at h1
  simp only [measureReal_restrict_apply_univ] at h1
  linarith

lemma binary_ineq (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    p * Real.log (1 / q) ≤
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) + Real.log 2 := by
  have e1 : p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; simp
    · rw [Real.log_div h.ne' hq0.ne']; ring
  have e2 : (1 - p) * Real.log ((1 - p) / (1 - q)) =
      (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q) := by
    rcases eq_or_lt_of_le (sub_nonneg.mpr hp1) with h | h
    · rw [← h]; simp
    · rw [Real.log_div h.ne' (by linarith)]; ring
  have hb := Real.binEntropy_le_log_two (p := p)
  unfold Real.binEntropy at hb
  rw [Real.log_inv, Real.log_inv] at hb
  have hlq : Real.log (1 - q) < 0 := Real.log_neg (by linarith) (by linarith)
  have : 0 ≤ -((1 - p) * Real.log (1 - q)) := by
    have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp1) hlq.le
    linarith
  rw [one_div, Real.log_inv, e1, e2]
  nlinarith

end FactIV

open InformationTheory in
theorem solution {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (E : Set X) (hE : MeasurableSet E) :
    (∀ q D : ℝ, 1 < q → HighConfRobust.renyiDivergence q P Q ≤ (D : EReal) →
        (P E).toReal ≤ (Q E).toReal ^ ((q - 1) / q) * Real.exp ((q - 1) / q * D)) ∧
    (∀ D : ℝ, HighConfRobust.renyiDivergence 1 P Q ≤ (D : EReal) → 0 < Q E → Q E < 1 →
        (P E).toReal ≤ (D + Real.log 2) / Real.log (1 / (Q E).toReal)) ∧
    (HighConfRobust.renyiDivergence 1 P Q ≠ ⊤ → (Q E = 0 ∨ Q E = 1) → P E = Q E) := by
  have hR1 : HighConfRobust.renyiDivergence 1 P Q = ((klDiv P Q : ENNReal) : EReal) := by
    unfold HighConfRobust.renyiDivergence; rw [if_pos rfl]
  refine ⟨fun q D hq hD => FactIV.clause1 P Q E hE q D hq hD, ?_, ?_⟩
  · intro D hD hQ0 hQ1
    rw [hR1] at hD
    have hne : klDiv P Q ≠ ⊤ := by
      intro h; rw [h] at hD; simp at hD
    obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hne
    have hKD : (klDiv P Q).toReal ≤ D := by
      rw [← EReal.coe_ennreal_toReal hne] at hD; exact_mod_cast hD
    have hKL : (klDiv P Q).toReal = ∫ x, llr P Q x ∂P := by
      rw [toReal_klDiv hac hint]; simp
    have hsplit := integral_add_compl hE hint
    have h1 := FactIV.restrict_mul_log_le P Q hac hint E hE
    have h2 := FactIV.restrict_mul_log_le P Q hac hint Eᶜ hE.compl
    rw [measureReal_compl hE, measureReal_compl hE] at h2
    simp only [probReal_univ] at h2
    set p := P.real E
    set q := Q.real E
    have hq0 : 0 < q := ENNReal.toReal_pos hQ0.ne' (measure_ne_top _ _)
    have hq1 : q < 1 := by
      have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hQ1
      simp only [ENNReal.toReal_one] at this
      exact this
    have hp0 : 0 ≤ p := measureReal_nonneg
    have hp1 : p ≤ 1 := measureReal_le_one
    have hb := FactIV.binary_ineq p q hp0 hp1 hq0 hq1
    have hlog : 0 < Real.log (1 / q) := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hq0, hq1⟩)
    change p ≤ (D + Real.log 2) / Real.log (1 / q)
    rw [le_div_iff₀ hlog]
    nlinarith
  · intro hne hQ
    rw [hR1] at hne
    have hne' : klDiv P Q ≠ ⊤ := by
      intro h; rw [h] at hne; exact hne rfl
    have hac := (klDiv_ne_top_iff.mp hne').1
    rcases hQ with h | h
    · rw [h]; exact hac h
    · rw [h]
      have : Q Eᶜ = 0 := by rw [prob_compl_eq_zero_iff hE]; exact h
      exact (prob_compl_eq_zero_iff hE).mp (hac this)

-- Prove2me | solution 1 for InfoRegimes.MarketEq.footnote_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:12:09.765026+00:00
-- url     : https://prove2.me/submissions/d3f3dc3e-e38b-4691-b20c-c0cbbeb3accd

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

open Filter Topology

namespace Aux_IR_F15

open InfoRegimes.MarketEq

lemma trans_nonneg (P : Params) (lam : State P → ℝ) (i j : State P) : 0 ≤ trans P lam i j :=
  ENNReal.toReal_nonneg

lemma trans_sum (P : Params) (lam : State P → ℝ) (i : State P) :
    ∑ j, trans P lam i j = 1 := by
  set c := P.af + P.bf * lam i + P.kf * (grid P i - P.af) with hc
  let A : State P → Set ℝ := fun j => {e : ℝ | projD P (c + e) = j}
  have hnat : Measurable (fun e : ℝ => min P.m ⌈(P.m : ℝ) * max 0 (min 1 (c + e))⌉₊) :=
    measurable_const.min ((measurable_const.mul (measurable_const.max
      (measurable_const.min (measurable_const.add measurable_id)))).nat_ceil)
  have hmeas : ∀ j, MeasurableSet (A j) := by
    intro j
    have : A j = (fun e : ℝ => min P.m ⌈(P.m : ℝ) * max 0 (min 1 (c + e))⌉₊) ⁻¹' {(j : ℕ)} := by
      ext e
      simp only [A, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, projD, Fin.ext_iff]
    rw [this]
    exact hnat (measurableSet_singleton _)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (State P))) A := by
    intro j _ k _ hjk
    rw [Function.onFun, Set.disjoint_left]
    intro e hej hek
    exact hjk (hej.symm.trans hek)
  have hunion : (⋃ j ∈ (Finset.univ : Finset (State P)), A j) = Set.univ := by
    ext e
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_univ, iff_true]
    exact ⟨projD P (c + e), rfl⟩
  have h1 := MeasureTheory.measure_biUnion_finset (μ := (P.shock : MeasureTheory.Measure ℝ))
    hdisj (fun j _ => hmeas j)
  rw [hunion, MeasureTheory.measure_univ] at h1
  unfold InfoRegimes.MarketEq.trans
  rw [← ENNReal.toReal_sum (fun j _ => MeasureTheory.measure_ne_top _ _)]
  have : (∑ j, (P.shock : MeasureTheory.Measure ℝ) {e : ℝ | projD P
      (P.af + P.bf * lam i + P.kf * (grid P i - P.af) + e) = j}) = 1 := by
    rw [h1]
  rw [this, ENNReal.toReal_one]

end Aux_IR_F15

open InfoRegimes.MarketEq Aux_IR_F15 in
theorem solution (P : Params) (hS : P.Standing) :
    (∀ (lam VB : State P → ℝ) (i : State P), grid P i = 0 → lam i = 0 → trans P lam i i = 1 →
        Tmap P lam VB i
          = (P.gam * ((1 + dConst P) ^ 2 * P.sigM ^ 2 + VB i) / P.R) ^ 2 * P.sigX ^ 2) ∧
      (∀ V : ℝ, V = (P.gam * ((1 + dConst P) ^ 2 * P.sigM ^ 2 + V) / P.R) ^ 2 * P.sigX ^ 2 ↔
        V ^ 2 + (2 * (1 + dConst P) ^ 2 * P.sigM ^ 2 - P.R ^ 2 / (P.gam ^ 2 * P.sigX ^ 2)) * V
          + (1 + dConst P) ^ 4 * P.sigM ^ 4 = 0) ∧
      ((1 + dConst P) * P.gam * P.sigM * P.sigX ≤ 7 / 25 →
        ∃ V₁ V₂ : ℝ, 0 < V₁ ∧ V₁ < V₂ ∧ ∀ V : ℝ,
          (V ^ 2 + (2 * (1 + dConst P) ^ 2 * P.sigM ^ 2 - P.R ^ 2 / (P.gam ^ 2 * P.sigX ^ 2)) * V
            + (1 + dConst P) ^ 4 * P.sigM ^ 4 = 0 ↔ V = V₁ ∨ V = V₂)) := by
  obtain ⟨hR, hρ1, hρ2, hσM, hσX, hγ, hφ0, hφ1, hX, hm⟩ := hS
  have hR0 : 0 < P.R := by linarith
  have hd : 1 + dConst P = P.R / (P.R - P.rho) := by
    unfold dConst
    have : P.R - P.rho ≠ 0 := by linarith
    field_simp
    ring
  have hdpos : 0 < 1 + dConst P := by rw [hd]; exact div_pos hR0 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro lam VB i hg hl htr
    have hEf : Ef P lam i VB = VB i := by
      have hsum := trans_sum P lam i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), htr] at hsum
      have hrest : ∑ j ∈ Finset.univ.erase i, trans P lam i j = 0 := by linarith
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => trans_nonneg P lam i j)).mp hrest
      unfold Ef
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), htr, one_mul]
      have : ∑ j ∈ Finset.univ.erase i, trans P lam i j * VB j = 0 :=
        Finset.sum_eq_zero (fun j hj => by rw [hz j hj, zero_mul])
      rw [this, add_zero]
    unfold Tmap cRec
    rw [if_neg (by rw [hl]; exact lt_irrefl 0)]
    unfold qUD0 qID0
    rw [hg, hEf]
    ring
  · intro V
    set A := (1 + dConst P) ^ 2 * P.sigM ^ 2 with hA
    set F := P.gam ^ 2 * P.sigX ^ 2 * (A + V) ^ 2 - P.R ^ 2 * V with hF
    have hk : 0 < P.gam ^ 2 * P.sigX ^ 2 := by positivity
    have key1 : (P.gam * (A + V) / P.R) ^ 2 * P.sigX ^ 2 - V = F / P.R ^ 2 := by
      rw [hF]; field_simp
    have key2 : V ^ 2 + (2 * (1 + dConst P) ^ 2 * P.sigM ^ 2 - P.R ^ 2 / (P.gam ^ 2 * P.sigX ^ 2)) * V
        + (1 + dConst P) ^ 4 * P.sigM ^ 4 = F / (P.gam ^ 2 * P.sigX ^ 2) := by
      rw [hF, hA]; field_simp; ring
    rw [key2]
    constructor
    · intro h
      have : (P.gam * (A + V) / P.R) ^ 2 * P.sigX ^ 2 - V = 0 := by rw [← h]; ring
      rw [key1, div_eq_zero_iff] at this
      rcases this with h1 | h1
      · rw [h1, zero_div]
      · exfalso; have : P.R ^ 2 ≠ 0 := by positivity
        exact this h1
    · intro h
      rw [div_eq_zero_iff] at h
      rcases h with h1 | h1
      · have : (P.gam * (A + V) / P.R) ^ 2 * P.sigX ^ 2 - V = 0 := by rw [key1, h1, zero_div]
        linarith
      · exfalso; exact hk.ne' h1
  · intro hsmall
    set A := (1 + dConst P) ^ 2 * P.sigM ^ 2 with hA
    have hApos : 0 < A := by positivity
    set u := P.R ^ 2 / (P.gam ^ 2 * P.sigX ^ 2) with hu
    have hk : 0 < P.gam ^ 2 * P.sigX ^ 2 := by positivity
    have hu4 : 4 * A < u := by
      rw [hu, lt_div_iff₀ hk, hA]
      have h1 : (1 + dConst P) * P.gam * P.sigM * P.sigX < P.R / 2 := by linarith
      have h0 : 0 < (1 + dConst P) * P.gam * P.sigM * P.sigX := by positivity
      nlinarith
    set b := 2 * A - u with hb
    set D := u * (u - 4 * A) with hD
    have hDpos : 0 < D := mul_pos (by linarith) (by linarith)
    set sq := Real.sqrt D with hsq
    have hsqpos : 0 < sq := Real.sqrt_pos.mpr hDpos
    have hss : sq * sq = D := Real.mul_self_sqrt hDpos.le
    have hdisc : discrim 1 b (A ^ 2) = sq * sq := by
      rw [discrim, hss, hD, hb]; ring
    refine ⟨(-b - sq) / 2, (-b + sq) / 2, ?_, by linarith, ?_⟩
    · have hnb : 0 < -b := by rw [hb]; linarith
      have : sq < -b := by
        rw [hsq, Real.sqrt_lt' hnb]
        rw [hD, hb]; nlinarith
      linarith
    · intro V
      have e1 : 2 * (1 + dConst P) ^ 2 * P.sigM ^ 2 - P.R ^ 2 / (P.gam ^ 2 * P.sigX ^ 2) = b := by
        rw [hb, hA, hu]; ring
      have e2 : (1 + dConst P) ^ 4 * P.sigM ^ 4 = A ^ 2 := by rw [hA]; ring
      rw [e1, e2]
      have hq := quadratic_eq_zero_iff (one_ne_zero) hdisc V
      have e3 : V ^ 2 + b * V + A ^ 2 = 1 * (V * V) + b * V + A ^ 2 := by ring
      rw [e3, hq]
      simp only [mul_one]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h

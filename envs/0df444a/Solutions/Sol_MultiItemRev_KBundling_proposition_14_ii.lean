-- Prove2me | solution 1 for MultiItemRev.KBundling.proposition_14_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:31:42.194073+00:00
-- url     : https://prove2.me/submissions/a565df76-60fc-4b60-9d4f-9520b010f472

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Theorems.Thm_MultiItemRev_KBundling_myerson_one_good

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace KBP14Aux
open MultiItemRev.Decomp

/-- Posted price `p` for one good: `p · P[X ≥ p] ≤ Rev(X)`. -/
lemma price_le_rev1 (ν : Measure ℝ≥0) (t : ℝ≥0) :
    (t : ℝ≥0∞) * ν {x | t ≤ x} ≤ Rev1 ν := by
  let M : Mechanism Unit :=
    ⟨fun x _ => if t ≤ x () then 1 else 0, fun x => if t ≤ x () then (t : ℝ) else 0⟩
  have hSm : MeasurableSet {x : Unit → ℝ≥0 | t ≤ x ()} :=
    measurableSet_le measurable_const (measurable_pi_apply ())
  have hadm : IsAdmissible M := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x i
      simp only [M]
      split_ifs <;> norm_num
    · intro x x'
      simp only [buyerPayoff, M, Finset.univ_unique, Finset.sum_singleton]
      split_ifs with h1 h2 h2
      · linarith
      · have := NNReal.coe_lt_coe.mpr (not_le.mp h2); linarith
      · have := NNReal.coe_le_coe.mpr h2; linarith
      · linarith
    · intro x
      simp only [buyerPayoff, M, Finset.univ_unique, Finset.sum_singleton]
      split_ifs with h1
      · have := NNReal.coe_le_coe.mpr h1; linarith
      · linarith
    · exact Measurable.ite hSm measurable_const measurable_const
  have hc : Measurable (fun (t : ℝ≥0) (_ : Unit) => t) := by fun_prop
  have hrev : expRevenue (oneGood ν) M = (((t : ℝ≥0∞) * ν {x | t ≤ x} : ℝ≥0∞) : EReal) := by
    unfold expRevenue oneGood
    have hMs : Measurable M.s := hadm.2.2.2
    rw [lintegral_map (f := fun x => ENNReal.ofReal (M.s x))
        (ENNReal.measurable_ofReal.comp hMs) hc,
      lintegral_map (f := fun x => ENNReal.ofReal (-M.s x))
        (ENNReal.measurable_ofReal.comp hMs.neg) hc]
    have h1 : (fun a : ℝ≥0 => ENNReal.ofReal (M.s fun _ => a)) =
        (Set.Ici t).indicator (fun _ => (t : ℝ≥0∞)) := by
      funext a
      simp only [M, Set.indicator, Set.mem_Ici]
      split_ifs <;> simp
    have h2 : (fun a : ℝ≥0 => ENNReal.ofReal (-M.s fun _ => a)) = fun _ => 0 := by
      funext a
      simp only [M]
      split_ifs <;> simp
    rw [h1, h2, lintegral_indicator_const measurableSet_Ici, lintegral_zero,
      EReal.coe_ennreal_zero, sub_zero]
    rfl
  unfold Rev1 Rev
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (M : Mechanism Unit) (_ : IsAdmissible M) =>
    (expRevenue (oneGood ν) M).toENNReal) M hadm)
  rw [hrev, EReal.toENNReal_coe]

lemma srev_pi (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (a : ℕ) :
    SRev (Measure.pi (fun _ : Fin a => ρ)) = (a : ℝ≥0∞) * Rev1 ρ := by
  unfold SRev
  have h : ∀ i : Fin a, (Measure.pi (fun _ : Fin a => ρ)).map (fun x => x i) = ρ := by
    intro i
    have := Measure.pi_map_eval (μ := fun _ : Fin a => ρ) i
    simp only [measure_univ, Finset.prod_const_one, one_smul] at this
    exact this
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- indicator of `X_i ≥ p`. -/
noncomputable def ind (p : ℝ≥0) (t : ℝ≥0) : ℝ := (Set.Ici p).indicator (fun _ => (1 : ℝ)) t

lemma ind_meas (p : ℝ≥0) : Measurable (ind p) :=
  measurable_const.indicator measurableSet_Ici

lemma ind_nonneg (p t : ℝ≥0) : 0 ≤ ind p t := by
  unfold ind; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma ind_le_one (p t : ℝ≥0) : ind p t ≤ 1 := by
  unfold ind; exact Set.indicator_le_self' (fun _ _ => zero_le_one) _

lemma ind_sq (p t : ℝ≥0) : ind p t * ind p t = ind p t := by
  unfold ind; by_cases h : t ∈ Set.Ici p <;> simp [h]

section
variable (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (k : ℕ) (p : ℝ≥0)

lemma integrable_bdd (f : (Fin k → ℝ≥0) → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : Integrable f (Measure.pi (fun _ : Fin k => ν)) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)

lemma int_ind (i : Fin k) :
    ∫ x, ind p (x i) ∂(Measure.pi (fun _ : Fin k => ν)) = ν.real (Set.Ici p) := by
  have hmp := measurePreserving_eval (fun _ : Fin k => ν) i
  rw [← integral_map hmp.measurable.aemeasurable (ind_meas p).aestronglyMeasurable,
    hmp.map_eq]
  exact integral_indicator_one measurableSet_Ici

lemma int_ind_mul (i j : Fin k) :
    ∫ x, ind p (x i) * ind p (x j) ∂(Measure.pi (fun _ : Fin k => ν)) ≤
      ν.real (Set.Ici p) ^ 2 + (if i = j then ν.real (Set.Ici p) else 0) := by
  have hα : 0 ≤ ν.real (Set.Ici p) := measureReal_nonneg
  by_cases hij : i = j
  · subst hij
    simp only [ind_sq, int_ind, if_true]
    nlinarith
  · have hind := (iIndepFun_pi (μ := fun _ : Fin k => ν) (X := fun _ => ind p)
      (fun _ => (ind_meas p).aemeasurable)).indepFun hij
    have := hind.integral_mul_eq_mul_integral
      ((ind_meas p).comp (measurable_pi_apply i)).aestronglyMeasurable
      ((ind_meas p).comp (measurable_pi_apply j)).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, int_ind, int_ind, if_neg hij]
    nlinarith

/-- number of goods with value at least `p`. -/
noncomputable def Z (x : Fin k → ℝ≥0) : ℝ := ∑ i, ind p (x i)

lemma Z_meas : Measurable (Z k p) := by
  unfold Z
  exact Finset.measurable_sum _ fun i _ => (ind_meas p).comp (measurable_pi_apply i)

lemma Z_eq_card (x : Fin k → ℝ≥0) :
    Z k p x = ((Finset.univ.filter (fun i => p ≤ x i)).card : ℝ) := by
  unfold Z ind
  simp only [Set.indicator, Set.mem_Ici]
  rw [Finset.sum_boole]

lemma Z_nonneg (x : Fin k → ℝ≥0) : 0 ≤ Z k p x :=
  Finset.sum_nonneg fun i _ => ind_nonneg p _

lemma Z_le (x : Fin k → ℝ≥0) : Z k p x ≤ k := by
  unfold Z
  calc ∑ i, ind p (x i) ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum fun i _ => ind_le_one p _
    _ = k := by simp

lemma int_Z : ∫ x, Z k p x ∂(Measure.pi (fun _ : Fin k => ν)) = k * ν.real (Set.Ici p) := by
  unfold Z
  rw [integral_finsetSum (f := fun i (x : Fin k → ℝ≥0) => ind p (x i)) _
    fun i _ => integrable_bdd ν k _
    ((ind_meas p).comp (measurable_pi_apply i)) 1 fun x => by
      rw [abs_of_nonneg (ind_nonneg p _)]; exact ind_le_one p _]
  simp [int_ind]

lemma int_Z_sq : ∫ x, Z k p x ^ 2 ∂(Measure.pi (fun _ : Fin k => ν)) ≤
    (k * ν.real (Set.Ici p)) ^ 2 + k * ν.real (Set.Ici p) := by
  have hexp : ∀ x, Z k p x ^ 2 = ∑ i, ∑ j, ind p (x i) * ind p (x j) := by
    intro x
    unfold Z
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  have hint : ∀ i j : Fin k, Integrable (fun x : Fin k → ℝ≥0 => ind p (x i) * ind p (x j))
      (Measure.pi (fun _ : Fin k => ν)) := by
    intro i j
    refine integrable_bdd ν k _ (((ind_meas p).comp (measurable_pi_apply i)).mul
      ((ind_meas p).comp (measurable_pi_apply j))) 1 fun x => ?_
    rw [abs_of_nonneg (mul_nonneg (ind_nonneg p _) (ind_nonneg p _))]
    exact mul_le_one₀ (ind_le_one p _) (ind_nonneg p _) (ind_le_one p _)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j]
  calc ∑ i, ∑ j, ∫ x, ind p (x i) * ind p (x j) ∂(Measure.pi (fun _ : Fin k => ν))
      ≤ ∑ i : Fin k, ∑ j : Fin k, (ν.real (Set.Ici p) ^ 2 +
          (if i = j then ν.real (Set.Ici p) else 0)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => int_ind_mul ν k p i j
    _ = (k * ν.real (Set.Ici p)) ^ 2 + k * ν.real (Set.Ici p) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

/-- Cantelli-type tail bound: `P[Z < m] ≤ (u² + μ)/(t+u)²` with `t = μ + 1 - m`. -/
lemma tail_bound (m : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (ht : 0 < (k * ν.real (Set.Ici p)) + 1 - m) :
    (Measure.pi (fun _ : Fin k => ν)).real {x | Z k p x < m} *
        ((k * ν.real (Set.Ici p)) + 1 - m + u) ^ 2 ≤
      u ^ 2 + k * ν.real (Set.Ici p) := by
  set P := Measure.pi (fun _ : Fin k => ν)
  set μ := k * ν.real (Set.Ici p)
  set t := μ + 1 - m
  set f : (Fin k → ℝ≥0) → ℝ := fun x => (μ + u - Z k p x) ^ 2
  have hfm : Measurable f := by
    have := Z_meas k p
    fun_prop
  have hfi : Integrable f P := by
    refine integrable_bdd ν k f hfm ((μ + u + k) ^ 2) fun x => ?_
    have h0 := Z_nonneg k p x
    have h1 := Z_le k p x
    have hμ : 0 ≤ μ := by positivity
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (Filter.Eventually.of_forall fun x => sq_nonneg (μ + u - Z k p x)) hfi ((t + u) ^ 2)
  have hsub : {x | Z k p x < m} ⊆ {x | (t + u) ^ 2 ≤ f x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hint : Z k p x ≤ m - 1 := by
      rw [Z_eq_card] at hx ⊢
      have : (Finset.univ.filter (fun i => p ≤ x i)).card < m := by exact_mod_cast hx
      have : ((Finset.univ.filter (fun i => p ≤ x i)).card : ℝ) + 1 ≤ m := by
        exact_mod_cast this
      linarith
    have : t + u ≤ μ + u - Z k p x := by simp only [t]; linarith
    exact pow_le_pow_left₀ (by linarith) this 2
  have hint : ∫ x, f x ∂P ≤ u ^ 2 + μ := by
    have hZ := int_Z ν k p
    have hZ2 := int_Z_sq ν k p
    have hexp : ∀ x, f x = (μ + u) ^ 2 - 2 * (μ + u) * Z k p x + Z k p x ^ 2 := by
      intro x; simp only [f]; ring
    simp_rw [hexp]
    have hZi : Integrable (Z k p) P := integrable_bdd ν k _ (Z_meas k p) k fun x => by
      rw [abs_of_nonneg (Z_nonneg k p x)]; exact Z_le k p x
    have hZ2i : Integrable (fun x => Z k p x ^ 2) P :=
      integrable_bdd ν k _ ((Z_meas k p).pow_const 2) (k ^ 2) fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (Z_nonneg k p x) (Z_le k p x) 2
    rw [integral_add (by exact (integrable_const _).sub (hZi.const_mul _)) hZ2i,
      integral_sub (integrable_const _) (hZi.const_mul _), integral_const_mul, hZ,
      integral_const]
    have hP1 : P.real Set.univ = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    rw [hP1, smul_eq_mul, one_mul]
    simp only [P] at hZ2 ⊢
    nlinarith
  calc P.real {x | Z k p x < m} * (t + u) ^ 2
      ≤ P.real {x | (t + u) ^ 2 ≤ f x} * (t + u) ^ 2 := by
        gcongr
        exact measure_ne_top P _
    _ ≤ ∫ x, f x ∂P := by rw [mul_comm]; exact hmarkov
    _ ≤ _ := hint

end

end KBP14Aux

namespace KBP14Aux
open MultiItemRev.Decomp

lemma arith (μ m t : ℝ) (hμ : 0 < μ) (h1 : μ ≤ 2 * m) (h2 : 2 * m < μ + 2)
    (ht : t = μ + 1 - m) : μ * (t ^ 2 + μ) ≤ 4 * m * t ^ 2 := by
  subst ht
  nlinarith [mul_pos hμ hμ, sq_nonneg (μ + 2 - 2*m),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2.le),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2.le)) hμ.le]

/-- For a single price `p` with `α = P[X ≥ p]`: `k p α ≤ 4 BRev`. -/
lemma key (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (k : ℕ) (hk : 1 ≤ k) (p : ℝ≥0) :
    ENNReal.ofReal (1 / 4) * ((k : ℝ≥0∞) * ((p : ℝ≥0∞) * ν {t | p ≤ t})) ≤
      BRev (Measure.pi (fun _ : Fin k => ν)) := by
  set α := ν.real (Set.Ici p) with hα
  have hα0 : 0 ≤ α := measureReal_nonneg
  have hνα : ν {t | p ≤ t} = ENNReal.ofReal α := by
    rw [hα, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top ν _)]
    rfl
  set μ := (k : ℝ) * α with hμdef
  have hLHS : ENNReal.ofReal (1 / 4) * ((k : ℝ≥0∞) * ((p : ℝ≥0∞) * ν {t | p ≤ t})) =
      ENNReal.ofReal ((p : ℝ) * μ / 4) := by
    rw [hνα, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hμdef]; ring
  rw [hLHS]
  rcases eq_or_lt_of_le (show 0 ≤ μ by positivity) with hμ0 | hμ0
  · rw [← hμ0]; simp
  -- the price `m p` with `m = ⌈μ/2⌉`
  set m : ℕ := ⌈μ / 2⌉₊ with hm
  have hm1 : μ ≤ 2 * (m : ℝ) := by
    have := Nat.le_ceil (μ / 2); linarith
  have hm2 : 2 * (m : ℝ) < μ + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ μ / 2 by positivity); linarith
  set t := μ + 1 - m with htdef
  have ht : 0 < t := by linarith
  set P := Measure.pi (fun _ : Fin k => ν)
  set Pr := P.real {x | Z k p x < m}
  have hTB := tail_bound ν k p m (μ / t) (by positivity) ht
  -- `Pr ≤ μ / (t² + μ)`
  have hPr : Pr * (t ^ 2 + μ) ≤ μ := by
    have h1 : (t + μ / t) ^ 2 = (t ^ 2 + μ) ^ 2 / t ^ 2 := by field_simp
    have h2 : (μ / t) ^ 2 + μ = μ * (t ^ 2 + μ) / t ^ 2 := by field_simp; ring
    rw [h1, h2] at hTB
    have hpos : 0 < t ^ 2 + μ := by positivity
    have := hTB
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)] at this
    nlinarith
  have hcompl : P.real {x | (m : ℝ) ≤ Z k p x} = 1 - Pr := by
    have : {x | (m : ℝ) ≤ Z k p x} = {x | Z k p x < m}ᶜ := by ext x; simp
    rw [this, probReal_compl_eq_one_sub (measurableSet_lt (Z_meas k p) measurable_const)]
  have hfinal : μ ≤ 4 * m * (1 - Pr) := by
    have := arith μ m t hμ0 hm1 hm2 rfl
    have hpos : 0 < t ^ 2 + μ := by positivity
    nlinarith
  -- bundled revenue at price `m p`
  have hprice := price_le_rev1 (P.map (fun x => ∑ i, x i)) ((m : ℝ≥0) * p)
  have hsum_meas : Measurable (fun x : Fin k → ℝ≥0 => ∑ i, x i) := by fun_prop
  rw [show {x : ℝ≥0 | (m : ℝ≥0) * p ≤ x} = Set.Ici ((m : ℝ≥0) * p) from rfl,
    Measure.map_apply hsum_meas measurableSet_Ici] at hprice
  have hsub : {x | (m : ℝ) ≤ Z k p x} ⊆
      (fun x : Fin k → ℝ≥0 => ∑ i, x i) ⁻¹' Set.Ici ((m : ℝ≥0) * p) := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici] at hx ⊢
    rw [Z_eq_card] at hx
    have hc : m ≤ (Finset.univ.filter (fun i => p ≤ x i)).card := by exact_mod_cast hx
    calc (m : ℝ≥0) * p ≤ ((Finset.univ.filter (fun i => p ≤ x i)).card : ℝ≥0) * p := by
          gcongr
      _ = ∑ i ∈ Finset.univ.filter (fun i => p ≤ x i), p := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => p ≤ x i), x i :=
          Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i, x i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc ENNReal.ofReal ((p : ℝ) * μ / 4)
      ≤ ENNReal.ofReal (((m : ℝ≥0) * p : ℝ≥0) * P.real {x | (m : ℝ) ≤ Z k p x}) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hcompl]
        push_cast
        have hp : (0 : ℝ) ≤ p := p.2
        nlinarith
    _ = (((m : ℝ≥0) * p : ℝ≥0) : ℝ≥0∞) * P {x | (m : ℝ) ≤ Z k p x} := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top P _)]
    _ ≤ (((m : ℝ≥0) * p : ℝ≥0) : ℝ≥0∞) *
          P ((fun x : Fin k → ℝ≥0 => ∑ i, x i) ⁻¹' Set.Ici ((m : ℝ≥0) * p)) := by
        gcongr
    _ ≤ Rev1 (P.map (fun x => ∑ i, x i)) := hprice
    _ = BRev (Measure.pi (fun _ : Fin k => ν)) := rfl

end KBP14Aux

open KBP14Aux in
theorem solution (k : ℕ) (hk : 1 ≤ k)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    ENNReal.ofReal (1 / 4) * MultiItemRev.Decomp.SRev (Measure.pi (fun _ : Fin k => ν)) ≤
      MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by
  rw [srev_pi, (MultiItemRev.KBundling.myerson_one_good ν).1, ENNReal.mul_iSup,
    ENNReal.mul_iSup]
  exact iSup_le fun p => key ν k hk p

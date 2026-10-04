-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.regime_switching_power_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:45:48.010594+00:00
-- url     : https://prove2.me/submissions/a4ddb8c8-c754-4330-98de-1b892f014b04

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimeMarket
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimePowerAuxiliary

open MeasureTheory ProbabilityTheory MDPFinance.ConsumptionInvestment

namespace RSPCex

/-- Two regimes, carrying the trivial σ-algebra. -/
def B2 : Type := Bool

instance : Fintype B2 := inferInstanceAs (Fintype Bool)
instance : DecidableEq B2 := inferInstanceAs (DecidableEq Bool)
instance : MeasurableSpace B2 := ⊥

def tt : B2 := (true : Bool)
def ff : B2 := (false : Bool)

theorem ff_ne_tt : ff ≠ tt := by decide

def zm : Fin 1 → ℝ := fun _ => -1
def zp : Fin 1 → ℝ := fun _ => 8
def z0 : Fin 1 → ℝ := fun _ => 0

noncomputable def Qt : Measure (Fin 1 → ℝ) :=
  (1 / 2 : ENNReal) • Measure.dirac zm + (1 / 2 : ENNReal) • Measure.dirac zp

noncomputable def Qf : Measure (Fin 1 → ℝ) := Measure.dirac z0

instance : IsProbabilityMeasure Qt := by
  constructor
  simp only [Qt, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

theorem int_dirac (f : (Fin 1 → ℝ) → ℝ) (a : Fin 1 → ℝ) : Integrable f (Measure.dirac a) :=
  (integrable_const (f a)).congr (ae_eq_dirac f).symm

theorem int_Qt (f : (Fin 1 → ℝ) → ℝ) : Integrable f Qt :=
  ((int_dirac f zm).smul_measure (by simp)).add_measure ((int_dirac f zp).smul_measure (by simp))

theorem integral_Qt (f : (Fin 1 → ℝ) → ℝ) : ∫ z, f z ∂Qt = (f zm + f zp) / 2 := by
  have h1 := (int_dirac f zm).smul_measure (c := (1 / 2 : ENNReal)) (by simp)
  have h2 := (int_dirac f zp).smul_measure (c := (1 / 2 : ENNReal)) (by simp)
  rw [Qt, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem ae_Qt_iff (p : (Fin 1 → ℝ) → Prop) : (∀ᵐ z ∂Qt, p z) ↔ p zm ∧ p zp := by
  rw [ae_iff, Qt, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : p zm <;> by_cases h2 : p zp <;> simp [Set.indicator_apply, h1, h2]

theorem ae_Qf_iff (p : (Fin 1 → ℝ) → Prop) : (∀ᵐ z ∂Qf, p z) ↔ p z0 := by
  rw [ae_iff, Qf, Measure.dirac_apply]
  by_cases h1 : p z0 <;> simp [Set.indicator_apply, h1]

noncomputable def QQ (j : B2) : Measure (Fin 1 → ℝ) := if j = tt then Qt else Qf

theorem QQ_prob (j : B2) : IsProbabilityMeasure (QQ j) := by
  unfold QQ; split_ifs
  · infer_instance
  · unfold Qf; infer_instance

noncomputable def U (x : ℝ) : ℝ := x ^ (1 / 2 : ℝ) / (1 / 2)

theorem U_mono : StrictMonoOn U (Set.Ici 0) := by
  intro a ha b hb hab
  exact div_lt_div_of_pos_right (Real.strictMonoOn_rpow_Ici_of_exponent_pos (by norm_num)
    ha hb hab) (by norm_num)

theorem U_conc : StrictConcaveOn ℝ (Set.Ici 0) U := by
  have h := Real.strictConcaveOn_rpow (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have := h.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul, U] at *
  rw [show a * (x ^ (1 / 2 : ℝ) / (1 / 2)) + b * (y ^ (1 / 2 : ℝ) / (1 / 2)) =
    (a * x ^ (1 / 2 : ℝ) + b * y ^ (1 / 2 : ℝ)) / (1 / 2) by ring]
  exact div_lt_div_of_pos_right this (by norm_num)

theorem U_cont : ContinuousOn U (Set.Ici 0) :=
  ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).div_const _).continuousOn

theorem sum1 (α z : Fin 1 → ℝ) : ∑ k, α k * z k = α 0 * z 0 := by simp

theorem NA (j : B2) : ¬ ∃ a : Fin 1 → ℝ, (∀ᵐ z ∂(QQ j), 0 ≤ ∑ k, a k * z k) ∧
    QQ j {z | 0 < ∑ k, a k * z k} > 0 := by
  rintro ⟨a, ha, hpos⟩
  unfold QQ at ha hpos
  split_ifs at ha hpos
  · rw [ae_Qt_iff] at ha
    simp only [sum1, zm, zp] at ha
    have ha0 : a 0 = 0 := by linarith [ha.1, ha.2]
    simp only [sum1, ha0, zero_mul, lt_self_iff_false, Set.setOf_false, measure_empty] at hpos
  · have : {z : Fin 1 → ℝ | 0 < ∑ k, a k * z k} ⊆ {z | z ≠ z0} := by
      intro z hz h; subst h; simp [sum1, z0] at hz
    have h0 : Qf {z | z ≠ z0} = 0 := by
      rw [Qf, Measure.dirac_apply]; simp [Set.indicator_apply]
    exact absurd (measure_mono_null this h0) (ne_of_gt hpos)

noncomputable def M : RegimeSwitchingMarket B2 1 where
  i := 0
  hi_pos := by norm_num
  β := 1
  hβ_pos := by norm_num
  hβ_le_one := le_rfl
  p := fun j k => if j = k then 1 else 0
  hp_nonneg := fun j k => by split_ifs <;> norm_num
  hp_sum := fun j => by simp
  Q := QQ
  hQ_prob := QQ_prob
  hNA := NA
  hFM2 := fun j => by
    unfold QQ; split_ifs
    · exact int_Qt _
    · exact int_dirac _ _
  domU := Set.Ici 0
  hdomU := rfl
  Uc := U
  Up := U
  hUc_mono := U_mono
  hUc_concave := U_conc
  hUc_cont := U_cont
  hUp_mono := U_mono
  hUp_concave := U_conc
  hUp_cont := U_cont

theorem MQ (j : B2) : M.Q j = QQ j := rfl

theorem mem_Afrac (j : B2) (α : Fin 1 → ℝ) :
    α ∈ M.Afrac j ↔ ∀ᵐ z ∂(QQ j), 0 ≤ 1 + ∑ k, α k * z k := by
  rw [RegimeSwitchingMarket.Afrac, Set.mem_setOf_eq, MQ]

theorem vff : M.vPower (1 / 2) ff = 1 := by
  have hQ : M.Q ff = Qf := by rw [MQ]; unfold QQ; rw [if_neg ff_ne_tt]
  have hmem : ∀ α, α ∈ M.Afrac ff := by
    intro α
    rw [mem_Afrac, ← MQ, hQ, ae_Qf_iff]; simp [z0]
  have hI : ∀ α : Fin 1 → ℝ, ∫ z, (1 + ∑ k, α k * z k) ^ (1 / 2 : ℝ) ∂(M.Q ff) = 1 := by
    intro α; rw [hQ, Qf, integral_dirac]; simp [z0]
  unfold RegimeSwitchingMarket.vPower
  simp only [hI]
  rw [show (fun α => ⨆ (_ : α ∈ M.Afrac ff), (1 : ℝ)) = fun _ => 1 by
    funext α; exact ciSup_pos (hmem α)]
  exact ciSup_const

theorem rp_le (y : ℝ) (hy : 0 ≤ y) : y ^ (1 / 2 : ℝ) ≤ 1 + y := by
  rcases le_total y 1 with h | h
  · have := Real.rpow_le_one hy h (by norm_num : (0 : ℝ) ≤ 1 / 2); linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 / 2 : ℝ) ≤ 1)
    rw [Real.rpow_one] at this; linarith

theorem vtt : 3 / 2 ≤ M.vPower (1 / 2) tt := by
  have hQ : M.Q tt = Qt := by rw [MQ]; unfold QQ; rw [if_pos rfl]
  have hmem : ∀ α : Fin 1 → ℝ, α ∈ M.Afrac tt ↔ 0 ≤ 1 + α 0 * (-1) ∧ 0 ≤ 1 + α 0 * 8 := by
    intro α
    rw [mem_Afrac, ← MQ, hQ, ae_Qt_iff]; simp [sum1, zm, zp]
  have hI : ∀ α : Fin 1 → ℝ, ∫ z, (1 + ∑ k, α k * z k) ^ (1 / 2 : ℝ) ∂(M.Q tt) =
      ((1 + α 0 * (-1)) ^ (1 / 2 : ℝ) + (1 + α 0 * 8) ^ (1 / 2 : ℝ)) / 2 := by
    intro α; rw [hQ, integral_Qt]; simp [sum1, zm, zp]
  unfold RegimeSwitchingMarket.vPower
  simp only [hI]
  have hbdd : BddAbove (Set.range fun α : Fin 1 → ℝ => ⨆ (_ : α ∈ M.Afrac tt),
      ((1 + α 0 * (-1)) ^ (1 / 2 : ℝ) + (1 + α 0 * 8) ^ (1 / 2 : ℝ)) / 2) := by
    refine ⟨10, ?_⟩
    rintro _ ⟨α, rfl⟩
    refine Real.iSup_le (fun h => ?_) (by norm_num)
    rw [hmem] at h
    have e1 := rp_le _ h.1
    have e2 := rp_le _ h.2
    linarith [h.1, h.2]
  refine le_ciSup_of_le hbdd (fun _ => 1) ?_
  have h1 : (fun _ : Fin 1 => (1 : ℝ)) ∈ M.Afrac tt := by rw [hmem]; norm_num
  rw [ciSup_pos h1]
  have h9 : (1 + (1 : ℝ) * 8) ^ (1 / 2 : ℝ) = 3 := by
    rw [← Real.sqrt_eq_rpow, show (1 + (1 : ℝ) * 8) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h0 : (1 + (1 : ℝ) * (-1)) ^ (1 / 2 : ℝ) = 0 := by
    rw [show (1 + (1 : ℝ) * (-1)) = 0 by norm_num, Real.zero_rpow (by norm_num)]
  rw [h9, h0]; norm_num

theorem v_nonneg (j : B2) : 0 ≤ M.vPower (1 / 2) j := by
  by_cases h : j = tt
  · subst h; linarith [vtt]
  · have : j = ff := by
      revert h; revert j; decide
    subst this; rw [vff]; norm_num

/-- The recursively defined `d_n`. -/
noncomputable def dseq : ℕ → B2 → ℝ
  | 0 => fun _ => (1 / 2 : ℝ)⁻¹
  | (n + 1) => fun j => ((1 / 2 : ℝ) ^ (-(1 - (1 / 2 : ℝ))⁻¹) +
      (M.β * (1 + M.i) ^ (1 / 2 : ℝ) * M.vPower (1 / 2) j) ^ ((1 - (1 / 2 : ℝ))⁻¹) *
        ∑ k, M.p j k * dseq n k ^ ((1 - (1 / 2 : ℝ))⁻¹)) ^ (1 - (1 / 2 : ℝ))

theorem inner_pos (n : ℕ) (j : B2) (hd : ∀ k, 0 < dseq n k) :
    0 < (1 / 2 : ℝ) ^ (-(1 - (1 / 2 : ℝ))⁻¹) +
      (M.β * (1 + M.i) ^ (1 / 2 : ℝ) * M.vPower (1 / 2) j) ^ ((1 - (1 / 2 : ℝ))⁻¹) *
        ∑ k, M.p j k * dseq n k ^ ((1 - (1 / 2 : ℝ))⁻¹) := by
  have hb : 0 ≤ M.β * (1 + M.i) ^ (1 / 2 : ℝ) * M.vPower (1 / 2) j := by
    have : M.β = 1 := rfl
    have : M.i = 0 := rfl
    simp only [*, add_zero, Real.one_rpow, one_mul]
    exact v_nonneg j
  have hs : 0 ≤ ∑ k, M.p j k * dseq n k ^ ((1 - (1 / 2 : ℝ))⁻¹) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (M.hp_nonneg j k) (Real.rpow_nonneg (hd k).le _)
  have := mul_nonneg (Real.rpow_nonneg hb ((1 - (1 / 2 : ℝ))⁻¹)) hs
  have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) (-(1 - (1 / 2 : ℝ))⁻¹)
  linarith

theorem dpos : ∀ n j, 0 < dseq n j := by
  intro n
  induction n with
  | zero => intro j; show (0 : ℝ) < (1 / 2 : ℝ)⁻¹; norm_num
  | succ n ih => intro j; exact Real.rpow_pos_of_pos (inner_pos n j ih) _

theorem drec : ∀ n, ∀ j,
    dseq (n + 1) j ^ ((1 - (1 / 2 : ℝ))⁻¹) = (1 / 2 : ℝ) ^ (-(1 - (1 / 2 : ℝ))⁻¹) +
      (M.β * (1 + M.i) ^ (1 / 2 : ℝ) * M.vPower (1 / 2) j) ^ ((1 - (1 / 2 : ℝ))⁻¹) *
        ∑ k, M.p j k * dseq n k ^ ((1 - (1 / 2 : ℝ))⁻¹) := by
  intro n j
  exact Real.rpow_rpow_inv (inner_pos n j (dpos n)).le (by norm_num)

/-- Measurable maps out of `ℝ × B2` (with `⊥` on `B2`) do not see the regime. -/
theorem meas_indep {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (f : ℝ × B2 → β) (hf : Measurable f) (x : ℝ) (j k : B2) : f (x, j) = f (x, k) := by
  have hS : MeasurableSet (f ⁻¹' {f (x, j)}) := hf (measurableSet_singleton _)
  have hprod : (Prod.instMeasurableSpace : MeasurableSpace (ℝ × B2)) =
      MeasurableSpace.comap Prod.fst inferInstance := by
    show MeasurableSpace.comap Prod.fst _ ⊔ MeasurableSpace.comap Prod.snd (⊥ : MeasurableSpace B2) = _
    rw [MeasurableSpace.comap_bot, sup_bot_eq]
  rw [hprod] at hS
  obtain ⟨t, -, ht⟩ := hS
  have hj : (x, j) ∈ f ⁻¹' {f (x, j)} := rfl
  rw [← ht] at hj
  have hk : (x, k) ∈ Prod.fst ⁻¹' t := hj
  rw [ht] at hk
  exact hk.symm

end RSPCex

open RSPCex in
theorem solution : ¬ (∀ {EY : Type} [Fintype EY] [MeasurableSpace EY] {d : ℕ}
    (M : RegimeSwitchingMarket EY d) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hUc : ∀ x ≥ (0 : ℝ), M.Uc x = x ^ γ / γ) (hUp : ∀ x ≥ (0 : ℝ), M.Up x = x ^ γ / γ)
    (dseq : ℕ → EY → ℝ) (hdpos : ∀ n j, 0 < dseq n j) (hd0 : ∀ j, dseq 0 j = γ⁻¹)
    (hdrec : ∀ n, ∀ j,
      dseq (n + 1) j ^ ((1 - γ)⁻¹) = γ ^ (-(1 - γ)⁻¹) +
        (M.β * (1 + M.i) ^ γ * M.vPower γ j) ^ ((1 - γ)⁻¹) *
          ∑ k, M.p j k * dseq n k ^ ((1 - γ)⁻¹)),
    (∀ n, ∀ x ≥ (0 : ℝ), ∀ j, M.J n x j = ((dseq n j * x ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : EY → (Fin d → ℝ), (∀ j, αstar j ∈ M.Afrac j ∧
          ∫ z, (1 + ∑ k, αstar j k * z k) ^ γ ∂(M.Q j) = M.vPower γ j) ∧
        ∃ fstar : ℕ → ℝ × EY → ℝ × (Fin d → ℝ),
          (∀ n, ∀ x ≥ (0 : ℝ), ∀ j, (fstar n (x, j)).1 = x * (γ * dseq n j) ^ (-(1 - γ)⁻¹)) ∧
          (∀ n, ∀ x ≥ (0 : ℝ), ∀ j,
            (fstar n (x, j)).2 = fun k => (x - (fstar n (x, j)).1) * αstar j k) ∧
          ∀ N : ℕ, M.IsAdmissible N (fun l => fstar (N - l)) ∧
            ∀ x ≥ (0 : ℝ), ∀ j, M.Jpi (fun l => fstar (N - l)) N x j = M.J N x j)) := by
  intro h
  have H := h RSPCex.M (1 / 2) (by norm_num) (by norm_num) (fun x _ => rfl) (fun x _ => rfl)
    dseq dpos (fun j => rfl) drec
  obtain ⟨-, -, -, fstar, hf1, -, hadm⟩ := H
  have hmeas : Measurable (fstar 1) := ((hadm 1).1 0 (by norm_num)).2
  have heq := meas_indep (fun p => (fstar 1 p).1) (measurable_fst.comp hmeas) 1 tt ff
  rw [hf1 1 1 (by norm_num) tt, hf1 1 1 (by norm_num) ff, one_mul, one_mul] at heq
  -- `(γ d₁ tt)^r = (γ d₁ ff)^r` with `r ≠ 0` forces `d₁ tt = d₁ ff`
  have hpos : ∀ j, 0 ≤ (1 / 2 : ℝ) * dseq 1 j := fun j => by
    have := dpos 1 j; positivity
  have hd1 : (1 / 2 : ℝ) * dseq 1 tt = (1 / 2 : ℝ) * dseq 1 ff :=
    Real.rpow_left_injOn (by norm_num : (-(1 - (1 / 2 : ℝ))⁻¹) ≠ 0) (hpos tt) (hpos ff) heq
  have hd1' : dseq 1 tt = dseq 1 ff := by linarith
  have r1 := drec 0 tt
  have r2 := drec 0 ff
  rw [hd1', r2] at r1
  have hsum : ∀ j : B2, ∑ k, RSPCex.M.p j k * dseq 0 k ^ ((1 - (1 / 2 : ℝ))⁻¹) =
      (1 / 2 : ℝ)⁻¹ ^ ((1 - (1 / 2 : ℝ))⁻¹) := by
    intro j
    show ∑ k, (if j = k then (1 : ℝ) else 0) * (1 / 2 : ℝ)⁻¹ ^ ((1 - (1 / 2 : ℝ))⁻¹) = _
    simp
  rw [hsum, hsum] at r1
  have hc : (0 : ℝ) < (1 / 2 : ℝ)⁻¹ ^ ((1 - (1 / 2 : ℝ))⁻¹) := by positivity
  have hB : ∀ j, RSPCex.M.β * (1 + RSPCex.M.i) ^ (1 / 2 : ℝ) * RSPCex.M.vPower (1 / 2) j =
      RSPCex.M.vPower (1 / 2) j := by
    intro j
    show (1 : ℝ) * (1 + 0) ^ (1 / 2 : ℝ) * _ = _
    simp
  rw [hB, hB] at r1
  have hv : RSPCex.M.vPower (1 / 2) ff ^ ((1 - (1 / 2 : ℝ))⁻¹) =
      RSPCex.M.vPower (1 / 2) tt ^ ((1 - (1 / 2 : ℝ))⁻¹) := by
    have := mul_right_cancel₀ hc.ne' (add_left_cancel r1)
    exact this
  have := Real.rpow_left_injOn (by norm_num : ((1 - (1 / 2 : ℝ))⁻¹) ≠ 0) (v_nonneg ff)
    (v_nonneg tt) hv
  rw [vff] at this
  linarith [vtt]

#print axioms solution

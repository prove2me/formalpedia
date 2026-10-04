-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.regime_monotone_value_consumption
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:10:20.50396+00:00
-- url     : https://prove2.me/submissions/f0742888-3677-4136-97a8-aaf5b950c065

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimeMarket
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimePowerAuxiliary
import Definitions.Def_MDPFinance_ConsumptionInvestment_StochasticOrders

open MeasureTheory ProbabilityTheory MDPFinance.ConsumptionInvestment

namespace RMVCex

def pt (r : ℝ) : Fin 1 → ℝ := fun _ => r

/-- `w δ_{-1} + (1-w) δ_1` on `ℝ^1`. -/
noncomputable def Qw (w : ℝ) : Measure (Fin 1 → ℝ) :=
  ENNReal.ofReal w • Measure.dirac (pt (-1)) + ENNReal.ofReal (1 - w) • Measure.dirac (pt 1)

/-- The same law on `ℝ`. -/
noncomputable def Rw (w : ℝ) : Measure ℝ :=
  ENNReal.ofReal w • Measure.dirac (-1) + ENNReal.ofReal (1 - w) • Measure.dirac 1

theorem Qw_prob (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) : IsProbabilityMeasure (Qw w) := by
  constructor
  simp only [Qw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]; norm_num

theorem int_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ)
    (a : α) : Integrable f (Measure.dirac a) :=
  (integrable_const (f a)).congr (ae_eq_dirac f).symm

theorem int_sm {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ)
    (c : ℝ) (a : α) : Integrable f (ENNReal.ofReal c • Measure.dirac a) :=
  (int_dirac f a).smul_measure ENNReal.ofReal_ne_top

theorem integral_sm {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ)
    (c : ℝ) (a : α) (hc : 0 ≤ c) :
    ∫ y, f y ∂(ENNReal.ofReal c • Measure.dirac a) = c * f a := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hc, smul_eq_mul]

theorem int_Qw (w : ℝ) (f : (Fin 1 → ℝ) → ℝ) : Integrable f (Qw w) :=
  (int_sm f _ _).add_measure (int_sm f _ _)

theorem integral_Qw (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) (f : (Fin 1 → ℝ) → ℝ) :
    ∫ z, f z ∂(Qw w) = w * f (pt (-1)) + (1 - w) * f (pt 1) := by
  rw [Qw, integral_add_measure (int_sm f _ _) (int_sm f _ _), integral_sm _ _ _ h0,
    integral_sm _ _ _ (by linarith)]

theorem integral_Rw (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) (f : ℝ → ℝ) :
    ∫ z, f z ∂(Rw w) = w * f (-1) + (1 - w) * f 1 := by
  rw [Rw, integral_add_measure (int_sm f _ _) (int_sm f _ _), integral_sm _ _ _ h0,
    integral_sm _ _ _ (by linarith)]

theorem map_Qw (w : ℝ) : (Qw w).map (fun z => z 0) = Rw w := by
  have hm : Measurable (fun z : Fin 1 → ℝ => z 0) := measurable_pi_apply 0
  rw [Qw, Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac, Measure.map_dirac]
  rfl

theorem ae_Qw (w : ℝ) (h0 : 0 < w) (h1 : w < 1) (p : (Fin 1 → ℝ) → Prop) :
    (∀ᵐ z ∂(Qw w), p z) ↔ p (pt (-1)) ∧ p (pt 1) := by
  have hw : ENNReal.ofReal w ≠ 0 := by simpa using h0
  have hw' : ENNReal.ofReal (1 - w) ≠ 0 := by simp; linarith
  rw [ae_iff, Qw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  by_cases a1 : p (pt (-1)) <;> by_cases a2 : p (pt 1) <;> simp [a1, a2, hw, hw']

theorem sum1 (α z : Fin 1 → ℝ) : ∑ k, α k * z k = α 0 * z 0 := by simp

theorem NAw (w : ℝ) (h0 : 0 < w) (h1 : w < 1) :
    ¬ ∃ a : Fin 1 → ℝ, (∀ᵐ z ∂(Qw w), 0 ≤ ∑ k, a k * z k) ∧
      Qw w {z | 0 < ∑ k, a k * z k} > 0 := by
  rintro ⟨a, ha, hpos⟩
  rw [ae_Qw w h0 h1] at ha
  simp only [sum1, pt] at ha
  have ha0 : a 0 = 0 := by linarith [ha.1, ha.2]
  simp only [sum1, ha0, zero_mul, lt_self_iff_false, Set.setOf_false, measure_empty] at hpos

theorem memA (w : ℝ) (h0 : 0 < w) (h1 : w < 1) (α : Fin 1 → ℝ) :
    (∀ᵐ z ∂(Qw w), 0 ≤ 1 + ∑ k, α k * z k) ↔ 0 ≤ 1 - α 0 ∧ 0 ≤ 1 + α 0 := by
  rw [ae_Qw w h0 h1]; simp only [sum1, pt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem sq_half (x : ℝ) : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

/-- The optimal fraction `α^* = (1-2w)/(w²+(1-w)²)`. -/
noncomputable def astar (w : ℝ) : Fin 1 → ℝ := fun _ => (1 - 2 * w) / (w ^ 2 + (1 - w) ^ 2)

theorem obj (w : ℝ) (h0 : 0 < w) (h1 : w < 1) (α : Fin 1 → ℝ) :
    ∫ z, (1 + ∑ k, α k * z k) ^ (1 / 2 : ℝ) ∂(Qw w) =
      w * Real.sqrt (1 - α 0) + (1 - w) * Real.sqrt (1 + α 0) := by
  rw [integral_Qw w h0.le h1.le]
  simp only [sum1, pt, sq_half]
  ring_nf

theorem obj_le (w : ℝ) (h0 : 0 < w) (h1 : w < 1) (α : Fin 1 → ℝ) (ha : 0 ≤ 1 - α 0 ∧ 0 ≤ 1 + α 0) :
    w * Real.sqrt (1 - α 0) + (1 - w) * Real.sqrt (1 + α 0) ≤
      Real.sqrt (2 * (w ^ 2 + (1 - w) ^ 2)) := by
  apply Real.le_sqrt_of_sq_le
  have hs := Real.sq_sqrt ha.1
  have ht := Real.sq_sqrt ha.2
  nlinarith [sq_nonneg ((1 - w) * Real.sqrt (1 - α 0) - w * Real.sqrt (1 + α 0))]

theorem obj_star (w : ℝ) (h0 : 0 < w) (h1 : w < 1) :
    w * Real.sqrt (1 - astar w 0) + (1 - w) * Real.sqrt (1 + astar w 0) =
      Real.sqrt (2 * (w ^ 2 + (1 - w) ^ 2)) := by
  set D := w ^ 2 + (1 - w) ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have e1 : 1 - astar w 0 = w ^ 2 * (2 / D) := by
    simp only [astar]; field_simp; ring
  have e2 : 1 + astar w 0 = (1 - w) ^ 2 * (2 / D) := by
    simp only [astar]; field_simp; ring
  rw [e1, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq h0.le, Real.sqrt_sq (by linarith)]
  have hsum : w * (w * Real.sqrt (2 / D)) + (1 - w) * ((1 - w) * Real.sqrt (2 / D)) =
      D * Real.sqrt (2 / D) := by rw [hD]; ring
  rw [hsum, show 2 * D = D ^ 2 * (2 / D) by field_simp, Real.sqrt_mul (sq_nonneg D),
    Real.sqrt_sq hD0.le]

theorem vP_eq (w : ℝ) (h0 : 0 < w) (h1 : w < 1) :
    (⨆ α ∈ {α : Fin 1 → ℝ | ∀ᵐ z ∂(Qw w), 0 ≤ 1 + ∑ k, α k * z k},
      ∫ z, (1 + ∑ k, α k * z k) ^ (1 / 2 : ℝ) ∂(Qw w)) =
      Real.sqrt (2 * (w ^ 2 + (1 - w) ^ 2)) := by
  have hmem : astar w ∈ {α : Fin 1 → ℝ | ∀ᵐ z ∂(Qw w), 0 ≤ 1 + ∑ k, α k * z k} := by
    show _
    rw [Set.mem_setOf_eq, memA w h0 h1]
    have hD : 0 < w ^ 2 + (1 - w) ^ 2 := by positivity
    simp only [astar]
    constructor
    · rw [sub_nonneg, div_le_one hD]; nlinarith
    · have : -1 ≤ (1 - 2 * w) / (w ^ 2 + (1 - w) ^ 2) := by
        rw [le_div_iff₀ hD]; nlinarith
      linarith
  have hb : ∀ α : Fin 1 → ℝ, (⨆ (_ : α ∈ {α : Fin 1 → ℝ | ∀ᵐ z ∂(Qw w), 0 ≤ 1 + ∑ k, α k * z k}),
      ∫ z, (1 + ∑ k, α k * z k) ^ (1 / 2 : ℝ) ∂(Qw w)) ≤ Real.sqrt (2 * (w ^ 2 + (1 - w) ^ 2)) := by
    intro α
    refine Real.iSup_le (fun h => ?_) (Real.sqrt_nonneg _)
    rw [Set.mem_setOf_eq, memA w h0 h1] at h
    rw [obj w h0 h1]
    exact obj_le w h0 h1 α h
  apply le_antisymm
  · exact Real.iSup_le hb (Real.sqrt_nonneg _)
  · refine le_ciSup_of_le ⟨_, Set.forall_mem_range.mpr hb⟩ (astar w) ?_
    rw [ciSup_pos hmem, obj w h0 h1, obj_star w h0 h1]

/-- Regime `0`: `⅘ δ_{-1} + ⅕ δ_1`; regime `1`: `⅗ δ_{-1} + ⅖ δ_1` (first-order better). -/
noncomputable def wt (j : Fin 2) : ℝ := if j = 0 then 4 / 5 else 3 / 5

theorem wt0 (j : Fin 2) : 0 < wt j := by unfold wt; split_ifs <;> norm_num
theorem wt1 (j : Fin 2) : wt j < 1 := by unfold wt; split_ifs <;> norm_num

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

noncomputable def M : RegimeSwitchingMarket (Fin 2) 1 where
  i := 0
  hi_pos := by norm_num
  β := 1
  hβ_pos := by norm_num
  hβ_le_one := le_rfl
  p := fun j k => if j = k then 1 else 0
  hp_nonneg := fun j k => by split_ifs <;> norm_num
  hp_sum := fun j => by simp
  Q := fun j => Qw (wt j)
  hQ_prob := fun j => Qw_prob _ (wt0 j).le (wt1 j).le
  hNA := fun j => NAw _ (wt0 j) (wt1 j)
  hFM2 := fun j => int_Qw _ _
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

theorem vP (j : Fin 2) : M.vPower (1 / 2) j = Real.sqrt (2 * (wt j ^ 2 + (1 - wt j) ^ 2)) :=
  vP_eq _ (wt0 j) (wt1 j)

theorem v_nonneg (j : Fin 2) : 0 ≤ M.vPower (1 / 2) j := by rw [vP]; exact Real.sqrt_nonneg _

noncomputable def dseq : ℕ → Fin 2 → ℝ
  | 0 => fun _ => (1 / 2 : ℝ)⁻¹
  | (n + 1) => fun j => ((1 / 2 : ℝ) ^ (-(1 - (1 / 2 : ℝ))⁻¹) +
      (M.β * (1 + M.i) ^ (1 / 2 : ℝ) * M.vPower (1 / 2) j) ^ ((1 - (1 / 2 : ℝ))⁻¹) *
        ∑ k, M.p j k * dseq n k ^ ((1 - (1 / 2 : ℝ))⁻¹)) ^ (1 - (1 / 2 : ℝ))

theorem hB (j : Fin 2) : M.β * (1 + M.i) ^ (1 / 2 : ℝ) * M.vPower (1 / 2) j = M.vPower (1 / 2) j := by
  show (1 : ℝ) * (1 + 0) ^ (1 / 2 : ℝ) * _ = _
  simp

theorem inner_pos (n : ℕ) (j : Fin 2) (hd : ∀ k, 0 < dseq n k) :
    0 < (1 / 2 : ℝ) ^ (-(1 - (1 / 2 : ℝ))⁻¹) +
      (M.β * (1 + M.i) ^ (1 / 2 : ℝ) * M.vPower (1 / 2) j) ^ ((1 - (1 / 2 : ℝ))⁻¹) *
        ∑ k, M.p j k * dseq n k ^ ((1 - (1 / 2 : ℝ))⁻¹) := by
  rw [hB]
  have hs : 0 ≤ ∑ k, M.p j k * dseq n k ^ ((1 - (1 / 2 : ℝ))⁻¹) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (M.hp_nonneg j k) (Real.rpow_nonneg (hd k).le _)
  have := mul_nonneg (Real.rpow_nonneg (v_nonneg j) ((1 - (1 / 2 : ℝ))⁻¹)) hs
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

theorem MQ (j : Fin 2) : M.Q j = Qw (wt j) := rfl

theorem mem_Afrac (j : Fin 2) (α : Fin 1 → ℝ) :
    α ∈ M.Afrac j ↔ ∀ᵐ z ∂(Qw (wt j)), 0 ≤ 1 + ∑ k, α k * z k := by
  rw [RegimeSwitchingMarket.Afrac, Set.mem_setOf_eq, MQ]

theorem Afrac_eq (j : Fin 2) : M.Afrac j = {α | 0 ≤ 1 - α 0 ∧ 0 ≤ 1 + α 0} := by
  ext α
  rw [mem_Afrac, memA _ (wt0 j) (wt1 j)]; rfl

theorem icv (j k : Fin 2) (hjk : j ≤ k) :
    LEIncreasingConcaveOrder ((M.Q j).map (fun z => z 0)) ((M.Q k).map (fun z => z 0)) := by
  intro f hf _ _ _
  rw [MQ, MQ, map_Qw, map_Qw, integral_Rw _ (wt0 j).le (wt1 j).le, integral_Rw _ (wt0 k).le (wt1 k).le]
  have hm : f (-1) ≤ f 1 := hf (by norm_num)
  fin_cases j <;> fin_cases k
  · exact le_rfl
  · simp only [wt]; norm_num; linarith
  · exact absurd hjk (by decide)
  · exact le_rfl

theorem smono : IsStochasticallyMonotoneChain M.p := by
  intro v hv
  have : (fun j => ∑ k, M.p j k * v k) = v := by
    funext j
    show ∑ k, (if j = k then (1 : ℝ) else 0) * v k = v j
    simp
  rw [this]; exact hv

end RMVCex

open RMVCex in
theorem solution : ¬ (∀ {m : ℕ} (M : RegimeSwitchingMarket (Fin m) 1)
    (hsupp : ∀ j k : Fin m, M.Afrac j = M.Afrac k)
    (hmono : IsStochasticallyMonotoneChain M.p)
    (hicv : ∀ j k : Fin m, j ≤ k →
      LEIncreasingConcaveOrder ((M.Q j).map (fun z => z 0)) ((M.Q k).map (fun z => z 0)))
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hUc : ∀ x ≥ (0 : ℝ), M.Uc x = x ^ γ / γ) (hUp : ∀ x ≥ (0 : ℝ), M.Up x = x ^ γ / γ)
    (dseq : ℕ → Fin m → ℝ) (hdpos : ∀ n j, 0 < dseq n j) (hd0 : ∀ j, dseq 0 j = γ⁻¹)
    (hdrec : ∀ n, ∀ j,
      dseq (n + 1) j ^ ((1 - γ)⁻¹) = γ ^ (-(1 - γ)⁻¹) +
        (M.β * (1 + M.i) ^ γ * M.vPower γ j) ^ ((1 - γ)⁻¹) *
          ∑ k, M.p j k * dseq n k ^ ((1 - γ)⁻¹))
    (αstar : Fin m → (Fin 1 → ℝ)) (hαstar_mem : ∀ j, αstar j ∈ M.Afrac j)
    (hαstar_opt : ∀ j, ∫ z, (1 + ∑ k, αstar j k * z k) ^ γ ∂(M.Q j) = M.vPower γ j),
    (∀ n, Monotone (dseq n)) ∧
      (∀ n, ∀ x ≥ (0 : ℝ), Antitone (fun j => x * (γ * dseq n j) ^ (-(1 - γ)⁻¹))) ∧
      ((∀ j, 0 ≤ αstar j 0) → ∀ n, ∀ x ≥ (0 : ℝ), Monotone (fun j =>
        (x - x * (γ * dseq n j) ^ (-(1 - γ)⁻¹)) * αstar j 0))) := by
  intro h
  have hmemS : ∀ j : Fin 2, astar (wt j) ∈ RMVCex.M.Afrac j := by
    intro j
    rw [mem_Afrac, memA _ (wt0 j) (wt1 j)]
    have hD : 0 < wt j ^ 2 + (1 - wt j) ^ 2 := by have := wt0 j; positivity
    have h0 := wt0 j
    have h1 := wt1 j
    simp only [astar]
    constructor
    · rw [sub_nonneg, div_le_one hD]; nlinarith
    · have : -1 ≤ (1 - 2 * wt j) / (wt j ^ 2 + (1 - wt j) ^ 2) := by
        rw [le_div_iff₀ hD]; nlinarith
      linarith
  have hopt : ∀ j : Fin 2, ∫ z, (1 + ∑ k, astar (wt j) k * z k) ^ (1 / 2 : ℝ) ∂(RMVCex.M.Q j) =
      RMVCex.M.vPower (1 / 2) j := by
    intro j
    rw [vP]
    rw [MQ, obj _ (wt0 j) (wt1 j), obj_star _ (wt0 j) (wt1 j)]
  obtain ⟨hmon, -, -⟩ := h RMVCex.M (fun j k => by rw [Afrac_eq, Afrac_eq]) smono icv (1 / 2)
    (by norm_num) (by norm_num) (fun x _ => rfl) (fun x _ => rfl) dseq dpos (fun j => rfl) drec
    (fun j => astar (wt j)) hmemS hopt
  have hle : dseq 1 0 ≤ dseq 1 1 := hmon 1 (by decide)
  have e := (1 - (1 / 2 : ℝ))⁻¹
  have hpow : dseq 1 0 ^ ((1 - (1 / 2 : ℝ))⁻¹) ≤ dseq 1 1 ^ ((1 - (1 / 2 : ℝ))⁻¹) :=
    Real.rpow_le_rpow (dpos 1 0).le hle (by norm_num)
  rw [drec 0 0, drec 0 1, hB, hB] at hpow
  have hsum : ∀ j : Fin 2, ∑ k, RMVCex.M.p j k * dseq 0 k ^ ((1 - (1 / 2 : ℝ))⁻¹) =
      (1 / 2 : ℝ)⁻¹ ^ ((1 - (1 / 2 : ℝ))⁻¹) := by
    intro j
    show ∑ k, (if j = k then (1 : ℝ) else 0) * (1 / 2 : ℝ)⁻¹ ^ ((1 - (1 / 2 : ℝ))⁻¹) = _
    simp
  rw [hsum, hsum] at hpow
  have hc : (0 : ℝ) < (1 / 2 : ℝ)⁻¹ ^ ((1 - (1 / 2 : ℝ))⁻¹) := by positivity
  have hv : RMVCex.M.vPower (1 / 2) 0 ^ ((1 - (1 / 2 : ℝ))⁻¹) ≤
      RMVCex.M.vPower (1 / 2) 1 ^ ((1 - (1 / 2 : ℝ))⁻¹) :=
    le_of_mul_le_mul_right (by linarith) hc
  have hv' := (Real.rpow_le_rpow_iff (v_nonneg 0) (v_nonneg 1) (by norm_num)).mp hv
  rw [vP, vP] at hv'
  have := Real.sqrt_le_sqrt_iff (by positivity) |>.mp hv'
  simp only [wt] at this
  norm_num at this

#print axioms solution

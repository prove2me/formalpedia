-- Prove2me | solution 1 for MDPFinance.Stationary.cash_balance_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:23:36.806525+00:00
-- url     : https://prove2.me/submissions/b4c1ba37-2667-4e78-b37d-cdaa8f317849

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory

open MDPFinance.Stationary

namespace CashCex

noncomputable def tc (cu cd : ℝ) (z : ℝ) : ℝ := cu * (max z 0) + cd * (max (-z) 0)

noncomputable def M1 : StationaryMarkovDecisionModel ℝ ℝ where
  D := Set.univ
  hD_meas := MeasurableSet.univ
  hD_sel := ⟨id, measurable_id, fun _ => Set.mem_univ _⟩
  Q := Kernel.deterministic (fun xa : ℝ × ℝ => xa.2) measurable_snd
  hQ_prob := fun _ => by
    simp only [Kernel.deterministic_apply]
    infer_instance
  r := fun xa => -(tc 1 1 (xa.2 - xa.1)) - xa.2 ^ 2
  hr_meas := by
    unfold tc
    fun_prop
  g := 0
  hg_meas := measurable_const
  β := 1
  hβ_pos := one_pos
  hβ_le_one := le_rfl

theorem erealIntegral_nonpos {μ : Measure ℝ} {v : ℝ → EReal} (hv : ∀ x, v x ≤ 0) :
    erealIntegral μ v ≤ 0 := by
  unfold erealIntegral
  have h0 : (∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) = 0 := by
    have : (fun x => (v x ⊔ 0).toENNReal) = fun _ => 0 := by
      funext x
      rw [sup_eq_right.mpr (hv x)]
      simp
    rw [this, lintegral_zero]
  rw [h0]
  simp only [EReal.coe_ennreal_zero, zero_add, EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

theorem erealIntegral_zero (μ : Measure ℝ) : erealIntegral μ (fun _ => (0 : EReal)) = 0 := by
  unfold erealIntegral
  simp

theorem r_nonpos (xa : ℝ × ℝ) : M1.r xa ≤ 0 := by
  show -(tc 1 1 (xa.2 - xa.1)) - xa.2 ^ 2 ≤ 0
  unfold tc
  have h1 : 0 ≤ max (xa.2 - xa.1) 0 := le_max_right _ _
  have h2 : 0 ≤ max (-(xa.2 - xa.1)) 0 := le_max_right _ _
  nlinarith [sq_nonneg xa.2]

theorem J0 (x : ℝ) : J M1 0 x = 0 := by
  unfold J
  apply le_antisymm
  · refine iSup₂_le fun π _ => ?_
    show (0 : EReal) + ((1 : ℝ) : EReal) * ((M1.g x : ℝ) : EReal) ≤ 0
    simp [M1]
  · refine le_trans ?_ (le_iSup₂ (f := fun π (_ : π ∈ {π : ℕ → ℝ → ℝ | IsPolicySeq M1 0 π}) =>
      Jpi M1 π 0 x) (fun _ => id) (fun k hk => absurd hk (Nat.not_lt_zero k)))
    show (0 : EReal) ≤ (0 : EReal) + ((1 : ℝ) : EReal) * ((M1.g x : ℝ) : EReal)
    simp [M1]

theorem J1_nonpos (x : ℝ) : J M1 1 x ≤ 0 := by
  unfold J
  refine iSup₂_le fun π _ => ?_
  show erealIntegral (M1.Q (x, π 0 x)) (fun x' => (0 + ((1 : ℝ) : EReal) *
      (M1.r (x, π 0 x) : EReal)) + ((1 * M1.β : ℝ) : EReal) * ((M1.g x' : ℝ) : EReal)) ≤ 0
  apply erealIntegral_nonpos
  intro x'
  have hr := r_nonpos (x, π 0 x)
  have hg : M1.g x' = 0 := rfl
  rw [hg]
  simp only [zero_add, EReal.coe_one, one_mul, EReal.coe_zero, mul_zero, add_zero]
  exact_mod_cast hr

end CashCex

open CashCex in
theorem solution : ¬ (∀ (M : StationaryMarkovDecisionModel ℝ ℝ) (cu cd : ℝ)
    (hcu : 0 < cu) (hcd : 0 < cd) (L : ℝ → ℝ) (hL_nonneg : ∀ x, 0 ≤ L x) (hL0 : L 0 = 0)
    (hL_convex : ConvexOn ℝ Set.univ L)
    (hL_coercive : Filter.Tendsto (fun x => L x / |x|) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun x => L x / |x|) Filter.atBot Filter.atTop)
    (μZ : Measure ℝ) [IsProbabilityMeasure μZ] (hZ_integrable : Integrable id μZ)
    (hD : M.D = Set.univ) (hg : M.g = 0)
    (hQ : ∀ x a : ℝ, M.Q (x, a) = μZ.map (fun z => a - z))
    (hr : ∀ x a : ℝ, M.r (x, a) = -(cu * (max (a - x) 0) + cd * (max (-(a - x)) 0)) - L a)
    (N : ℕ),
    J M 0 = 0 ∧
    ∃ Sminus Splus : ℕ → ℝ,
      (∀ n, 1 ≤ n → n ≤ N → Sminus n ≤ Splus n ∧
        ∀ x : ℝ, J M n x =
          if x < Sminus n then
            ((Sminus n - x) * cu + L (Sminus n) : EReal) +
              (M.β : EReal) * erealIntegral μZ (fun z => J M (n - 1) (Sminus n - z))
          else if x ≤ Splus n then
            (L x : EReal) + (M.β : EReal) * erealIntegral μZ (fun z => J M (n - 1) (x - z))
          else
            ((x - Splus n) * cd + L (Splus n) : EReal) +
              (M.β : EReal) * erealIntegral μZ (fun z => J M (n - 1) (Splus n - z))) ∧
      Jpi M (fun k x =>
          if x < Sminus (N - k) then Sminus (N - k)
          else if x ≤ Splus (N - k) then x else Splus (N - k)) N = J M N) := by
  intro h
  have hcoer : Filter.Tendsto (fun x : ℝ => x ^ 2 / |x|) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun x : ℝ => x ^ 2 / |x|) Filter.atBot Filter.atTop := by
    have e : ∀ x : ℝ, x ≠ 0 → x ^ 2 / |x| = |x| := by
      intro x hx
      rw [← sq_abs, pow_two, mul_div_assoc, div_self (abs_ne_zero.mpr hx), mul_one]
    constructor
    · refine Filter.Tendsto.congr' ?_ (Filter.tendsto_abs_atTop_atTop)
      filter_upwards [Filter.eventually_ne_atTop 0] with x hx
      exact (e x hx).symm
    · refine Filter.Tendsto.congr' ?_ (Filter.tendsto_abs_atBot_atTop)
      filter_upwards [Filter.eventually_ne_atBot 0] with x hx
      exact (e x hx).symm
  have hQ : ∀ x a : ℝ, M1.Q (x, a) = (Measure.dirac (0 : ℝ)).map (fun z => a - z) := by
    intro x a
    rw [Measure.map_dirac]
    show Kernel.deterministic (fun xa : ℝ × ℝ => xa.2) measurable_snd (x, a) = _
    rw [Kernel.deterministic_apply]
    simp
  obtain ⟨_, Sm, Sp, hS, _⟩ := h M1 1 1 one_pos one_pos (fun x => x ^ 2)
    (fun x => sq_nonneg x) (by norm_num) (even_two.convexOn_pow) hcoer
    (Measure.dirac 0) (integrable_dirac (by simp)) rfl rfl hQ
    (fun x a => by simp [M1, tc]) 1
  obtain ⟨_, hJ⟩ := hS 1 le_rfl le_rfl
  have key := hJ (Sm 1 - 1)
  rw [if_pos (by linarith)] at key
  have hz : (fun z => J M1 (1 - 1) (Sm 1 - z)) = fun _ => (0 : EReal) := by
    funext z
    exact J0 _
  rw [hz, erealIntegral_zero, mul_zero, add_zero] at key
  have hle := J1_nonpos (Sm 1 - 1)
  rw [key] at hle
  have : ((Sm 1 - (Sm 1 - 1)) * 1 + (Sm 1) ^ 2 : ℝ) ≤ 0 := by
    have : (((Sm 1 - (Sm 1 - 1)) * 1 + (Sm 1) ^ 2 : ℝ) : EReal) ≤ 0 := by
      push_cast
      exact hle
    exact_mod_cast this
  nlinarith [sq_nonneg (Sm 1)]

#print axioms solution

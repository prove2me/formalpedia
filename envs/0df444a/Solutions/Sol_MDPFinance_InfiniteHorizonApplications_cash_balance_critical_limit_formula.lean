-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.cash_balance_critical_limit_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:45:10.788005+00:00
-- url     : https://prove2.me/submissions/28ec39f7-6a2f-47b4-8b3c-756d6ea24bc7

import Theorems.Thm_MDPFinance_InfiniteHorizonApplications_cash_balance_finite_horizon
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_CashBalance

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MDPFinance.InfiniteHorizonApplications

namespace CashLimit

private lemma c_nonneg (Mk : CashBalanceMarket) (x : ℝ) : 0 ≤ Mk.c x := by
  exact add_nonneg (mul_nonneg Mk.hcu.le (le_max_right _ _))
    (mul_nonneg Mk.hcd.le (le_max_right _ _))

private lemma c_integrable (Mk : CashBalanceMarket) : Integrable Mk.c Mk.μZ := by
  have := Mk.isProbμZ
  exact ((Mk.hZ_int.sup (integrable_const 0)).const_mul Mk.cu).add
    ((Mk.hZ_int.neg.sup (integrable_const 0)).const_mul Mk.cd)

private lemma zero_policy (k : ℕ) : Measurable ((fun (_ : ℕ) (_ : ℝ) => (0 : ℝ)) k) :=
  measurable_const

private lemma reset_bound (Mk : CashBalanceMarket) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n x,
      Mk.Vpi (fun _ _ => 0) n x ≤ ENNReal.ofReal (Mk.c (-x) + D) := by
  have := Mk.isProbμZ
  let E := ∫ z, Mk.c z ∂Mk.μZ
  have hE : 0 ≤ E := integral_nonneg (c_nonneg Mk)
  let D := Mk.β * E / (1 - Mk.β)
  have hD : 0 ≤ D := div_nonneg (mul_nonneg Mk.hβ0.le hE) (by linarith [Mk.hβ1])
  have hfix : Mk.β * (E + D) = D := by
    dsimp [D]
    field_simp [ne_of_gt (sub_pos.mpr Mk.hβ1)]
    ring
  refine ⟨D, hD, ?_⟩
  intro n
  induction n with
  | zero => intro x; simp [CashBalanceMarket.Vpi]
  | succ n ih =>
    intro x
    simp only [CashBalanceMarket.Vpi, zero_sub, Mk.hL0, add_zero]
    calc
      _ ≤ ENNReal.ofReal (Mk.c (-x)) + ENNReal.ofReal Mk.β *
          ∫⁻ z, ENNReal.ofReal (Mk.c z + D) ∂Mk.μZ := by
        gcongr
        simpa using ih (-z)
      _ = ENNReal.ofReal (Mk.c (-x) + D) := by
        have heq := ofReal_integral_eq_lintegral_ofReal
          ((c_integrable Mk).add (integrable_const D))
          (Filter.Eventually.of_forall (fun z => add_nonneg (c_nonneg Mk z) hD))
        change ENNReal.ofReal (∫ z, Mk.c z + D ∂Mk.μZ) =
          ∫⁻ z, ENNReal.ofReal (Mk.c z + D) ∂Mk.μZ at heq
        rw [← heq]
        rw [integral_add (c_integrable Mk) (integrable_const D)]
        simp only [integral_const, probReal_univ, one_smul]
        rw [← ENNReal.ofReal_mul Mk.hβ0.le, hfix, ENNReal.ofReal_add (c_nonneg Mk _) hD]

private lemma horizon_mono (Mk : CashBalanceMarket) (π : ℕ → ℝ → ℝ) :
    ∀ n x, Mk.Vpi π n x ≤ Mk.Vpi π (n+1) x := by
  intro n
  induction n generalizing π with
  | zero => intro x; exact bot_le
  | succ n ih =>
    intro x
    simp only [CashBalanceMarket.Vpi]
    gcongr with z
    exact ih _ _

private lemma value_mono (Mk : CashBalanceMarket) (x : ℝ) :
    Monotone (fun n => Mk.Jn n x) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold CashBalanceMarket.Jn
  exact iInf_mono (fun π => iInf_mono (fun _ => horizon_mono Mk π n x))

private lemma c_bound (Mk : CashBalanceMarket) (x : ℝ) :
    Mk.c (-x) ≤ (Mk.cu + Mk.cd) * |x| := by
  have h₁ : max (-x) 0 ≤ |x| := max_le (neg_le_abs x) (abs_nonneg x)
  have h₂ : max (-(-x)) 0 ≤ |x| := max_le (by simpa using le_abs_self x) (abs_nonneg x)
  have := mul_le_mul_of_nonneg_left h₁ Mk.hcu.le
  have := mul_le_mul_of_nonneg_left h₂ Mk.hcd.le
  unfold CashBalanceMarket.c
  nlinarith

private lemma c_add_le (Mk : CashBalanceMarket) (u v : ℝ) :
    Mk.c (u + v) ≤ Mk.c u + Mk.c v := by
  have hp : max (u+v) 0 ≤ max u 0 + max v 0 :=
    max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have hm : max (-(u+v)) 0 ≤ max (-u) 0 + max (-v) 0 := by
    rw [neg_add]
    exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have := mul_le_mul_of_nonneg_left hp Mk.hcu.le
  have := mul_le_mul_of_nonneg_left hm Mk.hcd.le
  unfold CashBalanceMarket.c
  linarith

private lemma value_shift (Mk : CashBalanceMarket) (n : ℕ) (x y : ℝ) :
    Mk.Jn n x ≤ ENNReal.ofReal (Mk.c (y-x)) + Mk.Jn n y := by
  classical
  unfold CashBalanceMarket.Jn
  simp only [ENNReal.add_iInf]
  refine le_iInf fun π => le_iInf fun hπ => ?_
  let ρ : ℕ → ℝ → ℝ := fun k => if k=0 then fun _ => π 0 y else π k
  have hρ : IsCBPolicy ρ := by
    intro k
    by_cases hk : k=0
    · simp [ρ, hk]
    · simpa [ρ, hk] using hπ k
  apply iInf_le_of_le ρ
  apply iInf_le_of_le hρ
  cases n with
  | zero => simp [CashBalanceMarket.Vpi]
  | succ n =>
    have ht : (fun k => ρ (k+1)) = (fun k => π (k+1)) := by
      funext k; simp [ρ]
    simp only [CashBalanceMarket.Vpi, ρ, if_pos rfl, ht]
    have hcost : Mk.c (π 0 y - x) + Mk.L (π 0 y) ≤
        Mk.c (y-x) + (Mk.c (π 0 y-y) + Mk.L (π 0 y)) := by
      have hh := c_add_le Mk (y-x) (π 0 y-y)
      ring_nf at hh ⊢
      linarith
    calc
      _ ≤ ENNReal.ofReal (Mk.c (y-x) + (Mk.c (π 0 y-y) + Mk.L (π 0 y))) +
          ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Vpi (fun k => π (k+1)) n (π 0 y-z) ∂Mk.μZ :=
        add_le_add (ENNReal.ofReal_le_ofReal hcost) le_rfl
      _ = _ := by rw [ENNReal.ofReal_add (c_nonneg Mk _) (add_nonneg (c_nonneg Mk _) (Mk.hL_nonneg _)), add_assoc]

private lemma envelope (Mk : CashBalanceMarket) :
    ∃ D : ℝ, 0 ≤ D ∧ (∀ n x, Mk.Jn n x ≤ ENNReal.ofReal (Mk.c (-x)+D)) ∧
      ∀ x, Mk.Jlim x ≤ ENNReal.ofReal (Mk.c (-x)+D) := by
  obtain ⟨D, hD, hb⟩ := reset_bound Mk
  have hn : ∀ n x, Mk.Jn n x ≤ ENNReal.ofReal (Mk.c (-x)+D) := by
    intro n x
    exact iInf_le_of_le (fun _ _ => (0 : ℝ)) (iInf_le_of_le zero_policy (hb n x))
  exact ⟨D, hD, hn, fun x => iSup_le (fun n => hn n x)⟩

private lemma value_finite (Mk : CashBalanceMarket) (n : ℕ) (x : ℝ) : Mk.Jn n x ≠ ⊤ := by
  obtain ⟨D, _, hn, _⟩ := envelope Mk
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hn n x)

private lemma limit_finite (Mk : CashBalanceMarket) (x : ℝ) : Mk.Jlim x ≠ ⊤ := by
  obtain ⟨D, _, _, hlim⟩ := envelope Mk
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hlim x)

private lemma value_lipschitz (Mk : CashBalanceMarket) (n : ℕ) (x y : ℝ) :
    |(Mk.Jn n x).toReal - (Mk.Jn n y).toReal| ≤ (Mk.cu+Mk.cd)*|x-y| := by
  have hxy := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, value_finite Mk n y⟩) (value_shift Mk n x y)
  have hyx := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, value_finite Mk n x⟩) (value_shift Mk n y x)
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (value_finite Mk n y),
    ENNReal.toReal_ofReal (c_nonneg Mk _)] at hxy
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (value_finite Mk n x),
    ENNReal.toReal_ofReal (c_nonneg Mk _)] at hyx
  have hb₁ := c_bound Mk (x-y)
  have hb₂ := c_bound Mk (y-x)
  rw [neg_sub] at hb₁ hb₂
  rw [abs_sub_comm y x] at hb₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma value_continuous (Mk : CashBalanceMarket) (n : ℕ) :
    Continuous (fun x => (Mk.Jn n x).toReal) := by
  have hM : 0 ≤ Mk.cu+Mk.cd := by linarith [Mk.hcu, Mk.hcd]
  apply LipschitzWith.continuous (K := ⟨Mk.cu+Mk.cd, hM⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |(Mk.Jn n x).toReal - (Mk.Jn n y).toReal| ≤ (Mk.cu+Mk.cd)*|x-y|
  exact value_lipschitz Mk n x y

private lemma value_tendsto (Mk : CashBalanceMarket) (x : ℝ) :
    Filter.Tendsto (fun n => (Mk.Jn n x).toReal) Filter.atTop (nhds (Mk.Jlim x).toReal) :=
  (ENNReal.tendsto_toReal (limit_finite Mk x)).comp (tendsto_atTop_iSup (value_mono Mk x))

private lemma limit_lipschitz (Mk : CashBalanceMarket) (x y : ℝ) :
    |(Mk.Jlim x).toReal - (Mk.Jlim y).toReal| ≤ (Mk.cu+Mk.cd)*|x-y| := by
  exact le_of_tendsto ((value_tendsto Mk x).sub (value_tendsto Mk y)).abs
    (Filter.Eventually.of_forall (fun n => value_lipschitz Mk n x y))

private lemma limit_continuous (Mk : CashBalanceMarket) :
    Continuous (fun x => (Mk.Jlim x).toReal) := by
  have hM : 0 ≤ Mk.cu+Mk.cd := by linarith [Mk.hcu, Mk.hcd]
  apply LipschitzWith.continuous (K := ⟨Mk.cu+Mk.cd, hM⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact limit_lipschitz Mk x y

private lemma real_bound (Mk : CashBalanceMarket) {D : ℝ} (hD : 0 ≤ D)
    {u : ℝ≥0∞} {x : ℝ} (hu : u ≤ ENNReal.ofReal (Mk.c (-x)+D)) :
    u.toReal ≤ (Mk.cu+Mk.cd)*|x|+D := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (add_nonneg (c_nonneg Mk _) hD)] at hh
  exact hh.trans (add_le_add (c_bound Mk x) le_rfl)

private lemma integrable_shift (Mk : CashBalanceMarket) {f : ℝ → ℝ}
    (hf : Continuous f) {D : ℝ} (hb : ∀ x, |f x| ≤ (Mk.cu+Mk.cd)*|x|+D) (a : ℝ) :
    Integrable (fun z => f (a-z)) Mk.μZ := by
  have := Mk.isProbμZ
  apply (((integrable_const |a|).add Mk.hZ_int.abs).const_mul (Mk.cu+Mk.cd) |>.add
    (integrable_const D)).mono' (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  calc
    |f (a-z)| ≤ (Mk.cu+Mk.cd)*|a-z|+D := hb _
    _ ≤ (Mk.cu+Mk.cd)*(|a|+|z|)+D := by
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_sub a z)
        (add_nonneg Mk.hcu.le Mk.hcd.le)) le_rfl

private lemma moving_value_tendsto (Mk : CashBalanceMarket) {r : ℕ → ℕ}
    (hr : Filter.Tendsto r Filter.atTop Filter.atTop) {a : ℕ → ℝ} {b : ℝ}
    (ha : Filter.Tendsto a Filter.atTop (nhds b)) (z : ℝ) :
    Filter.Tendsto (fun n => (Mk.Jn (r n) (a n-z)).toReal)
      Filter.atTop (nhds (Mk.Jlim (b-z)).toReal) := by
  have he : Filter.Tendsto (fun n => (Mk.cu+Mk.cd)*|a n-b|) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := Mk.cu+Mk.cd)).mul
      (ha.sub (tendsto_const_nhds (x := b))).abs
  have hd : Filter.Tendsto
      (fun n => (Mk.Jn (r n) (a n-z)).toReal - (Mk.Jn (r n) (b-z)).toReal)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm
    · intro n
      simpa [Real.norm_eq_abs] using value_lipschitz Mk (r n) (a n-z) (b-z)
    · exact he
  have hv := (value_tendsto Mk (b-z)).comp hr
  simpa using hd.add hv

private lemma moving_expectation_tendsto (Mk : CashBalanceMarket) {r : ℕ → ℕ}
    (hr : Filter.Tendsto r Filter.atTop Filter.atTop) {a : ℕ → ℝ} {b : ℝ}
    (ha : Filter.Tendsto a Filter.atTop (nhds b)) :
    Filter.Tendsto (fun n => ∫⁻ z, Mk.Jn (r n) (a n-z) ∂Mk.μZ)
      Filter.atTop (nhds (∫⁻ z, Mk.Jlim (b-z) ∂Mk.μZ)) := by
  have := Mk.isProbμZ
  obtain ⟨D, hD, hn, hl⟩ := envelope Mk
  let M := Mk.cu+Mk.cd
  have hM : 0 ≤ M := by dsimp [M]; linarith [Mk.hcu, Mk.hcd]
  have hb : ∀ n x, |(Mk.Jn n x).toReal| ≤ M*|x|+D := by
    intro n x
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact real_bound Mk hD (hn n x)
  have hbl : ∀ x, |(Mk.Jlim x).toReal| ≤ M*|x|+D := by
    intro x
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact real_bound Mk hD (hl x)
  have hconv : Filter.Tendsto
      (fun n => ∫ z, (Mk.Jn (r n) (a n-z)).toReal ∂Mk.μZ) Filter.atTop
      (nhds (∫ z, (Mk.Jlim (b-z)).toReal ∂Mk.μZ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun z => M*(|b|+1+|z|)+D)
    · exact Filter.Eventually.of_forall (fun n =>
        ((value_continuous Mk _).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    · have he : ∀ᶠ n in Filter.atTop, |a n| < |b|+1 :=
        ha.abs.eventually (gt_mem_nhds (by linarith : |b| < |b|+1))
      exact he.mono (fun n hn => Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact (hb _ _).trans (add_le_add
          (mul_le_mul_of_nonneg_left ((abs_sub (a n) z).trans (by linarith)) hM) le_rfl)))
    · exact (((integrable_const (|b|+1)).add Mk.hZ_int.abs).const_mul M).add (integrable_const D)
    · exact Filter.Eventually.of_forall (moving_value_tendsto Mk hr ha)
  have hnint : ∀ n, ENNReal.ofReal (∫ z, (Mk.Jn (r n) (a n-z)).toReal ∂Mk.μZ) =
      ∫⁻ z, Mk.Jn (r n) (a n-z) ∂Mk.μZ := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrable_shift Mk (value_continuous Mk _) (hb _) _)
      (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
    simp only [ENNReal.ofReal_toReal (value_finite Mk _ _)]
  have hlint : ENNReal.ofReal (∫ z, (Mk.Jlim (b-z)).toReal ∂Mk.μZ) =
      ∫⁻ z, Mk.Jlim (b-z) ∂Mk.μZ := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrable_shift Mk (limit_continuous Mk) hbl _)
      (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
    simp only [ENNReal.ofReal_toReal (limit_finite Mk _)]
  simpa only [Function.comp_def, hnint, hlint] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconv

private lemma c_continuous (Mk : CashBalanceMarket) : Continuous Mk.c := by
  unfold CashBalanceMarket.c
  fun_prop

private lemma clip_formula (Mk : CashBalanceMarket) (n : ℕ) (Sm Sp : ℝ) (ho : Sm ≤ Sp)
    (hf : ∀ x, Mk.Jn n x =
      if x < Sm then ENNReal.ofReal ((Sm-x)*Mk.cu+Mk.L Sm) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n-1) (Sm-z) ∂Mk.μZ
      else if x ≤ Sp then ENNReal.ofReal (Mk.L x) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n-1) (x-z) ∂Mk.μZ
      else ENNReal.ofReal ((x-Sp)*Mk.cd+Mk.L Sp) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n-1) (Sp-z) ∂Mk.μZ) (x : ℝ) :
    Mk.Jn n x = ENNReal.ofReal (Mk.c (max Sm (min x Sp)-x)+Mk.L (max Sm (min x Sp))) +
      ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n-1) (max Sm (min x Sp)-z) ∂Mk.μZ := by
  rw [hf x]
  by_cases hx : x < Sm
  · have hxs : x ≤ Sp := hx.le.trans ho
    simp only [if_pos hx, min_eq_left hxs, max_eq_left hx.le]
    congr 2
    unfold CashBalanceMarket.c
    rw [max_eq_left (sub_nonneg.mpr hx.le), max_eq_right (by linarith : -(Sm-x) ≤ 0)]
    ring
  · by_cases hp : x ≤ Sp
    · simp [hx, hp, max_eq_right (not_lt.mp hx), CashBalanceMarket.c]
    · have hsx : Sp ≤ x := (not_le.mp hp).le
      simp only [if_neg hx, if_neg hp, min_eq_right hsx, max_eq_right ho]
      congr 2
      unfold CashBalanceMarket.c
      rw [max_eq_right (sub_nonpos.mpr hsx), max_eq_left (by linarith : 0 ≤ -(Sp-x))]
      ring

private lemma limiting_formula (Mk : CashBalanceMarket) (Smn Spn : ℕ → ℝ)
    (hf : ∀ n, 1 ≤ n → Smn n ≤ Spn n ∧ ∀ x, Mk.Jn n x =
      if x < Smn n then ENNReal.ofReal ((Smn n-x)*Mk.cu+Mk.L (Smn n)) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n-1) (Smn n-z) ∂Mk.μZ
      else if x ≤ Spn n then ENNReal.ofReal (Mk.L x) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n-1) (x-z) ∂Mk.μZ
      else ENNReal.ofReal ((x-Spn n)*Mk.cd+Mk.L (Spn n)) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n-1) (Spn n-z) ∂Mk.μZ)
    (φ : ℕ → ℕ) (Sm Sp : ℝ) (hφ : StrictMono φ)
    (hm : Filter.Tendsto (Smn ∘ φ) Filter.atTop (nhds Sm))
    (hp : Filter.Tendsto (Spn ∘ φ) Filter.atTop (nhds Sp)) (x : ℝ) :
    Mk.Jlim x =
      if x < Sm then ENNReal.ofReal ((Sm-x)*Mk.cu+Mk.L Sm) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (Sm-z) ∂Mk.μZ
      else if x ≤ Sp then ENNReal.ofReal (Mk.L x) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (x-z) ∂Mk.μZ
      else ENNReal.ofReal ((x-Sp)*Mk.cd+Mk.L Sp) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (Sp-z) ∂Mk.μZ := by
  have hn : ∀ᶠ n in Filter.atTop, 1 ≤ φ n :=
    hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop 1)
  have ho : Sm ≤ Sp := le_of_tendsto_of_tendsto hm hp (hn.mono (fun n hn => (hf _ hn).1))
  let a : ℕ → ℝ := fun n => max (Smn (φ n)) (min x (Spn (φ n)))
  let b : ℝ := max Sm (min x Sp)
  have ha : Filter.Tendsto a Filter.atTop (nhds b) := hm.max (tendsto_const_nhds.min hp)
  have hL : Continuous Mk.L := continuousOn_univ.mp (Mk.hL_convex.continuousOn isOpen_univ)
  have hc : Filter.Tendsto
      (fun n => ENNReal.ofReal (Mk.c (a n-x)+Mk.L (a n))) Filter.atTop
      (nhds (ENNReal.ofReal (Mk.c (b-x)+Mk.L b))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((((c_continuous Mk).tendsto _).comp (ha.sub tendsto_const_nhds)).add ((hL.tendsto _).comp ha))
  have hi := moving_expectation_tendsto Mk
    ((Filter.tendsto_sub_atTop_nat 1).comp hφ.tendsto_atTop) ha
  have hright := hc.add (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Mk.β) hi (Or.inr ENNReal.ofReal_ne_top))
  have hleft : Filter.Tendsto (fun n => Mk.Jn (φ n) x) Filter.atTop (nhds (Mk.Jlim x)) :=
    (tendsto_atTop_iSup (value_mono Mk x)).comp hφ.tendsto_atTop
  have he : Mk.Jlim x = ENNReal.ofReal (Mk.c (b-x)+Mk.L b) +
      ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (b-z) ∂Mk.μZ := by
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    exact hn.mono (fun n hn => (clip_formula Mk _ _ _ (hf _ hn).1 (hf _ hn).2 x).symm)
  rw [he]
  dsimp [b]
  by_cases hx : x < Sm
  · have hxs : x ≤ Sp := hx.le.trans ho
    simp only [if_pos hx, min_eq_left hxs, max_eq_left hx.le]
    congr 2
    unfold CashBalanceMarket.c
    rw [max_eq_left (sub_nonneg.mpr hx.le), max_eq_right (by linarith : -(Sm-x) ≤ 0)]
    ring
  · by_cases hxp : x ≤ Sp
    · simp [hx, hxp, max_eq_right (not_lt.mp hx), CashBalanceMarket.c]
    · have hsx : Sp ≤ x := (not_le.mp hxp).le
      simp only [if_neg hx, if_neg hxp, min_eq_right hsx, max_eq_right ho]
      congr 2
      unfold CashBalanceMarket.c
      rw [max_eq_right (sub_nonpos.mpr hsx), max_eq_left (by linarith : 0 ≤ -(Sp-x))]
      ring

end CashLimit

open CashLimit

theorem solution (Mk : CashBalanceMarket) :
    (∀ n, ConvexOn ℝ Set.univ (fun x => (Mk.Jn n x).toReal)) ∧
      (∃ Sminus Splus : ℕ → ℝ,
        (∀ n, 1 ≤ n → Sminus n ≤ Splus n ∧ ∀ x, Mk.Jn n x =
          if x < Sminus n then
            ENNReal.ofReal ((Sminus n - x) * Mk.cu + Mk.L (Sminus n)) +
              ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (Sminus n - z) ∂Mk.μZ
          else if x ≤ Splus n then
            ENNReal.ofReal (Mk.L x) + ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (x - z) ∂Mk.μZ
          else
            ENNReal.ofReal ((x - Splus n) * Mk.cd + Mk.L (Splus n)) +
              ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (Splus n - z) ∂Mk.μZ) ∧
        ∀ (φ : ℕ → ℕ) (Sm Sp : ℝ), StrictMono φ →
          Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm) →
          Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp) →
          (∀ x, Mk.Jlim x =
            if x < Sm then
              ENNReal.ofReal ((Sm - x) * Mk.cu + Mk.L Sm) +
                ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (Sm - z) ∂Mk.μZ
            else if x ≤ Sp then
              ENNReal.ofReal (Mk.L x) + ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (x - z) ∂Mk.μZ
            else
              ENNReal.ofReal ((x - Sp) * Mk.cd + Mk.L Sp) +
                ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (Sp - z) ∂Mk.μZ)) := by
  obtain ⟨hc, Smn, Spn, hf⟩ := cash_balance_finite_horizon Mk
  exact ⟨hc, Smn, Spn, hf, limiting_formula Mk Smn Spn hf⟩

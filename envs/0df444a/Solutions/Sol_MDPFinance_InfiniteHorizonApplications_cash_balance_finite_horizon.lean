-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.cash_balance_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:53:23.713593+00:00
-- url     : https://prove2.me/submissions/7de0158f-f497-4b2e-8ec2-14760f049da4

import Definitions.Def_MDPFinance_InfiniteHorizonApplications_CashBalance

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MDPFinance.InfiniteHorizonApplications

namespace CashFinite

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

private lemma convex_continuous {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    Continuous f := by
  exact continuousOn_univ.mp (hf.continuousOn isOpen_univ)

private lemma tilted_min (Mk : CashBalanceMarket) {H : ℝ → ℝ}
    (hH : Continuous H) (hlow : ∀ x, Mk.L x ≤ H x) (q : ℝ) :
    ∃ s, ∀ a, H s + q*s ≤ H a + q*a := by
  let F := fun x => H x + q*x
  let B := |q| + |F 0| + 1
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1
    (Mk.hL_coercive.1.eventually (Filter.eventually_ge_atTop B))
  obtain ⟨V, hV⟩ := Filter.eventually_atBot.1
    (Mk.hL_coercive.2.eventually (Filter.eventually_ge_atTop B))
  let R := max (max |U| |V|) 1
  have hR : 1 ≤ R := le_max_right _ _
  have hUR : |U| ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hVR : |V| ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hout : ∀ x, R < |x| → F 0 ≤ F x := by
    intro x hx
    have hr : B ≤ Mk.L x / |x| := by
      by_cases hs : 0 ≤ x
      · apply hU
        have := le_abs_self U
        rw [abs_of_nonneg hs] at hx
        linarith
      · apply hV
        have := neg_le_abs V
        rw [abs_of_neg (lt_of_not_ge hs)] at hx
        linarith
    have hh := (le_div_iff₀ (show 0 < |x| by linarith)).mp hr
    have hq : -(|q| * |x|) ≤ q*x := by
      simpa [abs_mul] using neg_abs_le (q*x)
    have hz := le_abs_self (F 0)
    have hz0 := abs_nonneg (F 0)
    have hl := hlow x
    dsimp [B, F] at *
    nlinarith
  have hc : Continuous F := hH.add (continuous_const.mul continuous_id)
  obtain ⟨s, hs, hm⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩) hc.continuousOn
  refine ⟨s, fun a => ?_⟩
  by_cases ha : a ∈ Set.Icc (-R) R
  · exact hm ha
  · exact (hm (show (0:ℝ) ∈ Set.Icc (-R) R by constructor <;> linarith)).trans
      (hout a (lt_of_not_ge (fun h => ha (abs_le.mp h))))

private lemma convex_right_min {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {s x y : ℝ} (hm : ∀ a, f s ≤ f a) (hsx : s ≤ x) (hxy : x ≤ y) :
    f x ≤ f y := by
  rcases hsx.eq_or_lt with rfl | hsx
  · exact hm y
  rcases hxy.eq_or_lt with rfl | hxy
  · rfl
  have hh := hf.slope_mono_adjacent (Set.mem_univ s) (Set.mem_univ y) hsx hxy
  have hfirst : 0 ≤ (f x - f s)/(x-s) := div_nonneg (sub_nonneg.mpr (hm x)) (by linarith)
  have hlast : 0 ≤ (f y - f x)/(y-x) := hfirst.trans hh
  have := (le_div_iff₀ (sub_pos.mpr hxy)).mp hlast
  linarith

private lemma convex_left_min {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {s x y : ℝ} (hm : ∀ a, f s ≤ f a) (hxy : x ≤ y) (hys : y ≤ s) :
    f y ≤ f x := by
  rcases hys.eq_or_lt with rfl | hys
  · exact hm x
  rcases hxy.eq_or_lt with rfl | hxy
  · rfl
  have hh := hf.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ s) hxy hys
  have hlast : (f s - f y)/(s-y) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hm y)) (by linarith)
  have hfirst : (f y - f x)/(y-x) ≤ 0 := hh.trans hlast
  have := (div_le_iff₀ (sub_pos.mpr hxy)).mp hfirst
  linarith

private lemma c_pos (Mk : CashBalanceMarket) {z : ℝ} (hz : 0 ≤ z) :
    Mk.c z = z*Mk.cu := by
  simp [CashBalanceMarket.c, max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), mul_comm]

private lemma c_neg (Mk : CashBalanceMarket) {z : ℝ} (hz : z ≤ 0) :
    Mk.c z = (-z)*Mk.cd := by
  simp [CashBalanceMarket.c, max_eq_right hz, max_eq_left (neg_nonneg.mpr hz), mul_comm]

private lemma threshold_min (Mk : CashBalanceMarket) {H : ℝ → ℝ}
    (hH : ConvexOn ℝ Set.univ H) (hlow : ∀ x, Mk.L x ≤ H x) :
    ∃ Sm Sp, Sm ≤ Sp ∧ ∀ x a,
      Mk.c (cbRule Sm Sp x - x) + H (cbRule Sm Sp x) ≤ Mk.c (a-x) + H a := by
  obtain ⟨Sm, hm⟩ := tilted_min Mk (convex_continuous hH) hlow Mk.cu
  obtain ⟨Sp, hp⟩ := tilted_min Mk (convex_continuous hH) hlow (-Mk.cd)
  have horder : Sm ≤ Sp := by
    have := hm Sp
    have := hp Sm
    nlinarith [Mk.hcu, Mk.hcd]
  have htilt : ∀ q : ℝ, ConvexOn ℝ Set.univ (fun a => H a + q*a) := by
    intro q
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hH.2 hx hy ha hb hab
    simp only [smul_eq_mul] at *
    nlinarith
  have hcu := htilt Mk.cu
  have hcd := htilt (-Mk.cd)
  refine ⟨Sm, Sp, horder, ?_⟩
  intro x a
  by_cases hx : x < Sm
  · simp only [cbRule, if_pos hx]
    rw [c_pos Mk (by linarith)]
    by_cases ha : x ≤ a
    · rw [c_pos Mk (sub_nonneg.mpr ha)]
      have := hm a
      linarith
    · rw [c_neg Mk (by linarith)]
      have hh := convex_left_min hcd hp (show a ≤ x by linarith) (show x ≤ Sp by linarith)
      have := hm x
      linarith
  · by_cases hx' : x ≤ Sp
    · simp only [cbRule, if_neg hx, if_pos hx', sub_self]
      rw [c_pos Mk (z := 0) le_rfl, zero_mul, zero_add]
      by_cases ha : x ≤ a
      · rw [c_pos Mk (sub_nonneg.mpr ha)]
        have hh := convex_right_min hcu hm (show Sm ≤ x by linarith) ha
        linarith
      · rw [c_neg Mk (by linarith)]
        have hh := convex_left_min hcd hp (show a ≤ x by linarith) hx'
        linarith
    · simp only [cbRule, if_neg hx, if_neg hx']
      rw [c_neg Mk (by linarith)]
      by_cases ha : a ≤ x
      · rw [c_neg Mk (sub_nonpos.mpr ha)]
        have := hp a
        linarith
      · rw [c_pos Mk (by linarith)]
        have hh := convex_right_min hcu hm (show Sm ≤ x by linarith) (show x ≤ a by linarith)
        have := hp x
        linarith
private noncomputable def H (Mk : CashBalanceMarket) (n : ℕ) (a : ℝ) : ℝ :=
  Mk.L a + Mk.β * ∫ z, (Mk.Jn n (a-z)).toReal ∂Mk.μZ

private lemma J_integrable (Mk : CashBalanceMarket) (n : ℕ) (a : ℝ) :
    Integrable (fun z => (Mk.Jn n (a-z)).toReal) Mk.μZ := by
  obtain ⟨D, hD, hb, _⟩ := envelope Mk
  apply integrable_shift Mk (value_continuous Mk n) (D := D) _ a
  intro x
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact real_bound Mk hD (hb n x)

private lemma H_lower (Mk : CashBalanceMarket) (n : ℕ) (a : ℝ) : Mk.L a ≤ H Mk n a := by
  have hi : 0 ≤ ∫ z, (Mk.Jn n (a-z)).toReal ∂Mk.μZ := integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  dsimp [H]
  nlinarith [Mk.hβ0]

private lemma H_convex (Mk : CashBalanceMarket) (n : ℕ)
    (hc : ConvexOn ℝ Set.univ (fun x => (Mk.Jn n x).toReal)) :
    ConvexOn ℝ Set.univ (H Mk n) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hl := Mk.hL_convex.2 hx hy ha hb hab
  have hi : (∫ z, (Mk.Jn n (a*x+b*y-z)).toReal ∂Mk.μZ) ≤
      a*(∫ z, (Mk.Jn n (x-z)).toReal ∂Mk.μZ) +
      b*(∫ z, (Mk.Jn n (y-z)).toReal ∂Mk.μZ) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((J_integrable Mk n x).const_mul a) ((J_integrable Mk n y).const_mul b)]
    apply integral_mono (J_integrable Mk n _) (((J_integrable Mk n x).const_mul a).add
      ((J_integrable Mk n y).const_mul b))
    intro z
    have he : a*x+b*y-z = a*(x-z)+b*(y-z) := by linear_combination z * hab
    change (Mk.Jn n (a*x+b*y-z)).toReal ≤ a*(Mk.Jn n (x-z)).toReal+b*(Mk.Jn n (y-z)).toReal
    rw [he]
    exact hc.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  simp only [smul_eq_mul] at *
  dsimp [H]
  nlinarith [Mk.hβ0]

private lemma step_eq (Mk : CashBalanceMarket) (n : ℕ) (x a : ℝ) :
    ENNReal.ofReal (Mk.c (a-x) + H Mk n a) =
      ENNReal.ofReal (Mk.c (a-x) + Mk.L a) + ENNReal.ofReal Mk.β *
        ∫⁻ z, Mk.Jn n (a-z) ∂Mk.μZ := by
  have hn : 0 ≤ ∫ z, (Mk.Jn n (a-z)).toReal ∂Mk.μZ := integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  have he := ofReal_integral_eq_lintegral_ofReal (J_integrable Mk n a)
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
  have he' : ENNReal.ofReal (∫ z, (Mk.Jn n (a-z)).toReal ∂Mk.μZ) =
      ∫⁻ z, Mk.Jn n (a-z) ∂Mk.μZ := by
    rw [he]
    congr 1
    funext z
    exact ENNReal.ofReal_toReal (value_finite Mk n _)
  dsimp [H]
  rw [← add_assoc, ENNReal.ofReal_add (add_nonneg (c_nonneg Mk _) (Mk.hL_nonneg _))
    (mul_nonneg Mk.hβ0.le hn), ENNReal.ofReal_mul Mk.hβ0.le, he']

private lemma rule_measurable (Sm Sp : ℝ) : Measurable (cbRule Sm Sp) := by
  unfold cbRule
  exact measurable_const.piecewise (measurableSet_lt measurable_id measurable_const)
    (measurable_id.piecewise (measurableSet_le measurable_id measurable_const) measurable_const)

private lemma bellman_attained (Mk : CashBalanceMarket) (n : ℕ)
    {π : ℕ → ℝ → ℝ} (hπ : IsCBPolicy π) (hopt : ∀ x, Mk.Vpi π n x = Mk.Jn n x)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hmin : ∀ x a, Mk.c (f x-x) + H Mk n (f x) ≤ Mk.c (a-x) + H Mk n a) :
    ∃ ρ, IsCBPolicy ρ ∧ (∀ x, Mk.Vpi ρ (n+1) x = Mk.Jn (n+1) x) ∧
      ∀ x, Mk.Jn (n+1) x = ENNReal.ofReal (Mk.c (f x-x) + H Mk n (f x)) := by
  let ρ : ℕ → ℝ → ℝ := fun k => if k=0 then f else π (k-1)
  have hρ : IsCBPolicy ρ := by
    intro k
    by_cases hk : k=0
    · simpa [ρ, hk] using hf
    · simpa [ρ, hk] using hπ (k-1)
  have htail : (fun k => ρ (k+1)) = π := by funext k; simp [ρ]
  have hval : ∀ x, Mk.Vpi ρ (n+1) x = ENNReal.ofReal (Mk.c (f x-x) + H Mk n (f x)) := by
    intro x
    rw [step_eq]
    simp only [CashBalanceMarket.Vpi, htail, hopt, ρ, if_pos rfl]
  have hj : ∀ x, Mk.Jn (n+1) x = ENNReal.ofReal (Mk.c (f x-x) + H Mk n (f x)) := by
    intro x
    apply le_antisymm
    · exact iInf_le_of_le ρ (iInf_le_of_le hρ (hval x).le)
    · apply le_iInf fun σ => le_iInf fun hσ => ?_
      calc
        _ ≤ ENNReal.ofReal (Mk.c (σ 0 x-x) + H Mk n (σ 0 x)) :=
          ENNReal.ofReal_le_ofReal (hmin x _)
        _ ≤ Mk.Vpi σ (n+1) x := by
          rw [step_eq, CashBalanceMarket.Vpi]
          gcongr with z
          exact iInf_le_of_le (fun k => σ (k+1))
            (iInf_le_of_le (fun k => hσ (k+1)) le_rfl)
  exact ⟨ρ, hρ, fun x => (hval x).trans (hj x).symm, hj⟩

private lemma c_convex (Mk : CashBalanceMarket) : ConvexOn ℝ Set.univ Mk.c := by
  have hi : ConvexOn ℝ Set.univ (fun x : ℝ => x) := convexOn_id convex_univ
  have hn : ConvexOn ℝ Set.univ (fun x : ℝ => -x) := (concaveOn_id convex_univ).neg
  exact (ConvexOn.smul Mk.hcu.le (hi.sup (convexOn_const _ convex_univ))).add
    (ConvexOn.smul Mk.hcd.le (hn.sup (convexOn_const _ convex_univ)))

private lemma minimized_convex (Mk : CashBalanceMarket) {H v f : ℝ → ℝ}
    (hH : ConvexOn ℝ Set.univ H)
    (hv : ∀ x, v x = Mk.c (f x-x) + H (f x))
    (hm : ∀ x a, v x ≤ Mk.c (a-x)+H a) : ConvexOn ℝ Set.univ v := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hH.2 (Set.mem_univ (f x)) (Set.mem_univ (f y)) ha hb hab
  have ht := (c_convex Mk).2 (Set.mem_univ (f x-x)) (Set.mem_univ (f y-y)) ha hb hab
  have h := hm (a*x+b*y) (a*f x+b*f y)
  have he : a*f x+b*f y-(a*x+b*y) = a*(f x-x)+b*(f y-y) := by ring
  simp only [smul_eq_mul] at *
  rw [he] at h
  rw [hv x, hv y]
  linarith
private lemma stage (Mk : CashBalanceMarket) : ∀ n,
    ConvexOn ℝ Set.univ (fun x => (Mk.Jn n x).toReal) ∧
    (∃ π, IsCBPolicy π ∧ ∀ x, Mk.Vpi π n x = Mk.Jn n x) ∧
    (1 ≤ n → ∃ Sm Sp, Sm ≤ Sp ∧ ∀ x,
      Mk.Jn n x = ENNReal.ofReal (Mk.c (cbRule Sm Sp x-x) + H Mk (n-1) (cbRule Sm Sp x))) := by
  intro n
  induction n with
  | zero =>
    have hz : ∀ x, Mk.Jn 0 x = 0 := by
      intro x
      apply le_antisymm _ bot_le
      exact iInf_le_of_le (fun _ _ => (0:ℝ)) (iInf_le_of_le zero_policy (by simp [CashBalanceMarket.Vpi]))
    refine ⟨?_, ⟨fun _ _ => 0, zero_policy, ?_⟩, by omega⟩
    · simp only [hz, ENNReal.toReal_zero]
      exact convexOn_const _ convex_univ
    · intro x; simp [CashBalanceMarket.Vpi, hz]
  | succ n ih =>
    obtain ⟨hc, ⟨π, hπ, hopt⟩, _⟩ := ih
    have hH := H_convex Mk n hc
    obtain ⟨Sm, Sp, horder, hm⟩ := threshold_min Mk hH (H_lower Mk n)
    obtain ⟨ρ, hρ, ho, hv⟩ := bellman_attained Mk n hπ hopt (rule_measurable Sm Sp) hm
    have hnn : ∀ x, 0 ≤ Mk.c (cbRule Sm Sp x-x) + H Mk n (cbRule Sm Sp x) := by
      intro x
      exact add_nonneg (c_nonneg Mk _) ((Mk.hL_nonneg _).trans (H_lower Mk n _))
    have hvr : ∀ x, (Mk.Jn (n+1) x).toReal = Mk.c (cbRule Sm Sp x-x) + H Mk n (cbRule Sm Sp x) := by
      intro x
      rw [hv x, ENNReal.toReal_ofReal (hnn x)]
    refine ⟨minimized_convex Mk hH hvr ?_, ⟨ρ, hρ, ho⟩, ?_⟩
    · intro x a; rw [hvr x]; exact hm x a
    · intro _
      exact ⟨Sm, Sp, horder, by simpa only [Nat.add_sub_cancel] using hv⟩

end CashFinite

open CashFinite

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
              ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (Splus n - z) ∂Mk.μZ)) := by
  classical
  have hs : ∀ n, ∃ Sm Sp, Sm ≤ Sp ∧ (1 ≤ n → ∀ x,
      Mk.Jn n x = ENNReal.ofReal (Mk.c (cbRule Sm Sp x-x) + H Mk (n-1) (cbRule Sm Sp x))) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨Sm, Sp, ho, hf⟩ := (stage Mk n).2.2 hn
      exact ⟨Sm, Sp, ho, fun _ => hf⟩
    · exact ⟨0, 0, le_rfl, fun h => (hn h).elim⟩
  choose Sm Sp horder hf using hs
  refine ⟨fun n => (stage Mk n).1, Sm, Sp, fun n hn => ⟨horder n, ?_⟩⟩
  intro x
  rw [hf n hn x, step_eq]
  by_cases hx : x < Sm n
  · simp only [cbRule, if_pos hx]
    rw [c_pos Mk (by linarith)]
  · by_cases hx' : x ≤ Sp n
    · simp only [cbRule, if_neg hx, if_pos hx', sub_self]
      rw [c_pos Mk (z := 0) le_rfl, zero_mul, zero_add]
    · simp only [cbRule, if_neg hx, if_neg hx']
      rw [c_neg Mk (by linarith)]
      congr 2; ring

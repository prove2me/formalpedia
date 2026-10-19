-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.theorem_7_6_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:33:06.806527+00:00
-- url     : https://prove2.me/submissions/9d6c6ba6-d851-460a-b290-1be26854b9ef

import Theorems.Thm_MDPFinance_InfiniteHorizonApplications_cash_balance_critical_limit_formula
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_CashBalance

open MeasureTheory ProbabilityTheory
open MDPFinance.InfiniteHorizonApplications

namespace CashVerification

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

private lemma finite_value (Mk : CashBalanceMarket) : ∀ x, Mk.Jinf x < ⊤ := by
  obtain ⟨D, hD, hb⟩ := reset_bound Mk
  intro x
  have hi : Mk.Jinf x ≤ Mk.Jinfpi (fun _ _ => 0) x := by
    unfold CashBalanceMarket.Jinf
    exact iInf_le_of_le (fun _ _ => (0 : ℝ)) (iInf_le_of_le zero_policy le_rfl)
  exact lt_of_le_of_lt (hi.trans (iSup_le (fun n => hb n x))) ENNReal.ofReal_lt_top

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

private lemma lower_bound (Mk : CashBalanceMarket) (x : ℝ) : Mk.Jlim x ≤ Mk.Jinf x := by
  unfold CashBalanceMarket.Jlim CashBalanceMarket.Jinf CashBalanceMarket.Jn CashBalanceMarket.Jinfpi
  apply iSup_le
  intro n
  apply le_iInf
  intro π
  apply le_iInf
  intro hπ
  calc
    (⨅ π ∈ {π : ℕ → ℝ → ℝ | IsCBPolicy π}, Mk.Vpi π n x) ≤ Mk.Vpi π n x :=
      iInf_le_of_le π (iInf_le_of_le hπ le_rfl)
    _ ≤ ⨆ n, Mk.Vpi π n x := le_iSup (fun n => Mk.Vpi π n x) n

private lemma value_mono (Mk : CashBalanceMarket) (x : ℝ) :
    Monotone (fun n => Mk.Jn n x) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold CashBalanceMarket.Jn
  exact iInf_mono (fun π => iInf_mono (fun _ => horizon_mono Mk π n x))

private lemma limit_convex (Mk : CashBalanceMarket)
    (hc : ∀ n, ConvexOn ℝ Set.univ (fun x => (Mk.Jn n x).toReal)) :
    ConvexOn ℝ Set.univ (fun x => (Mk.Jlim x).toReal) := by
  have ht : ∀ x, Filter.Tendsto (fun n => (Mk.Jn n x).toReal)
      Filter.atTop (nhds (Mk.Jlim x).toReal) := by
    intro x
    exact (ENNReal.tendsto_toReal (ne_of_lt ((lower_bound Mk x).trans_lt (finite_value Mk x)))).comp
      (tendsto_atTop_iSup (value_mono Mk x))
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact le_of_tendsto_of_tendsto (ht (a • x + b • y))
    ((tendsto_const_nhds.smul (ht x)).add (tendsto_const_nhds.smul (ht y)))
    (Filter.Eventually.of_forall (fun n => (hc n).2 hx hy ha hb hab))

private lemma c_bound (Mk : CashBalanceMarket) (x : ℝ) :
    Mk.c (-x) ≤ (Mk.cu + Mk.cd) * |x| := by
  have h₁ : max (-x) 0 ≤ |x| := max_le (neg_le_abs x) (abs_nonneg x)
  have h₂ : max (-(-x)) 0 ≤ |x| := max_le (by simpa using le_abs_self x) (abs_nonneg x)
  have := mul_le_mul_of_nonneg_left h₁ Mk.hcu.le
  have := mul_le_mul_of_nonneg_left h₂ Mk.hcd.le
  unfold CashBalanceMarket.c
  nlinarith

private lemma level_bound (Mk : CashBalanceMarket) (D : ℝ) (hD : 0 ≤ D) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, Mk.L x ≤ Mk.c (-x) + D → |x| ≤ R := by
  let B := Mk.cu + Mk.cd + D + 1
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1
    (Mk.hL_coercive.1.eventually (Filter.eventually_ge_atTop B))
  obtain ⟨V, hV⟩ := Filter.eventually_atBot.1
    (Mk.hL_coercive.2.eventually (Filter.eventually_ge_atTop B))
  let R := max (max |U| |V|) 1
  have hR : 1 ≤ R := le_max_right _ _
  have hUR : |U| ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hVR : |V| ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨R, by linarith, ?_⟩
  intro x hx
  by_contra hn
  have hbig : R < |x| := lt_of_not_ge hn
  have hratio : B ≤ Mk.L x / |x| := by
    by_cases hsign : 0 ≤ x
    · apply hU
      have := le_abs_self U
      rw [abs_of_nonneg hsign] at hbig
      linarith
    · apply hV
      have := neg_le_abs V
      rw [abs_of_neg (lt_of_not_ge hsign)] at hbig
      linarith
  have hpos : 0 < |x| := by linarith
  have hlow := (le_div_iff₀ hpos).1 hratio
  have hupper := c_bound Mk x
  have hDmul : D ≤ D * |x| := by nlinarith
  dsimp [B] at hlow
  nlinarith

private lemma critical_subsequence (Mk : CashBalanceMarket) (Sminus Splus : ℕ → ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hm : ∀ n, 1 ≤ n → Mk.L (Sminus n) ≤ Mk.c (-Sminus n) + D)
    (hp : ∀ n, 1 ≤ n → Mk.L (Splus n) ≤ Mk.c (-Splus n) + D) :
    ∃ (φ : ℕ → ℕ) (Sm Sp : ℝ), StrictMono φ ∧
      Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm) ∧
      Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp) := by
  obtain ⟨R, hR, hb⟩ := level_bound Mk D hD
  have hmem : ∀ n, (Sminus (n+1), Splus (n+1)) ∈
      Set.Icc (-R) R ×ˢ Set.Icc (-R) R := by
    intro n
    exact ⟨abs_le.mp (hb _ (hm _ (by omega))), abs_le.mp (hb _ (hp _ (by omega)))⟩
  obtain ⟨z, hz, ψ, hψ, ht⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
  refine ⟨fun n => ψ n + 1, z.1, z.2, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.add_lt_add_right (hψ hij) 1
  · simpa [Function.comp_def] using (continuous_fst.tendsto z).comp ht
  · simpa [Function.comp_def] using (continuous_snd.tendsto z).comp ht

private lemma verify (Mk : CashBalanceMarket) (f : ℝ → ℝ) (hf : Measurable f)
    (hfix : ∀ x, Mk.Jlim x = ENNReal.ofReal (Mk.c (f x - x) + Mk.L (f x)) +
      ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (f x - z) ∂Mk.μZ) :
    (∀ x, Mk.Jinf x = Mk.Jlim x) ∧
      ∀ x, Mk.Jinfpi (fun _ => f) x = Mk.Jinf x := by
  have hb : ∀ n x, Mk.Vpi (fun _ => f) n x ≤ Mk.Jlim x := by
    intro n
    induction n with
    | zero => intro x; exact bot_le
    | succ n ih =>
      intro x
      rw [hfix x]
      change ENNReal.ofReal _ + ENNReal.ofReal Mk.β * ∫⁻ z, _ ∂Mk.μZ ≤ _
      gcongr with z
      exact ih _
  have hpi : ∀ x, Mk.Jinfpi (fun _ => f) x ≤ Mk.Jlim x := fun x => iSup_le (fun n => hb n x)
  have hi : ∀ x, Mk.Jinf x ≤ Mk.Jinfpi (fun _ => f) x := by
    intro x
    unfold CashBalanceMarket.Jinf
    exact iInf_le_of_le (fun _ => f) (iInf_le_of_le (fun _ => hf) le_rfl)
  refine ⟨fun x => le_antisymm ((hi x).trans (hpi x)) (lower_bound Mk x), ?_⟩
  intro x
  exact le_antisymm ((hpi x).trans (lower_bound Mk x)) (hi x)

end CashVerification

namespace CashVerification

private lemma rule_measurable (Sm Sp : ℝ) : Measurable (cbRule Sm Sp) := by
  unfold cbRule
  exact measurable_const.piecewise (measurableSet_lt measurable_id measurable_const)
    (measurable_id.piecewise (measurableSet_le measurable_id measurable_const) measurable_const)

private lemma c_of_nonneg (Mk : CashBalanceMarket) {z : ℝ} (hz : 0 ≤ z) :
    Mk.c z = z * Mk.cu := by
  simp [CashBalanceMarket.c, max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), mul_comm]

private lemma c_of_nonpos (Mk : CashBalanceMarket) {z : ℝ} (hz : z ≤ 0) :
    Mk.c z = (-z) * Mk.cd := by
  simp [CashBalanceMarket.c, max_eq_right hz, max_eq_left (neg_nonneg.mpr hz), mul_comm]

end CashVerification

open CashVerification

theorem solution (Mk : CashBalanceMarket) :
    (∀ x, Mk.Jinf x < ⊤) ∧
      ConvexOn ℝ Set.univ (fun x => (Mk.Jinf x).toReal) ∧
      (∀ x, Mk.Jinf x = Mk.Jlim x) ∧
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
        (∃ (φ : ℕ → ℕ) (Sm Sp : ℝ), StrictMono φ ∧
          Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm) ∧
          Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp)) ∧
        ∀ (φ : ℕ → ℕ) (Sm Sp : ℝ), StrictMono φ →
          Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm) →
          Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp) →
          Sm ≤ Sp ∧
          (∀ x, Mk.Jinf x =
            if x < Sm then
              ENNReal.ofReal ((Sm - x) * Mk.cu + Mk.L Sm) +
                ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jinf (Sm - z) ∂Mk.μZ
            else if x ≤ Sp then
              ENNReal.ofReal (Mk.L x) + ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jinf (x - z) ∂Mk.μZ
            else
              ENNReal.ofReal ((x - Sp) * Mk.cd + Mk.L Sp) +
                ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jinf (Sp - z) ∂Mk.μZ) ∧
          ∀ x, Mk.Jinfpi (fun _ => cbRule Sm Sp) x = Mk.Jinf x) := by

  obtain ⟨hc, Sminus, Splus, hf, hlim⟩ := cash_balance_critical_limit_formula Mk
  obtain ⟨D, hD, hb⟩ := reset_bound Mk
  have hW : ∀ n x, Mk.Jn n x ≤ ENNReal.ofReal (Mk.c (-x) + D) := by
    intro n x
    unfold CashBalanceMarket.Jn
    exact iInf_le_of_le (fun _ _ => (0 : ℝ)) (iInf_le_of_le zero_policy (hb n x))
  have hlevels : ∀ n, 1 ≤ n →
      Mk.L (Sminus n) ≤ Mk.c (-Sminus n) + D ∧
      Mk.L (Splus n) ≤ Mk.c (-Splus n) + D := by
    intro n hn
    obtain ⟨horder, hform⟩ := hf n hn
    have h₁ : ENNReal.ofReal (Mk.L (Sminus n)) ≤ Mk.Jn n (Sminus n) := by
      rw [hform, if_neg (lt_irrefl _), if_pos horder]
      exact le_self_add
    have h₂ : ENNReal.ofReal (Mk.L (Splus n)) ≤ Mk.Jn n (Splus n) := by
      rw [hform, if_neg (not_lt.mpr horder), if_pos le_rfl]
      exact le_self_add
    constructor
    · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h₁.trans (hW n _))
      simpa only [ENNReal.toReal_ofReal (Mk.hL_nonneg _),
        ENNReal.toReal_ofReal (add_nonneg (c_nonneg Mk _) hD)] using hh
    · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h₂.trans (hW n _))
      simpa only [ENNReal.toReal_ofReal (Mk.hL_nonneg _),
        ENNReal.toReal_ofReal (add_nonneg (c_nonneg Mk _) hD)] using hh
  obtain ⟨φ₀, Sm₀, Sp₀, hφ₀, hm₀, hp₀⟩ := critical_subsequence Mk Sminus Splus D hD
    (fun n hn => (hlevels n hn).1) (fun n hn => (hlevels n hn).2)
  have ordered : ∀ (φ : ℕ → ℕ) (Sm Sp : ℝ), StrictMono φ →
      Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm) →
      Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp) → Sm ≤ Sp := by
    intro φ Sm Sp hφ hm hp
    exact le_of_tendsto_of_tendsto hm hp
      ((hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop 1)).mono
        (fun n hn => (hf (φ n) hn).1))
  have bell : ∀ (φ : ℕ → ℕ) (Sm Sp : ℝ) (hφ : StrictMono φ)
      (hm : Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm))
      (hp : Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp)),
      ∀ x, Mk.Jlim x = ENNReal.ofReal (Mk.c (cbRule Sm Sp x - x) + Mk.L (cbRule Sm Sp x)) +
        ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (cbRule Sm Sp x - z) ∂Mk.μZ := by
    intro φ Sm Sp hφ hm hp x
    have hs := ordered φ Sm Sp hφ hm hp
    have he := hlim φ Sm Sp hφ hm hp x
    by_cases hlow : x < Sm
    · simpa only [cbRule, if_pos hlow, c_of_nonneg Mk (sub_nonneg.mpr hlow.le)] using he
    · by_cases hhigh : x ≤ Sp
      · simpa [cbRule, hlow, hhigh, CashBalanceMarket.c] using he
      · simpa only [cbRule, if_neg hlow, if_neg hhigh,
          c_of_nonpos Mk (sub_nonpos.mpr (not_le.mp hhigh).le), neg_sub] using he
  obtain ⟨heq, _⟩ := verify Mk (cbRule Sm₀ Sp₀) (rule_measurable _ _)
    (bell φ₀ Sm₀ Sp₀ hφ₀ hm₀ hp₀)
  refine ⟨finite_value Mk, ?_, heq, Sminus, Splus, hf,
    ⟨φ₀, Sm₀, Sp₀, hφ₀, hm₀, hp₀⟩, ?_⟩
  · simpa only [heq] using limit_convex Mk hc
  · intro φ Sm Sp hφ hm hp
    refine ⟨ordered φ Sm Sp hφ hm hp, ?_, ?_⟩
    · simpa only [heq] using hlim φ Sm Sp hφ hm hp
    · exact (verify Mk (cbRule Sm Sp) (rule_measurable _ _) (bell φ Sm Sp hφ hm hp)).2

-- Prove2me | solution 1 for MDPFinance.Contracting.theorem_7_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:39:22.890996+00:00
-- url     : https://prove2.me/submissions/45ebf4c1-f69b-4903-854e-660f06662371

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory Filter Topology
open MDPFinance.Contracting

namespace Ver734Aux

lemma toENNReal_coe_sup (t : ℝ) : ((t : EReal) ⊔ 0).toENNReal = ENNReal.ofReal t := by
  rcases le_total t 0 with h | h
  · rw [sup_of_le_right (by exact_mod_cast h)]; simp [ENNReal.ofReal_of_nonpos h]
  · rw [sup_of_le_left (by exact_mod_cast h), EReal.toENNReal_of_ne_top (EReal.coe_ne_top t)]
    simp

lemma erealIntegral_mono {E : Type*} [MeasurableSpace E] (μ : Measure E) {f g : E → EReal}
    (h : ∀ x, f x ≤ g x) : erealIntegral μ f ≤ erealIntegral μ g := by
  unfold erealIntegral
  apply add_le_add
  · apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _)
  · apply EReal.neg_le_neg_iff.2
    apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (EReal.neg_le_neg_iff.2 (h x)) _)

lemma erealIntegral_coe {E : Type*} [MeasurableSpace E] (μ : Measure E) {g : E → ℝ}
    (hg : Integrable g μ) :
    erealIntegral μ (fun y => (g y : EReal)) = ((∫ y, g y ∂μ : ℝ) : EReal) := by
  unfold erealIntegral
  have h1 : ∀ y, ((g y : EReal) ⊔ 0).toENNReal = ENNReal.ofReal (g y) :=
    fun y => toENNReal_coe_sup _
  have h2 : ∀ y, ((-(g y : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-g y) := by
    intro y; rw [← EReal.coe_neg]; exact toENNReal_coe_sup _
  simp only [h1, h2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  have f1 : ∫⁻ a, ENNReal.ofReal (g a) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (le_abs_self (g a)))
      (by simpa [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm g).1 hg.2)).ne
  have f2 : ∫⁻ a, ENNReal.ofReal (-g a) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (neg_le_abs (g a)))
      (by simpa [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm g).1 hg.2)).ne
  rw [← EReal.coe_ennreal_toReal f1, ← EReal.coe_ennreal_toReal f2, ← EReal.coe_neg,
    ← EReal.coe_add, sub_eq_add_neg]

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma b_integrable (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D) :
    Integrable b (M.Q xa) := by
  refine ⟨hb.hb_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hb.hb_nonneg)]
  exact lt_of_le_of_lt (hb.hQ xa hxa) ENNReal.ofReal_lt_top

lemma b_int_le (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D) :
    ∫ y, b y ∂(M.Q xa) ≤ αb * b xa.1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hb.hb_nonneg)
    hb.hb_meas.aestronglyMeasurable]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb.hQ xa hxa)
  rwa [ENNReal.toReal_ofReal (mul_nonneg hb.hαb (hb.hb_nonneg _))] at this

lemma v_integrable (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D)
    {v : E → ℝ} (hv : Measurable v) {c : ℝ} (hc : ∀ x, |v x| ≤ c * b x) :
    Integrable v (M.Q xa) :=
  Integrable.mono' ((b_integrable M hb hxa).const_mul c) hv.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hc y)

end Ver734Aux

open Ver734Aux in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1)
    (v : E → ℝ) (hvIBb : v ∈ IBb b) (hvfix : ∀ x, T M (fun y => (v y : EReal)) x = (v x : EReal))
    (fstar : E → A) (hfstar : IsMaximizerOf M (fun y => (v y : EReal)) fstar) :
    (∀ x, (v x : EReal) = Jinf M x) ∧ (∀ x, (v x : EReal) = Jlim M x) ∧
      ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x := by
  obtain ⟨hvm, c, hc0, hc⟩ := hvIBb
  have hβ0 := M.hβ0
  have hq0 : 0 ≤ M.β * αb := mul_nonneg hβ0.le hb.hαb
  set ε : ℕ → ℝ := fun n => (M.β * αb) ^ n * c with hε
  have hε0 : ∀ n, 0 ≤ ε n := fun n => mul_nonneg (pow_nonneg hq0 n) hc0
  have hεs : ∀ n, ε (n + 1) = M.β * αb * ε n := fun n => by simp only [hε]; ring
  -- integral of v + t * b
  have hint : ∀ xa ∈ M.D, ∀ t : ℝ,
      erealIntegral (M.Q xa) (fun y => ((v y + t * b y : ℝ) : EReal)) =
        (((∫ y, v y ∂(M.Q xa)) + t * ∫ y, b y ∂(M.Q xa) : ℝ) : EReal) := by
    intro xa hxa t
    have hI : Integrable (fun y => v y + t * b y) (M.Q xa) :=
      (v_integrable M hb hxa hvm hc).add ((b_integrable M hb hxa).const_mul t)
    rw [erealIntegral_coe _ hI, integral_add (v_integrable M hb hxa hvm hc)
      ((b_integrable M hb hxa).const_mul t), integral_const_mul]
  have hLv : ∀ xa ∈ M.D, L M (fun y => (v y : EReal)) xa =
      ((M.r xa + M.β * ∫ y, v y ∂(M.Q xa) : ℝ) : EReal) := by
    intro xa hxa
    unfold L
    rw [erealIntegral_coe _ (v_integrable M hb hxa hvm hc)]
    simp only [EReal.coe_add, EReal.coe_mul]
  -- real Bellman inequality
  have hLle : ∀ x a, (x, a) ∈ M.D → M.r (x, a) + M.β * ∫ y, v y ∂(M.Q (x, a)) ≤ v x := by
    intro x a hxa
    have h1 : L M (fun y => (v y : EReal)) (x, a) ≤ T M (fun y => (v y : EReal)) x := by
      unfold T
      exact le_biSup (fun a => L M (fun y => (v y : EReal)) (x, a)) (show a ∈ M.Dx x from hxa)
    rw [hvfix, hLv _ hxa] at h1
    exact_mod_cast h1
  have hfeq : ∀ x, M.r (x, fstar x) + M.β * ∫ y, v y ∂(M.Q (x, fstar x)) = v x := by
    intro x
    have h1 := congrFun hfstar.2 x
    rw [hvfix, hLv _ (hfstar.1.2 x)] at h1
    exact_mod_cast h1
  -- upper bound for all policies
  have hup : ∀ n (π : ℕ → E → A), IsPolicyOf M π → ∀ x,
      Jnpi M M.r π n x ≤ ((v x + ε n * b x : ℝ) : EReal) := by
    intro n
    induction n with
    | zero =>
      intro π _ x
      simp only [Jnpi]
      have := hc x
      have : (0 : ℝ) ≤ v x + ε 0 * b x := by
        simp only [hε, pow_zero, one_mul]; linarith [neg_abs_le (v x)]
      exact_mod_cast this
    | succ n ih =>
      intro π hπ x
      have hxa : (x, π 0 x) ∈ M.D := (hπ 0).2 x
      have hσ : IsPolicyOf M (fun k => π (k + 1)) := fun k => hπ (k + 1)
      simp only [Jnpi]
      have h1 := erealIntegral_mono (M.Q (x, π 0 x)) (ih _ hσ)
      rw [hint _ hxa] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : EReal) ≤ (M.β : EReal) by
        exact_mod_cast hβ0.le)
      refine le_trans (add_le_add_right h2 _) ?_
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h3 := hLle x _ hxa
      have h4 := b_int_le M hb hxa
      have h5 := mul_le_mul_of_nonneg_left h4 (hε0 n)
      rw [hεs]
      nlinarith
  -- lower bound for fstar
  have hlow : ∀ n x, (((v x - ε n * b x : ℝ)) : EReal) ≤ Jnpi M M.r (fun _ => fstar) n x := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [Jnpi]
      have := hc x
      have : v x - ε 0 * b x ≤ 0 := by
        simp only [hε, pow_zero, one_mul]; linarith [le_abs_self (v x)]
      exact_mod_cast this
    | succ n ih =>
      intro x
      have hxa : (x, fstar x) ∈ M.D := hfstar.1.2 x
      simp only [Jnpi]
      have h1 := erealIntegral_mono (M.Q (x, fstar x))
        (g := Jnpi M M.r (fun _ => fstar) n)
        (f := fun y => ((v y + (-ε n) * b y : ℝ) : EReal)) (fun y => by
          have := ih y; rw [show v y + -ε n * b y = v y - ε n * b y by ring]; exact this)
      rw [hint _ hxa] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : EReal) ≤ (M.β : EReal) by
        exact_mod_cast hβ0.le)
      refine le_trans ?_ (add_le_add_right h2 _)
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h3 := hfeq x
      have h4 := b_int_le M hb hxa
      have h5 := mul_le_mul_of_nonneg_left h4 (hε0 n)
      rw [hεs]
      nlinarith
  -- limits
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hαb).mul_const c
    simpa [hε] using this
  have hTup : ∀ x, Tendsto (fun n => ((v x + ε n * b x : ℝ) : EReal)) atTop (𝓝 (v x : EReal)) := by
    intro x
    have : Tendsto (fun n => v x + ε n * b x) atTop (𝓝 (v x)) := by
      simpa using tendsto_const_nhds.add (hεt.mul_const (b x))
    exact (continuous_coe_real_ereal.tendsto _).comp this
  have hTlow : ∀ x, Tendsto (fun n => ((v x - ε n * b x : ℝ) : EReal)) atTop (𝓝 (v x : EReal)) := by
    intro x
    have : Tendsto (fun n => v x - ε n * b x) atTop (𝓝 (v x)) := by
      simpa using tendsto_const_nhds.sub (hεt.mul_const (b x))
    exact (continuous_coe_real_ereal.tendsto _).comp this
  have hfpol : IsPolicyOf M (fun _ => fstar) := fun _ => hfstar.1
  have hfstarT : ∀ x, Tendsto (fun n => Jnpi M M.r (fun _ => fstar) n x) atTop
      (𝓝 (v x : EReal)) := fun x =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le (hTlow x) (hTup x) (fun n => hlow n x)
      (fun n => hup n _ hfpol x)
  have hfstarInf : ∀ x, Jinfpi M M.r (fun _ => fstar) x = (v x : EReal) := fun x =>
    (hfstarT x).limsup_eq
  have hJinf : ∀ x, (v x : EReal) = Jinf M x := by
    intro x
    apply le_antisymm
    · rw [← hfstarInf x]
      exact le_biSup (fun π => Jinfpi M M.r π x) (show (fun _ => fstar) ∈
        {π : ℕ → E → A | IsPolicyOf M π} from hfpol)
    · apply iSup₂_le
      intro π hπ
      rw [← (hTup x).limsup_eq]
      exact limsup_le_limsup (Eventually.of_forall fun n => hup n π hπ x)
  refine ⟨hJinf, ?_, fun x => by rw [hfstarInf, hJinf]⟩
  intro x
  have hJn : Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (v x : EReal)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hfstarT x) (hTup x) (fun n => ?_)
      (fun n => ?_)
    · exact le_biSup (fun π => Jnpi M M.r π n x) (show (fun _ => fstar) ∈
        {π : ℕ → E → A | IsPolicyOf M π} from hfpol)
    · exact iSup₂_le fun π hπ => hup n π hπ x
  exact hJn.limsup_eq.symm

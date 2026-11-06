-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.g_pos_opt_ge_g
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:17:02.820831+00:00
-- url     : https://prove2.me/submissions/c9526800-469f-4c63-8cca-ef9790279a70

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LSExpGapGOpt

open CappedBaseStock

lemma measurable_history (t : ℕ) : Measurable (history t) := by
  unfold history
  refine Measurable.prodMk (measurable_pi_lambda _ (fun i => ?_)) measurable_snd
  exact (measurable_pi_apply (i : ℕ)).comp measurable_fst

lemma measurable_run (c : Parameters) (π : AdmissiblePolicy) (t : ℕ) :
    Measurable (fun ω => run c π ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ho : Measurable (fun ω => order π t ω) :=
      (π.measurable_decision t).comp (measurable_history t)
    have hd : Measurable (fun ω : Sample => ω.1 t) :=
      (measurable_pi_apply t).comp measurable_fst
    have h1 : Measurable (fun ω => (run c π ω t).1) := measurable_fst.comp ih
    have h2 : Measurable (fun ω => (run c π ω t).2) := measurable_snd.comp ih
    have h3 : ∀ i : Fin c.L, Measurable (fun ω => (run c π ω t).2 i) :=
      fun i => (measurable_pi_apply i).comp h2
    simp only [run, step, arrival]
    refine Measurable.prodMk ?_ (measurable_pi_lambda _ (fun i => ?_))
    · exact (h1.add (h3 _)).sub hd
    · split_ifs
      · exact h3 _
      · exact ho

/-- Post-delivery stock level. -/
def level (c : Parameters) (s : State c.L) : ℝ≥0 := s.1 + arrival c s

lemma measurable_level (c : Parameters) : Measurable (level c) := by
  unfold level arrival
  fun_prop

lemma run_congr (c : Parameters) (π : AdmissiblePolicy) (t : ℕ) (ω η : Sample)
    (h1 : ∀ k < t, ω.1 k = η.1 k) (h2 : ω.2 = η.2) : run c π ω t = run c π η t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun k hk => h1 k (Nat.lt_succ_of_lt hk))
    have hh : history t ω = history t η := by
      simp only [history, h2, Prod.mk.injEq, and_true]
      funext i; exact h1 i (Nat.lt_succ_of_lt i.2)
    simp only [run, order, hs, hh, h1 t (Nat.lt_succ_self t)]

/-- Newsvendor integrand. -/
noncomputable def nv (c : Parameters) (x : ℝ) (d : ℝ≥0) : ℝ :=
  c.h * max (x - (d : ℝ)) 0 + c.p * max ((d : ℝ) - x) 0

lemma nv_nonneg (c : Parameters) (x : ℝ) (d : ℝ≥0) : 0 ≤ nv c x d := by
  unfold nv
  have := c.holding_pos; have := c.penalty_pos
  positivity

lemma nv_integrable (P : DemandLaw) (c : Parameters) (x : ℝ) :
    Integrable (fun d => nv c x d) P.law := by
  unfold nv
  have hd : Integrable (fun d : ℝ≥0 => (d : ℝ)) P.law := P.finiteMean
  have h1 : Integrable (fun d : ℝ≥0 => max (x - (d : ℝ)) 0) P.law :=
    ((integrable_const x).sub hd).pos_part
  have h2 : Integrable (fun d : ℝ≥0 => max ((d : ℝ) - x) 0) P.law :=
    (hd.sub (integrable_const x)).pos_part
  exact (h1.const_mul _).add (h2.const_mul _)

lemma periodCost_eq (c : Parameters) (s : State c.L) (d : ℝ≥0) :
    periodCost c s d = ENNReal.ofReal (nv c ((s.1 + arrival c s : ℝ≥0) : ℝ) d) := by
  have hh := c.holding_pos; have hp := c.penalty_pos
  unfold periodCost lostSales nv
  set y := s.1 + arrival c s
  have e1 : ((y - d : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (max ((y : ℝ) - d) 0) := by
    rw [NNReal.sub_def, ENNReal.ofReal]
    congr 1; ext; simp [Real.coe_toNNReal']
  have e2 : ((d - y : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (max ((d : ℝ) - y) 0) := by
    rw [NNReal.sub_def, ENNReal.ofReal]
    congr 1; ext; simp [Real.coe_toNNReal']
  rw [e1, e2, ← ENNReal.ofReal_mul hh.le, ← ENNReal.ofReal_mul hp.le,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

lemma per_period (P : DemandLaw) (c : Parameters) (π : AdmissiblePolicy) (t : ℕ)
    (F : ℝ≥0 × ℝ≥0 → ℝ≥0∞) (hF : Measurable F) (K : ℝ≥0∞)
    (hK : ∀ y : ℝ≥0, K ≤ ∫⁻ d, F (y, d) ∂P.law) :
    K ≤ ∫⁻ ω, F (level c (run c π ω t), ω.1 t) ∂sampleLaw P := by
  have hmeas : Measurable (fun ω : Sample => F (level c (run c π ω t), ω.1 t)) :=
    hF.comp (((measurable_level c).comp (measurable_run c π t)).prodMk
      ((measurable_pi_apply t).comp measurable_fst))
  rw [sampleLaw, lintegral_prod_symm _ hmeas.aemeasurable]
  have hinner : ∀ u : ℝ, K ≤ ∫⁻ x, F (level c (run c π (x, u) t), x t) ∂demandPathLaw P := by
    intro u
    set μ := demandPathLaw P with hμ
    let S : Finset ℕ := Finset.range t
    let T : Finset ℕ := {t}
    let ext : (S → ℝ≥0) → Sample := fun v =>
      ((fun k => if hk : k < t then v ⟨k, Finset.mem_range.mpr hk⟩ else 0), u)
    have hext : Measurable ext := by
      refine Measurable.prodMk (measurable_pi_lambda _ (fun k => ?_)) measurable_const
      by_cases hk : k < t
      · simp only [hk, dif_pos]; exact measurable_pi_apply _
      · simp only [hk, dif_neg, not_false_eq_true]; exact measurable_const
    let G : (S → ℝ≥0) → ℝ≥0 := fun v => level c (run c π (ext v) t)
    have hGm : Measurable G := ((measurable_level c).comp (measurable_run c π t)).comp hext
    let RS : DemandPath → (S → ℝ≥0) := fun x i => x i
    let RT : DemandPath → (T → ℝ≥0) := fun x i => x i
    have hRSm : Measurable RS := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hRTm : Measurable RT := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hind : IndepFun RS RT μ := by
      have hi := iIndepFun_infinitePi (P := fun _ : ℕ => P.law)
        (X := fun _ (x : ℝ≥0) => x) (fun _ => measurable_id)
      exact hi.indepFun_finset S T (by simp [S, T]) (fun i => measurable_pi_apply i)
    let ev : (T → ℝ≥0) → ℝ≥0 := fun w => w ⟨t, Finset.mem_singleton_self t⟩
    have hev : Measurable ev := measurable_pi_apply _
    have hind2 : IndepFun (G ∘ RS) (ev ∘ RT) μ := hind.comp hGm hev
    have hY : ∀ x : DemandPath, (G ∘ RS) x = level c (run c π (x, u) t) := by
      intro x
      simp only [Function.comp, G]
      congr 1
      apply run_congr
      · intro k hk; simp [ext, RS, hk]
      · rfl
    have hD : ∀ x : DemandPath, (ev ∘ RT) x = x t := fun x => rfl
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hGm.comp hRSm).aemeasurable
      (hev.comp hRTm).aemeasurable).mp hind2
    have hlawD : μ.map (ev ∘ RT) = P.law := by
      have : (ev ∘ RT) = fun x : DemandPath => x t := funext hD
      rw [this, hμ, demandPathLaw]
      exact Measure.infinitePi_map_eval _ t
    have hpair : Measurable (fun x : DemandPath => ((G ∘ RS) x, (ev ∘ RT) x)) :=
      (hGm.comp hRSm).prodMk (hev.comp hRTm)
    have : IsProbabilityMeasure (μ.map (G ∘ RS)) :=
      Measure.isProbabilityMeasure_map (hGm.comp hRSm).aemeasurable
    have e1 : ∫⁻ x, F (level c (run c π (x, u) t), x t) ∂μ
        = ∫⁻ x, F ((G ∘ RS) x, (ev ∘ RT) x) ∂μ := by
      congr 1; funext x; rw [hY x, hD x]
    have e2 : ∫⁻ x, F ((G ∘ RS) x, (ev ∘ RT) x) ∂μ
        = ∫⁻ z, F z ∂((μ.map (G ∘ RS)).prod (μ.map (ev ∘ RT))) := by
      rw [← hmap, lintegral_map hF hpair]
    have e3 : ∫⁻ z, F z ∂((μ.map (G ∘ RS)).prod (μ.map (ev ∘ RT)))
        = ∫⁻ y, ∫⁻ d, F (y, d) ∂P.law ∂(μ.map (G ∘ RS)) := by
      rw [hlawD, lintegral_prod _ hF.aemeasurable]
    rw [e1, e2, e3]
    calc K = ∫⁻ _y, K ∂(μ.map (G ∘ RS)) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono hK
  calc K = ∫⁻ _u, K ∂seedLaw := by rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := lintegral_mono hinner

end LSExpGapGOpt

open LostSalesExpGap.ConstOrder LSExpGapGOpt CappedBaseStock in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    0 < gNV P c ∧ ENNReal.ofReal (gNV P c) ≤ CappedBaseStock.OPT P c := by
  have hh := c.holding_pos; have hp := c.penalty_pos
  have hgdef : gNV P c = ⨅ x : ℝ, ∫ d, nv c x d ∂P.law := rfl
  have hbdd : BddBelow (Set.range fun x : ℝ => ∫ d, nv c x d ∂P.law) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact integral_nonneg (nv_nonneg c x)⟩
  have hg_le : ∀ x : ℝ, gNV P c ≤ ∫ d, nv c x d ∂P.law := fun x => ciInf_le hbdd x
  constructor
  · -- g > 0
    set m := CappedBaseStock.mean P
    have hd : Integrable (fun d : ℝ≥0 => (d : ℝ)) P.law := P.finiteMean
    have habs : ∀ x : ℝ, Integrable (fun d : ℝ≥0 => |(d : ℝ) - x|) P.law :=
      fun x => (hd.sub (integrable_const x)).abs
    set A := ∫ d, |(d : ℝ) - m| ∂P.law
    have hApos : 0 < A := by
      rcases (integral_nonneg (f := fun d : ℝ≥0 => |(d : ℝ) - m|) (μ := P.law) (fun d => abs_nonneg ((d : ℝ) - m))).lt_or_eq with h | h
      · exact h
      exfalso
      have hz := (integral_eq_zero_iff_of_nonneg (f := fun d : ℝ≥0 => |(d : ℝ) - m|) (fun d => abs_nonneg ((d : ℝ) - m))
        (habs m)).mp h.symm
      have hm0 : 0 ≤ m := P.positiveMean.le
      set a : ℝ≥0 := ⟨m, hm0⟩
      have hae : ∀ᵐ d ∂P.law, d = a := by
        filter_upwards [hz] with d hd'
        simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] at hd'
        exact NNReal.eq hd'
      apply hP a
      ext s hs
      rw [Measure.dirac_apply' a hs]
      have hcongr : (s : Set ℝ≥0) =ᵐ[P.law] {_x | a ∈ s} := by
        filter_upwards [hae] with d hd'
        rw [hd']; rfl
      rw [measure_congr hcongr]
      by_cases has : a ∈ s
      · simp [has]
      · simp [has]
    have hkey : ∀ x : ℝ, min c.h c.p / 2 * A ≤ ∫ d, nv c x d ∂P.law := by
      intro x
      have h1 : ∫ d, min c.h c.p * |(d : ℝ) - x| ∂P.law ≤ ∫ d, nv c x d ∂P.law := by
        refine integral_mono ((habs x).const_mul _) (nv_integrable P c x) (fun d => ?_)
        simp only [nv]
        rcases le_total (d : ℝ) x with hdx | hdx
        · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
          nlinarith [min_le_left c.h c.p]
        · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]
          nlinarith [min_le_right c.h c.p]
      rw [integral_const_mul] at h1
      have h2 : A ≤ 2 * ∫ d, |(d : ℝ) - x| ∂P.law := by
        have hxm : |x - m| ≤ ∫ d, |(d : ℝ) - x| ∂P.law := by
          have : x - m = ∫ d, (x - (d : ℝ)) ∂P.law := by
            rw [integral_sub (integrable_const x) hd]; simp [m, CappedBaseStock.mean]
          rw [this]
          refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
          congr 1; funext d; exact abs_sub_comm _ _
        have : A ≤ ∫ d, (|(d : ℝ) - x| + |x - m|) ∂P.law := by
          refine integral_mono (habs m) ((habs x).add (integrable_const _)) (fun d => ?_)
          exact abs_sub_le _ _ _
        rw [integral_add (habs x) (integrable_const _)] at this
        simp at this
        linarith
      have hmin : 0 < min c.h c.p := lt_min hh hp
      nlinarith
    have hmin : 0 < min c.h c.p := lt_min hh hp
    have : min c.h c.p / 2 * A ≤ gNV P c := le_ciInf hkey
    have : 0 < min c.h c.p / 2 * A := by positivity
    linarith
  · -- OPT ≥ g
    -- one-period bound for a fixed post-delivery stock level
    have hy : ∀ y : ℝ≥0, ENNReal.ofReal (gNV P c) ≤ ∫⁻ d, ENNReal.ofReal (nv c y d) ∂P.law := by
      intro y
      rw [← ofReal_integral_eq_lintegral_ofReal (nv_integrable P c y)
        (ae_of_all _ (nv_nonneg c y))]
      exact ENNReal.ofReal_le_ofReal (hg_le y)
    have hnvm : Measurable (fun z : ℝ≥0 × ℝ≥0 => ENNReal.ofReal (nv c (z.1 : ℝ) z.2)) := by
      unfold nv; fun_prop
    have hper : ∀ (π : AdmissiblePolicy) (t : ℕ), ENNReal.ofReal (gNV P c) ≤
        ∫⁻ ω, periodCost c (run c π ω t) (ω.1 t) ∂sampleLaw P := by
      intro π t
      have := per_period P c π t (fun z : ℝ≥0 × ℝ≥0 => ENNReal.ofReal (nv c (z.1 : ℝ) z.2))
        hnvm _ hy
      refine this.trans (le_of_eq ?_)
      congr 1; funext ω
      rw [periodCost_eq]; rfl
    -- average cost
    refine le_iInf (fun π => ?_)
    unfold policyCost averageCost
    refine Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall (fun T => ?_))
      (by isBoundedDefault)
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]
    calc ENNReal.ofReal (gNV P c) * ((T : ℝ≥0∞) + 1)
        = ∑ _t ∈ Finset.range (T + 1), ENNReal.ofReal (gNV P c) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum (fun t _ => hper π t)

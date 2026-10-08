-- Prove2me | solution 1 for MechanismDesign.PublicGoods.exAnte_budget_balance_to_exPost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:40:09.387902+00:00
-- url     : https://prove2.me/submissions/c1793778-3491-47ad-98a8-0ebb84f64f9a

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory


namespace MechanismDesign.PublicGoods

open Set

section Infra
variable {N : ℕ} (S : Setting N)

lemma pg_intOn (i : Fin N) : IntegrableOn (S.f i) (Icc S.θlo S.θhi) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le S.θlo_lt_θhi.le).mp (S.f_intervalIntegrable i)

lemma pg_marg_apply (i : Fin N) {s : Set ℝ} (hs : MeasurableSet s) :
    S.marginal i s = ENNReal.ofReal (∫ x in s ∩ Icc S.θlo S.θhi, S.f i x) := by
  rw [Setting.marginal, withDensity_apply _ hs, Measure.restrict_restrict hs,
    ofReal_integral_eq_lintegral_ofReal]
  · exact (pg_intOn S i).mono_set inter_subset_right
  · filter_upwards [ae_restrict_mem (hs.inter measurableSet_Icc)] with x hx
    exact (S.f_pos i x hx.2).le

lemma pg_marg_univ (i : Fin N) : S.marginal i univ = 1 := by
  rw [pg_marg_apply S i MeasurableSet.univ, univ_inter, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le S.θlo_lt_θhi.le, S.f_integral]
  simp

instance pg_probMarg (i : Fin N) : IsProbabilityMeasure (S.marginal i) := ⟨pg_marg_univ S i⟩

instance pg_probμ : IsProbabilityMeasure S.μ := by
  unfold Setting.μ; infer_instance

lemma pg_ae_marg (i : Fin N) : ∀ᵐ x ∂S.marginal i, x ∈ Icc S.θlo S.θhi :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

lemma pg_ae_type : ∀ᵐ θ ∂S.μ, θ ∈ S.typeSpace := by
  have h : ∀ i, ∀ᵐ θ ∂S.μ, θ i ∈ Icc S.θlo S.θhi := fun i =>
    (Measure.tendsto_eval_ae_ae (μ := S.marginal) (i := i)).eventually (pg_ae_marg S i)
  filter_upwards [Filter.eventually_all.mpr h] with θ hθ
  exact mem_univ_pi.mpr hθ

lemma pg_upd_mem {θ : Fin N → ℝ} (hθ : θ ∈ S.typeSpace) (i : Fin N) {x : ℝ}
    (hx : x ∈ Icc S.θlo S.θhi) : Function.update θ i x ∈ S.typeSpace := by
  simp only [Setting.typeSpace, mem_pi, mem_univ, true_implies] at hθ ⊢
  intro j
  by_cases h : j = i
  · subst h; simpa using hx
  · rw [Function.update_of_ne h]; exact hθ j

lemma pg_ae_upd (i : Fin N) {x : ℝ} (hx : x ∈ Icc S.θlo S.θhi) :
    ∀ᵐ θ ∂S.μ, Function.update θ i x ∈ S.typeSpace := by
  filter_upwards [pg_ae_type S] with θ hθ using pg_upd_mem S hθ i hx

lemma pg_int_bdd {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (C : ℝ)
    (hC : ∀ θ ∈ S.typeSpace, |g θ| ≤ C) : Integrable g S.μ := by
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [pg_ae_type S] with θ hθ
  simpa [Real.norm_eq_abs] using hC θ hθ

lemma pg_int_bdd' {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (C : ℝ)
    (hC : ∀ θ, |g θ| ≤ C) : Integrable g S.μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun θ => by
    simpa [Real.norm_eq_abs] using hC θ)

lemma pg_qStar_meas : Measurable S.qStar := by
  unfold Setting.qStar
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le measurable_const
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)

lemma pg_sum_upd (θ : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    ∑ j, Function.update θ i y j = y + ∑ j ∈ Finset.univ.erase i, θ j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma pg_sum_erase_upd (θ : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    ∑ j ∈ Finset.univ.erase i, Function.update θ i y j = ∑ j ∈ Finset.univ.erase i, θ j := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma pg_qStar_upd (θ : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    S.qStar (Function.update θ i y) =
      if S.c ≤ y + ∑ j ∈ Finset.univ.erase i, θ j then 1 else 0 := by
  rw [Setting.qStar, pg_sum_upd]

lemma pg_pivt_upd (θ : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    S.pivot.t i (Function.update θ i y) =
      S.θlo * (if S.c ≤ S.θlo + ∑ j ∈ Finset.univ.erase i, θ j then 1 else 0) +
      ((if S.c ≤ y + ∑ j ∈ Finset.univ.erase i, θ j then 1 else 0) -
        (if S.c ≤ S.θlo + ∑ j ∈ Finset.univ.erase i, θ j then 1 else 0)) *
        (S.c - ∑ j ∈ Finset.univ.erase i, θ j) := by
  simp only [Setting.pivot]
  rw [Function.update_idem, pg_qStar_upd, pg_qStar_upd, pg_sum_erase_upd]

lemma pg_pivt_meas (i : Fin N) : Measurable (S.pivot.t i) := by
  simp only [Setting.pivot]
  have hq := pg_qStar_meas S
  have hu : Measurable fun θ : Fin N → ℝ => Function.update θ i S.θlo :=
    measurable_update' (a := i) |>.comp (measurable_id.prodMk measurable_const)
  refine ((measurable_const.mul (hq.comp hu)).add ((hq.sub (hq.comp hu)).mul
    (measurable_const.sub (Finset.measurable_sum _ fun j _ => measurable_pi_apply j))))

lemma pg_upd_meas (i : Fin N) (y : ℝ) : Measurable fun θ : Fin N → ℝ => Function.update θ i y :=
  measurable_update' (a := i) |>.comp (measurable_id.prodMk measurable_const)

lemma pg_pivt_abs (θ : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    |S.pivot.t i (Function.update θ i y)| ≤ 2 * |S.θlo| + |y| := by
  rw [pg_pivt_upd]
  set s := ∑ j ∈ Finset.univ.erase i, θ j
  have h1 := abs_nonneg S.θlo
  have h2 := le_abs_self S.θlo
  have h3 := neg_abs_le S.θlo
  have h4 := le_abs_self y
  have h5 := neg_abs_le y
  rw [abs_le]
  split_ifs with ha hb hb <;> constructor <;> nlinarith

lemma pg_qStar_abs (θ : Fin N → ℝ) : |S.qStar θ| ≤ 1 := by
  unfold Setting.qStar; split_ifs <;> simp

/-- Ex post incentive compatibility of the pivot mechanism. -/
lemma pg_pivot_expost (θ : Fin N → ℝ) (i : Fin N) (x y : ℝ) :
    x * S.qStar (Function.update θ i y) - S.pivot.t i (Function.update θ i y) ≤
      x * S.qStar (Function.update θ i x) - S.pivot.t i (Function.update θ i x) := by
  rw [pg_pivt_upd, pg_pivt_upd, pg_qStar_upd, pg_qStar_upd]
  split_ifs <;> nlinarith

lemma pg_pivot_ir (θ : Fin N → ℝ) (i : Fin N) {x : ℝ} (hx : S.θlo ≤ x) :
    0 ≤ S.qStar (Function.update θ i x) * x - S.pivot.t i (Function.update θ i x) := by
  rw [pg_pivt_upd, pg_qStar_upd]
  split_ifs <;> nlinarith

lemma pg_pivQ_int (i : Fin N) (y : ℝ) :
    Integrable (fun θ => S.qStar (Function.update θ i y)) S.μ :=
  pg_int_bdd' S ((pg_qStar_meas S).comp (pg_upd_meas i y)) 1 (fun θ => pg_qStar_abs S _)

lemma pg_pivT_int (i : Fin N) (y : ℝ) :
    Integrable (fun θ => S.pivot.t i (Function.update θ i y)) S.μ :=
  pg_int_bdd' S ((pg_pivt_meas S i).comp (pg_upd_meas i y)) _ (fun θ => pg_pivt_abs S θ i y)

lemma pg_pivot_ic_ir_core : S.pivot.IsIC S ∧ S.pivot.IsIR S := by
  constructor
  · intro i x _ y _
    simp only [DirectMechanism.interimQ, DirectMechanism.interimT]
    have e : ∀ z, x * ∫ θ, S.pivot.q (Function.update θ i z) ∂S.μ -
        ∫ θ, S.pivot.t i (Function.update θ i z) ∂S.μ =
        ∫ θ, (x * S.qStar (Function.update θ i z) - S.pivot.t i (Function.update θ i z)) ∂S.μ := by
      intro z
      rw [integral_sub ((pg_pivQ_int S i z).const_mul x) (pg_pivT_int S i z),
        integral_const_mul]
      rfl
    rw [e, e]
    exact integral_mono ((pg_pivQ_int S i y).const_mul x |>.sub (pg_pivT_int S i y))
      ((pg_pivQ_int S i x).const_mul x |>.sub (pg_pivT_int S i x))
      (fun θ => pg_pivot_expost S θ i x y)
  · intro i x hx
    simp only [DirectMechanism.interimU, DirectMechanism.interimQ, DirectMechanism.interimT]
    have e : (∫ θ, S.pivot.q (Function.update θ i x) ∂S.μ) * x -
        ∫ θ, S.pivot.t i (Function.update θ i x) ∂S.μ =
        ∫ θ, (S.qStar (Function.update θ i x) * x - S.pivot.t i (Function.update θ i x)) ∂S.μ := by
      rw [integral_sub ((pg_pivQ_int S i x).mul_const x) (pg_pivT_int S i x),
        integral_mul_const]
      rfl
    rw [e]
    exact integral_nonneg (fun θ => pg_pivot_ir S θ i hx.1)

end Infra

section Deficit
variable {N : ℕ} (S : Setting N)

lemma pg_pivt_self (θ : Fin N → ℝ) (i : Fin N) :
    S.pivot.t i θ =
      S.θlo * (if S.c ≤ S.θlo + ((∑ j, θ j) - θ i) then 1 else 0) +
      ((if S.c ≤ ∑ j, θ j then 1 else 0) -
        (if S.c ≤ S.θlo + ((∑ j, θ j) - θ i) then 1 else 0)) *
        (S.c - ((∑ j, θ j) - θ i)) := by
  have := pg_pivt_upd S θ i (θ i)
  rw [Function.update_eq_self] at this
  rw [this, Finset.sum_erase_eq_sub (Finset.mem_univ i), add_sub_cancel]

lemma pg_piv_sum_le (hlow : (N : ℝ) * S.θlo < S.c) (θ : Fin N → ℝ)
    (hθ : ∀ i, S.θlo ≤ θ i) : ∑ i, S.pivot.t i θ ≤ S.c * S.qStar θ := by
  have hs : ∀ i, ∑ j ∈ Finset.univ.erase i, θ j = (∑ j, θ j) - θ i := fun i => by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  unfold Setting.qStar
  by_cases hc : S.c ≤ ∑ j, θ j
  · rw [if_pos hc]
    by_cases hp : ∃ i, ¬ (S.c ≤ S.θlo + ((∑ j, θ j) - θ i))
    · obtain ⟨i0, hi0⟩ := hp
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      have h1 : S.pivot.t i0 θ = S.c - ((∑ j, θ j) - θ i0) := by
        rw [pg_pivt_self, if_pos hc, if_neg hi0]; ring
      have h2 : ∀ j, S.pivot.t j θ ≤ θ j := by
        intro j; rw [pg_pivt_self, if_pos hc]
        split_ifs with h
        · nlinarith [hθ j]
        · linarith
      have h3 : ∑ j ∈ Finset.univ.erase i0, S.pivot.t j θ ≤ ∑ j ∈ Finset.univ.erase i0, θ j :=
        Finset.sum_le_sum (fun j _ => h2 j)
      rw [hs i0] at h3
      linarith
    · push_neg at hp
      have : ∀ i, S.pivot.t i θ = S.θlo := by
        intro i; rw [pg_pivt_self, if_pos hc, if_pos (hp i)]; ring
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linarith
  · rw [if_neg hc]
    have : ∀ i, S.pivot.t i θ = 0 := by
      intro i
      rw [pg_pivt_self, if_neg hc, if_neg (by linarith [hθ i])]; ring
    simp [this]

lemma pg_piv_sum_lt (θ : Fin N → ℝ) (hc : S.c < ∑ j, θ j)
    (hp : ∀ i, S.θlo + ((∑ j, θ j) - θ i) < S.c) :
    ∑ i, S.pivot.t i θ < S.c * S.qStar θ := by
  unfold Setting.qStar
  rw [if_pos hc.le]
  have : ∀ i, S.pivot.t i θ = S.c - ((∑ j, θ j) - θ i) := by
    intro i; rw [pg_pivt_self, if_pos hc.le, if_neg (not_le.mpr (hp i))]; ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast S.two_le
  nlinarith

lemma pg_pivt_int (i : Fin N) : Integrable (S.pivot.t i) S.μ := by
  refine pg_int_bdd S (pg_pivt_meas S i) (2 * |S.θlo| + (|S.θlo| + |S.θhi|)) (fun θ hθ => ?_)
  have := pg_pivt_abs S θ i (θ i)
  rw [Function.update_eq_self] at this
  have hθi : θ i ∈ Icc S.θlo S.θhi := hθ i (mem_univ i)
  have : |θ i| ≤ |S.θlo| + |S.θhi| := by
    rw [abs_le]; constructor
    · have := neg_abs_le S.θlo; have := abs_nonneg S.θhi; linarith [hθi.1]
    · have := le_abs_self S.θhi; have := abs_nonneg S.θlo; linarith [hθi.2]
  linarith

lemma pg_qStar_int : Integrable S.qStar S.μ :=
  pg_int_bdd' S (pg_qStar_meas S) 1 (fun θ => pg_qStar_abs S θ)

lemma pg_marg_Ioo_pos (i : Fin N) {a b : ℝ} (hab : a < b) (ha : S.θlo ≤ a) (hb : b ≤ S.θhi) :
    0 < S.marginal i (Ioo a b) := by
  rw [pg_marg_apply S i measurableSet_Ioo, inter_eq_left.mpr
    (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha hb)), ENNReal.ofReal_pos,
    integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le hab.le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) hab
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
      ((pg_intOn S i).mono_set (Icc_subset_Icc ha hb)))
  · exact S.f_pos i x ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩

lemma pg_pivot_budget_deficit_core (hlow : (N : ℝ) * S.θlo < S.c)
    (hhigh : S.c < (N : ℝ) * S.θhi) : S.pivot.budgetSurplus S < 0 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast S.two_le
  have hN : (0 : ℝ) < N := by linarith
  haveI : Nonempty (Fin N) := ⟨⟨0, by have := S.two_le; omega⟩⟩
  set a := S.c / N with ha
  have ha1 : S.θlo < a := by rw [ha, lt_div_iff₀ hN]; linarith
  have ha2 : a < S.θhi := by rw [ha, div_lt_iff₀ hN]; linarith
  set δ := min (S.θhi - a) ((a - S.θlo) / N) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (div_pos (by linarith) hN)
  have hδ1 : δ ≤ S.θhi - a := min_le_left _ _
  have hδ2 : δ * N ≤ a - S.θlo := by
    have := min_le_right (S.θhi - a) ((a - S.θlo) / N)
    rw [le_div_iff₀ hN] at this; linarith
  set B : Set (Fin N → ℝ) := univ.pi fun _ => Ioo a (a + δ) with hB
  set g : (Fin N → ℝ) → ℝ := fun θ => S.c * S.qStar θ - ∑ i, S.pivot.t i θ with hg
  have hgi : Integrable g S.μ :=
    ((pg_qStar_int S).const_mul S.c).sub (integrable_finsetSum _ fun i _ => pg_pivt_int S i)
  have hg0 : 0 ≤ᵐ[S.μ] g := by
    filter_upwards [pg_ae_type S] with θ hθ
    have := pg_piv_sum_le S hlow θ (fun i => (hθ i (mem_univ i)).1)
    simp only [hg, Pi.zero_apply]; linarith
  have hBsub : B ⊆ Function.support g := by
    intro θ hθ
    have hθ' : ∀ i, θ i ∈ Ioo a (a + δ) := fun i => hθ i (mem_univ i)
    have hsum1 : N * a < ∑ j, θ j := by
      have := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
        (f := fun _ => a) (g := θ) (fun i _ => (hθ' i).1)
      simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
    have hsum2 : ∑ j, θ j < N * (a + δ) := by
      have := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
        (f := θ) (g := fun _ => a + δ) (fun i _ => (hθ' i).2)
      simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add] using this
    have hNa : N * a = S.c := by rw [ha]; field_simp
    have hlt := pg_piv_sum_lt S θ (by linarith) (fun i => by
      have := (hθ' i).1; nlinarith)
    simp only [Function.mem_support, hg]
    linarith
  have hBpos : 0 < S.μ B := by
    rw [hB, Setting.μ, Measure.pi_pi]
    exact CanonicallyOrderedAdd.prod_pos.mpr fun i _ =>
      pg_marg_Ioo_pos S i (by linarith) ha1.le (by linarith)
  have hpos : 0 < ∫ θ, g θ ∂S.μ :=
    (integral_pos_iff_support_of_nonneg_ae hg0 hgi).mpr (hBpos.trans_le (measure_mono hBsub))
  have e : S.pivot.budgetSurplus S = - ∫ θ, g θ ∂S.μ := by
    rw [DirectMechanism.budgetSurplus, ← integral_neg]
    congr 1; ext θ; simp only [hg]; show _ - S.c * S.qStar θ = _; ring
  rw [e]; linarith

end Deficit

section Envelope
open Filter Topology
/-- `x` clamped to `[a, b]`. -/
noncomputable def msClamp (a b x : ℝ) : ℝ := max a (min x b)

lemma msClamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : msClamp a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma msClamp_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : msClamp a b x = x := by
  unfold msClamp; rw [min_eq_left hx.2, max_eq_right hx.1]

lemma msClamp_cont (a b : ℝ) : Continuous (msClamp a b) :=
  continuous_const.max (continuous_id.min continuous_const)

lemma msClamp_mono (a b : ℝ) : Monotone (msClamp a b) :=
  fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

/-! ### The envelope argument -/

/-- If `(y - x) P x ≤ S y - S x` on `[a, b]`, then `S` has derivative `P x` at every interior
point where `P` is continuous. -/
lemma ms_re_deriv {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) {x : ℝ}
    (hx : x ∈ Ioo a b) (hPc : ContinuousAt P x) : HasDerivAt S (P x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hlo : Tendsto (fun y => min (P x) (P y)) (𝓝[≠] x) (𝓝 (P x)) := by
    have : Tendsto (fun y => min (P x) (P y)) (𝓝 x) (𝓝 (min (P x) (P x))) :=
      tendsto_const_nhds.min hPc
    rw [min_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun y => max (P x) (P y)) (𝓝[≠] x) (𝓝 (P x)) := by
    have : Tendsto (fun y => max (P x) (P y)) (𝓝 x) (𝓝 (max (P x) (P x))) :=
      tendsto_const_nhds.max hPc
    rw [max_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hxI : x ∈ Icc a b := Ioo_subset_Icc_self hx
  have hev : ∀ᶠ y in 𝓝[≠] x, y ∈ Icc a b ∧ y ≠ x := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
      with y hy hyI
    exact ⟨hyI, hy⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev] with y hy
    obtain ⟨hyI, hyx⟩ := hy
    have h1 := hsand x hxI y hyI
    have h2 := hsand y hyI x hxI
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · have hneg : y - x < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      calc (S y - S x) ≤ (y - x) * P y := by linarith
        _ ≤ min (P x) (P y) * (y - x) := by
          rw [mul_comm]; exact mul_le_mul_of_nonpos_right (min_le_right _ _) hneg.le
    · have hpos : 0 < y - x := by linarith
      rw [le_div_iff₀ hpos]
      calc min (P x) (P y) * (y - x) ≤ P x * (y - x) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hpos.le
        _ ≤ S y - S x := by linarith
  · filter_upwards [hev] with y hy
    obtain ⟨hyI, hyx⟩ := hy
    have h1 := hsand x hxI y hyI
    have h2 := hsand y hyI x hxI
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · have hneg : y - x < 0 := by linarith
      rw [div_le_iff_of_neg hneg]
      calc max (P x) (P y) * (y - x) ≤ P x * (y - x) :=
            mul_le_mul_of_nonpos_right (le_max_left _ _) hneg.le
        _ ≤ S y - S x := by linarith
    · have hpos : 0 < y - x := by linarith
      rw [div_le_iff₀ hpos]
      calc S y - S x ≤ (y - x) * P y := by linarith
        _ ≤ max (P x) (P y) * (y - x) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le

/-- The sandwich makes `P` monotone. -/
lemma ms_re_mono {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    MonotoneOn P (Icc a b) := by
  intro x hx y hy hxy
  rcases hxy.lt_or_eq with h | h
  · have h1 := hsand x hx y hy
    have h2 := hsand y hy x hx
    have : (y - x) * P x ≤ (y - x) * P y := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  · rw [h]

/-- The sandwich makes `S` continuous on `[a, b]` (it is Lipschitz). -/
lemma ms_re_cont {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    ContinuousOn S (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty (not_le.mpr hba)]; exact continuousOn_empty _
  have hm := ms_re_mono hsand
  set L := max |P a| |P b| with hL
  have hbound : ∀ x ∈ Icc a b, |P x| ≤ L := by
    intro x hx
    have h1 := hm ⟨le_rfl, hab⟩ hx hx.1
    have h2 := hm hx ⟨hab, le_rfl⟩ hx.2
    rw [abs_le]
    constructor
    · have := neg_abs_le (P a); have := le_max_left |P a| |P b|; linarith
    · have := le_abs_self (P b); have := le_max_right |P a| |P b|; linarith
  have hlip : LipschitzOnWith (Real.toNNReal L) S (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ ((abs_nonneg _).trans (hbound x hx))]
    have h1 := hsand x hx y hy
    have h2 := hsand y hy x hx
    have bx := abs_le.mp (hbound x hx)
    have by' := abs_le.mp (hbound y hy)
    rcases le_total x y with hxy | hxy
    · rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
      rw [abs_le]
      constructor <;> nlinarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
      rw [abs_le]
      constructor <;> nlinarith
  exact hlip.continuousOn

/-- The countable set of discontinuities of `P` (through its clamped monotone extension). -/
lemma ms_re_countable {P : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hm : MonotoneOn P (Icc a b)) :
    ∃ D : Set ℝ, D.Countable ∧ ∀ x ∈ Ioo a b \ D, ContinuousAt P x := by
  have hmono : Monotone (fun x => P (msClamp a b x)) := fun x y hxy =>
    hm (msClamp_mem hab x) (msClamp_mem hab y) (msClamp_mono a b hxy)
  refine ⟨{x | ¬ContinuousAt (fun x => P (msClamp a b x)) x}, hmono.countable_not_continuousAt,
    fun x hx => ?_⟩
  have hc : ContinuousAt (fun x => P (msClamp a b x)) x := by
    by_contra h; exact hx.2 h
  refine hc.congr ?_
  filter_upwards [Ioo_mem_nhds hx.1.1 hx.1.2] with y hy
  rw [msClamp_of_mem (Ioo_subset_Icc_self hy)]

/-- The envelope formula: `S b - S a = ∫_a^b P`. -/
lemma ms_re_ftc {P S : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    S b - S a = ∫ x in a..b, P x := by
  obtain ⟨D, hD, hDc⟩ := ms_re_countable hab (ms_re_mono hsand)
  have hint : IntervalIntegrable P volume a b :=
    (ms_re_mono hsand).mono (by rw [uIcc_of_le hab]) |>.intervalIntegrable
  exact (integral_eq_of_hasDerivAt_off_countable_of_le S P hab hD (ms_re_cont hsand)
    (fun x hx => ms_re_deriv hsand hx.1 (hDc x hx)) hint).symm

end Envelope

section Fubini
variable {N : ℕ} (S : Setting N)

lemma pg_mp (j : Fin N) :
    MeasurePreserving (fun p : (Fin N → ℝ) × ℝ => Function.update p.1 j p.2)
      (S.μ.prod (S.marginal j)) S.μ := by
  refine ⟨measurable_update', ?_⟩
  symm
  unfold Setting.μ
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin N → ℝ) × ℝ => Function.update p.1 j p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s j Set.univ)) ×ˢ s j := by
    ext ⟨θ, x⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun k => ?_, by simpa using h j⟩
      by_cases hk : k = j
      · subst hk; simp
      · have := h k
        rw [Function.update_of_ne hk] at this
        rw [Function.update_of_ne hk]; exact this
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = j
      · subst hk; simpa using h2
      · have := h1 k
        rw [Function.update_of_ne hk] at this
        rw [Function.update_of_ne hk]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : ∀ k, S.marginal k (Function.update s j Set.univ k) =
      if k = j then 1 else S.marginal k (s k) := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Function.update_of_ne hk, if_neg hk]
  simp only [this]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => S.marginal k (s k)) (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun k => if k = j then (1 : ENNReal) else
      S.marginal k (s k)) (Finset.mem_univ j)]
  simp only [if_true, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [if_neg (Finset.ne_of_mem_erase hk)]

/-- Fubini for the interim expectation. -/
lemma pg_marg (j : Fin N) (g : (Fin N → ℝ) → ℝ) (hg : Integrable g S.μ) :
    Integrable (fun x => ∫ θ, g (Function.update θ j x) ∂S.μ) (S.marginal j) ∧
    ∫ x, (∫ θ, g (Function.update θ j x) ∂S.μ) ∂S.marginal j = ∫ θ, g θ ∂S.μ := by
  have hΦ := pg_mp S j
  have hgΦ : Integrable (fun p : (Fin N → ℝ) × ℝ => g (Function.update p.1 j p.2))
      (S.μ.prod (S.marginal j)) := hΦ.integrable_comp hg.aestronglyMeasurable |>.2 hg
  refine ⟨hgΦ.integral_prod_right, ?_⟩
  rw [← integral_prod_symm _ hgΦ]
  conv_rhs => rw [← hΦ.map_eq]
  rw [integral_map hΦ.measurable.aemeasurable (by rw [hΦ.map_eq]; exact hg.aestronglyMeasurable)]

lemma pg_eval (j : Fin N) (G : ℝ → ℝ) (hG : Integrable G (S.marginal j)) :
    Integrable (fun θ : Fin N → ℝ => G (θ j)) S.μ ∧
    ∫ θ, G (θ j) ∂S.μ = ∫ x, G x ∂S.marginal j := by
  have hev : MeasurePreserving (fun θ : Fin N → ℝ => θ j) S.μ (S.marginal j) := by
    unfold Setting.μ; exact measurePreserving_eval _ j
  refine ⟨hev.integrable_comp hG.aestronglyMeasurable |>.2 hG, ?_⟩
  rw [← hev.map_eq, integral_map hev.measurable.aemeasurable
    (by rw [hev.map_eq]; exact hG.aestronglyMeasurable)]

end Fubini

section MaxSurplus
variable {N : ℕ} (S : Setting N)

lemma pg_q_int (M : DirectMechanism N) (hM : M.IsDirect S) : Integrable M.q S.μ :=
  pg_int_bdd S hM.2.1 1 (fun θ hθ => by rcases hM.1 θ hθ with h | h <;> simp [h])

lemma pg_Q_eq (M : DirectMechanism N) (hq : ∀ θ ∈ S.typeSpace, M.q θ = S.qStar θ)
    (i : Fin N) {x : ℝ} (hx : x ∈ Icc S.θlo S.θhi) :
    M.interimQ S i x = S.pivot.interimQ S i x := by
  unfold DirectMechanism.interimQ
  refine integral_congr_ae ?_
  filter_upwards [pg_ae_upd S i hx] with θ hθ
  exact hq _ hθ

lemma pg_env (M : DirectMechanism N) (hic : M.IsIC S) (i : Fin N) {x : ℝ}
    (hx : x ∈ Icc S.θlo S.θhi) :
    M.interimU S i x = M.interimU S i S.θlo + ∫ z in S.θlo..x, M.interimQ S i z := by
  have := ms_re_ftc (P := M.interimQ S i) (S := M.interimU S i) hx.1 (fun a ha b hb => by
    have ha' : a ∈ Icc S.θlo S.θhi := ⟨ha.1, ha.2.trans hx.2⟩
    have hb' : b ∈ Icc S.θlo S.θhi := ⟨hb.1, hb.2.trans hx.2⟩
    have := hic i b hb' a ha'
    unfold DirectMechanism.interimU; linarith)
  linarith

lemma pg_pivq : S.pivot.q = S.qStar := rfl

lemma pg_piv_U0 (i : Fin N) : S.pivot.interimU S i S.θlo = 0 := by
  unfold DirectMechanism.interimU DirectMechanism.interimQ DirectMechanism.interimT
  rw [pg_pivq]
  rw [← integral_mul_const, ← integral_sub ((pg_pivQ_int S i _).mul_const _) (pg_pivT_int S i _)]
  rw [← integral_zero (Fin N → ℝ) ℝ]
  congr 1; ext θ
  show S.qStar _ * _ - _ = 0
  rw [pg_pivt_upd, pg_qStar_upd]; ring

lemma pg_T_le (M : DirectMechanism N) (hic : M.IsIC S) (hir : M.IsIR S)
    (hq : ∀ θ ∈ S.typeSpace, M.q θ = S.qStar θ) (i : Fin N) {x : ℝ}
    (hx : x ∈ Icc S.θlo S.θhi) : M.interimT S i x ≤ S.pivot.interimT S i x := by
  have hlo : S.θlo ∈ Icc S.θlo S.θhi := ⟨le_rfl, S.θlo_lt_θhi.le⟩
  have h1 := pg_env S M hic i hx
  have h2 := pg_env S S.pivot (pg_pivot_ic_ir_core S).1 i hx
  have hQ := pg_Q_eq S M hq i hx
  have hI : ∫ z in S.θlo..x, M.interimQ S i z = ∫ z in S.θlo..x, S.pivot.interimQ S i z := by
    refine intervalIntegral.integral_congr (fun z hz => ?_)
    rw [uIcc_of_le hx.1] at hz
    exact pg_Q_eq S M hq i ⟨hz.1, hz.2.trans hx.2⟩
  have h0 := pg_piv_U0 S i
  have hr := hir i S.θlo hlo
  unfold DirectMechanism.interimU at h1 h2 h0 hr
  rw [hQ, hI] at h1
  linarith

lemma pg_pivot_max_core (M : DirectMechanism N)
    (hM : M.IsDirect S) (hIC : M.IsIC S) (hIR : M.IsIR S)
    (hq : ∀ θ ∈ S.typeSpace, M.q θ = S.qStar θ) :
    M.budgetSurplus S ≤ S.pivot.budgetSurplus S := by
  unfold DirectMechanism.budgetSurplus
  rw [pg_pivq]
  have hMt : ∀ i, Integrable (M.t i) S.μ := fun i => (hM.2.2 i).2.1
  have hPt : ∀ i, Integrable (S.pivot.t i) S.μ := fun i => pg_pivt_int S i
  rw [integral_sub (integrable_finsetSum _ fun i _ => hMt i)
      ((pg_q_int S M hM).const_mul S.c),
    integral_sub (integrable_finsetSum _ fun i _ => hPt i)
      ((pg_qStar_int S).const_mul S.c),
    integral_finsetSum _ fun i _ => hMt i, integral_finsetSum _ fun i _ => hPt i]
  have hqe : ∫ θ, S.c * M.q θ ∂S.μ = ∫ θ, S.c * S.qStar θ ∂S.μ := by
    refine integral_congr_ae ?_
    filter_upwards [pg_ae_type S] with θ hθ
    rw [hq θ hθ]
  rw [hqe]
  have hti : ∀ i, ∫ θ, M.t i θ ∂S.μ ≤ ∫ θ, S.pivot.t i θ ∂S.μ := by
    intro i
    rw [← (pg_marg S i _ (hMt i)).2, ← (pg_marg S i _ (hPt i)).2]
    refine integral_mono_ae (pg_marg S i _ (hMt i)).1 (pg_marg S i _ (hPt i)).1 ?_
    filter_upwards [pg_ae_marg S i] with x hx
    exact pg_T_le S M hIC hIR hq i hx
  have := Finset.sum_le_sum (s := Finset.univ) fun i _ => hti i
  linarith

end MaxSurplus

section BB
variable {N : ℕ} (S : Setting N)

lemma pg_comp_int (G : ℝ → ℝ) (k j : Fin N) (x : ℝ) (hG : Integrable G (S.marginal k)) :
    Integrable (fun θ => G (Function.update θ j x k)) S.μ := by
  by_cases h : k = j
  · subst h; simp only [Function.update_self]; exact integrable_const _
  · simp only [Function.update_of_ne h]; exact (pg_eval S k G hG).1

lemma pg_comp_int_eq (G : ℝ → ℝ) (k j : Fin N) (x : ℝ) (hG : Integrable G (S.marginal k)) :
    ∫ θ, G (Function.update θ j x k) ∂S.μ = if k = j then G x else ∫ y, G y ∂S.marginal k := by
  by_cases h : k = j
  · subst h; simp
  · simp only [Function.update_of_ne h, if_neg h]; exact (pg_eval S k G hG).2

lemma pg_interim_meas (g : (Fin N → ℝ) → ℝ) (hg : Measurable g) (j : Fin N) :
    Measurable fun y => ∫ θ, g (Function.update θ j y) ∂S.μ := by
  have : StronglyMeasurable (Function.uncurry fun (y : ℝ) (θ : Fin N → ℝ) =>
      g (Function.update θ j y)) := by
    refine (hg.comp ?_).stronglyMeasurable
    exact measurable_update'.comp (measurable_snd.prodMk measurable_fst)
  exact this.integral_prod_right.measurable

lemma pg_exante_core (M : DirectMechanism N) (hM : M.IsDirect S) (hBB : M.IsExAnteBB S) :
    ∃ M' : DirectMechanism N, M'.IsDirect S ∧ M.Equivalent S M' ∧ M'.IsExPostBB S := by
  have hN := S.two_le
  let a : Fin N := ⟨0, by omega⟩
  let b : Fin N := ⟨1, by omega⟩
  have hab : b ≠ a := by simp [a, b, Fin.ext_iff]
  have hMt : ∀ i, Integrable (M.t i) S.μ := fun i => (hM.2.2 i).2.1
  have hMq := pg_q_int S M hM
  let T : Fin N → ℝ → ℝ := fun j y => M.interimT S j y
  let Q1 : ℝ → ℝ := fun y => M.interimQ S a y
  let E : Fin N → ℝ := fun j => ∫ θ, M.t j θ ∂S.μ
  have hT : ∀ j, Integrable (T j) (S.marginal j) ∧ ∫ y, T j y ∂S.marginal j = E j :=
    fun j => pg_marg S j (M.t j) (hMt j)
  have hQ1 : Integrable Q1 (S.marginal a) ∧ ∫ y, Q1 y ∂S.marginal a = ∫ θ, M.q θ ∂S.μ :=
    pg_marg S a M.q hMq
  have hTm : ∀ j, Measurable (T j) := fun j => pg_interim_meas S (M.t j) (hM.2.2 j).1 j
  have hQm : Measurable Q1 := pg_interim_meas S M.q hM.2.1 a
  let D : ℝ → ℝ := fun y => S.c * Q1 y - T a y - ∑ k ∈ Finset.univ.erase a, E k
  have hD : Integrable D (S.marginal a) :=
    ((hQ1.1.const_mul S.c).sub (hT a).1).sub (integrable_const _)
  have hDm : Measurable D := ((measurable_const.mul hQm).sub (hTm a)).sub measurable_const
  let Dbar : ℝ := ∫ y, D y ∂S.marginal a
  let R : (Fin N → ℝ) → ℝ := fun θ => S.c * M.q θ - ∑ k, T k (θ k) - D (θ a)
  let t' : Fin N → (Fin N → ℝ) → ℝ := fun i θ =>
    T i (θ i) + (if i = a then R θ else 0) + (if i = b then D (θ a) - Dbar else 0)
  -- sum of the new transfers
  have hsum : ∀ θ, ∑ i, t' i θ = S.c * M.q θ - Dbar := by
    intro θ
    simp only [t', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, R]
    ring
  have hDbar : Dbar ≤ 0 := by
    have e1 : Dbar = S.c * ∫ θ, M.q θ ∂S.μ - E a - ∑ k ∈ Finset.univ.erase a, E k := by
      simp only [Dbar, D]
      have i1 : Integrable (fun y => S.c * Q1 y) (S.marginal a) := hQ1.1.const_mul S.c
      have i2 : Integrable (fun y => S.c * Q1 y - T a y) (S.marginal a) := i1.sub (hT a).1
      rw [integral_sub i2 (integrable_const _),
        integral_sub i1 (hT a).1, integral_const_mul, hQ1.2, (hT a).2]
      simp
    have e2 : ∫ θ, ∑ i, M.t i θ ∂S.μ = ∑ k, E k := integral_finsetSum _ fun i _ => hMt i
    have e3 : ∫ θ, S.c * M.q θ ∂S.μ = S.c * ∫ θ, M.q θ ∂S.μ := integral_const_mul _ _
    have hb := hBB
    unfold DirectMechanism.IsExAnteBB at hb
    rw [e2, e3, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hb
    linarith
  -- integrability of pieces after an update
  have hqU : ∀ j x, x ∈ Icc S.θlo S.θhi → Integrable (fun θ => M.q (Function.update θ j x)) S.μ := by
    intro j x hx
    refine pg_int_bdd S (hM.2.1.comp (pg_upd_meas j x)) 1 (fun θ hθ => ?_)
    rcases hM.1 _ (pg_upd_mem S hθ j hx) with h | h <;> simp [h]
  have hRU : ∀ j x, x ∈ Icc S.θlo S.θhi →
      Integrable (fun θ => R (Function.update θ j x)) S.μ := by
    intro j x hx
    exact (((hqU j x hx).const_mul S.c).sub (integrable_finsetSum _ fun k _ =>
      pg_comp_int S (T k) k j x (hT k).1)).sub (pg_comp_int S D a j x hD)
  have hR0 : ∀ x, x ∈ Icc S.θlo S.θhi → ∫ θ, R (Function.update θ a x) ∂S.μ = 0 := by
    intro x hx
    simp only [R]
    have j1 : Integrable (fun θ => S.c * M.q (Function.update θ a x)) S.μ :=
      (hqU a x hx).const_mul S.c
    have j2 : Integrable (fun θ => ∑ k, T k (Function.update θ a x k)) S.μ :=
      integrable_finsetSum _ fun k _ => pg_comp_int S (T k) k a x (hT k).1
    have j3 : Integrable (fun θ => S.c * M.q (Function.update θ a x) -
        ∑ k, T k (Function.update θ a x k)) S.μ := j1.sub j2
    rw [integral_sub j3 (pg_comp_int S D a a x hD), integral_sub j1 j2, integral_const_mul,
      integral_finsetSum _ fun k _ => pg_comp_int S (T k) k a x (hT k).1]
    simp only [Function.update_self, integral_const, probReal_univ, one_smul]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), pg_comp_int_eq S _ a a x (hT a).1,
      if_pos rfl]
    have : ∀ k ∈ Finset.univ.erase a, ∫ θ, T k (Function.update θ a x k) ∂S.μ = E k := by
      intro k hk
      rw [pg_comp_int_eq S _ k a x (hT k).1, if_neg (Finset.ne_of_mem_erase hk), (hT k).2]
    rw [Finset.sum_congr rfl this]
    simp only [D, Q1, T, DirectMechanism.interimQ]
    ring
  refine ⟨⟨M.q, t'⟩, ⟨hM.1, hM.2.1, fun i => ⟨?_, ?_, fun j x hx => ?_⟩⟩, ⟨fun θ _ => rfl, ?_⟩, ?_⟩
  · -- measurability
    have hRm : Measurable R := ((measurable_const.mul hM.2.1).sub (Finset.measurable_sum _
      fun k _ => (hTm k).comp (measurable_pi_apply k))).sub (hDm.comp (measurable_pi_apply a))
    refine (((hTm i).comp (measurable_pi_apply i)).add ?_).add ?_
    · split_ifs
      · exact hRm
      · exact measurable_const
    · split_ifs
      · exact (hDm.comp (measurable_pi_apply a)).sub measurable_const
      · exact measurable_const
  · have hR : Integrable R S.μ := ((hMq.const_mul S.c).sub (integrable_finsetSum _
      fun k _ => (pg_eval S k _ (hT k).1).1)).sub (pg_eval S a _ hD).1
    refine ((pg_eval S i _ (hT i).1).1.add ?_).add ?_
    · split_ifs
      · exact hR
      · exact integrable_const _
    · split_ifs
      · exact (pg_eval S a _ hD).1.sub (integrable_const _)
      · exact integrable_const _
  · refine ((pg_comp_int S (T i) i j x (hT i).1).add ?_).add ?_
    · split_ifs
      · exact hRU j x hx
      · exact integrable_const _
    · split_ifs
      · exact (pg_comp_int S D a j x hD).sub (integrable_const _)
      · exact integrable_const _
  · -- equivalence
    intro i x hx
    show T i x = ∫ θ, t' i (Function.update θ i x) ∂S.μ
    have hI1 : Integrable (fun θ => (if i = a then R (Function.update θ i x) else 0)) S.μ := by
      split_ifs
      · exact hRU i x hx
      · exact integrable_const _
    have hI2 : Integrable (fun θ => (if i = b then D (Function.update θ i x a) - Dbar else 0))
        S.μ := by
      split_ifs
      · exact (pg_comp_int S D a i x hD).sub (integrable_const _)
      · exact integrable_const _
    simp only [t', Function.update_self]
    have k1 : Integrable (fun θ => T i x + (if i = a then R (Function.update θ i x) else 0))
        S.μ := (integrable_const _).add hI1
    rw [integral_add k1 hI2, integral_add (integrable_const _) hI1,
      integral_const, probReal_univ, one_smul]
    have z1 : ∫ θ, (if i = a then R (Function.update θ i x) else 0) ∂S.μ = 0 := by
      split_ifs with h
      · subst h; exact hR0 x hx
      · simp
    have z2 : ∫ θ, (if i = b then D (Function.update θ i x a) - Dbar else 0) ∂S.μ = 0 := by
      split_ifs with h
      · rw [integral_sub (pg_comp_int S D a i x hD) (integrable_const _),
          pg_comp_int_eq S D a i x hD, if_neg (by rw [h]; exact hab.symm)]
        simp [Dbar]
      · simp
    rw [z1, z2]; ring
  · intro θ _
    rw [hsum]
    show S.c * M.q θ ≤ S.c * M.q θ - Dbar
    linarith

end BB

end MechanismDesign.PublicGoods

open MechanismDesign.PublicGoods


theorem solution {N : ℕ} (S : Setting N) (M : DirectMechanism N)
    (hM : M.IsDirect S) (hBB : M.IsExAnteBB S) :
    ∃ M' : DirectMechanism N, M'.IsDirect S ∧ M.Equivalent S M' ∧ M'.IsExPostBB S := by
  exact pg_exante_core S M hM hBB

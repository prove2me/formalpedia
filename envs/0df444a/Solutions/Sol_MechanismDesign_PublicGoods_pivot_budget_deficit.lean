-- Prove2me | solution 1 for MechanismDesign.PublicGoods.pivot_budget_deficit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:31:26.707737+00:00
-- url     : https://prove2.me/submissions/1fc2530d-ee0d-4169-b4c5-4c71beac5d5d

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
    ((pg_qStar_int S).const_mul S.c).sub (integrable_finset_sum _ fun i _ => pg_pivt_int S i)
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

end MechanismDesign.PublicGoods

open MechanismDesign.PublicGoods


theorem solution {N : ℕ} (S : Setting N)
    (hlow : (N : ℝ) * S.θlo < S.c) (hhigh : S.c < (N : ℝ) * S.θhi) :
    S.pivot.budgetSurplus S < 0 := by
  exact pg_pivot_budget_deficit_core S hlow hhigh

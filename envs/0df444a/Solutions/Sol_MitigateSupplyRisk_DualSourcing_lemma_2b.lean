-- Prove2me | solution 1 for MitigateSupplyRisk.DualSourcing.lemma_2b
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T11:26:54.055327+00:00
-- url     : https://prove2.me/submissions/7b0fb5fe-8b3a-4c9f-ae5a-c2c44a35e44e

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model
open MeasureTheory ProbabilityTheory
open MitigateSupplyRisk.DualSourcing
set_option autoImplicit false

namespace SupplySubmodularity

def quantity (M : Model) (q ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i, Model.deliv (M.K i) (q i) (ξ i)

def charge (M : Model) (q ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i, (M.η i * q i + (1 - M.η i) * Model.deliv (M.K i) (q i) (ξ i)) * M.c i

lemma revenue_identity (r v p x y : ℝ) :
    r * min x y + v * max (y-x) 0 - p * max (x-y) 0 =
      (r+p)*y - (r+p-v)*max (y-x) 0 - p*x := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

lemma profit_identity (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) :
    M.profit q ξ x = -charge M q ξ + (M.r+M.p)*quantity M q ξ -
      (M.r+M.p-M.v)*max (quantity M q ξ-x) 0 - M.p*x := by
  have h := revenue_identity M.r M.v M.p x (quantity M q ξ)
  unfold Model.profit charge quantity at *
  linarith

lemma quantity_mono (M : Model) (q q' ξ : Fin 2 → ℝ) (h : q ≤ q') :
    quantity M q ξ ≤ quantity M q' ξ := by
  apply Finset.sum_le_sum
  intro i _
  exact min_le_min_right _ (h i)

lemma quantity_balance (M : Model) (q q' ξ : Fin 2 → ℝ) :
    quantity M (q ⊔ q') ξ + quantity M (q ⊓ q') ξ =
      quantity M q ξ + quantity M q' ξ := by
  unfold quantity
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_total (q i) (q' i) with h | h
  · simp [Pi.sup_apply, Pi.inf_apply, max_eq_right h, min_eq_left h, add_comm]
  · simp [Pi.sup_apply, Pi.inf_apply, max_eq_left h, min_eq_right h]

lemma charge_balance (M : Model) (q q' ξ : Fin 2 → ℝ) :
    charge M (q ⊔ q') ξ + charge M (q ⊓ q') ξ = charge M q ξ + charge M q' ξ := by
  unfold charge
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_total (q i) (q' i) with h | h
  · simp [Pi.sup_apply, Pi.inf_apply, max_eq_right h, min_eq_left h, add_comm]
  · simp [Pi.sup_apply, Pi.inf_apply, max_eq_left h, min_eq_right h]

lemma positive_part_inequality (a b u l x : ℝ) (ha : a ≤ u) (hb : b ≤ u)
    (he : u+l=a+b) : max (a-x) 0 + max (b-x) 0 ≤ max (u-x) 0 + max (l-x) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

lemma profit_submodular (M : Model) (q q' ξ : Fin 2 → ℝ) (x : ℝ) :
    M.profit (q ⊔ q') ξ x + M.profit (q ⊓ q') ξ x ≤ M.profit q ξ x + M.profit q' ξ x := by
  have hb := quantity_balance M q q' ξ
  have hc := charge_balance M q q' ξ
  have hp := positive_part_inequality (quantity M q ξ) (quantity M q' ξ)
    (quantity M (q ⊔ q') ξ) (quantity M (q ⊓ q') ξ) x
    (quantity_mono M q (q ⊔ q') ξ le_sup_left)
    (quantity_mono M q' (q ⊔ q') ξ le_sup_right) hb
  have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr M.v_lt.le)
  have he := congrArg (fun z : ℝ => (M.r+M.p)*z) hb
  simp only [profit_identity]
  nlinarith only [hc, hm, he]

lemma profit_integrable (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a q : Fin 2 → ℝ) (hq : q ∈ Model.orders) :
    Integrable (fun ω => M.profit q ω.1 ω.2) ((Measure.pi fun i => M.ν i (a i)).prod μ) := by
  let ν := (Measure.pi fun i => M.ν i (a i)).prod μ
  have hd (i : Fin 2) : Integrable (fun ω : (Fin 2 → ℝ) × ℝ =>
      Model.deliv (M.K i) (q i) (ω.1 i)) ν := by
    apply (integrable_const (q i)).mono'
    · apply Continuous.aestronglyMeasurable
      unfold Model.deliv
      fun_prop
    · apply ae_of_all
      intro ω
      unfold Model.deliv
      rw [Real.norm_of_nonneg (le_min (hq i) (le_max_right _ _))]
      exact min_le_left _ _
  have hy : Integrable (fun ω : (Fin 2 → ℝ) × ℝ => quantity M q ω.1) ν :=
    integrable_finsetSum _ (fun i _ => hd i)
  have hc : Integrable (fun ω : (Fin 2 → ℝ) × ℝ => charge M q ω.1) ν :=
    integrable_finsetSum _ (fun i _ =>
      ((integrable_const (M.η i * q i)).add ((hd i).const_mul (1-M.η i))).mul_const (M.c i))
  have hx : Integrable (fun ω : (Fin 2 → ℝ) × ℝ => ω.2) ν := hμint.comp_snd _
  have hz : Integrable (fun _ : (Fin 2 → ℝ) × ℝ => (0 : ℝ)) ν := integrable_const 0
  change Integrable _ ν
  have h := ((hc.neg.add ((hx.inf hy).const_mul M.r)).add
    (((hy.sub hx).sup hz).const_mul M.v)).sub (((hx.sub hy).sup hz).const_mul M.p)
  apply h.congr
  apply ae_of_all
  intro ω
  rfl

end SupplySubmodularity

theorem prior_submodularity (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (a : Fin 2 → ℝ)
    (q q' : Fin 2 → ℝ) (hq : q ∈ Model.orders) (hq' : q' ∈ Model.orders) :
    M.Pi2 μ (q ⊔ q') a + M.Pi2 μ (q ⊓ q') a ≤ M.Pi2 μ q a + M.Pi2 μ q' a := by
  have hsup : q ⊔ q' ∈ Model.orders := fun i => le_trans (hq i) (le_max_left _ _)
  have hinf : q ⊓ q' ∈ Model.orders := fun i => le_min (hq i) (hq' i)
  have hqI := SupplySubmodularity.profit_integrable M μ hμint a q hq
  have hq'I := SupplySubmodularity.profit_integrable M μ hμint a q' hq'
  have hsI := SupplySubmodularity.profit_integrable M μ hμint a (q ⊔ q') hsup
  have hiI := SupplySubmodularity.profit_integrable M μ hμint a (q ⊓ q') hinf
  unfold Model.Pi2
  rw [← integral_add hsI hiI, ← integral_add hqI hq'I]
  exact integral_mono (hsI.add hiI) (hqI.add hq'I)
    (fun ω => SupplySubmodularity.profit_submodular M q q' ω.1 ω.2)

#print axioms prior_submodularity

namespace SupplyExistence
open SupplySubmodularity

lemma lip_eval (i : Fin 2) : LipschitzWith 1 (fun q : Fin 2 → ℝ => q i) := by
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  simpa using dist_le_pi_dist q q' i

lemma lip_mul {α : Type*} [PseudoMetricSpace α] {f : α → ℝ} {K : NNReal}
    (h : LipschitzWith K f) (c : ℝ) : LipschitzWith (‖c‖₊ * K) (fun x => c*f x) := by
  simpa only [smul_eq_mul, Function.comp_def] using (lipschitzWith_smul c).comp h

noncomputable def lipBound (M : Model) : NNReal :=
  (‖M.c 0‖₊*(‖M.η 0‖₊+‖1-M.η 0‖₊) + ‖M.c 1‖₊*(‖M.η 1‖₊+‖1-M.η 1‖₊)) +
  ‖M.r‖₊*2 + ‖M.v‖₊*2 + ‖M.p‖₊*2

lemma profit_lipschitz (M : Model) (ξ : Fin 2 → ℝ) (x : ℝ) :
    LipschitzWith (lipBound M) (fun q => M.profit q ξ x) := by
  have hd (i : Fin 2) : LipschitzWith 1 (fun q : Fin 2 → ℝ =>
      Model.deliv (M.K i) (q i) (ξ i)) := (lip_eval i).min_const _
  have hy : LipschitzWith 2 (fun q => quantity M q ξ) := by
    simpa [quantity, Fin.sum_univ_two, one_add_one_eq_two] using (hd 0).add (hd 1)
  have hc (i : Fin 2) : LipschitzWith
      (‖M.c i‖₊*(‖M.η i‖₊+‖1-M.η i‖₊))
      (fun q : Fin 2 → ℝ => (M.η i*q i+(1-M.η i)*Model.deliv (M.K i) (q i) (ξ i))*M.c i) := by
    simpa [mul_comm] using lip_mul ((lip_mul (lip_eval i) (M.η i)).add
      (lip_mul (hd i) (1-M.η i))) (M.c i)
  have h1 := lip_mul (hy.const_min x) M.r
  have h2 := lip_mul ((hy.sub (LipschitzWith.const x)).max_const 0) M.v
  have h3 := lip_mul (((LipschitzWith.const x).sub hy).max_const 0) M.p
  simpa [Model.profit, charge, quantity, Fin.sum_univ_two, lipBound] using
    ((((hc 0).add (hc 1)).neg.add h1).add h2).sub h3

lemma integrable_profit (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a q : Fin 2 → ℝ) :
    Integrable (fun ω => M.profit q ω.1 ω.2) ((Measure.pi fun i => M.ν i (a i)).prod μ) := by
  have h0 := profit_integrable M μ hμint a 0 (fun _ => le_rfl)
  have hdiff : Integrable (fun ω : (Fin 2 → ℝ) × ℝ => M.profit q ω.1 ω.2-M.profit 0 ω.1 ω.2)
      ((Measure.pi fun i => M.ν i (a i)).prod μ) := by
    apply (integrable_const ((lipBound M : ℝ)*‖q‖)).mono'
    · apply Continuous.aestronglyMeasurable
      unfold Model.profit Model.deliv
      fun_prop
    · apply ae_of_all
      intro ω
      simpa using (profit_lipschitz M ω.1 ω.2).norm_sub_le q 0
  apply (hdiff.add h0).congr
  exact ae_of_all _ (fun ω => sub_add_cancel _ _)

lemma Pi2_lipschitz (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a : Fin 2 → ℝ) :
    LipschitzWith (lipBound M) (fun q => M.Pi2 μ q a) := by
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  rw [dist_eq_norm, Model.Pi2, Model.Pi2,
    ← integral_sub (integrable_profit M μ hμint a q) (integrable_profit M μ hμint a q')]
  have h := norm_integral_le_of_norm_le_const (μ := (Measure.pi fun i => M.ν i (a i)).prod μ)
    (ae_of_all _ (fun ω : (Fin 2 → ℝ) × ℝ => (profit_lipschitz M ω.1 ω.2).norm_sub_le q q'))
  simpa [dist_eq_norm] using h

lemma clip_profit (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) (hξ : ∀ i, 0 ≤ ξ i) :
    M.profit q ξ x ≤ M.profit (fun i => min (q i) (M.K i)) ξ x := by
  have hd (i : Fin 2) : Model.deliv (M.K i) (min (q i) (M.K i)) (ξ i) =
      Model.deliv (M.K i) (q i) (ξ i) := by
    have hc : max (M.K i-ξ i) 0 ≤ M.K i := max_le (sub_le_self _ (hξ i)) (M.K_pos i).le
    simp only [Model.deliv, min_assoc, min_eq_right hc]
  have hc : (∑ i, (M.η i*min (q i) (M.K i)+(1-M.η i)*Model.deliv (M.K i) (q i) (ξ i))*M.c i) ≤
      ∑ i, (M.η i*q i+(1-M.η i)*Model.deliv (M.K i) (q i) (ξ i))*M.c i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (add_le_add
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (M.η_nonneg i)) le_rfl) (M.c_nonneg i)
  simp only [Model.profit, hd]
  linarith

lemma ae_capacity_nonneg (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : Fin 2 → ℝ) :
    ∀ᵐ ω : (Fin 2 → ℝ) × ℝ ∂((Measure.pi fun i => M.ν i (a i)).prod μ), ∀ i, 0 ≤ ω.1 i := by
  have h (i : Fin 2) : ∀ᵐ t ∂M.ν i (a i), 0 ≤ t := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using M.ν_nonneg i (a i)
  have hh : ∀ᵐ ξ ∂Measure.pi (fun i => M.ν i (a i)), ∀ i, 0 ≤ ξ i := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually (h i)
  exact measurePreserving_fst.quasiMeasurePreserving.tendsto_ae.eventually hh

lemma optimal_exists (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a : Fin 2 → ℝ) : ∃ q, M.IsOptimal μ a q := by
  have hK : (0 : Fin 2 → ℝ) ≤ M.K := fun i => (M.K_pos i).le
  obtain ⟨q,hq,hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : Fin 2 → ℝ) M.K)).exists_isMaxOn
    ⟨0, le_rfl, hK⟩ (Pi2_lipschitz M μ hμint a).continuous.continuousOn
  refine ⟨q,hq.1,?_⟩
  intro q' hq'
  let qc := fun i => min (q' i) (M.K i)
  have hqc : qc ∈ Set.Icc (0 : Fin 2 → ℝ) M.K :=
    ⟨fun i => le_min (hq' i) (M.K_pos i).le, fun i => min_le_right _ _⟩
  apply le_trans (b := M.Pi2 μ qc a) _ (hmax hqc)
  apply integral_mono_ae (integrable_profit M μ hμint a q') (integrable_profit M μ hμint a qc)
  filter_upwards [ae_capacity_nonneg M μ a] with ω hω
  exact clip_profit M q' ω.1 ω.2 hω

lemma diff_min_const {f : ℝ → ℝ} {t c : ℝ} (hf : DifferentiableAt ℝ f t) (hne : f t ≠ c) :
    DifferentiableAt ℝ (fun x => min (f x) c) t := by
  rcases lt_or_gt_of_ne hne with h | h
  · apply hf.congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (Iio_mem_nhds h)] with x hx
    exact min_eq_left hx.le
  · apply (differentiableAt_const c).congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds h)] with x hx
    exact min_eq_right hx.le

lemma diff_max_const {f : ℝ → ℝ} {t c : ℝ} (hf : DifferentiableAt ℝ f t) (hne : f t ≠ c) :
    DifferentiableAt ℝ (fun x => max (f x) c) t := by
  rcases lt_or_gt_of_ne hne with h | h
  · apply (differentiableAt_const c).congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (Iio_mem_nhds h)] with x hx
    exact max_eq_right hx.le
  · apply hf.congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds h)] with x hx
    exact max_eq_left hx.le

lemma profit_diff (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) (i : Fin 2)
    (hcap : q i ≠ max (M.K i-ξ i) 0) (hx : quantity M q ξ ≠ x) :
    DifferentiableAt ℝ (fun t => M.profit (Function.update q i t) ξ x) (q i) := by
  have he (j : Fin 2) : DifferentiableAt ℝ (fun t => Function.update q i t j) (q i) := by
    by_cases hj : j=i
    · subst j
      simpa using (differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ => t) (q i))
    · simpa [Function.update_of_ne hj] using (differentiableAt_const (q j) :
        DifferentiableAt ℝ (fun _ : ℝ => q j) (q i))
  have hd (j : Fin 2) : DifferentiableAt ℝ (fun t =>
      Model.deliv (M.K j) (Function.update q i t j) (ξ j)) (q i) := by
    by_cases hj : j=i
    · subst j
      simpa [Model.deliv] using diff_min_const differentiableAt_id hcap
    · simpa [Function.update_of_ne hj] using (differentiableAt_const (Model.deliv (M.K j) (q j) (ξ j)) :
        DifferentiableAt ℝ (fun _ : ℝ => Model.deliv (M.K j) (q j) (ξ j)) (q i))
  have hy : DifferentiableAt ℝ (fun t => quantity M (Function.update q i t) ξ) (q i) := by
    simpa [quantity, Fin.sum_univ_two] using (hd 0).fun_add (hd 1)
  have hc : DifferentiableAt ℝ (fun t => charge M (Function.update q i t) ξ) (q i) := by
    have hh (j : Fin 2) := ((he j).const_mul (M.η j) |>.add ((hd j).const_mul (1-M.η j))).mul_const (M.c j)
    simpa [charge, Fin.sum_univ_two] using (hh 0).fun_add (hh 1)
  have hh : quantity M (Function.update q i (q i)) ξ-x ≠ 0 := by
    simpa only [Function.update_eq_self] using sub_ne_zero.mpr hx
  simp_rw [profit_identity]
  exact ((hc.neg.add (hy.const_mul (M.r+M.p))).sub
    ((diff_max_const (hy.sub_const x) hh).const_mul (M.r+M.p-M.v))).sub (differentiableAt_const _)

lemma ae_profit_diff (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμac : μ ≪ volume) (a q : Fin 2 → ℝ) (i : Fin 2) (hqi : 0 < q i) :
    ∀ᵐ ω : (Fin 2 → ℝ) × ℝ ∂((Measure.pi fun j => M.ν j (a j)).prod μ),
      DifferentiableAt ℝ (fun t => M.profit (Function.update q i t) ω.1 ω.2) (q i) := by
  letI : NullSingletonClass (M.ν i (a i)) := ⟨M.ν_noAtoms i (a i)⟩
  have hz := Measure.ae_eval_ne (fun j => M.ν j (a j)) i (M.K i-q i)
  have hc : ∀ᵐ ξ ∂Measure.pi (fun j => M.ν j (a j)), q i ≠ max (M.K i-ξ i) 0 := by
    filter_upwards [hz] with ξ hξ
    intro h
    by_cases hh : 0 ≤ M.K i-ξ i
    · rw [max_eq_left hh] at h
      apply hξ
      linarith
    · rw [max_eq_right (le_of_not_ge hh)] at h
      linarith
  have hcp : ∀ᵐ ω : (Fin 2 → ℝ) × ℝ ∂((Measure.pi fun j => M.ν j (a j)).prod μ),
      q i ≠ max (M.K i-ω.1 i) 0 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae.eventually hc
  have hx : ∀ᵐ ω : (Fin 2 → ℝ) × ℝ ∂((Measure.pi fun j => M.ν j (a j)).prod μ),
      quantity M q ω.1 ≠ ω.2 := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · apply ae_of_all
      intro ξ
      apply hμac.ae_le
      have h : ∀ᵐ x : ℝ, x ≠ quantity M q ξ := by
        rw [ae_iff]
        simp
      exact h.mono (fun x hx => Ne.symm hx)
    · exact (isClosed_eq (by unfold quantity Model.deliv; fun_prop) continuous_snd).measurableSet.compl
  filter_upwards [hcp,hx] with ω hcap hx
  exact profit_diff M q ω.1 ω.2 i hcap hx

lemma update_lipschitz (q : Fin 2 → ℝ) (i : Fin 2) :
    LipschitzWith 1 (fun t => Function.update q i t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).2
  intro j
  by_cases hj : j=i
  · subst j
    simp
  · simp only [Function.update_of_ne hj, dist_self]
    exact dist_nonneg

lemma Pi2_diff (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (hμac : μ ≪ volume) (a q : Fin 2 → ℝ)
    (i : Fin 2) (hqi : 0 < q i) :
    DifferentiableAt ℝ (fun t => M.Pi2 μ (Function.update q i t) a) (q i) := by
  let ν := (Measure.pi fun j => M.ν j (a j)).prod μ
  let F := fun (t : ℝ) (ω : (Fin 2 → ℝ) × ℝ) => M.profit (Function.update q i t) ω.1 ω.2
  have hcont : Continuous (fun p : ((Fin 2 → ℝ) × ℝ) × ℝ => F p.2 p.1) := by
    unfold F Model.profit Model.deliv
    fun_prop
  have hm : AEStronglyMeasurable (fun ω => deriv (fun t => F t ω) (q i)) ν := by
    exact ((stronglyMeasurable_deriv_with_param (f := fun ω t => F t ω) hcont).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hl : ∀ᵐ ω ∂ν, LipschitzOnWith (Real.nnabs (lipBound M : ℝ)) (fun t => F t ω) Set.univ := by
    apply ae_of_all
    intro ω
    have h := (profit_lipschitz M ω.1 ω.2).comp (update_lipschitz q i)
    simpa only [mul_one, Real.nnabs_coe, Function.comp_def, F] using h.lipschitzOnWith (s := Set.univ)
  have hi : Integrable (F (q i)) ν := integrable_profit M μ hμint a _
  have hd : ∀ᵐ ω ∂ν, HasDerivAt (fun t => F t ω) (deriv (fun t => F t ω) (q i)) (q i) := by
    filter_upwards [ae_profit_diff M μ hμac a q i hqi] with ω hω
    exact hω.hasDerivAt
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (μ := ν) (s := Set.univ) (bound := fun _ => (lipBound M : ℝ))
    Filter.univ_mem (Filter.Eventually.of_forall (fun t =>
      (integrable_profit M μ hμint a (Function.update q i t)).aestronglyMeasurable))
    hi hm hl (integrable_const _) hd
  exact h.2.differentiableAt

end SupplyExistence

theorem prior_optimality (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (hμac : μ ≪ volume)
    (a : Fin 2 → ℝ) :
    ∃ q, M.IsOptimal μ a q ∧
      ∀ i : Fin 2, q i = 0 ∨ q i = M.K i ∨
        HasDerivAt (fun t => M.Pi2 μ (Function.update q i t) a) 0 (q i) := by
  obtain ⟨q,hq⟩ := SupplyExistence.optimal_exists M μ hμint a
  refine ⟨q,hq,?_⟩
  intro i
  by_cases h0 : q i=0
  · exact Or.inl h0
  · have hpos : 0 < q i := lt_of_le_of_ne (hq.1 i) (Ne.symm h0)
    have hd := SupplyExistence.Pi2_diff M μ hμint hμac a q i hpos
    have hm : IsLocalMax (fun t => M.Pi2 μ (Function.update q i t) a) (q i) := by
      filter_upwards [Ioi_mem_nhds hpos] with t ht
      have hf : Function.update q i t ∈ Model.orders := by
        intro j
        by_cases hj : j=i
        · subst j
          simpa using ht.le
        · simpa [Function.update_of_ne hj] using hq.1 j
      simpa only [Function.update_eq_self] using hq.2 (Function.update q i t) hf
    have hz := hm.hasDerivAt_eq_zero hd.hasDerivAt
    exact Or.inr (Or.inr (hz ▸ hd.hasDerivAt))

#print axioms prior_optimality

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace SupplyReliability

lemma level_measure_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, cdf μ x ≤ cdf ν x) {f : ℝ → ℝ}
    (hc : Continuous f) (ha : Antitone f) (t : ℝ) :
    μ {x | t ≤ f x} ≤ ν {x | t ≤ f x} := by
  let S : Set ℝ := {x | t ≤ f x}
  change μ S ≤ ν S
  by_cases hn : S.Nonempty
  · by_cases hb : BddAbove S
    · have hm : sSup S ∈ S := (isClosed_le continuous_const hc).csSup_mem hn hb
      have he : S = Iic (sSup S) := by
        ext x
        constructor
        · exact fun hx => le_csSup hb hx
        · exact fun hx => le_trans hm (ha hx)
      rw [he, ← ofReal_cdf, ← ofReal_cdf]
      exact ENNReal.ofReal_le_ofReal (h _)
    · have he : S = univ := by
        apply eq_univ_of_forall
        intro x
        obtain ⟨y,hy,hxy⟩ := not_bddAbove_iff.mp hb x
        exact le_trans hy (ha hxy.le)
      simp [he]
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he]

lemma integral_antitone_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, cdf μ x ≤ cdf ν x) {f : ℝ → ℝ}
    (hc : Continuous f) (ha : Antitone f) (hm : Integrable f μ) (hn : Integrable f ν)
    (c : ℝ) (hb : ∀ x, c ≤ f x) : (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
  let g := fun x => f x-c
  have hgc : Continuous g := hc.sub continuous_const
  have hga : Antitone g := fun x y hxy => sub_le_sub_right (ha hxy) c
  have hgm : Integrable g μ := hm.sub (integrable_const c)
  have hgn : Integrable g ν := hn.sub (integrable_const c)
  have hg0 : ∀ x, 0 ≤ g x := fun x => sub_nonneg.mpr (hb x)
  have hl : (∫ x, g x ∂μ) ≤ ∫ x, g x ∂ν := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgn.aestronglyMeasurable]
    apply ENNReal.toReal_mono hgn.lintegral_lt_top.ne
    rw [lintegral_eq_lintegral_meas_le μ (ae_of_all _ hg0) hgc.measurable.aemeasurable,
      lintegral_eq_lintegral_meas_le ν (ae_of_all _ hg0) hgc.measurable.aemeasurable]
    exact lintegral_mono (fun t => level_measure_le μ ν h hgc hga t)
  dsimp [g] at hl
  rw [integral_sub hm (integrable_const c), integral_sub hn (integrable_const c)] at hl
  simpa using hl

lemma monotone_before_max {f : ℝ → ℝ} {Q z : ℝ}
    (hc : ConcaveOn ℝ (Icc 0 Q) f) (hz : z ∈ Icc 0 Q)
    (hmax : IsMaxOn f (Icc 0 Q) z) : MonotoneOn f (Icc 0 z) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with he | hxy
  · simp [he]
  rcases hy.2.eq_or_lt with he | hyz
  · subst y
    exact hmax ⟨hx.1,hx.2.trans hz.2⟩
  have hs := hc.slope_anti_adjacent ⟨hx.1,hx.2.trans hz.2⟩ hz hxy hyz
  have hm := hmax (show y ∈ Icc 0 Q from ⟨hy.1,hy.2.trans hz.2⟩)
  have hnon : 0 ≤ (f z-f y)/(z-y) := div_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hyz.le)
  have hp : 0 ≤ (f y-f x)/(y-x) := hnon.trans hs
  rcases div_nonneg_iff.mp hp with h | h
  · exact sub_nonneg.mp h.1
  · linarith [h.2]

open MitigateSupplyRisk.DualSourcing

lemma deliv_mem {K q ξ : ℝ} (hq : q ∈ Icc 0 K) : Model.deliv K q ξ ∈ Icc 0 K :=
  ⟨le_min hq.1 (le_max_right _ _), (min_le_left _ _).trans hq.2⟩

lemma deliv_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hc : Continuous f) {K q : ℝ} (hq : q ∈ Icc 0 K) :
    Integrable (fun ξ => f (Model.deliv K q ξ)) μ := by
  obtain ⟨z,hz,hm⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) K)).exists_isMaxOn
    ⟨q,hq⟩ hc.norm.continuousOn
  apply (integrable_const ‖f z‖).mono'
  · apply Continuous.aestronglyMeasurable
    exact hc.comp (by unfold Model.deliv; fun_prop)
  · exact ae_of_all _ (fun ξ => hm (deliv_mem hq))

lemma clip_at_max {f : ℝ → ℝ} {K z q : ℝ} (hz : z ∈ Icc 0 K)
    (hq : q ∈ Icc 0 K) (hm : IsMaxOn f (Icc 0 K) z) (ξ : ℝ) :
    f (Model.deliv K q ξ) ≤ f (Model.deliv K (min q z) ξ) := by
  have he : Model.deliv K (min q z) ξ = min (Model.deliv K q ξ) z := by
    exact min_right_comm _ _ _
  rw [he]
  by_cases h : Model.deliv K q ξ ≤ z
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
    exact hm (deliv_mem hq)

lemma deliv_antitone {f : ℝ → ℝ} {K z q : ℝ}
    (hm : MonotoneOn f (Icc 0 z)) (hq : q ∈ Icc 0 z) :
    Antitone (fun ξ => f (Model.deliv K q ξ)) := by
  intro x y hxy
  apply hm
  · exact ⟨le_min hq.1 (le_max_right _ _), (min_le_left _ _).trans hq.2⟩
  · exact ⟨le_min hq.1 (le_max_right _ _), (min_le_left _ _).trans hq.2⟩
  · exact min_le_min_left _ (max_le_max_right _ (sub_le_sub_left hxy K))

lemma reoptimize_one_coordinate (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (horder : ∀ x, cdf μ x ≤ cdf ν x)
    {f : ℝ → ℝ} (hc : Continuous f) {K : ℝ} (hK : 0 ≤ K)
    (hconc : ConcaveOn ℝ (Icc 0 K) f) {k q : ℝ} (hk : 0 ≤ k)
    (hq : q ∈ Icc 0 K) : ∃ q' ∈ Icc 0 q,
      (∫ ξ, f (Model.deliv K q ξ) ∂μ)-k*q ≤
        (∫ ξ, f (Model.deliv K q' ξ) ∂ν)-k*q' := by
  obtain ⟨z,hz,hm⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) K)).exists_isMaxOn
    ⟨0,le_rfl,hK⟩ hc.continuousOn
  obtain ⟨b,hb,hmin⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) K)).exists_isMinOn
    ⟨0,le_rfl,hK⟩ hc.continuousOn
  let q' := min q z
  have hq' : q' ∈ Icc 0 K := ⟨le_min hq.1 hz.1,(min_le_left _ _).trans hq.2⟩
  refine ⟨q',⟨hq'.1,min_le_left _ _⟩,?_⟩
  have hclip : (∫ ξ, f (Model.deliv K q ξ) ∂μ) ≤ ∫ ξ, f (Model.deliv K q' ξ) ∂μ :=
    integral_mono (deliv_integrable μ hc hq) (deliv_integrable μ hc hq')
      (clip_at_max hz hq hm)
  have hdom := integral_antitone_le μ ν horder
    (hc.comp (show Continuous (fun ξ => Model.deliv K q' ξ) by unfold Model.deliv; fun_prop))
    (deliv_antitone (monotone_before_max hconc hz hm) ⟨hq'.1,min_le_right _ _⟩)
    (deliv_integrable μ hc hq') (deliv_integrable ν hc hq')
    (f b) (fun ξ => hmin (deliv_mem hq'))
  simp only [Function.comp_def] at hdom
  have hcost : k*q' ≤ k*q := mul_le_mul_of_nonneg_left (min_le_left _ _) hk
  linarith

end SupplyReliability
#print axioms SupplyReliability.reoptimize_one_coordinate
namespace SupplyReliability
open MitigateSupplyRisk.DualSourcing

noncomputable def cash (M : Model) (i j : Fin 2) (qj t : ℝ) (ω : ℝ × ℝ) : ℝ :=
  let y := Model.deliv (M.K j) qj ω.1;
  -(M.η j*qj+(1-M.η j)*y)*M.c j + (M.r+M.p)*(t+y) -
    (M.r+M.p-M.v)*max (t+y-ω.2) 0-M.p*ω.2-((1-M.η i)*M.c i)*t

lemma cash_integrable (M : Model) (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμint : Integrable id μ) (i j : Fin 2) (qj t : ℝ)
    (hqj : 0 ≤ qj) : Integrable (cash M i j qj t) (ν.prod μ) := by
  have hd : Integrable (fun ω : ℝ × ℝ => Model.deliv (M.K j) qj ω.1) (ν.prod μ) := by
    apply (integrable_const qj).mono'
    · exact (show Continuous (fun ω : ℝ × ℝ => Model.deliv (M.K j) qj ω.1) by
        unfold Model.deliv; fun_prop).aestronglyMeasurable
    · apply ae_of_all
      intro ω
      unfold Model.deliv
      rw [Real.norm_of_nonneg (le_min hqj (le_max_right _ _))]
      exact min_le_left _ _
  have hx : Integrable (fun ω : ℝ × ℝ => ω.2) (ν.prod μ) := hμint.comp_snd ν
  have hcharge := ((integrable_const (M.η j*qj)).add (hd.const_mul (1-M.η j))).neg.mul_const (M.c j)
  have htotal := (integrable_const t).add hd
  have hover := ((htotal.sub hx).sup (integrable_const 0)).const_mul (M.r+M.p-M.v)
  exact (((hcharge.add (htotal.const_mul (M.r+M.p))).sub hover).sub (hx.const_mul M.p)).sub
    (integrable_const (((1-M.η i)*M.c i)*t))

noncomputable def cashBound (M : Model) (i : Fin 2) : NNReal :=
  ‖M.r+M.p‖₊+‖M.r+M.p-M.v‖₊+‖(1-M.η i)*M.c i‖₊

lemma cash_lipschitz (M : Model) (i j : Fin 2) (qj : ℝ) (ω : ℝ × ℝ) :
    LipschitzWith (cashBound M i) (fun t => cash M i j qj t ω) := by
  have hy : LipschitzWith 1 (fun t : ℝ => t+Model.deliv (M.K j) qj ω.1) :=
    by simpa using LipschitzWith.id.add (LipschitzWith.const (Model.deliv (M.K j) qj ω.1))
  have hz := (hy.sub (LipschitzWith.const ω.2)).max_const 0
  have h1 := SupplyExistence.lip_mul hy (M.r+M.p)
  have h2 := SupplyExistence.lip_mul hz (M.r+M.p-M.v)
  have h3 := SupplyExistence.lip_mul LipschitzWith.id ((1-M.η i)*M.c i)
  simpa [cash,cashBound] using
    ((((LipschitzWith.const (-(M.η j*qj+(1-M.η j)*Model.deliv (M.K j) qj ω.1)*M.c j)).add h1).sub h2).sub (LipschitzWith.const (M.p*ω.2))).sub h3

noncomputable def gain (M : Model) (μ ν : Measure ℝ) (i j : Fin 2) (qj t : ℝ) : ℝ :=
  ∫ ω, cash M i j qj t ω ∂ν.prod μ

lemma gain_continuous (M : Model) (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμint : Integrable id μ) (i j : Fin 2) (qj : ℝ)
    (hqj : 0 ≤ qj) : Continuous (gain M μ ν i j qj) := by
  suffices h : LipschitzWith (cashBound M i) (gain M μ ν i j qj) from h.continuous
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, gain, gain, ← integral_sub
    (cash_integrable M μ ν hμint i j qj u hqj) (cash_integrable M μ ν hμint i j qj v hqj)]
  have h := norm_integral_le_of_norm_le_const (μ := ν.prod μ)
    (ae_of_all _ (fun ω => (cash_lipschitz M i j qj ω).norm_sub_le u v))
  simpa [dist_eq_norm] using h

lemma cash_concave (M : Model) (i j : Fin 2) (qj : ℝ) (ω : ℝ × ℝ) :
    ConcaveOn ℝ univ (fun t => cash M i j qj t ω) := by
  refine ⟨convex_univ,?_⟩
  intro u _ v _ a b ha hb hab
  simp only [smul_eq_mul]
  let y := Model.deliv (M.K j) qj ω.1;
  have hmax : max ((a*u+b*v)+y-ω.2) 0 ≤ a*max (u+y-ω.2) 0+b*max (v+y-ω.2) 0 := by
    apply max_le
    · have h1 := mul_le_mul_of_nonneg_left (le_max_left (u+y-ω.2) 0) ha
      have h2 := mul_le_mul_of_nonneg_left (le_max_left (v+y-ω.2) 0) hb
      have he : (a+b)*(y-ω.2) = y-ω.2 := by rw [hab, one_mul]
      nlinarith only [h1,h2,he]
    · positivity
  have hh := mul_le_mul_of_nonneg_left hmax (sub_nonneg.mpr M.v_lt.le)
  dsimp [cash]
  dsimp [y] at hh
  linear_combination hh + (-(M.η j*qj+(1-M.η j)*Model.deliv (M.K j) qj ω.1)*M.c j +
    (M.r+M.p)*Model.deliv (M.K j) qj ω.1-M.p*ω.2)*hab

lemma gain_concave (M : Model) (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμint : Integrable id μ) (i j : Fin 2) (qj : ℝ)
    (hqj : 0 ≤ qj) : ConcaveOn ℝ univ (gain M μ ν i j qj) := by
  refine ⟨convex_univ,?_⟩
  intro u _ v _ a b ha hb hab
  simp only [smul_eq_mul, gain]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((cash_integrable M μ ν hμint i j qj u hqj).const_mul a)
    ((cash_integrable M μ ν hμint i j qj v hqj).const_mul b)]
  exact integral_mono
    (((cash_integrable M μ ν hμint i j qj u hqj).const_mul a).add
      ((cash_integrable M μ ν hμint i j qj v hqj).const_mul b))
    (cash_integrable M μ ν hμint i j qj (a*u+b*v) hqj)
    (fun ω => (cash_concave M i j qj ω).2 (mem_univ u) (mem_univ v) ha hb hab)

lemma profit_cash (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) (i j : Fin 2) (hij : i ≠ j) :
    M.profit q ξ x = cash M i j (q j) (Model.deliv (M.K i) (q i) (ξ i)) (ξ j,x)-M.η i*M.c i*q i := by
  rw [SupplySubmodularity.profit_identity]
  fin_cases i <;> fin_cases j <;> simp_all [cash, SupplySubmodularity.charge,
    SupplySubmodularity.quantity, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] <;> ring

lemma coordinate_law (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : Fin 2 → ℝ) (i j : Fin 2) (hij : i ≠ j) :
    MeasurePreserving (fun ω : (Fin 2 → ℝ) × ℝ => (ω.1 i,(ω.1 j,ω.2)))
      ((Measure.pi fun k => M.ν k (a k)).prod μ) ((M.ν i (a i)).prod ((M.ν j (a j)).prod μ)) := by
  let ν := fun k => M.ν k (a k)
  have hind : IndepFun (fun ξ : Fin 2 → ℝ => ξ i) (fun ξ => ξ j) (Measure.pi ν) :=
    (iIndepFun_pi (μ := ν) (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have hp : MeasurePreserving (fun ξ : Fin 2 → ℝ => (ξ i, ξ j)) (Measure.pi ν)
      ((ν i).prod (ν j)) := by
    refine ⟨by fun_prop,?_⟩
    rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable,
      (measurePreserving_eval ν i).map_eq, (measurePreserving_eval ν j).map_eq]
  exact (measurePreserving_prodAssoc (ν i) (ν j) μ).comp (hp.prod (MeasurePreserving.id μ))

lemma Pi2_gain (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a q : Fin 2 → ℝ) (hq : q ∈ Model.orders)
    (i j : Fin 2) (hij : i ≠ j) :
    M.Pi2 μ q a = (∫ ξ, gain M μ (M.ν j (a j)) i j (q j)
      (Model.deliv (M.K i) (q i) ξ) ∂M.ν i (a i))-M.η i*M.c i*q i := by
  let H := fun ω : ℝ × (ℝ × ℝ) =>
    cash M i j (q j) (Model.deliv (M.K i) (q i) ω.1) ω.2-M.η i*M.c i*q i
  have hmeas : Continuous H := by unfold H cash Model.deliv; fun_prop
  have hp := coordinate_law M μ a i j hij
  have he : (fun ω : (Fin 2 → ℝ) × ℝ => M.profit q ω.1 ω.2) =
      H ∘ (fun ω => (ω.1 i,(ω.1 j,ω.2))) := by
    funext ω
    exact profit_cash M q ω.1 ω.2 i j hij
  have hI : Integrable H ((M.ν i (a i)).prod ((M.ν j (a j)).prod μ)) := by
    apply (hp.integrable_comp hmeas.aestronglyMeasurable).mp
    rw [← he]
    exact SupplyExistence.integrable_profit M μ hμint a q
  have heq : M.Pi2 μ q a = ∫ ω, H ω ∂((M.ν i (a i)).prod ((M.ν j (a j)).prod μ)) := by
    unfold Model.Pi2
    rw [he, ← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hmeas.aestronglyMeasurable).symm
  rw [heq, integral_prod _ hI]
  have heach (ξ : ℝ) : (∫ ω, H (ξ,ω) ∂(M.ν j (a j)).prod μ) =
      gain M μ (M.ν j (a j)) i j (q j) (Model.deliv (M.K i) (q i) ξ)-M.η i*M.c i*q i := by
    dsimp [H,gain]
    rw [integral_sub (cash_integrable M μ (M.ν j (a j)) hμint i j (q j) _ (hq j))
      (integrable_const _)]; simp
  simp_rw [heach]
  have houter : Integrable (fun ξ => gain M μ (M.ν j (a j)) i j (q j)
      (Model.deliv (M.K i) (q i) ξ)) (M.ν i (a i)) := by
    have hh := hI.integral_prod_left
    simp_rw [heach] at hh
    apply (hh.add (integrable_const (M.η i*M.c i*q i))).congr
    exact ae_of_all _ (fun ξ => sub_add_cancel _ _)
  rw [integral_sub houter (integrable_const _)]; simp

end SupplyReliability

namespace SupplyReliability
open MitigateSupplyRisk.DualSourcing

lemma clipped_value_le (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (q a : Fin 2 → ℝ) :
    M.Pi2 μ q a ≤ M.Pi2 μ (fun k => min (q k) (M.K k)) a := by
  apply integral_mono_ae (SupplyExistence.integrable_profit M μ hμint a q)
    (SupplyExistence.integrable_profit M μ hμint a _)
  filter_upwards [SupplyExistence.ae_capacity_nonneg M μ a] with ω hω
  exact SupplyExistence.clip_profit M q ω.1 ω.2 hω

lemma value_reliability_mono (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a : Fin 2 → ℝ) (i : Fin 2) (t t' : ℝ) (htt : t ≤ t')
    (q : Fin 2 → ℝ) (hq : q ∈ Model.orders) :
    ∃ q' ∈ Model.orders,
      M.Pi2 μ q (Function.update a i t) ≤ M.Pi2 μ q' (Function.update a i t') := by
  obtain ⟨j,hij⟩ : ∃ j : Fin 2, i ≠ j := by
    fin_cases i
    · exact ⟨1,by decide⟩
    · exact ⟨0,by decide⟩
  have hji := hij.symm
  let qc := fun k => min (q k) (M.K k)
  have hqc (k : Fin 2) : qc k ∈ Icc 0 (M.K k) :=
    ⟨le_min (hq k) (M.K_pos k).le,min_le_right _ _⟩
  let f := gain M μ (M.ν j (a j)) i j (qc j)
  obtain ⟨u,hu,hgain⟩ := reoptimize_one_coordinate (M.ν i t) (M.ν i t')
    (M.ν_mono i t t' htt) (gain_continuous M μ (M.ν j (a j)) hμint i j (qc j) (hqc j).1)
    (M.K_pos i).le
    ((gain_concave M μ (M.ν j (a j)) hμint i j (qc j) (hqc j).1).subset
      (subset_univ _) (convex_Icc _ _))
    (mul_nonneg (M.η_nonneg i) (M.c_nonneg i)) (hqc i)
  let q' := Function.update qc i u
  have hq' : q' ∈ Model.orders := by
    intro k
    by_cases hk : k=i
    · subst k
      simpa [q'] using hu.1
    · simpa [q',Function.update_of_ne hk] using (hqc k).1
  refine ⟨q',hq',le_trans (clipped_value_le M μ hμint q (Function.update a i t)) ?_⟩
  change M.Pi2 μ qc (Function.update a i t) ≤ M.Pi2 μ q' (Function.update a i t')
  rw [Pi2_gain M μ hμint _ qc (fun k => (hqc k).1) i j hij,
    Pi2_gain M μ hμint _ q' hq' i j hij]
  simpa [q',Function.update_of_ne hji] using hgain

end SupplyReliability

open MitigateSupplyRisk.DualSourcing

theorem solution (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (i : Fin 2) (a : Fin 2 → ℝ) :
    Monotone (fun t : ℝ => M.Pi2star μ (Function.update a i t)) := by
  intro t t' htt
  obtain ⟨qmax,hmax⟩ := SupplyExistence.optimal_exists M μ hμint (Function.update a i t')
  have hb : BddAbove ((fun q => M.Pi2 μ q (Function.update a i t')) '' Model.orders) := by
    refine ⟨M.Pi2 μ qmax (Function.update a i t'),?_⟩
    rintro _ ⟨q,hq,rfl⟩
    exact hmax.2 q hq
  unfold Model.Pi2star
  apply csSup_le
  · exact ⟨_,⟨0,(fun _ => le_rfl),rfl⟩⟩
  · rintro _ ⟨q,hq,rfl⟩
    obtain ⟨q',hq',hle⟩ := SupplyReliability.value_reliability_mono M μ hμint a i t t' htt q hq
    exact hle.trans (le_csSup hb ⟨q',hq',rfl⟩)

#print axioms solution

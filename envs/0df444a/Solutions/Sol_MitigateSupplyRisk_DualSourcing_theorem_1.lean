-- Prove2me | solution 1 for MitigateSupplyRisk.DualSourcing.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T09:26:44.875836+00:00
-- url     : https://prove2.me/submissions/8ed08cea-6a98-4cd3-a968-c48d7b76618a

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

theorem solution (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
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

#print axioms solution

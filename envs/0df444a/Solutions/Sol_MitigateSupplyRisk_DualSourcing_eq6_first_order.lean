-- Prove2me | solution 1 for MitigateSupplyRisk.DualSourcing.eq6_first_order
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T10:42:48.761967+00:00
-- url     : https://prove2.me/submissions/1cbda48d-c378-4473-92e6-f21a355cd27a

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

namespace SupplyCDF
open SupplySubmodularity SupplyExistence

lemma deriv_min {f : ℝ → ℝ} {d t c : ℝ} (hf : HasDerivAt f d t) (hne : f t ≠ c) :
    HasDerivAt (fun x => min (f x) c) (if f t < c then d else 0) t := by
  by_cases h : f t < c
  · rw [if_pos h]
    apply hf.congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (Iio_mem_nhds h)] with x hx
    exact min_eq_left hx.le
  · rw [if_neg h]
    have hc : c < f t := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
    apply (hasDerivAt_const t c).congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds hc)] with x hx
    exact min_eq_right hx.le

lemma deriv_max {f : ℝ → ℝ} {d t c : ℝ} (hf : HasDerivAt f d t) (hne : f t ≠ c) :
    HasDerivAt (fun x => max (f x) c) (if c < f t then d else 0) t := by
  by_cases h : c < f t
  · rw [if_pos h]
    apply hf.congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds h)] with x hx
    exact max_eq_left hx.le
  · rw [if_neg h]
    have hc : f t < c := lt_of_le_of_ne (le_of_not_gt h) hne
    apply (hasDerivAt_const t c).congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (Iio_mem_nhds hc)] with x hx
    exact max_eq_right hx.le

noncomputable def cap (M : Model) (q ξ : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if ξ i < M.K i-q i then 1 else 0

noncomputable def marginal (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) (i j : Fin 2) : ℝ :=
  -(M.η i*M.c i) + cap M q ξ i *
    (M.r+M.p-(1-M.η i)*M.c i - (M.r+M.p-M.v) *
      (if x < q i + Model.deliv (M.K j) (q j) (ξ j) then 1 else 0))

lemma profit_deriv (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) (i j : Fin 2)
    (hij : i ≠ j) (hqi : 0 < q i)
    (hcap : q i ≠ max (M.K i-ξ i) 0) (hx : quantity M q ξ ≠ x) :
    HasDerivAt (fun t => M.profit (Function.update q i t) ξ x)
      (marginal M q ξ x i j) (q i) := by
  have hc : (q i < max (M.K i-ξ i) 0) ↔ ξ i < M.K i-q i := by
    rw [lt_max_iff]
    constructor
    · intro h; rcases h with h | h <;> linarith
    · intro h; exact Or.inl (by linarith)
  have hd (k : Fin 2) : HasDerivAt (fun t =>
      Model.deliv (M.K k) (Function.update q i t k) (ξ k))
      (if k=i then cap M q ξ i else 0) (q i) := by
    by_cases hk : k=i
    · subst k
      simpa [Model.deliv,cap,hc] using deriv_min (hasDerivAt_id (q i)) hcap
    · simpa [Function.update_of_ne hk,hk] using hasDerivAt_const (q i)
        (Model.deliv (M.K k) (q k) (ξ k))
  have he (k : Fin 2) : HasDerivAt (fun t => Function.update q i t k)
      (if k=i then (1:ℝ) else 0) (q i) := by
    by_cases hk : k=i
    · subst k; simpa using hasDerivAt_id' (q i)
    · simpa [Function.update_of_ne hk,hk] using hasDerivAt_const (q i) (q k)
  have hy : HasDerivAt (fun t => quantity M (Function.update q i t) ξ)
      (cap M q ξ i) (q i) := by
    simpa [quantity] using HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hd k)
  have hcharge : HasDerivAt (fun t => charge M (Function.update q i t) ξ)
      ((M.η i+(1-M.η i)*cap M q ξ i)*M.c i) (q i) := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (((he k).const_mul (M.η k)).add ((hd k).const_mul (1-M.η k))).mul_const (M.c k))
    fin_cases i <;> simpa [charge, Fin.sum_univ_two] using hsum
  have hne : quantity M (Function.update q i (q i)) ξ-x ≠ 0 := by
    simpa using sub_ne_zero.mpr hx
  have hm := deriv_max (hy.sub_const x) hne
  have h := ((hcharge.neg.add (hy.const_mul (M.r+M.p))).sub
    (hm.const_mul (M.r+M.p-M.v))).sub (hasDerivAt_const (q i) (M.p*x))
  simp only [Function.update_eq_self] at h
  simp_rw [profit_identity]
  convert h using 1 <;> try rfl
  unfold marginal
  by_cases hh : ξ i < M.K i-q i
  · have hdel : Model.deliv (M.K i) (q i) (ξ i) = q i := by
      unfold Model.deliv
      exact min_eq_left (hc.mpr hh).le
    have hyval : quantity M q ξ = q i + Model.deliv (M.K j) (q j) (ξ j) := by
      fin_cases i <;> fin_cases j <;> simp_all [quantity,Fin.sum_univ_two,add_comm]
    simp only [hyval,sub_pos,cap,if_pos hh]
    split_ifs <;> ring
  · simp [cap,hh]

#print axioms profit_deriv
end SupplyCDF

namespace SupplyCDF
open SupplySubmodularity SupplyExistence

lemma indicator_integral (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ)
    (hn : μ {t} = 0) : (∫ x, (if x < t then (1:ℝ) else 0) ∂μ) = cdf μ t := by
  have he : (fun x => if x<t then (1:ℝ) else 0) = (Set.Iio t).indicator (fun _ => (1:ℝ)) := by
    funext x; simp [Set.indicator]
  rw [he, integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio' hn]
  simp [cdf_eq_real]

lemma measurable_cap (M : Model) (q : Fin 2 → ℝ) (i : Fin 2) :
    Measurable (fun ξ => cap M q ξ i) := by
  unfold cap
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply i) measurable_const)
    measurable_const measurable_const

lemma measurable_marginal (M : Model) (q : Fin 2 → ℝ) (i j : Fin 2) :
    Measurable (fun ω : (Fin 2 → ℝ) × ℝ => marginal M q ω.1 ω.2 i j) := by
  unfold marginal
  apply Measurable.add measurable_const
  apply Measurable.mul ((measurable_cap M q i).comp measurable_fst)
  apply Measurable.sub measurable_const
  apply Measurable.const_mul
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt measurable_snd (by unfold Model.deliv; fun_prop)

lemma integrable_bounded {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (f : Ω → ℝ) (h : Measurable f) (C : ℝ) (hb : ∀ ω, |f ω| ≤ C) : Integrable f ν := by
  apply (integrable_const C).mono' h.aestronglyMeasurable
  exact ae_of_all _ (by simpa [Real.norm_eq_abs] using hb)

lemma integrable_marginal (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a q : Fin 2 → ℝ) (i j : Fin 2) :
    Integrable (fun ω : (Fin 2 → ℝ) × ℝ => marginal M q ω.1 ω.2 i j)
      ((Measure.pi fun k => M.ν k (a k)).prod μ) := by
  apply integrable_bounded _ _ (measurable_marginal M q i j)
    (|M.η i*M.c i| + |M.r+M.p-(1-M.η i)*M.c i| + |M.r+M.p-M.v|)
  intro ω
  unfold marginal cap
  split_ifs <;> simp only [zero_mul,one_mul,mul_one,mul_zero,add_zero,sub_zero]
  · calc
      _ ≤ |-(M.η i*M.c i)| + |M.r+M.p-(1-M.η i)*M.c i - (M.r+M.p-M.v)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith [abs_sub (M.r+M.p-(1-M.η i)*M.c i) (M.r+M.p-M.v)]
  · calc
      _ ≤ |-(M.η i*M.c i)| + |M.r+M.p-(1-M.η i)*M.c i| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith [abs_nonneg (M.r+M.p-M.v)]
  · rw [abs_neg]
    linarith [abs_nonneg (M.r+M.p-(1-M.η i)*M.c i), abs_nonneg (M.r+M.p-M.v)]
  · rw [abs_neg]
    linarith [abs_nonneg (M.r+M.p-(1-M.η i)*M.c i), abs_nonneg (M.r+M.p-M.v)]

lemma ae_marginal_deriv (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμac : μ ≪ volume) (a q : Fin 2 → ℝ) (i j : Fin 2) (hij : i ≠ j) (hqi : 0 < q i) :
    ∀ᵐ ω : (Fin 2 → ℝ) × ℝ ∂((Measure.pi fun k => M.ν k (a k)).prod μ),
      HasDerivAt (fun t => M.profit (Function.update q i t) ω.1 ω.2)
        (marginal M q ω.1 ω.2 i j) (q i) := by
  letI : NullSingletonClass (M.ν i (a i)) := ⟨M.ν_noAtoms i (a i)⟩
  have hz := Measure.ae_eval_ne (fun k => M.ν k (a k)) i (M.K i-q i)
  have hc : ∀ᵐ ξ ∂Measure.pi (fun k => M.ν k (a k)), q i ≠ max (M.K i-ξ i) 0 := by
    filter_upwards [hz] with ξ hξ
    intro h
    by_cases hh : 0 ≤ M.K i-ξ i
    · rw [max_eq_left hh] at h; apply hξ; linarith
    · rw [max_eq_right (le_of_not_ge hh)] at h; linarith
  have hcp : ∀ᵐ ω : (Fin 2 → ℝ) × ℝ ∂((Measure.pi fun k => M.ν k (a k)).prod μ),
      q i ≠ max (M.K i-ω.1 i) 0 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae.eventually hc
  have hx : ∀ᵐ ω : (Fin 2 → ℝ) × ℝ ∂((Measure.pi fun k => M.ν k (a k)).prod μ),
      quantity M q ω.1 ≠ ω.2 := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · apply ae_of_all
      intro ξ
      apply hμac.ae_le
      have h : ∀ᵐ x : ℝ, x ≠ quantity M q ξ := by rw [ae_iff]; simp
      exact h.mono (fun x hx => Ne.symm hx)
    · exact (isClosed_eq (by unfold quantity Model.deliv; fun_prop) continuous_snd).measurableSet.compl
  filter_upwards [hcp,hx] with ω hcap hx
  exact profit_deriv M q ω.1 ω.2 i j hij hqi hcap hx

lemma Pi2_deriv_integral (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (hμac : μ ≪ volume) (a q : Fin 2 → ℝ)
    (i j : Fin 2) (hij : i ≠ j) (hqi : 0 < q i) :
    HasDerivAt (fun t => M.Pi2 μ (Function.update q i t) a)
      (∫ ω, marginal M q ω.1 ω.2 i j ∂((Measure.pi fun k => M.ν k (a k)).prod μ)) (q i) := by
  let ν := (Measure.pi fun k => M.ν k (a k)).prod μ
  let F := fun (t : ℝ) (ω : (Fin 2 → ℝ) × ℝ) => M.profit (Function.update q i t) ω.1 ω.2
  have hm := (measurable_marginal M q i j).aestronglyMeasurable (μ := ν)
  have hl : ∀ᵐ ω ∂ν, LipschitzOnWith (Real.nnabs (lipBound M : ℝ)) (fun t => F t ω) Set.univ := by
    apply ae_of_all
    intro ω
    have h := (profit_lipschitz M ω.1 ω.2).comp (update_lipschitz q i)
    simpa only [mul_one, Real.nnabs_coe, Function.comp_def, F] using h.lipschitzOnWith (s := Set.univ)
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (μ := ν) (s := Set.univ) (bound := fun _ => (lipBound M : ℝ))
    Filter.univ_mem (Filter.Eventually.of_forall (fun t =>
      (integrable_profit M μ hμint a (Function.update q i t)).aestronglyMeasurable))
    (integrable_profit M μ hμint a _) hm hl (integrable_const _)
    (ae_marginal_deriv M μ hμac a q i j hij hqi)
  exact h.2

#print axioms Pi2_deriv_integral
end SupplyCDF

namespace SupplyCDF
open SupplySubmodularity SupplyExistence

lemma marginal_inner (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμac : μ ≪ volume) (q ξ : Fin 2 → ℝ) (i j : Fin 2) :
    (∫ x, marginal M q ξ x i j ∂μ) =
      -(M.η i*M.c i) + cap M q ξ i *
        (M.r+M.p-(1-M.η i)*M.c i - (M.r+M.p-M.v) *
          cdf μ (q i + Model.deliv (M.K j) (q j) (ξ j))) := by
  let t := q i + Model.deliv (M.K j) (q j) (ξ j)
  have hi : Integrable (fun x => if x<t then (1:ℝ) else 0) μ := by
    apply integrable_bounded _ _ (Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const) 1
    intro x; split_ifs <;> norm_num
  dsimp [t] at hi
  have hb : Integrable (fun x => (M.r+M.p-M.v) *
      (if x<q i + Model.deliv (M.K j) (q j) (ξ j) then (1:ℝ) else 0)) μ := hi.const_mul _
  have hs : Integrable (fun x => M.r+M.p-(1-M.η i)*M.c i - (M.r+M.p-M.v) *
      (if x<q i + Model.deliv (M.K j) (q j) (ξ j) then (1:ℝ) else 0)) μ := by
    exact ((integrable_const (M.r+M.p-(1-M.η i)*M.c i)).sub hb).congr
      (Filter.Eventually.of_forall (fun x => rfl))
  unfold marginal
  rw [integral_add (integrable_const _) (hs.const_mul _), integral_const_mul,
    integral_sub (integrable_const _) hb, integral_const_mul]
  rw [indicator_integral μ t (hμac (by simp))]
  simp [t]

lemma integral_cap_cdf (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a q : Fin 2 → ℝ) (i j : Fin 2) (hij : i ≠ j) :
    (∫ ξ, cap M q ξ i * cdf μ (q i + Model.deliv (M.K j) (q j) (ξ j))
      ∂Measure.pi (fun k => M.ν k (a k))) =
    M.G i (M.K i-q i) (a i) *
      ∫ s, cdf μ (q i + Model.deliv (M.K j) (q j) s) ∂M.ν j (a j) := by
  let ν := fun k => M.ν k (a k)
  have hc : Measurable (fun x : ℝ => if x<M.K i-q i then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  have hf : Measurable (fun x => cdf μ (q i + Model.deliv (M.K j) (q j) x)) :=
    (monotone_cdf μ).measurable.comp (by unfold Model.deliv; fun_prop)
  have hind : IndepFun (fun ξ : Fin 2 → ℝ => ξ i) (fun ξ => ξ j) (Measure.pi ν) :=
    (iIndepFun_pi (μ := ν) (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have h := (hind.comp hc hf).integral_fun_mul_eq_mul_integral
    (hc.comp (measurable_pi_apply i)).aestronglyMeasurable
    (hf.comp (measurable_pi_apply j)).aestronglyMeasurable
  change (∫ ξ, (if ξ i<M.K i-q i then (1:ℝ) else 0) *
      cdf μ (q i + Model.deliv (M.K j) (q j) (ξ j)) ∂Measure.pi ν) = _
  simp only [Function.comp_def] at h
  rw [h, integral_comp_eval (μ := ν) (i := i) hc.aestronglyMeasurable,
    integral_comp_eval (μ := ν) (i := j) hf.aestronglyMeasurable]
  rw [indicator_integral (ν i) _ (M.ν_noAtoms i (a i) _)]; rfl

lemma marginal_integral (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμac : μ ≪ volume) (a q : Fin 2 → ℝ) (i j : Fin 2) (hij : i ≠ j) :
    (∫ ω, marginal M q ω.1 ω.2 i j ∂((Measure.pi fun k => M.ν k (a k)).prod μ)) =
      (M.r+M.p-M.v) * (M.psi i + M.G i (M.K i-q i) (a i) *
        (M.phi i - ∫ s, cdf μ (q i + Model.deliv (M.K j) (q j) s) ∂M.ν j (a j))) := by
  let ν := Measure.pi fun k => M.ν k (a k)
  have hc : Integrable (fun ξ => cap M q ξ i) ν := by
    apply integrable_bounded _ _ (measurable_cap M q i) 1
    intro ξ; unfold cap; split_ifs <;> norm_num
  have hf : Measurable (fun ξ : Fin 2 → ℝ => cdf μ (q i + Model.deliv (M.K j) (q j) (ξ j))) :=
    (monotone_cdf μ).measurable.comp (by unfold Model.deliv; fun_prop)
  have hcf : Integrable (fun ξ => cap M q ξ i * cdf μ (q i + Model.deliv (M.K j) (q j) (ξ j))) ν := by
    apply integrable_bounded _ _ ((measurable_cap M q i).mul hf) 1
    intro ξ
    dsimp only [Pi.mul_apply,cap]
    split_ifs <;> simp only [one_mul,zero_mul,abs_zero]
    · rw [abs_of_nonneg (cdf_nonneg _ _)]; exact cdf_le_one _ _
    · norm_num
  have hci : (∫ ξ, cap M q ξ i ∂ν) = M.G i (M.K i-q i) (a i) := by
    unfold cap ν
    have hi : Measurable (fun x : ℝ => if x < M.K i-q i then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
    rw [integral_comp_eval (μ := fun k => M.ν k (a k)) (i := i) hi.aestronglyMeasurable]
    exact indicator_integral _ _ (M.ν_noAtoms i (a i) _)
  rw [integral_prod _ (integrable_marginal M μ a q i j)]
  simp_rw [marginal_inner M μ hμac q _ i j]
  have he : (fun ξ => -(M.η i*M.c i) + cap M q ξ i *
      (M.r+M.p-(1-M.η i)*M.c i - (M.r+M.p-M.v) *
        cdf μ (q i + Model.deliv (M.K j) (q j) (ξ j)))) =
    (fun ξ => -(M.η i*M.c i) + (M.r+M.p-(1-M.η i)*M.c i)*cap M q ξ i -
      (M.r+M.p-M.v) * (cap M q ξ i * cdf μ (q i + Model.deliv (M.K j) (q j) (ξ j)))) := by
    funext ξ; ring
  rw [he, integral_sub ((integrable_const _).fun_add (hc.const_mul _)) (hcf.const_mul _),
    integral_add (integrable_const _) (hc.const_mul _), integral_const_mul, integral_const_mul,
    integral_cap_cdf M μ a q i j hij]
  change _ + _ * (∫ ξ, cap M q ξ i ∂ν) - _ = _
  rw [hci]
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  unfold Model.psi Model.phi
  have hd : M.r+M.p-M.v ≠ 0 := ne_of_gt (sub_pos.mpr M.v_lt)
  field_simp [hd]
  <;> ring

#print axioms marginal_integral
end SupplyCDF

theorem solution (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (hμac : μ ≪ volume)
    (a q : Fin 2 → ℝ) (hq : q ∈ Model.orders) (i j : Fin 2) (hij : i ≠ j)
    (hqi0 : 0 < q i) (hqiK : q i < M.K i) :
    HasDerivAt (fun t => M.Pi2 μ (Function.update q i t) a)
      ((M.r + M.p - M.v) * (M.psi i + M.G i (M.K i - q i) (a i) *
        (M.phi i - ∫ s, cdf μ (q i + Model.deliv (M.K j) (q j) s) ∂(M.ν j (a j))))) (q i) ∧
    (M.IsOptimal μ a q →
      M.psi i + M.G i (M.K i - q i) (a i) *
        (M.phi i - ∫ s, cdf μ (q i + Model.deliv (M.K j) (q j) s) ∂(M.ν j (a j))) = 0) := by
  have hd := SupplyCDF.Pi2_deriv_integral M μ hμint hμac a q i j hij hqi0
  rw [SupplyCDF.marginal_integral M μ hμac a q i j hij] at hd
  refine ⟨hd,fun ho => ?_⟩
  have hm : IsLocalMax (fun t => M.Pi2 μ (Function.update q i t) a) (q i) := by
    filter_upwards [Ioi_mem_nhds hqi0] with t ht
    have hf : Function.update q i t ∈ Model.orders := by
      intro k
      by_cases hk : k=i
      · subst k; simpa using ht.le
      · simpa [Function.update_of_ne hk] using hq k
    simpa only [Function.update_eq_self] using ho.2 (Function.update q i t) hf
  have hz := hm.hasDerivAt_eq_zero hd
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr M.v_lt))

#print axioms solution

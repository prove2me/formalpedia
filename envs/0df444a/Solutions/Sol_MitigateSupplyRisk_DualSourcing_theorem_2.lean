-- Prove2me | solution 1 for MitigateSupplyRisk.DualSourcing.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T16:11:08.477988+00:00
-- url     : https://prove2.me/submissions/2b8b367e-f9f2-4574-8d76-0450fb691b10

/-
Complete corrected region-by-region optimality, Wang--Gilland--Tomlin (2010), Theorem 2.
Original mathematics: Yimin Wang, Wendell Gilland and Brian Tomlin.
Platform model, added hypotheses and corrected min/max region bounds: mikedeng1.
Shuze Chen supplied prior statement confirmation, not proof review.
Alexander Richard Towell (queelius): research direction and stewardship.
OpenAI Codex: substantial proof construction, formalization, verification and documentation.
Lean and Mathlib contributors: the underlying formal proof infrastructure.
The full accepted submodularity, Theorem 1 and Equation 6 bodies are retained inline;
prior local threshold and hedged-region proofs are retained with declaration renaming.
The retained older local header refers to prior_hedge only. The final solution below
also proves Omega1 and Omega2, completing every conjunct of the current corrected target.
The original printed region bounds are not silently proved or reinterpreted.
No mathematical novelty or independent human review is claimed.
-/
-- Source mathematics: Yimin Wang, Wendell Gilland and Brian Tomlin (2010),
-- Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Theorem 2.
-- Platform model and corrected region bounds: mikedeng1.
-- Prior platform statement confirmation: Shuze Chen; not new proof review.
-- Research direction and stewardship: Alexander Richard Towell (queelius).
-- Substantial proof construction, checking and documentation: OpenAI Codex.
-- Retains accepted queelius Equation 6 / Theorem 1 / submodularity bodies,
-- and the earlier locally checked threshold/balance proof, with declaration renaming.
-- The new Dirac-demand derivative is proved separately; no absolute continuity
-- of the point-mass demand law is assumed. Lean/Mathlib infrastructure is credited.
-- This local theorem proves regions Omega3--Omega6 only. Omega1 and Omega2
-- remain unresolved; this is not a proof or submission of the complete Theorem 2.

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Regions
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

theorem prior_cdf_derivative (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
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

#print axioms prior_cdf_derivative


namespace SupplyDeterministic
open SupplySubmodularity SupplyExistence

lemma profit_unsaturated (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ)
    (hη : ∀ i, M.η i = 0) (h : quantity M q ξ ≤ x) :
    M.profit q ξ x =
      (M.r + M.p - M.c 0) * Model.deliv (M.K 0) (q 0) (ξ 0) +
      (M.r + M.p - M.c 1) * Model.deliv (M.K 1) (q 1) (ξ 1) - M.p*x := by
  rw [profit_identity, max_eq_right (sub_nonpos.mpr h)]
  simp only [charge, quantity, Fin.sum_univ_two, hη, zero_mul, zero_add,
    sub_zero, one_mul, sub_self]
  ring

lemma margin_nonneg (M : Model) (hη : ∀ i, M.η i = 0)
    (hφ : ∀ i, 0 ≤ M.phi i) (i : Fin 2) : 0 ≤ M.r + M.p - M.c i := by
  have h := hφ i
  simp only [Model.phi, hη, sub_zero, one_mul] at h
  have hh := (le_div_iff₀ (sub_pos.mpr M.v_lt)).mp h
  simpa using hh

lemma deliv_capacity (M : Model) (q ξ : Fin 2 → ℝ) (hξ : ∀ i, 0 ≤ ξ i)
    (i : Fin 2) : Model.deliv (M.K i) (q i) (ξ i) ≤
      Model.deliv (M.K i) (M.K i) (ξ i) := by
  have hc : max (M.K i - ξ i) 0 ≤ M.K i :=
    max_le (sub_le_self _ (hξ i)) (M.K_pos i).le
  simpa only [Model.deliv, min_eq_right hc] using
    (min_le_right (q i) (max (M.K i-ξ i) 0))

lemma high_demand_pointwise (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i)
    (hξ : ∀ i, 0 ≤ ξ i) (hx : M.K 0 + M.K 1 ≤ x) :
    M.profit q ξ x ≤ M.profit M.K ξ x := by
  have hfull : quantity M M.K ξ ≤ x := by
    have h0 := min_le_left (M.K 0) (max (M.K 0-ξ 0) 0)
    have h1 := min_le_left (M.K 1) (max (M.K 1-ξ 1) 0)
    simpa only [quantity, Fin.sum_univ_two, Model.deliv] using
      (le_trans (add_le_add h0 h1) hx)
  have hq : quantity M q ξ ≤ quantity M M.K ξ := by
    apply Finset.sum_le_sum
    intro i _
    exact deliv_capacity M q ξ hξ i
  rw [profit_unsaturated M q ξ x hη (hq.trans hfull),
    profit_unsaturated M M.K ξ x hη hfull]
  exact sub_le_sub_right (add_le_add
    (mul_le_mul_of_nonneg_left (deliv_capacity M q ξ hξ 0) (margin_nonneg M hη hφ 0))
    (mul_le_mul_of_nonneg_left (deliv_capacity M q ξ hξ 1) (margin_nonneg M hη hφ 1))) _

lemma high_demand_optimal (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a : Fin 2 → ℝ)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i)
    (hμ : ∀ᵐ x ∂μ, M.K 0 + M.K 1 ≤ x) : M.IsOptimal μ a M.K := by
  refine ⟨fun i => (M.K_pos i).le, ?_⟩
  intro q hq
  apply integral_mono_ae (integrable_profit M μ hμint a q)
    (integrable_profit M μ hμint a M.K)
  have hd : ∀ᵐ ω : (Fin 2 → ℝ) × ℝ ∂((Measure.pi fun i => M.ν i (a i)).prod μ),
      M.K 0 + M.K 1 ≤ ω.2 :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae.eventually hμ
  filter_upwards [ae_capacity_nonneg M μ a, hd] with ω hξ hx
  exact high_demand_pointwise M q ω.1 ω.2 hη hφ hξ hx

lemma high_demand_dirac (M : Model) (a : Fin 2 → ℝ) (x : ℝ)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i)
    (hx : M.K 0 + M.K 1 ≤ x) : M.IsOptimal (Measure.dirac x) a M.K := by
  apply high_demand_optimal M (Measure.dirac x) (integrable_dirac (by simp)) a hη hφ
  simpa [ae_dirac_eq] using hx

lemma zero_demand_pointwise (M : Model) (q ξ : Fin 2 → ℝ)
    (hη : ∀ i, M.η i = 0) (hc : ∀ i, M.v ≤ M.c i)
    (hq : ∀ i, 0 ≤ q i) : M.profit q ξ 0 ≤ M.profit 0 ξ 0 := by
  have hd (i : Fin 2) : 0 ≤ Model.deliv (M.K i) (q i) (ξ i) :=
    le_min (hq i) (le_max_right _ _)
  have hy : 0 ≤ quantity M q ξ := Finset.sum_nonneg (fun i _ => hd i)
  have h0 : M.profit 0 ξ 0 = 0 := by
    simp [Model.profit, Model.deliv, min_eq_left (le_max_right _ _)]
  rw [h0, profit_identity, max_eq_left (by simpa using hy)]
  have hc0 := mul_nonneg (sub_nonneg.mpr (hc 0)) (hd 0)
  have hc1 := mul_nonneg (sub_nonneg.mpr (hc 1)) (hd 1)
  simp only [charge, quantity, Fin.sum_univ_two, hη, zero_mul, zero_add,
    sub_zero, one_mul] at *
  nlinarith

lemma salvage_le_cost (M : Model) (hη : ∀ i, M.η i = 0)
    (hφ : ∀ i, M.phi i ≤ 1) (i : Fin 2) : M.v ≤ M.c i := by
  have h := hφ i
  simp only [Model.phi, hη, sub_zero, one_mul] at h
  have hh := (div_le_one (sub_pos.mpr M.v_lt)).mp h
  linarith

lemma zero_demand_optimal (M : Model) (a : Fin 2 → ℝ)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, M.phi i ≤ 1) :
    M.IsOptimal (Measure.dirac 0) a 0 := by
  refine ⟨fun _ => le_rfl, ?_⟩
  intro q hq
  apply integral_mono_ae (integrable_profit M (Measure.dirac 0) (integrable_dirac (by simp)) a q)
    (integrable_profit M (Measure.dirac 0) (integrable_dirac (by simp)) a 0)
  have hz : ∀ᵐ y : ℝ ∂Measure.dirac (0 : ℝ), y = 0 := by simp [ae_dirac_eq]
  have hd : ∀ᵐ ω : (Fin 2 → ℝ) × ℝ
      ∂((Measure.pi fun i => M.ν i (a i)).prod (Measure.dirac (0 : ℝ))), ω.2 = 0 :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae.eventually hz
  filter_upwards [hd] with ω h
  rw [h]
  exact zero_demand_pointwise M q ω.1 hη (salvage_le_cost M hη hφ) hq

end SupplyDeterministic

namespace SupplyDeterministic
open SupplySubmodularity SupplyExistence

lemma hinge_separable (u v a b x : ℝ) (hu : u ≤ x) (hv : v ≤ x)
    (h : x ≤ u+v) :
    max (min u a + min v b - x) 0 + max (min x a + min x b - x) 0 =
      max (min u a + min x b - x) 0 + max (min x a + min v b - x) 0 := by
  by_cases ha : a ≤ u
  · simp only [min_eq_right ha, min_eq_right (ha.trans hu)]
    ring
  by_cases hb : b ≤ v
  · simp only [min_eq_right hb, min_eq_right (hb.trans hv)]
  have ha' : u ≤ a := (lt_of_not_ge ha).le
  have hb' : v ≤ b := (lt_of_not_ge hb).le
  have hxa : u ≤ min x a := le_min hu ha'
  have hxb : v ≤ min x b := le_min hv hb'
  rw [min_eq_left ha', min_eq_left hb']
  rw [max_eq_left (by linarith : 0 ≤ u+v-x),
    max_eq_left (by linarith : 0 ≤ min x a + min x b-x),
    max_eq_left (by linarith : 0 ≤ u+min x b-x),
    max_eq_left (by linarith : 0 ≤ min x a+v-x)]
  ring

lemma profit_separable (M : Model) (ξ : Fin 2 → ℝ) (u v x : ℝ)
    (hu : u ≤ x) (hv : v ≤ x) (h : x ≤ u+v) :
    M.profit ![u,v] ξ x + M.profit ![x,x] ξ x =
      M.profit ![u,x] ξ x + M.profit ![x,v] ξ x := by
  have hc : charge M ![u,v] ξ + charge M ![x,x] ξ =
      charge M ![u,x] ξ + charge M ![x,v] ξ := by
    simp only [charge, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  have hq : quantity M ![u,v] ξ + quantity M ![x,x] ξ =
      quantity M ![u,x] ξ + quantity M ![x,v] ξ := by
    simp only [quantity, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  have hh : max (quantity M ![u,v] ξ-x) 0 + max (quantity M ![x,x] ξ-x) 0 =
      max (quantity M ![u,x] ξ-x) 0 + max (quantity M ![x,v] ξ-x) 0 := by
    simpa only [quantity, Fin.sum_univ_two, Model.deliv, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] using
      hinge_separable u v (max (M.K 0-ξ 0) 0) (max (M.K 1-ξ 1) 0) x hu hv h
  have hq' := congrArg (fun z : ℝ => (M.r+M.p)*z) hq
  have hh' := congrArg (fun z : ℝ => (M.r+M.p-M.v)*z) hh
  simp only [profit_identity]
  linarith

lemma Pi2_separable (M : Model) (a : Fin 2 → ℝ) (u v x : ℝ)
    (hu : u ≤ x) (hv : v ≤ x) (h : x ≤ u+v) :
    M.Pi2 (Measure.dirac x) ![u,v] a + M.Pi2 (Measure.dirac x) ![x,x] a =
      M.Pi2 (Measure.dirac x) ![u,x] a + M.Pi2 (Measure.dirac x) ![x,v] a := by
  have hi : Integrable id (Measure.dirac x) := integrable_dirac (by simp)
  unfold Model.Pi2
  rw [← integral_add (integrable_profit M _ hi a _) (integrable_profit M _ hi a _),
    ← integral_add (integrable_profit M _ hi a _) (integrable_profit M _ hi a _)]
  apply integral_congr_ae
  have hx : ∀ᵐ y : ℝ ∂Measure.dirac x, y = x := by simp [ae_dirac_eq]
  have hd : ∀ᵐ ω : (Fin 2 → ℝ) × ℝ
      ∂((Measure.pi fun i => M.ν i (a i)).prod (Measure.dirac x)), ω.2 = x :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae.eventually hx
  filter_upwards [hd] with ω he
  rw [he]
  exact profit_separable M ω.1 u v x hu hv h

end SupplyDeterministic

namespace SupplyDeterministic
open SupplySubmodularity SupplyExistence SupplyCDF

lemma inactive_deriv (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) (i : Fin 2)
    (hη : ∀ k, M.η k = 0) (h : max (M.K i-ξ i) 0 < q i) :
    HasDerivAt (fun t => M.profit (Function.update q i t) ξ x) 0 (q i) := by
  apply (hasDerivAt_const (q i) (M.profit q ξ x)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds h] with t ht
  have hd (k : Fin 2) : Model.deliv (M.K k) (Function.update q i t k) (ξ k) =
      Model.deliv (M.K k) (q k) (ξ k) := by
    by_cases hk : k=i
    · subst k
      have ht' : max (M.K i-ξ i) 0 < t := ht
      simp [Model.deliv,min_eq_right ht'.le,min_eq_right h.le]
    · simp [Function.update_of_ne hk]
  simp only [Model.profit,hη,zero_mul,sub_zero,one_mul,zero_add,hd]

lemma slice_ae_deriv (M : Model) (a q : Fin 2 → ℝ) (x : ℝ) (i j : Fin 2)
    (hij : i ≠ j) (hη : ∀ k, M.η k = 0) (hqi : 0 < q i)
    (hqix : q i < x) (hqj : q j=x) :
    ∀ᵐ ξ ∂Measure.pi (fun k => M.ν k (a k)),
      HasDerivAt (fun t => M.profit (Function.update q i t) ξ x)
        (marginal M q ξ x i j) (q i) := by
  letI : NullSingletonClass (M.ν i (a i)) := ⟨M.ν_noAtoms i (a i)⟩
  letI : NullSingletonClass (M.ν j (a j)) := ⟨M.ν_noAtoms j (a j)⟩
  filter_upwards [Measure.ae_eval_ne (fun k => M.ν k (a k)) i (M.K i-q i),
    Measure.ae_eval_ne (fun k => M.ν k (a k)) j (M.K j-(x-q i))] with ξ hi hj
  have hc : q i ≠ max (M.K i-ξ i) 0 := by
    intro he
    by_cases h : 0 ≤ M.K i-ξ i
    · rw [max_eq_left h] at he; apply hi; linarith
    · rw [max_eq_right (le_of_not_ge h)] at he; linarith
  by_cases ha : q i < max (M.K i-ξ i) 0
  · apply profit_deriv M q ξ x i j hij hqi hc
    have he : quantity M q ξ = q i + Model.deliv (M.K j) (q j) (ξ j) := by
      have hd : Model.deliv (M.K i) (q i) (ξ i) = q i := min_eq_left ha.le
      fin_cases i <;> fin_cases j <;> simp_all [quantity,Fin.sum_univ_two,add_comm]
    rw [he,Model.deliv,hqj]
    intro heq
    by_cases hh : x ≤ max (M.K j-ξ j) 0
    · rw [min_eq_left hh] at heq; linarith
    · rw [min_eq_right (le_of_not_ge hh)] at heq
      by_cases hb : 0 ≤ M.K j-ξ j
      · rw [max_eq_left hb] at heq; apply hj; linarith
      · rw [max_eq_right (le_of_not_ge hb)] at heq; linarith
  · have ha' : max (M.K i-ξ i) 0 < q i := lt_of_le_of_ne (le_of_not_gt ha) hc.symm
    have hn : ¬ξ i < M.K i-q i := by
      have hh := le_max_left (M.K i-ξ i) 0
      linarith
    simpa only [marginal,hη,zero_mul,neg_zero,cap,if_neg hn,zero_add] using
      inactive_deriv M q ξ x i hη ha'

lemma slice_deriv_integral (M : Model) (a q : Fin 2 → ℝ) (x : ℝ) (i j : Fin 2)
    (hij : i ≠ j) (hη : ∀ k, M.η k = 0) (hqi : 0 < q i)
    (hqix : q i < x) (hqj : q j=x) :
    HasDerivAt (fun t => M.Pi2 (Measure.dirac x) (Function.update q i t) a)
      (∫ ω, marginal M q ω.1 ω.2 i j
        ∂((Measure.pi fun k => M.ν k (a k)).prod (Measure.dirac x))) (q i) := by
  let ν := (Measure.pi fun k => M.ν k (a k)).prod (Measure.dirac x)
  let F := fun (t : ℝ) (ω : (Fin 2 → ℝ) × ℝ) => M.profit (Function.update q i t) ω.1 ω.2
  have hi : Integrable id (Measure.dirac x) := integrable_dirac (by simp)
  have hm := (measurable_marginal M q i j).aestronglyMeasurable (μ := ν)
  have hl : ∀ᵐ ω ∂ν, LipschitzOnWith (Real.nnabs (lipBound M : ℝ)) (fun t => F t ω) Set.univ := by
    apply ae_of_all
    intro ω
    have h := (profit_lipschitz M ω.1 ω.2).comp (update_lipschitz q i)
    simpa only [mul_one, Real.nnabs_coe, Function.comp_def, F] using h.lipschitzOnWith (s := Set.univ)
  have ha : ∀ᵐ ω ∂ν, HasDerivAt (fun t => F t ω) (marginal M q ω.1 ω.2 i j) (q i) := by
    have hh : ∀ᵐ ω ∂ν, HasDerivAt (fun t => M.profit (Function.update q i t) ω.1 x)
        (marginal M q ω.1 x i j) (q i) :=
      measurePreserving_fst.quasiMeasurePreserving.tendsto_ae.eventually
        (slice_ae_deriv M a q x i j hij hη hqi hqix hqj)
    have hz : ∀ᵐ y : ℝ ∂Measure.dirac x, y=x := by simp [ae_dirac_eq]
    have hx : ∀ᵐ ω ∂ν, ω.2=x :=
      measurePreserving_snd.quasiMeasurePreserving.tendsto_ae.eventually hz
    filter_upwards [hh,hx] with ω hd he
    simpa only [F,he] using hd
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (μ := ν) (s := Set.univ) (bound := fun _ => (lipBound M : ℝ))
    Filter.univ_mem (Filter.Eventually.of_forall (fun t =>
      (integrable_profit M _ hi a (Function.update q i t)).aestronglyMeasurable))
    (integrable_profit M _ hi a _) hm hl (integrable_const _) ha
  exact h.2

end SupplyDeterministic

namespace SupplyDeterministic
open SupplySubmodularity SupplyExistence SupplyCDF

lemma cap_mean (M : Model) (a q : Fin 2 → ℝ) (i : Fin 2) :
    (∫ ξ, cap M q ξ i ∂Measure.pi (fun k => M.ν k (a k))) = M.G i (M.K i-q i) (a i) := by
  have hi : Measurable (fun y : ℝ => if y < M.K i-q i then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  unfold cap
  rw [integral_comp_eval (μ := fun k => M.ν k (a k)) (i := i) hi.aestronglyMeasurable]
  exact indicator_integral _ _ (M.ν_noAtoms i (a i) _)

lemma cap_product (M : Model) (a q : Fin 2 → ℝ) (i j : Fin 2) (hij : i ≠ j) (t : ℝ) :
    (∫ ξ, cap M q ξ i * (if ξ j < t then (1:ℝ) else 0)
      ∂Measure.pi (fun k => M.ν k (a k))) = M.G i (M.K i-q i) (a i) * M.G j t (a j) := by
  let ν := fun k => M.ν k (a k)
  have hi : Measurable (fun y : ℝ => if y<M.K i-q i then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  have hj : Measurable (fun y : ℝ => if y<t then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  have hind : IndepFun (fun ξ : Fin 2 → ℝ => ξ i) (fun ξ => ξ j) (Measure.pi ν) :=
    (iIndepFun_pi (μ := ν) (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have hh := (hind.comp hi hj).integral_fun_mul_eq_mul_integral
    (hi.comp (measurable_pi_apply i)).aestronglyMeasurable
    (hj.comp (measurable_pi_apply j)).aestronglyMeasurable
  simp only [Function.comp_def] at hh
  change (∫ ξ, (if ξ i<M.K i-q i then (1:ℝ) else 0) *
      (if ξ j<t then (1:ℝ) else 0) ∂Measure.pi ν) = _
  rw [hh, integral_comp_eval (μ := ν) (i := i) hi.aestronglyMeasurable,
    integral_comp_eval (μ := ν) (i := j) hj.aestronglyMeasurable]
  rw [indicator_integral (ν i) _ (M.ν_noAtoms i (a i) _),
    indicator_integral (ν j) _ (M.ν_noAtoms j (a j) _)]
  rfl

lemma slice_marginal_integral (M : Model) (a q : Fin 2 → ℝ) (x : ℝ) (i j : Fin 2)
    (hij : i ≠ j) (hη : ∀ k, M.η k = 0) (hqi : 0 < q i)
    (hqix : q i < x) (hqj : q j=x) :
    (∫ ω, marginal M q ω.1 ω.2 i j
      ∂((Measure.pi fun k => M.ν k (a k)).prod (Measure.dirac x))) =
      (M.r+M.p-M.v) * M.G i (M.K i-q i) (a i) *
        (M.phi i - M.G j (M.K j-(x-q i)) (a j)) := by
  let ν := Measure.pi fun k => M.ν k (a k)
  have hc : Integrable (fun ξ => cap M q ξ i) ν := by
    apply integrable_bounded _ _ (measurable_cap M q i) 1
    intro ξ; unfold cap; split_ifs <;> norm_num
  have hj : Measurable (fun ξ : Fin 2 → ℝ => if ξ j<M.K j-(x-q i) then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_lt (measurable_pi_apply j) measurable_const)
      measurable_const measurable_const
  have hp : Integrable (fun ξ => cap M q ξ i *
      (if ξ j<M.K j-(x-q i) then (1:ℝ) else 0)) ν := by
    apply integrable_bounded _ _ ((measurable_cap M q i).mul hj) 1
    intro ξ; dsimp only [Pi.mul_apply]; unfold cap; split_ifs <;> norm_num
  rw [integral_prod _ (integrable_marginal M (Measure.dirac x) a q i j)]
  simp only [integral_dirac]
  have he : (fun ξ : Fin 2 → ℝ => marginal M q ξ x i j) =
      (fun ξ => (M.r+M.p-M.c i)*cap M q ξ i - (M.r+M.p-M.v) *
        (cap M q ξ i * (if ξ j<M.K j-(x-q i) then (1:ℝ) else 0))) := by
    funext ξ
    have ht : (x < q i + Model.deliv (M.K j) (q j) (ξ j)) ↔
        ξ j < M.K j-(x-q i) := by
      unfold Model.deliv
      rw [hqj]
      constructor
      · intro hh
        have hh' : x-q i < min x (max (M.K j-ξ j) 0) := by linarith
        have ht := (lt_min_iff.mp hh').2
        rcases lt_max_iff.mp ht with h | h <;> linarith
      · intro hh
        have ht : x-q i < min x (max (M.K j-ξ j) 0) :=
          lt_min (by linarith) (lt_max_of_lt_left (by linarith))
        linarith
    simp only [marginal,hη,zero_mul,neg_zero,zero_add,sub_zero,one_mul,ht]
    ring
  rw [he,integral_sub (hc.const_mul _) (hp.const_mul _),
    integral_const_mul,integral_const_mul,cap_mean,cap_product M a q i j hij]
  unfold Model.phi
  simp only [hη,sub_zero,one_mul]
  have hd : M.r+M.p-M.v ≠ 0 := ne_of_gt (sub_pos.mpr M.v_lt)
  field_simp [hd]
  <;> ring

lemma slice_derivative (M : Model) (a q : Fin 2 → ℝ) (x : ℝ) (i j : Fin 2)
    (hij : i ≠ j) (hη : ∀ k, M.η k = 0) (hqi : 0 < q i)
    (hqix : q i < x) (hqj : q j=x) :
    HasDerivAt (fun t => M.Pi2 (Measure.dirac x) (Function.update q i t) a)
      ((M.r+M.p-M.v) * M.G i (M.K i-q i) (a i) *
        (M.phi i - M.G j (M.K j-(x-q i)) (a j))) (q i) := by
  have h := slice_deriv_integral M a q x i j hij hη hqi hqix hqj
  rw [slice_marginal_integral M a q x i j hij hη hqi hqix hqj] at h
  exact h

end SupplyDeterministic

namespace SupplyDeterministic
open SupplySubmodularity SupplyExistence

lemma clip_value (r p v c d x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hc : v ≤ c) (hd : v ≤ d) :
    -c*y-d*z+(r+p)*(y+z)-(r+p-v)*max (y+z-x) 0 ≤
      -c*(min y x)-d*(min z x)+(r+p)*(min y x+min z x)-
        (r+p-v)*max (min y x+min z x-x) 0 := by
  by_cases h1 : y ≤ x
  · rw [min_eq_left h1]
    by_cases h2 : z ≤ x
    · rw [min_eq_left h2]
    · have h2' : x ≤ z := (lt_of_not_ge h2).le
      rw [min_eq_right h2',max_eq_left (by linarith : 0 ≤ y+z-x),
        max_eq_left (by linarith : 0 ≤ y+x-x)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr h2')]
  · have h1' : x ≤ y := (lt_of_not_ge h1).le
    rw [min_eq_right h1']
    by_cases h2 : z ≤ x
    · rw [min_eq_left h2,max_eq_left (by linarith : 0 ≤ y+z-x),
        max_eq_left (by linarith : 0 ≤ x+z-x)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h1')]
    · have h2' : x ≤ z := (lt_of_not_ge h2).le
      rw [min_eq_right h2',max_eq_left (by linarith : 0 ≤ y+z-x),
        max_eq_left (by linarith : 0 ≤ x+x-x)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h1'),
        mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr h2')]

lemma profit_clip_demand (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hq : ∀ i, 0 ≤ q i) (hη : ∀ i, M.η i = 0) (hc : ∀ i, M.v ≤ M.c i) :
    M.profit q ξ x ≤ M.profit (fun i => min (q i) x) ξ x := by
  have hd (i : Fin 2) : Model.deliv (M.K i) (min (q i) x) (ξ i) =
      min (Model.deliv (M.K i) (q i) (ξ i)) x := by
    simp only [Model.deliv,min_assoc,min_left_comm,min_comm]
  have hh := clip_value M.r M.p M.v (M.c 0) (M.c 1) x
    (Model.deliv (M.K 0) (q 0) (ξ 0)) (Model.deliv (M.K 1) (q 1) (ξ 1)) hx
    (le_min (hq 0) (le_max_right _ _)) (le_min (hq 1) (le_max_right _ _)) (hc 0) (hc 1)
  simp only [profit_identity,charge,quantity,Fin.sum_univ_two,hη,zero_mul,
    zero_add,sub_zero,one_mul,hd]
  linarith

lemma profit_fill (M : Model) (q q' ξ : Fin 2 → ℝ) (x : ℝ)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i)
    (hqq : q ≤ q') (hs : q' 0+q' 1 ≤ x) : M.profit q ξ x ≤ M.profit q' ξ x := by
  have hy : quantity M q' ξ ≤ x := by
    unfold quantity
    rw [Fin.sum_univ_two]
    exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans hs
  rw [profit_unsaturated M q ξ x hη ((quantity_mono M q q' ξ hqq).trans hy),
    profit_unsaturated M q' ξ x hη hy]
  exact sub_le_sub_right (add_le_add
    (mul_le_mul_of_nonneg_left (min_le_min_right _ (hqq 0)) (margin_nonneg M hη hφ 0))
    (mul_le_mul_of_nonneg_left (min_le_min_right _ (hqq 1)) (margin_nonneg M hη hφ 1))) _

lemma triangle_dominates (M : Model) (a : Fin 2 → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i ∧ M.phi i ≤ 1)
    (q : Fin 2 → ℝ) (hq : q ∈ Model.orders) :
    ∃ u v : ℝ, 0 ≤ u ∧ u ≤ x ∧ 0 ≤ v ∧ v ≤ x ∧ x ≤ u+v ∧
      M.Pi2 (Measure.dirac x) q a ≤ M.Pi2 (Measure.dirac x) ![u,v] a := by
  let u := min (q 0) x
  let v := min (q 1) x
  let u' := max u (x-v)
  have hu : 0 ≤ u := le_min (hq 0) hx
  have hv : 0 ≤ v := le_min (hq 1) hx
  have hux : u ≤ x := min_le_right _ _
  have hvx : v ≤ x := min_le_right _ _
  have huu : u ≤ u' := le_max_left _ _
  have hu' : 0 ≤ u' := hu.trans huu
  have hu'x : u' ≤ x := max_le hux (by linarith)
  have hs : x ≤ u'+v := by have := le_max_right u (x-v); dsimp [u'] at *; linarith
  refine ⟨u',v,hu',hu'x,hv,hvx,hs,?_⟩
  have hi : Integrable id (Measure.dirac x) := integrable_dirac (by simp)
  apply integral_mono_ae (integrable_profit M _ hi a q) (integrable_profit M _ hi a ![u',v])
  have hz : ∀ᵐ y : ℝ ∂Measure.dirac x, y=x := by simp [ae_dirac_eq]
  have hd : ∀ᵐ ω : (Fin 2 → ℝ) × ℝ
      ∂((Measure.pi fun i => M.ν i (a i)).prod (Measure.dirac x)), ω.2=x :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae.eventually hz
  filter_upwards [hd] with ω he
  rw [he]
  have hclip := profit_clip_demand M q ω.1 x hx hq hη
    (salvage_le_cost M hη (fun i => (hφ i).2))
  have hvec : (fun i => min (q i) x) = ![u,v] := by funext i; fin_cases i <;> rfl
  rw [hvec] at hclip
  apply hclip.trans
  by_cases hh : x-v ≤ u
  · simpa only [u',max_eq_left hh] using (le_rfl : M.profit ![u,v] ω.1 x ≤ M.profit ![u,v] ω.1 x)
  · have hle : u ≤ x-v := (lt_of_not_ge hh).le
    have heq : u'=x-v := max_eq_right hle
    apply profit_fill M ![u,v] ![u',v] ω.1 x hη (fun i => (hφ i).1)
    · intro i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
      · exact huu
      · exact le_rfl
    · simp only [Matrix.cons_val_zero,Matrix.cons_val_one,heq]; linarith

end SupplyDeterministic

namespace SupplyDeterministic
open SupplySubmodularity SupplyExistence

lemma slice_maximum (M : Model) (a q : Fin 2 → ℝ) (x z : ℝ) (i j : Fin 2)
    (hij : i ≠ j) (hη : ∀ k, M.η k = 0) (hqj : q j=x)
    (hz0 : 0 ≤ z) (hzx : z ≤ x)
    (hroot : M.G j (M.K j-(x-z)) (a j) = M.phi i) :
    IsMaxOn (fun t => M.Pi2 (Measure.dirac x) (Function.update q i t) a) (Set.Icc 0 x) z := by
  let f := fun t => M.Pi2 (Measure.dirac x) (Function.update q i t) a
  have hi : Integrable id (Measure.dirac x) := integrable_dirac (by simp)
  have hc : Continuous f := (Pi2_lipschitz M _ hi a).continuous.comp (update_lipschitz q i).continuous
  have hd (t : ℝ) (ht0 : 0 < t) (htx : t < x) :
      HasDerivAt f ((M.r+M.p-M.v) * M.G i (M.K i-t) (a i) *
        (M.phi i-M.G j (M.K j-(x-t)) (a j))) t := by
    have hh := slice_derivative M a (Function.update q i t) x i j hij hη
      (by simpa using ht0) (by simpa using htx) (by simpa [Function.update_of_ne hij.symm] using hqj)
    simpa [f,Function.update_idem] using hh
  apply isMaxOn_Icc_of_deriv hc.continuousAt hc.continuousAt hc.continuousAt
  · intro t ht
    exact (hd t ht.1 (lt_of_lt_of_le ht.2 hzx)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (hd t (lt_of_le_of_lt hz0 ht.1) ht.2).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t ht.1 (lt_of_lt_of_le ht.2 hzx)).deriv]
    have hg : M.G j (M.K j-(x-t)) (a j) ≤ M.phi i := by
      rw [← hroot]
      exact monotone_cdf _ (by linarith [ht.1,ht.2])
    exact mul_nonneg (mul_nonneg (sub_pos.mpr M.v_lt).le (cdf_nonneg _ _)) (sub_nonneg.mpr hg)
  · intro t ht
    rw [(hd t (lt_of_le_of_lt hz0 ht.1) ht.2).deriv]
    have hg : M.phi i ≤ M.G j (M.K j-(x-t)) (a j) := by
      rw [← hroot]
      exact monotone_cdf _ (by linarith [ht.1,ht.2])
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sub_pos.mpr M.v_lt).le (cdf_nonneg _ _)) (sub_nonpos.mpr hg)

lemma roots_optimal (M : Model) (a : Fin 2 → ℝ) (x u v : ℝ) (hx : 0 ≤ x)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i ∧ M.phi i ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ x) (hv : 0 ≤ v ∧ v ≤ x) (hs : x ≤ u+v)
    (h0 : M.G 1 (M.K 1-(x-u)) (a 1) = M.phi 0)
    (h1 : M.G 0 (M.K 0-(x-v)) (a 0) = M.phi 1) :
    M.IsOptimal (Measure.dirac x) a ![u,v] := by
  refine ⟨?_,?_⟩
  · intro i; fin_cases i
    · exact hu.1
    · exact hv.1
  intro q hq
  obtain ⟨s,t,hs0,hsx,ht0,htx,hst,hdom⟩ := triangle_dominates M a x hx hη hφ q hq
  apply hdom.trans
  have hm0 := slice_maximum M a ![u,x] x u 0 1 (by decide) hη rfl hu.1 hu.2 h0
  have hm1 := slice_maximum M a ![x,v] x v 1 0 (by decide) hη rfl hv.1 hv.2 h1
  have hle0 := hm0 ⟨hs0,hsx⟩
  have hle1 := hm1 ⟨ht0,htx⟩
  have he0 (z : ℝ) : Function.update ![u,x] 0 z = ![z,x] := by funext i; fin_cases i <;> simp
  have he1 (z : ℝ) : Function.update ![x,v] 1 z = ![x,z] := by funext i; fin_cases i <;> simp
  simp only [he0,Set.mem_setOf_eq] at hle0
  simp only [he1,Set.mem_setOf_eq] at hle1
  have he := Pi2_separable M a s t x hsx htx hst
  have he' := Pi2_separable M a u v x hu.2 hv.2 hs
  linarith

lemma clip_optimal (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a q : Fin 2 → ℝ) (ho : M.IsOptimal μ a q) :
    M.IsOptimal μ a (fun i => min (q i) (M.K i)) := by
  refine ⟨fun i => le_min (ho.1 i) (M.K_pos i).le,?_⟩
  intro q' hq'
  apply (ho.2 q' hq').trans
  apply integral_mono_ae (integrable_profit M μ hμint a q) (integrable_profit M μ hμint a _)
  filter_upwards [ae_capacity_nonneg M μ a] with ω hξ
  exact clip_profit M q ω.1 ω.2 hξ

lemma hedge_optimal (M : Model) (a : Fin 2 → ℝ) (x A B : ℝ) (hx : 0 ≤ x)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i ∧ M.phi i ≤ 1)
    (hA : 0 ≤ A ∧ A ≤ M.K 0) (hB : 0 ≤ B ∧ B ≤ M.K 1)
    (hGA : M.G 0 A (a 0) = M.phi 1) (hGB : M.G 1 B (a 1) = M.phi 0)
    (hreg : M.K 0+M.K 1-(A+B) ≤ x) :
    M.IsOptimal (Measure.dirac x) a
      ![min (x-(M.K 1-B)) (M.K 0), min (x-(M.K 0-A)) (M.K 1)] := by
  have hu : 0 ≤ x-(M.K 1-B) ∧ x-(M.K 1-B) ≤ x := by constructor <;> linarith [hA.1,hA.2,hB.1,hB.2]
  have hv : 0 ≤ x-(M.K 0-A) ∧ x-(M.K 0-A) ≤ x := by constructor <;> linarith [hA.1,hA.2,hB.1,hB.2]
  have ho := roots_optimal M a x (x-(M.K 1-B)) (x-(M.K 0-A)) hx hη hφ hu hv
    (by linarith) (by convert hGB using 1 <;> congr 1 <;> ring) (by convert hGA using 1 <;> congr 1 <;> ring)
  have hc := clip_optimal M (Measure.dirac x) (integrable_dirac (by simp)) a _ ho
  convert hc using 1
  funext i; fin_cases i <;> rfl

end SupplyDeterministic

open Set
namespace SupplyThresholds

lemma cdf_nonpositive (M : Model) (i : Fin 2) (a t : ℝ) (ht : t ≤ 0) :
    M.G i t a = 0 := by
  have hz : M.ν i a (Iic (0 : ℝ)) = 0 := by
    apply measure_mono_null (t := Iio 0 ∪ {0})
    · intro y hy
      change y ≤ 0 at hy
      rcases lt_or_eq_of_le hy with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact measure_union_null (M.ν_nonneg i a) (M.ν_noAtoms i a 0)
  have hh : M.ν i a (Iic t) = 0 := measure_mono_null (Iic_subset_Iic.mpr ht) hz
  simp [Model.G, cdf_eq_real, measureReal_def, hh]

lemma cdf_continuousOn (M : Model) (i : Fin 2) (a b : ℝ) :
    ContinuousOn (fun t => M.G i t a) (Iic b) := by
  let : NullSingletonClass (M.ν i a) := ⟨M.ν_noAtoms i a⟩
  have hc := (integrable_const (1 : ℝ) (μ := M.ν i a)).integrableOn.continuousOn_Iic_primitive_Iic (a₀ := b)
  simpa [Model.G, cdf_eq_real] using hc

lemma quantile_inverse (M : Model) (i : Fin 2) (a b u : ℝ)
    (hb : 0 < b) (hb1 : M.G i b a = 1)
    (hstrict : StrictMonoOn (fun t => M.G i t a) (Icc 0 b))
    (hu : 0 < u) (hu1 : u ≤ 1) :
    M.Ginv i a u ∈ Ioc 0 b ∧ M.G i (M.Ginv i a u) a = u := by
  have hc : ContinuousOn (fun t => M.G i t a) (Icc 0 b) :=
    (cdf_continuousOn M i a b).mono Icc_subset_Iic_self
  obtain ⟨t, ht, htu⟩ := intermediate_value_Icc hb.le hc
    (show u ∈ Icc (M.G i 0 a) (M.G i b a) by
      rw [cdf_nonpositive M i a 0 le_rfl, hb1]
      exact ⟨hu.le, hu1⟩)
  have hEq : M.Ginv i a u = t := by
    unfold Model.Ginv
    apply le_antisymm
    · exact csInf_le ⟨0, fun y hy => hy.1⟩ ⟨ht.1, htu.ge⟩
    · apply le_csInf
      · exact ⟨b, hb.le, by simpa [hb1] using hu1⟩
      · intro y hy
        by_contra hn
        have hyt : y < t := lt_of_not_ge hn
        have hlt := hstrict ⟨hy.1, hyt.le.trans ht.2⟩ ht hyt
        rw [htu] at hlt
        exact (not_lt_of_ge hy.2) hlt
  rw [hEq]
  refine ⟨⟨?_, ht.2⟩, htu⟩
  by_contra hn
  have hz := cdf_nonpositive M i a t (le_of_not_gt hn)
  linarith

lemma cdf_continuous (M : Model) (i : Fin 2) (a : ℝ) :
    Continuous (fun t => M.G i t a) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (cdf_continuousOn M i a (t + 1)).continuousAt (Iic_mem_nhds (by linarith))

lemma cdf_at_capacity (M : Model) (i : Fin 2) (a b : ℝ)
    (hb : b ≤ M.K i) (hb1 : M.G i b a = 1) : M.G i (M.K i) a = 1 := by
  apply le_antisymm (cdf_le_one _ _)
  calc
    1 = M.G i b a := hb1.symm
    _ ≤ M.G i (M.K i) a := monotone_cdf _ hb

lemma below_inverse (M : Model) (i : Fin 2) (a u t : ℝ)
    (hu : 0 < u) (ht : t < M.Ginv i a u) : M.G i t a < u := by
  by_cases ht0 : t ≤ 0
  · rw [cdf_nonpositive M i a t ht0]
    exact hu
  · by_contra hn
    have hm : t ∈ {t : ℝ | 0 ≤ t ∧ u ≤ M.G i t a} :=
      ⟨(lt_of_not_ge ht0).le, le_of_not_gt hn⟩
    have hle : M.Ginv i a u ≤ t := csInf_le ⟨0, fun y hy => hy.1⟩ hm
    exact (not_lt_of_ge hle) ht

lemma balance_exists (M : Model) (a : Fin 2 → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (hcap : x ≤ M.K 0 + M.K 1)
    (hphi : ∀ i, 0 < M.phi i)
    (hG : ∀ i, M.G i (M.K i) (a i) = 1)
    (hord : M.phi 1 ≤ M.phi 0)
    (hregion : M.K 0 - M.B a < x) :
    ∃ q₂ : ℝ, 0 ≤ q₂ ∧ q₂ ≤ x ∧ q₂ ≤ M.K 1 ∧ x - q₂ ≤ M.K 0 ∧
      M.phi 0 * M.G 0 (M.K 0 - (x - q₂)) (a 0) =
        M.phi 1 * M.G 1 (M.K 1 - q₂) (a 1) := by
  let l := max 0 (x - M.K 0)
  let u := min x (M.K 1)
  let f := fun q : ℝ => M.phi 0 * M.G 0 (M.K 0 - x + q) (a 0) -
    M.phi 1 * M.G 1 (M.K 1 - q) (a 1)
  have hlu : l ≤ u := by
    dsimp [l, u]
    exact max_le (le_min hx (M.K_pos 1).le)
      (le_min (by linarith [M.K_pos 0]) (by linarith))
  have hc : Continuous f := by
    have h0 := cdf_continuous M 0 (a 0)
    have h1 := cdf_continuous M 1 (a 1)
    dsimp [f]
    fun_prop
  have hl : f l ≤ 0 := by
    by_cases hxK : M.K 0 ≤ x
    · have he : l = x - M.K 0 := max_eq_right (by linarith)
      have hz : M.K 0 - x + l = 0 := by rw [he]; ring
      dsimp [f]
      rw [hz, cdf_nonpositive M 0 (a 0) 0 le_rfl]
      have hg := cdf_nonneg (M.ν 1 (a 1)) (M.K 1 - l)
      have hp := mul_nonneg (hphi 1).le hg
      change 0 ≤ M.phi 1 * M.G 1 (M.K 1 - l) (a 1) at hp
      linarith
    · have he : l = 0 := max_eq_left (by linarith)
      have hb : M.B a = M.Ginv 0 (a 0) (M.phi 1 / M.phi 0) := by
        simp [Model.B, hG 1]
      have hlt : M.G 0 (M.K 0 - x) (a 0) < M.phi 1 / M.phi 0 := by
        apply below_inverse M 0 (a 0) _ _ (div_pos (hphi 1) (hphi 0))
        rw [← hb]
        linarith
      have hp := (lt_div_iff₀ (hphi 0)).mp hlt
      dsimp [f]
      rw [he]
      simp only [add_zero, sub_zero, hG 1, mul_one]
      nlinarith
  have hu : 0 ≤ f u := by
    by_cases hxK : M.K 1 ≤ x
    · have he : u = M.K 1 := min_eq_right hxK
      dsimp [f]
      rw [he, sub_self, cdf_nonpositive M 1 (a 1) 0 le_rfl]
      have hp := mul_nonneg (hphi 0).le (cdf_nonneg (M.ν 0 (a 0)) (M.K 0 - x + M.K 1))
      simpa [Model.G] using hp
    · have he : u = x := min_eq_left (le_of_not_ge hxK)
      have hg := cdf_le_one (M.ν 1 (a 1)) (M.K 1 - x)
      change M.G 1 (M.K 1 - x) (a 1) ≤ 1 at hg
      have hp := mul_le_mul_of_nonneg_left hg (hphi 1).le
      dsimp [f]
      rw [he, sub_add_cancel, hG 0]
      nlinarith
  obtain ⟨q, hq, hzero⟩ := intermediate_value_Icc hlu hc.continuousOn
    (show 0 ∈ Icc (f l) (f u) from ⟨hl, hu⟩)
  refine ⟨q, (le_max_left _ _).trans hq.1,
    hq.2.trans (min_le_left _ _), hq.2.trans (min_le_right _ _), ?_, ?_⟩
  · have h := (le_max_right 0 (x - M.K 0)).trans hq.1
    linarith
  · dsimp [f] at hzero
    rw [show M.K 0 - x + q = M.K 0 - (x - q) by ring] at hzero
    exact sub_eq_zero.mp hzero

end SupplyThresholds

#print axioms SupplyThresholds.quantile_inverse

#print axioms SupplyThresholds.balance_exists


/-- Threshold identities and a feasible balanced order in region Ω₂.
This statement does not assert optimality of expected profit. -/
theorem prior_thresholds (M : Model) (a : Fin 2 → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hphi : ∀ i, 0 < M.phi i ∧ M.phi i < 1)
    (hsupp : ∀ i, ∃ b : ℝ, 0 < b ∧ b ≤ M.K i ∧ M.G i b (a i) = 1 ∧
      StrictMonoOn (fun t => M.G i t (a i)) (Icc 0 b))
    (hord : M.phi 1 * M.G 1 (M.K 1) (a 1) ≤
      M.phi 0 * M.G 0 (M.K 0) (a 0)) :
    (0 < M.A1 a ∧ M.A1 a ≤ M.K 0 ∧ M.G 0 (M.A1 a) (a 0) = M.phi 1) ∧
    (0 < M.A2 a ∧ M.A2 a ≤ M.K 1 ∧ M.G 1 (M.A2 a) (a 1) = M.phi 0) ∧
    (0 < M.B a ∧ M.B a ≤ M.K 0 ∧ M.G 0 (M.B a) (a 0) = M.phi 1 / M.phi 0) ∧
    (M.K 0 - M.B a < x ∧ x ≤ M.K 0 + M.K 1 - (M.A1 a + M.A2 a) →
      ∃ q₂ : ℝ, 0 ≤ q₂ ∧ q₂ ≤ x ∧ q₂ ≤ M.K 1 ∧ x - q₂ ≤ M.K 0 ∧
        M.phi 0 * M.G 0 (M.K 0 - (x - q₂)) (a 0) =
          M.phi 1 * M.G 1 (M.K 1 - q₂) (a 1)) := by
  obtain ⟨b₀, hb₀, hbK₀, hbG₀, hstrict₀⟩ := hsupp 0
  obtain ⟨b₁, hb₁, hbK₁, hbG₁, hstrict₁⟩ := hsupp 1
  have hG : ∀ i, M.G i (M.K i) (a i) = 1 := by
    intro i
    obtain ⟨b, _, hbK, hbG, _⟩ := hsupp i
    exact SupplyThresholds.cdf_at_capacity M i (a i) b hbK hbG
  have horder : M.phi 1 ≤ M.phi 0 := by simpa [hG] using hord
  have h0 := SupplyThresholds.quantile_inverse M 0 (a 0) b₀ (M.phi 1)
    hb₀ hbG₀ hstrict₀ (hphi 1).1 (hphi 1).2.le
  have h1 := SupplyThresholds.quantile_inverse M 1 (a 1) b₁ (M.phi 0)
    hb₁ hbG₁ hstrict₁ (hphi 0).1 (hphi 0).2.le
  have hB := SupplyThresholds.quantile_inverse M 0 (a 0) b₀ (M.phi 1 / M.phi 0)
    hb₀ hbG₀ hstrict₀ (div_pos (hphi 1).1 (hphi 0).1)
    ((div_le_one (hphi 0).1).mpr horder)
  have hBeq : M.B a = M.Ginv 0 (a 0) (M.phi 1 / M.phi 0) := by
    simp [Model.B, hG]
  refine ⟨⟨h0.1.1, h0.1.2.trans hbK₀, h0.2⟩,
    ⟨h1.1.1, h1.1.2.trans hbK₁, h1.2⟩, ?_, ?_⟩
  · simpa [hBeq] using And.intro hB.1.1 (And.intro (hB.1.2.trans hbK₀) hB.2)
  · intro hreg
    apply SupplyThresholds.balance_exists M a x hx ?_ (fun i => (hphi i).1) hG horder hreg.1
    have hp0 : 0 < M.A1 a := h0.1.1
    have hp1 : 0 < M.A2 a := h1.1.1
    linarith [hreg.2]

#print axioms prior_thresholds

theorem prior_hedge (M : Model) (a : Fin 2 → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hη : ∀ i, M.η i = 0) (hφpos : ∀ i, 0 < M.phi i) (hφlt : ∀ i, M.phi i < 1)
    (hsupp : ∀ i, ∃ b : ℝ, 0 < b ∧ b ≤ M.K i ∧ M.G i b (a i) = 1 ∧
      StrictMonoOn (fun t => M.G i t (a i)) (Set.Icc 0 b))
    (hord : M.phi 1 * M.G 1 (M.K 1) (a 1) ≤ M.phi 0 * M.G 0 (M.K 0) (a 0)) :
    (M.K 0 + M.K 1 - (M.A1 a + M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1 - max (M.A1 a) (M.A2 a) →
      M.IsOptimal (Measure.dirac x) a ![x - (M.K 1 - M.A2 a), x - (M.K 0 - M.A1 a)]) ∧
    (M.K 0 + M.K 1 - max (M.A1 a) (M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1 - min (M.A1 a) (M.A2 a) →
      (M.A2 a ≤ M.A1 a → M.IsOptimal (Measure.dirac x) a ![x - (M.K 1 - M.A2 a), M.K 1]) ∧
      (M.A1 a < M.A2 a → M.IsOptimal (Measure.dirac x) a ![M.K 0, x - (M.K 0 - M.A1 a)])) ∧
    ((M.K 0 + M.K 1 - min (M.A1 a) (M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1) ∨ M.K 0 + M.K 1 < x →
      M.IsOptimal (Measure.dirac x) a ![M.K 0, M.K 1]) := by
  obtain ⟨hA,hB,_,_⟩ := prior_thresholds M a x hx (fun i => ⟨hφpos i,hφlt i⟩) hsupp hord
  have hopt (hr : M.K 0+M.K 1-(M.A1 a+M.A2 a) ≤ x) :=
    SupplyDeterministic.hedge_optimal M a x (M.A1 a) (M.A2 a) hx hη
      (fun i => ⟨(hφpos i).le,(hφlt i).le⟩) ⟨hA.1.le,hA.2.1⟩ ⟨hB.1.le,hB.2.1⟩ hA.2.2 hB.2.2 hr
  have hmax0 := le_max_left (M.A1 a) (M.A2 a)
  have hmax1 := le_max_right (M.A1 a) (M.A2 a)
  have hmin0 := min_le_left (M.A1 a) (M.A2 a)
  have hmin1 := min_le_right (M.A1 a) (M.A2 a)
  have hsum : max (M.A1 a) (M.A2 a) ≤ M.A1 a+M.A2 a := max_le (by linarith [hB.1]) (by linarith [hA.1])
  refine ⟨?_,?_,?_⟩
  · intro hr
    have ho := hopt hr.1.le
    have h0 : x-(M.K 1-M.A2 a) ≤ M.K 0 := by linarith [hr.2]
    have h1 : x-(M.K 0-M.A1 a) ≤ M.K 1 := by linarith [hr.2]
    simpa only [min_eq_left h0,min_eq_left h1] using ho
  · intro hr
    have ho := hopt (by linarith [hr.1])
    constructor
    · intro hh
      have hmax : max (M.A1 a) (M.A2 a) = M.A1 a := max_eq_left hh
      have hmin : min (M.A1 a) (M.A2 a) = M.A2 a := min_eq_right hh
      have h0 : x-(M.K 1-M.A2 a) ≤ M.K 0 := by rw [hmin] at hr; linarith [hr.2]
      have h1 : M.K 1 ≤ x-(M.K 0-M.A1 a) := by rw [hmax] at hr; linarith [hr.1]
      simpa only [min_eq_left h0,min_eq_right h1] using ho
    · intro hh
      have hmax : max (M.A1 a) (M.A2 a) = M.A2 a := max_eq_right hh.le
      have hmin : min (M.A1 a) (M.A2 a) = M.A1 a := min_eq_left hh.le
      have h0 : M.K 0 ≤ x-(M.K 1-M.A2 a) := by rw [hmax] at hr; linarith [hr.1]
      have h1 : x-(M.K 0-M.A1 a) ≤ M.K 1 := by rw [hmin] at hr; linarith [hr.2]
      simpa only [min_eq_right h0,min_eq_left h1] using ho
  · intro hr
    have hh : M.K 0+M.K 1-min (M.A1 a) (M.A2 a) < x := by
      rcases hr with hr | hr
      · exact hr.1
      · have hm : 0 ≤ min (M.A1 a) (M.A2 a) := le_min hA.1.le hB.1.le
        linarith
    have ho := hopt (by linarith [hA.1,hB.1])
    have h0 : M.K 0 ≤ x-(M.K 1-M.A2 a) := by linarith
    have h1 : M.K 1 ≤ x-(M.K 0-M.A1 a) := by linarith
    simpa only [min_eq_right h0,min_eq_right h1] using ho

#print axioms prior_hedge


namespace SupplyBoundary
open SupplyExistence SupplyDeterministic

noncomputable def slice (M : Model) (a : Fin 2 → ℝ) (x : ℝ) (i : Fin 2) (t : ℝ) : ℝ :=
  M.Pi2 (Measure.dirac x) (Function.update (fun _ => x) i t) a

lemma slice_cont (M : Model) (a : Fin 2 → ℝ) (x : ℝ) (i : Fin 2) :
    Continuous (slice M a x i) :=
  (Pi2_lipschitz M _ (integrable_dirac (by simp)) a).continuous.comp
    (update_lipschitz (fun _ => x) i).continuous

lemma slice_deriv (M : Model) (a : Fin 2 → ℝ) (x t : ℝ) (i j : Fin 2)
    (hij : i ≠ j) (hη : ∀ k, M.η k = 0) (ht0 : 0 < t) (htx : t < x) :
    HasDerivAt (slice M a x i)
      ((M.r+M.p-M.v)*M.G i (M.K i-t) (a i)*
        (M.phi i-M.G j (M.K j-(x-t)) (a j))) t := by
  change HasDerivAt (fun z => M.Pi2 (Measure.dirac x) (Function.update (fun _ => x) i z) a) _ t
  simpa only [Function.update_idem, Function.update_self] using
    slice_derivative M a (Function.update (fun _ => x) i t) x i j hij hη
      (by simpa using ht0) (by simpa using htx) (by simp [Function.update_of_ne hij.symm])

lemma slices_identity (M : Model) (a : Fin 2 → ℝ) (x u v : ℝ)
    (hu : u ≤ x) (hv : v ≤ x) (h : x ≤ u+v) :
    M.Pi2 (Measure.dirac x) ![u,v] a + M.Pi2 (Measure.dirac x) ![x,x] a =
      slice M a x 0 u + slice M a x 1 v := by
  have h0 : Function.update (fun _ : Fin 2 => x) 0 u = ![u,x] := by
    funext i; fin_cases i <;> simp
  have h1 : Function.update (fun _ : Fin 2 => x) 1 v = ![x,v] := by
    funext i; fin_cases i <;> simp
  simpa only [slice,h0,h1] using Pi2_separable M a u v x hu hv h

lemma slice_decreases (M : Model) (a : Fin 2 → ℝ) (x u v A : ℝ) (i j : Fin 2)
    (hij : i ≠ j) (hη : ∀ k, M.η k = 0)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ x)
    (hroot : M.G j A (a j) = M.phi i) (hstart : x-(M.K j-A) ≤ u) :
    slice M a x i v ≤ slice M a x i u := by
  have ha : AntitoneOn (slice M a x i) (Set.Icc u x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (slice_cont M a x i).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (slice_deriv M a x t i j hij hη (by linarith [ht.1]) ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(slice_deriv M a x t i j hij hη (by linarith [ht.1]) ht.2).deriv]
      have hg : M.phi i ≤ M.G j (M.K j-(x-t)) (a j) := by
        rw [← hroot]
        exact monotone_cdf _ (by linarith [ht.1])
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (sub_pos.mpr M.v_lt).le (cdf_nonneg _ _)) (sub_nonpos.mpr hg)
  exact ha ⟨le_rfl,huv.trans hv⟩ ⟨huv,hv⟩ huv

lemma triangle_to_boundary (M : Model) (a : Fin 2 → ℝ) (x A B u v : ℝ)
    (hη : ∀ i, M.η i = 0) (hA : M.G 0 A (a 0)=M.phi 1)
    (hB : M.G 1 B (a 1)=M.phi 0)
    (hreg : x ≤ M.K 0+M.K 1-(A+B))
    (hu : 0 ≤ u) (hux : u ≤ x) (hv : 0 ≤ v) (hvx : v ≤ x) (hs : x ≤ u+v) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ x ∧
      slice M a x 0 u+slice M a x 1 v ≤ slice M a x 0 (x-w)+slice M a x 1 w := by
  let z := max (x-v) (min u (x-(M.K 1-B)))
  have hz0 : 0 ≤ z := (sub_nonneg.mpr hvx).trans (le_max_left _ _)
  have hzu : z ≤ u := max_le (by linarith) (min_le_left _ _)
  have hzx : z ≤ x := hzu.trans hux
  have hwv : x-z ≤ v := by have := le_max_left (x-v) (min u (x-(M.K 1-B))); dsimp only [z] at *; linarith
  refine ⟨x-z,by linarith,by linarith,?_⟩
  have h0 : slice M a x 0 u ≤ slice M a x 0 z := by
    by_cases hh : u ≤ x-(M.K 1-B)
    · have hz : z=u := by dsimp [z]; rw [min_eq_left hh,max_eq_right (by linarith)]
      rw [hz]
    · apply slice_decreases M a x z u B 0 1 (by decide) hη hz0 hzu hux hB
      have h := le_max_right (x-v) (min u (x-(M.K 1-B)))
      simpa [z,min_eq_right (le_of_not_ge hh)] using h
  have h1 : slice M a x 1 v ≤ slice M a x 1 (x-z) := by
    by_cases hh : min u (x-(M.K 1-B)) ≤ x-v
    · have hz : z=x-v := max_eq_left hh
      simp [hz]
    · have hz : z=min u (x-(M.K 1-B)) := max_eq_right (le_of_not_ge hh)
      apply slice_decreases M a x (x-z) v A 1 0 (by decide) hη
        (by linarith) hwv hvx hA
      have h := min_le_right u (x-(M.K 1-B))
      rw [← hz] at h
      linarith
  have he : x-(x-z)=z := by ring
  rw [he]
  exact add_le_add h0 h1

noncomputable def boundary (M : Model) (a : Fin 2 → ℝ) (x t : ℝ) : ℝ :=
  slice M a x 0 (x-t)+slice M a x 1 t

lemma boundary_deriv (M : Model) (a : Fin 2 → ℝ) (x t : ℝ)
    (hη : ∀ i, M.η i = 0) (ht0 : 0<t) (htx : t<x) :
    HasDerivAt (boundary M a x)
      ((M.r+M.p-M.v)*(M.phi 1*M.G 1 (M.K 1-t) (a 1)-
        M.phi 0*M.G 0 (M.K 0-(x-t)) (a 0))) t := by
  have h0 := (slice_deriv M a x (x-t) 0 1 (by decide) hη (by linarith) (by linarith)).comp t
    ((hasDerivAt_const t x).sub (hasDerivAt_id t))
  have h1 := slice_deriv M a x t 1 0 (by decide) hη ht0 htx
  convert h0.add h1 using 1 <;> first | rfl | ring_nf

lemma boundary_maximum (M : Model) (a : Fin 2 → ℝ) (x t : ℝ)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i)
    (ht0 : 0 ≤ t) (htx : t ≤ x)
    (hl : 0<t → M.phi 0*M.G 0 (M.K 0-(x-t)) (a 0) ≤ M.phi 1*M.G 1 (M.K 1-t) (a 1))
    (hr : t<x → M.phi 1*M.G 1 (M.K 1-t) (a 1) ≤ M.phi 0*M.G 0 (M.K 0-(x-t)) (a 0)) :
    IsMaxOn (boundary M a x) (Set.Icc 0 x) t := by
  have hc : Continuous (boundary M a x) :=
    ((slice_cont M a x 0).comp (continuous_const.sub continuous_id)).add (slice_cont M a x 1)
  apply isMaxOn_Icc_of_deriv hc.continuousAt hc.continuousAt hc.continuousAt
  · intro z hz
    exact (boundary_deriv M a x z hη hz.1 (hz.2.trans_le htx)).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (boundary_deriv M a x z hη (ht0.trans_lt hz.1) hz.2).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [(boundary_deriv M a x z hη hz.1 (hz.2.trans_le htx)).deriv]
    apply mul_nonneg (sub_pos.mpr M.v_lt).le
    have h0 := mul_le_mul_of_nonneg_left (monotone_cdf (M.ν 0 (a 0)) (show M.K 0-(x-z) ≤ M.K 0-(x-t) by linarith [hz.2])) (hφ 0)
    have h1 := mul_le_mul_of_nonneg_left (monotone_cdf (M.ν 1 (a 1)) (show M.K 1-t ≤ M.K 1-z by linarith [hz.2])) (hφ 1)
    have he := hl (hz.1.trans hz.2)
    change M.phi 0*M.G 0 (M.K 0-(x-z)) (a 0) ≤ M.phi 0*M.G 0 (M.K 0-(x-t)) (a 0) at h0
    change M.phi 1*M.G 1 (M.K 1-t) (a 1) ≤ M.phi 1*M.G 1 (M.K 1-z) (a 1) at h1
    linarith
  · intro z hz
    rw [(boundary_deriv M a x z hη (ht0.trans_lt hz.1) hz.2).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr M.v_lt).le
    have h0 := mul_le_mul_of_nonneg_left (monotone_cdf (M.ν 0 (a 0)) (show M.K 0-(x-t) ≤ M.K 0-(x-z) by linarith [hz.1])) (hφ 0)
    have h1 := mul_le_mul_of_nonneg_left (monotone_cdf (M.ν 1 (a 1)) (show M.K 1-z ≤ M.K 1-t by linarith [hz.1])) (hφ 1)
    have he := hr (hz.1.trans hz.2)
    change M.phi 0*M.G 0 (M.K 0-(x-t)) (a 0) ≤ M.phi 0*M.G 0 (M.K 0-(x-z)) (a 0) at h0
    change M.phi 1*M.G 1 (M.K 1-z) (a 1) ≤ M.phi 1*M.G 1 (M.K 1-t) (a 1) at h1
    linarith

lemma lower_optimal (M : Model) (a : Fin 2 → ℝ) (x A B t : ℝ) (hx : 0 ≤ x)
    (hη : ∀ i, M.η i = 0) (hφ : ∀ i, 0 ≤ M.phi i ∧ M.phi i ≤ 1)
    (hA : M.G 0 A (a 0)=M.phi 1) (hB : M.G 1 B (a 1)=M.phi 0)
    (hreg : x ≤ M.K 0+M.K 1-(A+B)) (ht0 : 0 ≤ t) (htx : t ≤ x)
    (hm : IsMaxOn (boundary M a x) (Set.Icc 0 x) t) :
    M.IsOptimal (Measure.dirac x) a ![x-t,t] := by
  refine ⟨?_,?_⟩
  · intro i; fin_cases i
    · change 0 ≤ x-t; linarith
    · change 0 ≤ t; exact ht0
  intro q hq
  obtain ⟨u,v,hu,hux,hv,hvx,hs,hd⟩ := triangle_dominates M a x hx hη hφ q hq
  obtain ⟨w,hw0,hwx,hle⟩ := triangle_to_boundary M a x A B u v hη hA hB hreg hu hux hv hvx hs
  have hmax := hm ⟨hw0,hwx⟩
  change boundary M a x w ≤ boundary M a x t at hmax
  unfold boundary at hmax
  have he := slices_identity M a x u v hux hvx hs
  have he' := slices_identity M a x (x-t) t (by linarith) htx (by linarith)
  linarith

end SupplyBoundary

#print axioms SupplyBoundary.lower_optimal

theorem solution (M : Model) (a : Fin 2 → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hη : ∀ i, M.η i = 0)
    (hφpos : ∀ i, 0 < M.phi i) (hφlt : ∀ i, M.phi i < 1)
    (hsupp : ∀ i, ∃ b : ℝ, 0 < b ∧ b ≤ M.K i ∧ M.G i b (a i) = 1 ∧
      StrictMonoOn (fun t => M.G i t (a i)) (Set.Icc 0 b))
    (hord : M.phi 1 * M.G 1 (M.K 1) (a 1) ≤ M.phi 0 * M.G 0 (M.K 0) (a 0)) :
    (x ≤ M.K 0 - M.B a → M.IsOptimal (Measure.dirac x) a ![x, 0]) ∧
    (M.K 0 - M.B a < x ∧ x ≤ M.K 0 + M.K 1 - (M.A1 a + M.A2 a) →
      ∃ q₂ : ℝ, 0 ≤ q₂ ∧ q₂ ≤ x ∧
        M.phi 0 * M.G 0 (M.K 0 - (x - q₂)) (a 0) = M.phi 1 * M.G 1 (M.K 1 - q₂) (a 1) ∧
        M.IsOptimal (Measure.dirac x) a ![x - q₂, q₂]) ∧
    (M.K 0 + M.K 1 - (M.A1 a + M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1 - max (M.A1 a) (M.A2 a) →
      M.IsOptimal (Measure.dirac x) a ![x - (M.K 1 - M.A2 a), x - (M.K 0 - M.A1 a)]) ∧
    (M.K 0 + M.K 1 - max (M.A1 a) (M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1 - min (M.A1 a) (M.A2 a) →
      (M.A2 a ≤ M.A1 a → M.IsOptimal (Measure.dirac x) a ![x - (M.K 1 - M.A2 a), M.K 1]) ∧
      (M.A1 a < M.A2 a → M.IsOptimal (Measure.dirac x) a ![M.K 0, x - (M.K 0 - M.A1 a)])) ∧
    ((M.K 0 + M.K 1 - min (M.A1 a) (M.A2 a) < x ∧ x ≤ M.K 0 + M.K 1) ∨ M.K 0 + M.K 1 < x →
      M.IsOptimal (Measure.dirac x) a ![M.K 0, M.K 1]) := by
  obtain ⟨hA,hB,hD,hbal⟩ := prior_thresholds M a x hx (fun i => ⟨hφpos i,hφlt i⟩) hsupp hord
  have hG : ∀ i, M.G i (M.K i) (a i)=1 := by
    intro i
    obtain ⟨b,_,hb,hg,_⟩ := hsupp i
    exact SupplyThresholds.cdf_at_capacity M i (a i) b hb hg
  have hAB : M.A1 a ≤ M.B a := by
    by_contra hh
    have hg : M.G 0 (M.B a) (a 0) ≤ M.G 0 (M.A1 a) (a 0) :=
      monotone_cdf _ (le_of_not_ge hh)
    rw [hD.2.2,hA.2.2] at hg
    have h := (div_le_iff₀ (hφpos 0)).mp hg
    nlinarith [mul_pos (hφpos 1) (sub_pos.mpr (hφlt 0))]
  have hlow (t : ℝ) (ht0 : 0 ≤ t) (htx : t ≤ x)
      (hreg : x ≤ M.K 0+M.K 1-(M.A1 a+M.A2 a))
      (hm : IsMaxOn (SupplyBoundary.boundary M a x) (Set.Icc 0 x) t) :=
    SupplyBoundary.lower_optimal M a x (M.A1 a) (M.A2 a) t hx hη
      (fun i => ⟨(hφpos i).le,(hφlt i).le⟩) hA.2.2 hB.2.2 hreg ht0 htx hm
  refine ⟨?_,?_,prior_hedge M a x hx hη hφpos hφlt hsupp hord⟩
  · intro hr
    have hreg : x ≤ M.K 0+M.K 1-(M.A1 a+M.A2 a) := by linarith [hB.2.1]
    have hm : IsMaxOn (SupplyBoundary.boundary M a x) (Set.Icc 0 x) 0 := by
      apply SupplyBoundary.boundary_maximum M a x 0 hη (fun i => (hφpos i).le) le_rfl hx
      · intro hh; linarith
      · intro _
        simp only [sub_zero,hG,mul_one]
        have hg : M.phi 1/M.phi 0 ≤ M.G 0 (M.K 0-x) (a 0) := by
          rw [← hD.2.2]
          exact monotone_cdf _ (by linarith)
        have hh := (div_le_iff₀ (hφpos 0)).mp hg
        nlinarith
    simpa only [sub_zero] using hlow 0 le_rfl hx hreg hm
  · intro hr
    obtain ⟨t,ht0,htx,_,_,he⟩ := hbal hr
    refine ⟨t,ht0,htx,he,hlow t ht0 htx hr.2 ?_⟩
    apply SupplyBoundary.boundary_maximum M a x t hη (fun i => (hφpos i).le) ht0 htx
    · intro _; exact he.le
    · intro _; exact he.ge

#print axioms solution

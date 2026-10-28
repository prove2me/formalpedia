-- Prove2me | solution 1 for OAI.SharpTerminalLeave.main_l2_prefix_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:55:36.130701+00:00
-- url     : https://prove2.me/submissions/aefaafa2-0c3c-4ac9-b60a-7189c4dd7fed

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000
import Theorems.Thm_OAI_SharpTerminalLeave_averaged_disjoint_grid_collision
import Theorems.Thm_OAI_SharpTerminalLeave_averaged_singleton_grid_collision
import Theorems.Thm_OAI_SharpTerminalLeave_goodPrefix_cavity_semigroup

section
-- module Solutions.OAIQ4_Tr.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_UnitTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open Filter MeasureTheory
open scoped BigOperators Topology BoundedContinuousFunction

namespace SharpTerminalLeave

section Cavity
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem tendsto_cavityDepthBCF (H : τ → Finset ι) :
    Tendsto (cavityDepthBCF H) atTop (𝓝 (cavityLimitBCF H)) :=
  (cauchySeq_tendsto_of_complete (cavityDepthBCF_cauchy H)).choose_spec

theorem continuous_cavityLimit (H : τ → Finset ι) (e : ι) (p : Option τ) :
    Continuous (cavityLimit H e p) := (cavityLimitBCF H e p).continuous

theorem tendsto_cavityDepth (H : τ → Finset ι) (e : ι) (p : Option τ) (t : ℝ) :
    Tendsto (fun k => cavityDepth H k e p t) atTop (𝓝 (cavityLimit H e p t)) := by
  have h := ((tendsto_pi_nhds.mp (tendsto_cavityDepthBCF H)) e)
  have h' := (tendsto_pi_nhds.mp h) p
  exact ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto
    (cavityLimitBCF H e p)).comp h'

theorem cavityLimit_mem_unit (H : τ → Finset ι) (e : ι) (p : Option τ) (t : ℝ) :
    cavityLimit H e p t ∈ Set.Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (tendsto_cavityDepth H e p t)
    (Eventually.of_forall fun k => cavityDepth_mem_unit H k e p t)

omit [DecidableEq ι] [DecidableEq τ] in

theorem cavitySpace_eval_sub_le (q r : CavitySpace ι τ) (e : ι) (p : Option τ) (t : ℝ) :
    |q e p t - r e p t| ≤ ‖q - r‖ := by
  exact ((BoundedContinuousFunction.norm_coe_le_norm (q e p - r e p) t).trans
    (norm_le_pi_norm ((q - r) e) p)).trans (norm_le_pi_norm (q - r) e)

theorem cavityLimit_product (H : τ → Finset ι) (e : ι) (p : Option τ) (t : ℝ) :
    cavityLimit H e p t = cavityOperator H (cavityLimit H) e p t := by
  let d : ℕ → ℝ := fun k => ‖cavityDepthBCF H k - cavityLimitBCF H‖
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_cavityDepthBCF H).sub (tendsto_const_nhds (x := cavityLimitBCF H))).norm
  have hbound : ∀ k,
      |cavityDepth H (k + 1) e p t - cavityOperator H (cavityLimit H) e p t| ≤
        cavityBranching (ι := ι) (τ := τ) * (unitTime t * d k) := by
    intro k
    have h := cavityOperator_lipschitz H (cavityDepth H k) (cavityLimit H)
      (continuous_cavityDepth H k) (continuous_cavityLimit H)
      (cavityDepth_mem_unit H k) (cavityLimit_mem_unit H)
      (fun _ => d k) continuous_const (fun _ _ => norm_nonneg _)
      (fun f o s _ => cavitySpace_eval_sub_le (cavityDepthBCF H k) (cavityLimitBCF H) f o s)
      e p t
    simpa only [cavityDepth, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h
  have herr : Tendsto (fun k =>
      |cavityDepth H (k + 1) e p t - cavityOperator H (cavityLimit H) e p t|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) hbound
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.mul hd)
  have hop : Tendsto (fun k => cavityDepth H (k + 1) e p t) atTop
      (𝓝 (cavityOperator H (cavityLimit H) e p t)) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    simpa only [Real.dist_eq] using herr
  exact tendsto_nhds_unique ((tendsto_cavityDepth H e p t).comp
    (tendsto_add_atTop_nat 1)) hop

@[simp] theorem cavityLimit_zero_time (H : τ → Finset ι) (e : ι) (p : Option τ) :
    cavityLimit H e p 0 = 1 := by
  apply tendsto_nhds_unique (tendsto_cavityDepth H e p 0)
  simpa only [cavityDepth_zero_time] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
    atTop (𝓝 1))

omit [Fintype ι] in
theorem messageCandidates_omission (H : τ → Finset ι) (e : ι) (T : τ) :
    messageCandidates H e (some T) = (messageCandidates H e none).erase T := by
  ext U
  simp [messageCandidates, and_comm]

theorem cavityLimit_omission (H : τ → Finset ι) (e : ι) (T : τ)
    (he : e ∈ H T) (t : ℝ) :
    cavityLimit H e none t = cavityLimit H e (some T) t *
      (1 - messageIntegral H (cavityLimit H) e T t) := by
  rw [cavityLimit_product H e none t, cavityLimit_product H e (some T) t]
  unfold cavityOperator
  rw [messageCandidates_omission]
  exact (Finset.prod_erase_mul _ _ (by simp [messageCandidates, he])).symm

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem messageIntegral_le_time (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hc : ∀ e p, Continuous (q e p))
    (hq : ∀ e p t, q e p t ∈ Set.Icc (0 : ℝ) 1) (e : ι) (T : τ) (t : ℝ) :
    messageIntegral H q e T t ≤ unitTime t := by
  have hu := intervalIntegral.integral_mono_on (μ := volume) (unitTime_nonneg t)
    ((continuous_message_integrand H q hc e T).intervalIntegrable 0 (unitTime t))
    (continuous_const.intervalIntegrable 0 (unitTime t)) (fun s _ =>
      Finset.prod_le_one (fun edge _ => (hq edge (some T) s).1)
        (fun edge _ => (hq edge (some T) s).2))
  simpa [messageIntegral] using hu

theorem cavityLimit_factor_pos (H : τ → Finset ι) (e : ι) (T : τ)
    {t : ℝ} (ht : t < 1) :
    0 < 1 - messageIntegral H (cavityLimit H) e T t := by
  have hb := messageIntegral_le_time H (cavityLimit H) (continuous_cavityLimit H)
    (cavityLimit_mem_unit H) e T t
  have htime : unitTime t < 1 := by
    exact max_lt zero_lt_one ((min_le_right 1 t).trans_lt ht)
  linarith

theorem cavityLimit_pos (H : τ → Finset ι) (e : ι) (p : Option τ)
    {t : ℝ} (ht : t < 1) : 0 < cavityLimit H e p t := by
  rw [cavityLimit_product]
  exact Finset.prod_pos (fun T _ => cavityLimit_factor_pos H e T ht)

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem messageIntegral_hasDerivAt (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hc : ∀ e p, Continuous (q e p))
    (e : ι) (T : τ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (messageIntegral H q e T)
      (∏ f ∈ (H T).erase e, q f (some T) t) t := by
  have hcont := continuous_message_integrand H q hc e T
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 t) hcont.stronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  simp only [messageIntegral, unitTime_of_mem ⟨le_of_lt hx.1, le_of_lt hx.2⟩]

theorem cavityLimit_hasDerivAt (H : τ → Finset ι) (e : ι) (p : Option τ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (cavityLimit H e p)
      (-cavityLimit H e p t *
        ∑ T ∈ messageCandidates H e p,
          (∏ f ∈ (H T).erase e, cavityLimit H f (some T) t) /
            (1 - messageIntegral H (cavityLimit H) e T t)) t := by
  let F : τ → ℝ → ℝ := fun T s => 1 - messageIntegral H (cavityLimit H) e T s
  let J : τ → ℝ := fun T => ∏ f ∈ (H T).erase e, cavityLimit H f (some T) t
  have hF : ∀ T, HasDerivAt (F T) (-J T) t := by
    intro T
    convert (hasDerivAt_const t (1 : ℝ)).sub
      (messageIntegral_hasDerivAt H (cavityLimit H) (continuous_cavityLimit H) e T ht) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [J, zero_sub]
  have hd := HasDerivAt.finsetProd (u := messageCandidates H e p) (fun T _ => hF T)
  have heq : (∏ T ∈ messageCandidates H e p, F T) = cavityLimit H e p := by
    funext s
    simpa only [Finset.prod_apply, cavityOperator, F] using (cavityLimit_product H e p s).symm
  rw [heq] at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hc : cavityLimit H e p t =
      (∏ U ∈ (messageCandidates H e p).erase T, F U t) * F T t := by
    rw [cavityLimit_product]
    exact (Finset.prod_erase_mul _ _ hT).symm
  have hp : F T t ≠ 0 := ne_of_gt (cavityLimit_factor_pos H e T ht.2)
  simp only [smul_eq_mul]
  change -cavityLimit H e p t * (J T / F T t) = _
  rw [hc]
  field_simp

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem cavityTime_hasDerivAt (D s : ℝ) :
    HasDerivAt (cavityTime D) (Real.exp (2 * s) / D) s := by
  have hh := (((hasDerivAt_id s).const_mul 2).exp.sub_const 1).div_const (2 * D)
  convert hh using 1 <;> (try rfl)
  simp only [id_eq, mul_one]
  ring

theorem cavityLog_zero (H : τ → Finset ι) (D : ℝ) (e : ι) : cavityLog H D e 0 = 0 := by
  simp [cavityLog, cavityTime, cavityLimit_zero_time]

theorem cavityLog_exp (H : τ → Finset ι) (D : ℝ) (e : ι) {s : ℝ}
    (ht : cavityTime D s < 1) :
    cavityLimit H e none (cavityTime D s) = Real.exp (cavityLog H D e s - s) := by
  simp only [cavityLog, add_sub_cancel_right]
  exact (Real.exp_log (cavityLimit_pos H e none ht)).symm

theorem cavityLog_parent (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ)
    (he : e ∈ H T) {s : ℝ} (ht : cavityTime D s < 1) :
    cavityLimit H e (some T) (cavityTime D s) =
      Real.exp (cavityLog H D e s - s) / (1 - cavityMessage H D e T s) := by
  apply (eq_div_iff (ne_of_gt (cavityLimit_factor_pos H e T ht))).mpr
  simpa only [cavityMessage, cavityLog_exp H D e ht] using
    (cavityLimit_omission H e T he (cavityTime D s)).symm

theorem cavityLog_hasDerivAt (H : τ → Finset ι) (D : ℝ) (e : ι)
    {s : ℝ} (ht : cavityTime D s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (cavityLog H D e)
      (1 - Real.exp (2 * s) / D *
        ∑ T ∈ messageCandidates H e none,
          (∏ f ∈ (H T).erase e, cavityLimit H f (some T) (cavityTime D s)) /
            (1 - cavityMessage H D e T s)) s := by
  have hp := cavityLimit_pos H e none ht.2
  have hh := ((cavityLimit_hasDerivAt H e none ht).comp s (cavityTime_hasDerivAt D s)).log hp.ne'
  have hh' := hh.add (hasDerivAt_id s)
  convert hh' using 1 <;> try rfl
  dsimp only [Function.comp_apply, cavityMessage]
  field_simp
  ring

theorem cavityMessage_hasDerivAt (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ)
    {s : ℝ} (ht : cavityTime D s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (cavityMessage H D e T)
      (Real.exp (2 * s) / D *
        ∏ f ∈ (H T).erase e, cavityLimit H f (some T) (cavityTime D s)) s := by
  convert (messageIntegral_hasDerivAt H (cavityLimit H) (continuous_cavityLimit H) e T ht).comp s
    (cavityTime_hasDerivAt D s) using 1 <;> try rfl
  ring

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in

theorem triangle_children {H : τ → Finset ι} {e : ι} {T : τ}
    (hcard : (H T).card = 3) (he : e ∈ H T) :
    ∃ f g, f ≠ g ∧ (H T).erase e = {f, g} ∧ f ∈ H T ∧ g ∈ H T := by
  have hh : ((H T).erase e).card = 2 := by
    rw [Finset.card_erase_of_mem he, hcard]
  rcases Finset.card_eq_two.mp hh with ⟨f, g, hfg, hset⟩
  refine ⟨f, g, hfg, hset, ?_, ?_⟩
  · have hm : f ∈ (H T).erase e := by rw [hset]; simp
    exact Finset.mem_of_mem_erase hm
  · have hm : g ∈ (H T).erase e := by rw [hset]; simp
    exact Finset.mem_of_mem_erase hm

theorem cavity_triangle_summand (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ)
    {f g : ι} (hfg : f ≠ g) (hchildren : (H T).erase e = {f, g})
    (hf : f ∈ H T) (hg : g ∈ H T) {s : ℝ} (ht : cavityTime D s < 1) :
    Real.exp (2 * s) *
        ((∏ u ∈ (H T).erase e, cavityLimit H u (some T) (cavityTime D s)) /
          (1 - cavityMessage H D e T s)) =
      Real.exp (cavityLog H D f s + cavityLog H D g s) /
        ((1 - cavityMessage H D e T s) * (1 - cavityMessage H D f T s) *
          (1 - cavityMessage H D g T s)) := by
  have he0 := (cavityLimit_factor_pos H e T ht).ne'
  have hf0 := (cavityLimit_factor_pos H f T ht).ne'
  have hg0 := (cavityLimit_factor_pos H g T ht).ne'
  rw [hchildren, Finset.prod_pair hfg, cavityLog_parent H D f T hf ht,
    cavityLog_parent H D g T hg ht]
  have heq : Real.exp (2 * s) * (Real.exp (cavityLog H D f s - s) *
      Real.exp (cavityLog H D g s - s)) =
      Real.exp (cavityLog H D f s + cavityLog H D g s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  dsimp only [cavityMessage] at *
  field_simp
  nlinarith [heq]

theorem cavity_triangle_message_summand (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ)
    {f g : ι} (hfg : f ≠ g) (hchildren : (H T).erase e = {f, g})
    (hf : f ∈ H T) (hg : g ∈ H T) {s : ℝ} (ht : cavityTime D s < 1) :
    Real.exp (2 * s) *
        (∏ u ∈ (H T).erase e, cavityLimit H u (some T) (cavityTime D s)) =
      Real.exp (cavityLog H D f s + cavityLog H D g s) /
        ((1 - cavityMessage H D f T s) * (1 - cavityMessage H D g T s)) := by
  have hf0 := (cavityLimit_factor_pos H f T ht).ne'
  have hg0 := (cavityLimit_factor_pos H g T ht).ne'
  rw [hchildren, Finset.prod_pair hfg, cavityLog_parent H D f T hf ht,
    cavityLog_parent H D g T hg ht]
  have heq : Real.exp (2 * s) * (Real.exp (cavityLog H D f s - s) *
      Real.exp (cavityLog H D g s - s)) =
      Real.exp (cavityLog H D f s + cavityLog H D g s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  dsimp only [cavityMessage] at *
  field_simp
  nlinarith [heq]

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem continuous_cavityTime (D : ℝ) : Continuous (cavityTime D) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const |>.div_const _

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem cavityTime_mono {D : ℝ} (hD : 0 < D) : Monotone (cavityTime D) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sub_le_sub_right (Real.exp_le_exp.mpr (by linarith)) _

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem cavityTime_pos {D s : ℝ} (hD : 0 < D) (hs : 0 < s) : 0 < cavityTime D s := by
  apply div_pos _ (by positivity)
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))

theorem continuous_cavityMessage (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ) :
    Continuous (cavityMessage H D e T) :=
  (continuous_messageIntegral H (cavityLimit H) (continuous_cavityLimit H) e T).comp
    (continuous_cavityTime D)

theorem cavityMessage_nonneg (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ) (s : ℝ) :
    0 ≤ cavityMessage H D e T s :=
  (messageIntegral_mem_unit H (cavityLimit H) (continuous_cavityLimit H)
    (cavityLimit_mem_unit H) e T (cavityTime D s)).1

theorem continuousOn_cavityLog (H : τ → Finset ι) {D S : ℝ}
    (hD : 0 < D) (hS : cavityTime D S < 1) (e : ι) :
    ContinuousOn (cavityLog H D e) (Set.Icc 0 S) := by
  apply ContinuousOn.add _ continuousOn_id
  exact ((continuous_cavityLimit H e none).comp (continuous_cavityTime D)).continuousOn.log
    (fun s hs => (cavityLimit_pos H e none ((cavityTime_mono hD hs.2).trans_lt hS)).ne')

end Cavity
end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_ProductPMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

theorem productPMF_update_apply {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ρ : K → PMF V) (k : K) (v : V) (ω : K → V) :
    productPMF (Function.update ρ k (PMF.pure v)) ω =
      (if ω k = v then 1 else 0) * ∏ j ∈ Finset.univ.erase k, ρ j (ω j) := by
  rw [productPMF_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  have hh : (∏ j ∈ Finset.univ.erase k, Function.update ρ k (PMF.pure v) j (ω j)) =
      ∏ j ∈ Finset.univ.erase k, ρ j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hh, Function.update_self]
  simp only [PMF.pure_apply, eq_comm]
  exact mul_comm _ _

theorem productPMF_split {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ρ : K → PMF V) (k : K) :
    productPMF ρ = (ρ k).bind (fun v => productPMF (Function.update ρ k (PMF.pure v))) := by
  ext ω
  rw [PMF.bind_apply, tsum_fintype]
  simp only [productPMF_update_apply]
  rw [Finset.sum_eq_single (ω k)]
  · simp only [ite_true, one_mul]
    rw [productPMF_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    exact mul_comm _ _
  · intro v _ hv
    simp only [ite_eq_right (Ne.symm hv), zero_mul, mul_zero]
  · simp

namespace ExposureTree
variable {K V O : Type*}

theorem coupled_agrees [DecidableEq K] (ν : K → PMF V) (ω : K → V)
    (P : ExposureTree K V O) (seen : Finset K) (o : O)
    (ho : (o, false) ∈ (coupled ν ω P seen).support) : evaluate ω P = o := by
  induction P generalizing seen with
  | done a =>
    have hh : (o, false) = (a, false) := by simpa [coupled] using ho
    exact (congrArg Prod.fst hh).symm
  | ask k f ih =>
    by_cases hk : k ∈ seen
    · simp only [coupled, ite_eq_left hk, PMF.mem_support_bind_iff] at ho
      obtain ⟨v, _, hv⟩ := ho
      rcases (PMF.mem_support_map_iff _ _ _).mp hv with ⟨z, _, hz⟩
      exact False.elim (by simpa using congrArg Prod.snd hz)
    · exact ih (ω k) (insert k seen) (by simpa [coupled, hk] using ho)

theorem freshRecorded_outcome [DecidableEq K] (ν : K → PMF V)
    (P : ExposureTree K V O) (seen : Finset K) :
    (freshRecorded ν P seen).map Prod.fst = fresh ν P := by
  induction P generalizing seen with
  | done o => simp [freshRecorded, fresh, PMF.pure_map]
  | ask k f ih =>
    simp only [freshRecorded, PMF.map_bind, fresh]
    congr 1
    funext v
    by_cases hk : k ∈ seen
    · simp only [ite_eq_left hk, PMF.map_comp]
      exact ih v seen
    · simp only [ite_eq_right hk]
      exact ih v (insert k seen)

end ExposureTree

theorem pmf_bind_congr_on_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp only [ha, zero_mul]
  · rw [h a ha]

namespace ExposureTree
variable {K V O : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

theorem coupled_independent_law (ν : K → PMF V) (P : ExposureTree K V O)
    (seen : Finset K) (ρ : K → PMF V) (hρ : ∀ k ∉ seen, ρ k = ν k) :
    (productPMF ρ).bind (fun ω => coupled ν ω P seen) = freshRecorded ν P seen := by
  induction P generalizing seen ρ with
  | done o => simp [coupled, freshRecorded, PMF.bind_const]
  | ask k f ih =>
    by_cases hk : k ∈ seen
    · simp only [coupled, ite_eq_left hk, freshRecorded]
      rw [PMF.bind_comm]
      congr 1
      funext v
      rw [← PMF.map_bind]
      exact congrArg (fun p : PMF (O × Bool) => p.map (fun z => (z.1, true)))
        (ih v seen ρ hρ)
    · simp only [coupled, ite_eq_right hk, freshRecorded]
      rw [productPMF_split ρ k, PMF.bind_bind, hρ k hk]
      congr 1
      funext v
      let ρ' : K → PMF V := Function.update ρ k (PMF.pure v)
      have hv : ∀ ω ∈ (productPMF ρ').support, ω k = v := by
        intro ω hω
        have hh := (productPMF_support ρ' ω).mp hω k
        simpa only [ρ', Function.update_self, PMF.mem_support_pure_iff] using hh
      calc
        _ = (productPMF ρ').bind
            (fun ω => coupled ν ω (f v) (insert k seen)) := by
          apply pmf_bind_congr_on_support
          intro ω hω
          rw [hv ω hω]
        _ = freshRecorded ν (f v) (insert k seen) := by
          apply ih v (insert k seen) ρ'
          intro j hj
          have hjs : j ∉ seen := fun h => hj (Finset.mem_insert_of_mem h)
          have hjk : j ≠ k := fun h => hj (h ▸ Finset.mem_insert_self _ _)
          simp only [ρ', Function.update_of_ne hjk, hρ j hjs]

theorem coupled_independent_law_empty (ν : K → PMF V) (P : ExposureTree K V O) :
    (productPMF ν).bind (fun ω => coupled ν ω P ∅) = freshRecorded ν P ∅ :=
  coupled_independent_law ν P ∅ ν (fun _ _ => rfl)

omit [DecidableEq V] in

theorem jointLaw_fixed (ν : K → PMF V) (P : ExposureTree K V O) :
    (jointLaw ν P).map Prod.fst = (productPMF ν).map (fun ω => evaluate ω P) := by
  simp only [jointLaw, PMF.map_bind, PMF.map_comp]
  change (productPMF ν).bind (fun ω =>
    (coupled ν ω P ∅).map (Function.const (O × Bool) (evaluate ω P))) = _
  simp only [PMF.map_const]
  rfl

theorem jointLaw_fresh (ν : K → PMF V) (P : ExposureTree K V O) :
    (jointLaw ν P).map Prod.snd = freshRecorded ν P ∅ := by
  simp only [jointLaw, PMF.map_bind, PMF.map_comp]
  change (productPMF ν).bind (fun ω => (coupled ν ω P ∅).map id) = _
  simp only [PMF.map_id]
  exact coupled_independent_law_empty ν P

omit [DecidableEq V] in

theorem jointLaw_agrees (ν : K → PMF V) (P : ExposureTree K V O)
    (z : O × (O × Bool)) (hz : z ∈ (jointLaw ν P).support) (hf : z.2.2 = false) :
    z.1 = z.2.1 := by
  rcases (PMF.mem_support_bind_iff _ _ _).mp hz with ⟨ω, _, hω⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp hω with ⟨o, ho, hzo⟩
  subst z
  have he : o = (o.1, false) := Prod.ext rfl hf
  rw [he] at ho
  exact coupled_agrees ν ω P ∅ o.1 ho

end ExposureTree
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_TreeBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

theorem bool_probability_sum (p : PMF Bool) : trueProbability p + falseProbability p = 1 := by
  have hh := p.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at hh
  have hr := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_add (p.apply_ne_top _) (p.apply_ne_top _),
    ENNReal.toReal_one, trueProbability, falseProbability] using hr

theorem trueProbability_nonneg (p : PMF Bool) : 0 ≤ trueProbability p := ENNReal.toReal_nonneg

theorem falseProbability_nonneg (p : PMF Bool) : 0 ≤ falseProbability p := ENNReal.toReal_nonneg

theorem trueProbability_le_one (p : PMF Bool) : trueProbability p ≤ 1 := by
  have := bool_probability_sum p
  have := falseProbability_nonneg p
  linarith

theorem trueProbability_bind {V : Type*} [Fintype V] (p : PMF V) (f : V → PMF Bool) :
    trueProbability (p.bind f) = ∑ v, (p v).toReal * trueProbability (f v) := by
  unfold trueProbability
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro v _
    exact ENNReal.mul_ne_top (p.apply_ne_top v) ((f v).apply_ne_top true)

theorem trueProbability_bool_bind (p : PMF Bool) (f : Bool → PMF Bool) :
    trueProbability (p.bind f) = trueProbability p * trueProbability (f true) +
      falseProbability p * trueProbability (f false) := by
  rw [trueProbability_bind, Fintype.sum_bool]
  rfl

namespace ExposureTree
variable {K V : Type*}

theorem fresh_checkNone_true (ν : K → PMF V) (As : List (ExposureTree K V Bool)) :
    trueProbability (fresh ν (checkNone As)) = (As.map (fun A => falseProbability (fresh ν A))).prod := by
  induction As with
  | nil => simp [checkNone, fresh]
  | cons A As ih =>
    rw [checkNone, fresh_bind, trueProbability_bool_bind]
    simp [fresh, ih]

theorem exposeLabeled_product {A : Type*} [Fintype V] (ν : K → PMF V) (key : A → K) (ks : List A)
    (C : List (A × V) → ExposureTree K V Bool) (h : A → V → ℝ)
    (hc : ∀ xs, trueProbability (fresh ν (C xs)) = (xs.map (fun p => h p.1 p.2)).prod) :
    trueProbability (fresh ν (ExposureTree.bind (exposeLabeled key ks) C)) =
      (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod := by

  suffices hh : ∀ (ks : List A) (a : ℝ) (C : List (A × V) → ExposureTree K V Bool),
      (∀ xs, trueProbability (fresh ν (C xs)) = a * (xs.map (fun p => h p.1 p.2)).prod) →
      trueProbability (fresh ν (ExposureTree.bind (exposeLabeled key ks) C)) =
        a * (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod by
    simpa only [one_mul] using hh ks 1 C (by simpa only [one_mul] using hc)
  intro ks
  induction ks with
  | nil =>
    intro a C hh
    simpa only [exposeLabeled, bind, List.map_nil, List.prod_nil] using hh []
  | cons k ks ih =>
    intro a C hh
    simp only [exposeLabeled, bind, fresh, trueProbability_bind]
    have hx : ∀ v, trueProbability (fresh ν
        (bind (bind (exposeLabeled key ks) (fun xs => .done ((k, v) :: xs))) C)) =
        (a * h k v) * (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod := by
      intro v
      have hassoc : bind (bind (exposeLabeled (V := V) key ks) (fun xs => .done ((k, v) :: xs))) C =
          bind (exposeLabeled key ks) (fun xs => C ((k, v) :: xs)) := by
        induction exposeLabeled (V := V) key ks with
        | done xs => rfl
        | ask k f hi => simp only [bind, hi]
      rw [hassoc]
      apply ih
      intro xs
      rw [hh]
      simp only [List.map_cons, List.prod_cons]
      ring
    simp only [hx, List.map_cons, List.prod_cons]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring

end ExposureTree

section GridQuery
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem gridAnswerProbability_step (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N (d + 1) k focus parent =
      ∏ p ∈ gridCandidates H focus parent,
        ∑ u : Fin N, (1 / (N : ℝ)) *
          (if u.val < k then 1 - gridAnswerProbability H N d u.val
            ((H p.2).erase p.1) (some p.2) else 1) := by
  unfold gridAnswerProbability
  rw [gridQueryDepth]
  have hh := ExposureTree.exposeLabeled_product (gridPriorities (τ := τ) N) Prod.snd
    (gridCandidates H focus parent).toList
    (fun values => ExposureTree.checkNone
      (((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
        (fun p => if p.2.val < k then
          gridQueryDepth H N d p.2.val ((H p.1.2).erase p.1.1) (some p.1.2)
          else .done false))))
    (fun p u => if u.val < k then 1 - gridAnswerProbability H N d u.val
      ((H p.2).erase p.1) (some p.2) else 1) (by
      intro values
      rw [ExposureTree.fresh_checkNone_true, List.map_map]
      have hp := (List.mergeSort_perm values (fun a b => a.2.val ≤ b.2.val)).map
        (fun p => falseProbability (ExposureTree.fresh (gridPriorities N)
          (if p.2.val < k then gridQueryDepth H N d p.2.val
            ((H p.1.2).erase p.1.1) (some p.1.2) else .done false)))
      refine hp.prod_eq.trans ?_
      congr 1
      apply List.map_congr_left
      intro p _
      by_cases hpk : p.2.val < k
      · simp only [hpk, ite_true]
        have hb := bool_probability_sum (ExposureTree.fresh (gridPriorities N)
          (gridQueryDepth H N d p.2.val ((H p.1.2).erase p.1.1) (some p.1.2)))
        change falseProbability _ = 1 - trueProbability _
        linarith
      · simp [hpk, ExposureTree.fresh])
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [gridPriorities, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_fin, one_div]
  exact (Finset.prod_map_toList _ _).symm

theorem gridAnswerProbability_mem_unit (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N d k focus parent ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨trueProbability_nonneg _, trueProbability_le_one _⟩

theorem prod_gridCandidates {M : Type*} [CommMonoid M] (H : τ → Finset ι)
    (focus : Finset ι) (parent : Option τ) (f : ι × τ → M) :
    (∏ p ∈ gridCandidates H focus parent, f p) =
      ∏ e ∈ focus, ∏ T ∈ messageCandidates H e parent, f (e, T) := by
  simp only [gridCandidates, messageCandidates, Finset.prod_filter]
  exact Finset.prod_product _ _ _

theorem gridAnswerProbability_factor (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N d k focus parent =
      ∏ e ∈ focus, gridAnswerProbability H N d k {e} parent := by
  cases d with
  | zero => simp
  | succ d =>
    simp only [gridAnswerProbability_step, prod_gridCandidates, Finset.prod_singleton]

theorem uniform_grid_average (N : ℕ) [NeZero N] (k : ℕ) (f : Fin N → ℝ) :
    (∑ u : Fin N, (1 / (N : ℝ)) * (if u.val < k then 1 - f u else 1)) =
      1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), f u := by
  have hpoint : ∀ u : Fin N, (if u.val < k then 1 - f u else 1) =
      1 - (if u.val < k then f u else 0) := by
    intro u; split_ifs <;> ring
  simp only [hpoint, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum,
    Finset.sum_filter, mul_ite, mul_zero]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [mul_one_div_cancel hN]

theorem gridMessage_step (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (e : ι) (parent : Option τ) :
    gridMessage H N (d + 1) k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k),
          ∏ f ∈ (H T).erase e, gridMessage H N d u.val f (some T)) := by
  simp only [gridMessage, gridAnswerProbability_step, prod_gridCandidates,
    Finset.prod_singleton, uniform_grid_average]
  apply Finset.prod_congr rfl
  intro T _
  congr 2
  apply Finset.sum_congr rfl
  intro u _
  exact gridAnswerProbability_factor H N d u.val ((H T).erase e) (some T)

theorem gridQueryDepth_threshold_zero (H : τ → Finset ι) (N d : ℕ)
    (focus : Finset ι) (parent : Option τ) :
    gridQueryDepth H N d 0 focus parent = gridQueryDepth H N 0 0 focus parent := by
  cases d with
  | zero => rfl
  | succ d => simp only [gridQueryDepth, Nat.not_lt_zero, ↓reduceIte,
      ExposureTree.checkNone_done_false]

theorem gridQueryDepth_stable (H : τ → Finset ι) (N k d d' : ℕ)
    (hd : k ≤ d) (hd' : k ≤ d') (focus : Finset ι) (parent : Option τ) :
    gridQueryDepth H N d k focus parent = gridQueryDepth H N d' k focus parent := by
  induction k using Nat.strong_induction_on generalizing d d' focus parent with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      exact (gridQueryDepth_threshold_zero H N d focus parent).trans
        (gridQueryDepth_threshold_zero H N d' focus parent).symm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d' ≠ 0)
      simp only [gridQueryDepth]
      congr 1
      funext values
      congr 1
      apply List.map_congr_left
      intro x _
      split_ifs with hx
      · exact ih x.2.val hx d d' (by omega) (by omega) _ _
      · rfl

theorem gridMessage_stable (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k d d' : ℕ) (hd : k ≤ d) (hd' : k ≤ d') (e : ι) (parent : Option τ) :
    gridMessage H N d k e parent = gridMessage H N d' k e parent := by
  unfold gridMessage gridAnswerProbability
  rw [gridQueryDepth_stable H N k d d' hd hd']

theorem gridMessage_exact (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (parent : Option τ) :
    gridMessage H N N k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k),
          ∏ f ∈ (H T).erase e, gridMessage H N N u.val f (some T)) := by
  rw [gridMessage_stable H N k N (N + 1) hk (by omega), gridMessage_step]

end GridQuery
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_FreshLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
open scoped BigOperators

variable {K V O P : Type*}

theorem freshRecorded_eq_log [DecidableEq K] (ν : K → PMF V)
    (A : ExposureTree K V O) (seen : Finset K) :
    freshRecorded ν A seen =
      (freshLog ν A).map (fun z => (z.1, repeats seen z.2)) := by
  induction A generalizing seen with
  | done o => simp [freshRecorded, freshLog, repeats, PMF.pure_map]
  | ask k f ih =>
    simp only [freshRecorded, freshLog, PMF.map_bind, PMF.map_comp]
    congr 1
    funext v
    by_cases hk : k ∈ seen
    · simp only [ite_eq_left hk, ih, PMF.map_comp]
      congr 1
      funext z
      simp [repeats, hk]
    · simp only [ite_eq_right hk, ih]
      congr 1
      funext z
      simp [repeats, hk]

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_FiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmf_weight_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

@[simp] theorem pmfMean_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  simp only [pmfMean, ← Finset.sum_mul, pmf_weight_sum, one_mul]

theorem pmfMean_congr {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_add {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a + g a) = pmfMean p f + pmfMean p g := by
  simp only [pmfMean, mul_add, Finset.sum_add_distrib]

theorem pmfMean_sub {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a - g a) = pmfMean p f - pmfMean p g := by
  simp only [pmfMean, mul_sub, Finset.sum_sub_distrib]

theorem pmfMean_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => f a * c) = pmfMean p f * c := by
  simp only [pmfMean, ← mul_assoc, ← Finset.sum_mul]

theorem pmfMean_const_mul {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfMean p (fun a => c * f a) = c * pmfMean p f := by
  simpa only [mul_comm] using pmfMean_mul_const p f c

theorem pmfMean_nonneg {α : Type*} [Fintype α] (p : PMF α) {f : α → ℝ}
    (h : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ pmfMean p f := by
  apply Finset.sum_nonneg
  intro a _
  by_cases ha : a ∈ p.support
  · exact mul_nonneg ENNReal.toReal_nonneg (h a ha)
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_mono {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a ≤ g a) : pmfMean p f ≤ pmfMean p g := by
  have hh := pmfMean_nonneg p (fun a ha => sub_nonneg.mpr (h a ha))
  rwa [pmfMean_sub, sub_nonneg] at hh

theorem pmfMean_sq_sub {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => (f a - c) ^ 2) =
      pmfMean p (fun a => f a ^ 2) - 2 * c * pmfMean p f + c ^ 2 := by
  have hpoly : (fun a => (f a - c) ^ 2) =
      (fun a => (f a ^ 2 - (2 * c) * f a) + c ^ 2) := by
    funext a
    ring
  rw [hpoly, pmfMean_add, pmfMean_sub, pmfMean_const_mul, pmfMean_const]

theorem pmfMean_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  simp only [pmfMean, PMF.bind_apply, tsum_fintype]
  have hfin (b : β) (a : α) : p a * q a b ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hfin _ a), Finset.sum_mul,
    ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem pmfMean_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfMean (p.map g) f = pmfMean p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfMean_bind]
  simp

theorem pmfMean_uniformOfFinset {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfMean (PMF.uniformOfFinset s hs) f = (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [pmfMean, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  simp only [div_eq_mul_inv, mul_comm, Finset.sum_mul]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TerminalLaw
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem triangles_mono {n : ℕ} {G H : Graph n} (h : H ⊆ G) :
    triangles H ⊆ triangles G := by
  intro t ht
  obtain ⟨hc, he⟩ := mem_triangles.mp ht
  exact mem_triangles.mpr ⟨hc, he.trans h⟩

theorem triangle_edge_card {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) : (t.powersetCard 2).card = 3 := by
  rw [Finset.card_powersetCard, (mem_triangles.mp ht).1]
  decide

theorem three_le_card_of_triangle {n : ℕ} {G : Graph n}
    (h : (triangles G).Nonempty) : 3 ≤ G.card := by
  obtain ⟨t, ht⟩ := h
  have hc := Finset.card_le_card (mem_triangles.mp ht).2
  rwa [triangle_edge_card ht] at hc

theorem step_absorbing {n : ℕ} {G : Graph n} (h : triangles G = ∅) :
    step G = PMF.pure G := by
  simp [step, h]

theorem step_card_of_active {n : ℕ} {G H : Graph n}
    (hG : (triangles G).Nonempty) (h : H ∈ (step G).support) :
    H.card + 3 = G.card := by
  obtain ⟨t, ht, rfl⟩ := (step_support_active hG).mp h
  have hc := Finset.card_sdiff_add_card_eq_card (mem_triangles.mp ht).2
  rwa [triangle_edge_card ht] at hc

theorem evolve_support_subset {n : ℕ} (G : Graph n) (k : ℕ) {H : Graph n}
    (h : H ∈ (evolve G k).support) : H ⊆ G := by
  induction k generalizing H with
  | zero =>
    simp only [evolve, PMF.mem_support_pure_iff] at h
    exact h ▸ Finset.Subset.refl G
  | succ k ih =>
    obtain ⟨J, hJ, hH⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    exact (step_support_subset hH).trans (ih hJ)

theorem evolve_card_of_active {n : ℕ} (G : Graph n) (k : ℕ) {H : Graph n}
    (h : H ∈ (evolve G k).support) (hH : (triangles H).Nonempty) :
    H.card + 3 * k = G.card := by
  induction k generalizing H with
  | zero =>
    simp only [evolve, PMF.mem_support_pure_iff] at h
    simp [h]
  | succ k ih =>
    obtain ⟨J, hJ, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    have hJs : (triangles J).Nonempty :=
      hH.mono (triangles_mono (step_support_subset hstep))
    have hprev := ih hJ hJs
    have hcard := step_card_of_active hJs hstep
    omega

theorem evolve_terminal {n : ℕ} (G : Graph n) (k : ℕ) (hk : G.card ≤ k)
    {H : Graph n} (h : H ∈ (evolve G k).support) : triangles H = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hH
  have hcard := evolve_card_of_active G k h hH
  have hthree := three_le_card_of_triangle hH
  omega

@[simp] theorem evolve_absorbing {n : ℕ} (G : Graph n)
    (hG : triangles G = ∅) (k : ℕ) : evolve G k = PMF.pure G := by
  induction k with
  | zero => rfl
  | succ k ih => simp [evolve, ih, step_absorbing hG]

theorem evolve_add {n : ℕ} (G : Graph n) (k l : ℕ) :
    evolve G (k + l) = (evolve G k).bind (fun H => evolve H l) := by
  induction l with
  | zero => simp [evolve]
  | succ l ih => simp [evolve, ih, PMF.bind_bind]

theorem evolve_stable {n : ℕ} (G : Graph n) (k l : ℕ) (hk : G.card ≤ k) :
    evolve G (k + l) = evolve G k := by
  rw [evolve_add]
  conv_rhs => rw [← PMF.bind_pure (evolve G k)]
  apply PMF.ext
  intro H
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro J
  by_cases hJ : J ∈ (evolve G k).support
  · rw [evolve_absorbing J (evolve_terminal G k hk hJ)]
  · have hz : evolve G k J = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hJ
    simp [hz]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_TriangleDrift
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : β → α → ℝ) :
    pmfMean p (fun a => ∑ b, f b a) = ∑ b, pmfMean p (f b) := by
  simp only [pmfMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem step_mean {n : ℕ} (G : Graph n) (f : Graph n → ℝ)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) f =
      (∑ t ∈ triangles G, f (G \ t.powersetCard 2)) / ((triangles G).card : ℝ) := by
  rw [step, dite_eq_left hG, pmfMean_map, pmfMean_uniformOfFinset]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighbors
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem commonNeighbors_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (hw : w ∈ commonNeighbors G u v) : u ≠ w ∧ v ≠ w := by
  obtain ⟨hu,hv⟩ := (mem_commonNeighbors G u v w).mp hw
  constructor
  · intro h
    have hc := mem_completeGraph.mp (hG hu)
    simp [h] at hc
  · intro h
    have hc := mem_completeGraph.mp (hG hv)
    simp [h] at hc

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem prefixDensity_bounds (n : ℕ) (hn : 0 < n)
    (ht : 0 ≤ prefixTargetTime n) :
    prefixTargetDensity n ≤ prefixDensity n ∧
      prefixDensity n < prefixTargetDensity n + 6 / (n : ℝ)^2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  have hf : (prefixTime n : ℝ) ≤ prefixTargetTime n := Nat.floor_le ht
  have hg : prefixTargetTime n < (prefixTime n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx : prefixTargetTime n * 6 =
      (n : ℝ)^2 * (1 - 1 / (n : ℝ) - prefixTargetDensity n) := by
    unfold prefixTargetTime
    ring
  have hp : prefixDensity n * (n : ℝ)^2 =
      (1 - 1 / (n : ℝ)) * (n : ℝ)^2 - 6 * prefixTime n := by
    unfold prefixDensity
    field_simp
  constructor
  · apply (le_of_mul_le_mul_right (a := (n : ℝ)^2) _ hn2)
    nlinarith
  · apply (lt_of_mul_lt_mul_right (a := (n : ℝ)^2) _ (le_of_lt hn2))
    have he : (6 / (n : ℝ)^2) * (n : ℝ)^2 = 6 := div_mul_cancel₀ _ (ne_of_gt hn2)
    nlinarith

end SharpTerminalLeave

open InnerProductSpace
open scoped InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_OneAddLogRpow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Asymptotics

lemma one_add_log_rpow_isLittleO (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (fun x : ℝ => (1 + Real.log x) ^ C) =o[atTop] fun x => x ^ δ := by
  let C' := max C 1
  have hC' : 0 < C' := lt_max_iff.mpr (Or.inr zero_lt_one)
  have hq : 0 < δ / C' := div_pos hδ hC'
  have hc : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ (δ / C') := by
    apply (isLittleO_const_left_of_ne one_ne_zero).mpr
    apply (tendsto_rpow_atTop hq).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (Real.norm_of_nonneg (Real.rpow_nonneg hx _)).symm
  have hs := hc.add (isLittleO_log_rpow_atTop hq)
  calc
    (fun x : ℝ => (1 + Real.log x) ^ C) =O[atTop]
        fun x => (1 + Real.log x) ^ C' := by
      apply IsBigO.of_norm_eventuallyLE
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx
      simp only [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Real.log x) C)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    _ =o[atTop] fun x => (x ^ (δ / C')) ^ C' :=
      hs.rpow hC' ((eventually_ge_atTop (0 : ℝ)).mono fun x hx => Real.rpow_nonneg hx _)
    _ =ᶠ[atTop] fun x => x ^ δ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_mul hx,div_mul_cancel₀ _ hC'.ne']

 theorem prefixTemplateFactor_subpower (C : ℝ) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C ≤ b * (n : ℝ) ^ δ := by
  have h := ((one_add_log_rpow_isLittleO C hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound hb
  filter_upwards [h,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hb0 : 0 ≤ 1 + Real.log (n : ℝ) := by linarith
  simpa only [Function.comp_apply,Real.norm_of_nonneg (Real.rpow_nonneg hb0 C),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) δ),prefixTemplateFactor] using hn

lemma prefixTargetDensity_eq (n : ℕ) :
    prefixTargetDensity n = (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  unfold prefixTargetDensity prefixEpsilon
  congr 1
  norm_num

lemma prefixTargetDensity_tendsto : Tendsto prefixTargetDensity atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => prefixTargetDensity n) atTop (𝓝 0)
  simp_rw [prefixTargetDensity_eq]
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999 / 2000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixTargetTime_eventually_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ prefixTargetTime n := by
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [prefixTargetDensity_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    hi.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hp hi
  unfold prefixTargetTime
  exact mul_nonneg (by positivity) (by linarith)

theorem prefixDensity_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (-(999 / 2000 : ℝ)) ≤ prefixDensity n ∧
      prefixDensity n ≤ 2 * (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  filter_upwards [prefixTargetTime_eventually_nonneg,eventually_ge_atTop (6 : ℕ)] with n ht hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl,hu⟩ := prefixDensity_bounds n (by omega) ht
  rw [prefixTargetDensity_eq] at hl hu
  refine ⟨hl,?_⟩
  have h1 : 6 / (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2) hn0).mpr
    nlinarith
  have h2 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  linarith

lemma prefix_target_D_identity (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ) ^ (-(999 / 2000 : ℝ))) ^ 2 =
      (n : ℝ) ^ (1 / 1000 : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Real.rpow_natCast,← Real.rpow_mul hnR.le]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnR]
  congr 1
  norm_num

theorem prefixD_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (1 / 1000 : ℝ) ≤ prefixD n ∧
      prefixD n ≤ 4 * (n : ℝ) ^ (1 / 1000 : ℝ) := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hp hn
  have hn0 : 0 < n := by omega
  have hq : 0 ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpl : 0 ≤ prefixDensity n := hq.trans hp.1
  rw [← prefix_target_D_identity n hn0]
  unfold prefixD
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hp.1 2) (Nat.cast_nonneg n)
  · have hsq := pow_le_pow_left₀ hpl hp.2 2
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hsq)]

lemma prefixDensity_le_one (n : ℕ) : prefixDensity n ≤ 1 := by
  have h₁ : 0 ≤ 1 / (n : ℝ) := by positivity
  have h₂ : 0 ≤ 6 * (prefixTime n : ℝ) / (n : ℝ)^2 := by positivity
  unfold prefixDensity
  linarith

lemma prefix_scales_eventually_pos : ∀ᶠ n : ℕ in atTop,
    0 < prefixDensity n ∧ 1 ≤ prefixD n := by
  filter_upwards [prefixDensity_eventual_envelope,prefixD_eventual_envelope,
    eventually_ge_atTop (1 : ℕ)] with n hp hD hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨(Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < n) _).trans_le hp.1,
    (Real.one_le_rpow hnR (by norm_num : (0 : ℝ) ≤ 1/1000)).trans hD.1⟩

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_OrderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section RandomOrder
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem orderLaw_apply_cons (d : ℕ) (C : Finset K) (hC : C.Nonempty)
    (a : K) (as : List K) :
    orderLaw (d + 1) C (a :: as) =
      (PMF.uniformOfFinset C hC a) * orderLaw d (C.erase a) as := by
  simp only [orderLaw, dite_eq_left hC, PMF.bind_apply, tsum_fintype, pmf_map_cons_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem orderLaw_apply_nil (d : ℕ) (C : Finset K) (hC : C.Nonempty) :
    orderLaw (d + 1) C [] = 0 := by
  simp [orderLaw, hC, PMF.bind_apply]

theorem orderLaw_apply (d : ℕ) (C : Finset K) (hd : C.card ≤ d) (as : List K) :
    orderLaw d C as = if Enumerates C as then ((C.card.factorial : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  induction d generalizing C as with
  | zero =>
    have hC : C = ∅ := Finset.card_eq_zero.mp (by omega)
    subst C
    cases as with
    | nil => simp [orderLaw, Enumerates]
    | cons a as => simp [orderLaw, enumerates_cons]
  | succ d ih =>
    by_cases hC : C.Nonempty
    · cases as with
      | nil => simp [orderLaw_apply_nil d C hC, hC.ne_empty]
      | cons a as =>
        rw [orderLaw_apply_cons d C hC]
        by_cases ha : a ∈ C
        · have hcard : C.card = (C.erase a).card + 1 := (Finset.card_erase_add_one ha).symm
          have hde : (C.erase a).card ≤ d := by omega
          rw [ih (C.erase a) hde as, PMF.uniformOfFinset_apply_of_mem hC ha, enumerates_cons]
          simp only [ha, true_and]
          split_ifs with he
          · rw [hcard, Nat.factorial_succ, Nat.cast_mul]
            rw [ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness))]
          · simp
        · rw [PMF.uniformOfFinset_apply_of_notMem hC ha]
          simp only [zero_mul, enumerates_cons, ha, false_and, ↓reduceIte]
    · have hE : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      subst C
      cases as with
      | nil => simp [orderLaw, Enumerates]
      | cons a as => simp [orderLaw, enumerates_cons]

omit [Fintype K] in
theorem enumerates_mem {C : Finset K} {as : List K} (h : Enumerates C as) (a : K) :
    a ∈ as ↔ a ∈ C := by rw [← List.mem_toFinset, h.2]

omit [Fintype K] in
theorem enumerates_length {C : Finset K} {as : List K} (h : Enumerates C as) :
    as.length = C.card := by rw [← h.2, List.toFinset_card_of_nodup h.1]

theorem enumerates_map_perm {as : List K} (h : Enumerates Finset.univ as)
    (σ : Equiv.Perm K) : Enumerates Finset.univ (as.map σ) := by
  refine ⟨h.1.map σ.injective, ?_⟩
  apply Finset.eq_univ_of_forall
  intro x
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨σ.symm x, (enumerates_mem h _).mpr (Finset.mem_univ _), σ.apply_symm_apply x⟩

theorem relabel_injective {as : List K} (h : Enumerates Finset.univ as) :
    Function.Injective (fun σ : Equiv.Perm K => as.map σ) := by
  intro σ ρ he
  apply Equiv.ext
  intro a
  exact List.map_inj_left.mp he a ((enumerates_mem h _).mpr (Finset.mem_univ _))

theorem exists_relabel {as bs : List K} (ha : Enumerates Finset.univ as)
    (hb : Enumerates Finset.univ bs) : ∃ σ : Equiv.Perm K, as.map σ = bs := by
  let ea := ha.1.getEquivOfForallMemList as (fun x =>
    (enumerates_mem ha x).mpr (Finset.mem_univ x))
  let eb := hb.1.getEquivOfForallMemList bs (fun x =>
    (enumerates_mem hb x).mpr (Finset.mem_univ x))
  have hel : as.length = bs.length := (enumerates_length ha).trans (enumerates_length hb).symm
  let σ := ea.symm.trans ((finCongr hel).trans eb)
  refine ⟨σ, ?_⟩
  apply List.ext_get (by simpa using hel)
  intro i hi hj
  simp only [List.get_eq_getElem, List.getElem_map]
  change σ (as.get ⟨i, by simpa using hi⟩) = bs.get ⟨i, hj⟩
  change eb (finCongr hel (ea.symm (ea ⟨i, by simpa using hi⟩))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem uniform_relabel_eq_orderLaw (d : ℕ) (hd : Fintype.card K ≤ d)
    (as : List K) (ha : Enumerates Finset.univ as) :
    (PMF.uniformOfFintype (Equiv.Perm K)).map (fun σ : Equiv.Perm K => as.map σ) =
      orderLaw d Finset.univ := by
  classical
  apply PMF.ext
  intro bs
  rw [orderLaw_apply d Finset.univ (by simpa using hd) bs, PMF.map_apply, tsum_fintype]
  by_cases hb : Enumerates Finset.univ bs
  · obtain ⟨σ, rfl⟩ := exists_relabel ha hb
    have he : ∀ ρ : Equiv.Perm K, as.map σ = as.map ρ ↔ ρ = σ := by
      intro ρ
      exact ⟨fun h => (relabel_injective ha h).symm, fun h => h ▸ rfl⟩
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      PMF.uniformOfFintype_apply, Fintype.card_perm, hb, Finset.card_univ]
  · have he : ∀ ρ : Equiv.Perm K, bs ≠ as.map ρ := by
      intro ρ hρ
      apply hb
      rw [hρ]
      exact enumerates_map_perm ha ρ
    simp only [he, ↓reduceIte, Finset.sum_const_zero, hb]

end RandomOrder
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_TrueProbabilityMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
open scoped BigOperators

theorem trueProbability_map {A : Type*} [Fintype A] (p : PMF A) (b : A → Bool) :
    trueProbability (p.map b) = ∑ x, (p x).toReal * (if b x then 1 else 0) := by
  change trueProbability (p.bind (fun x => PMF.pure (b x))) = _
  simp only [trueProbability_bind, trueProbability_pure]

theorem boolean_coupling_bound {A : Type*} [Fintype A] (p : PMF A)
    (b₁ b₂ bad : A → Bool)
    (hagrees : ∀ x ∈ p.support, bad x = false → b₁ x = b₂ x) :
    |trueProbability (p.map b₁) - trueProbability (p.map b₂)| ≤
      trueProbability (p.map bad) := by
  rw [trueProbability_map, trueProbability_map, trueProbability_map,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p x = 0
  · simp only [hx, ENNReal.toReal_zero, zero_mul, sub_self, abs_zero, le_refl]
  · have hs : x ∈ p.support := hx
    have ha := hagrees x hs
    rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    cases h₁ : b₁ x <;> cases h₂ : b₂ x <;> cases hb : bad x <;>
      simp_all

namespace ExposureTree
variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

theorem independent_exposure_error (ν : K → PMF V) (P : ExposureTree K V Bool) :
    |trueProbability ((productPMF ν).map (fun ω => evaluate ω P)) -
      trueProbability (fresh ν P)| ≤
        trueProbability ((freshRecorded ν P ∅).map Prod.snd) := by
  have hh := boolean_coupling_bound (jointLaw ν P) Prod.fst (fun x => x.2.1)
    (fun x => x.2.2) (fun x hx hb => jointLaw_agrees ν P x hx hb)
  have hfst : (jointLaw ν P).map Prod.fst =
      (productPMF ν).map (fun ω => evaluate ω P) := jointLaw_fixed ν P
  have hsnd : (jointLaw ν P).map (fun x => x.2.1) = fresh ν P := by
    change (jointLaw ν P).map (Prod.fst ∘ Prod.snd) = _
    rw [← PMF.map_comp, jointLaw_fresh, freshRecorded_outcome]
  have hbad : (jointLaw ν P).map (fun x => x.2.2) =
      (freshRecorded ν P ∅).map Prod.snd := by
    change (jointLaw ν P).map (Prod.snd ∘ Prod.snd) = _
    rw [← PMF.map_comp, jointLaw_fresh]
  simpa only [hfst, hsnd, hbad] using hh

end ExposureTree

theorem pmf_map_congr_support {A B : Type*} (p : PMF A) (f g : A → B)
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  unfold PMF.map
  apply pmf_bind_congr_on_support
  intro x hx
  rw [Function.comp_apply, Function.comp_apply, h x hx]

theorem productPMF_coord {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ν : K → PMF V) (k : K) :
    (productPMF ν).map (fun ω => ω k) = ν k := by
  rw [productPMF_split ν k, PMF.map_bind]
  have hconst : ∀ v, (productPMF (Function.update ν k (PMF.pure v))).map (fun ω => ω k) =
      PMF.pure v := by
    intro v
    conv_rhs => rw [← PMF.map_const (p := productPMF (Function.update ν k (PMF.pure v)))]
    apply pmf_map_congr_support
    intro ω hω
    have hh := (productPMF_support _ _).mp hω k
    simpa only [Function.update_self, PMF.mem_support_pure_iff, Function.const_apply] using hh
  simp only [hconst, PMF.bind_pure]

theorem productPMF_pair {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ν : K → PMF V) (a b : K) (hab : a ≠ b) :
    (productPMF ν).map (fun ω => (ω a, ω b)) =
      (ν a).bind (fun v => (ν b).map (fun w => (v, w))) := by
  rw [productPMF_split ν a, PMF.map_bind]
  congr 1
  funext v
  have hm : (productPMF (Function.update ν a (PMF.pure v))).map (fun ω => (ω a, ω b)) =
      (productPMF (Function.update ν a (PMF.pure v))).map (fun ω => (v, ω b)) := by
    apply pmf_map_congr_support
    intro ω hω
    have hh := (productPMF_support _ _).mp hω a
    have ha : ω a = v := by simpa only [Function.update_self, PMF.mem_support_pure_iff] using hh
    rw [ha]
  rw [hm]
  change (productPMF (Function.update ν a (PMF.pure v))).map
    ((fun w => (v, w)) ∘ (fun ω => ω b)) = _
  rw [← PMF.map_comp, productPMF_coord, Function.update_of_ne (Ne.symm hab)]

theorem boolean_union_bound {A I : Type*} [Fintype A] [Fintype I]
    (p : PMF A) (bad : A → Bool) (events : I → A → Bool)
    (hcover : ∀ x ∈ p.support, bad x = true → ∃ i, events i x = true) :
    trueProbability (p.map bad) ≤ ∑ i, trueProbability (p.map (events i)) := by
  classical
  simp only [trueProbability_map]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  by_cases hx : p x = 0
  · simp [hx]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  by_cases hb : bad x = true
  · obtain ⟨i, hi⟩ := hcover x hx hb
    simp only [hb, ↓reduceIte]
    have him : (if events i x then (1 : ℝ) else 0) = 1 := by simp [hi]
    calc
      (1 : ℝ) = (if events i x then 1 else 0) := him.symm
      _ ≤ ∑ j, (if events j x then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun j => if events j x then (1 : ℝ) else 0)
          (fun j _ => by split <;> positivity) (Finset.mem_univ i)
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact Finset.sum_nonneg (fun i _ => by split <;> positivity)

theorem grid_table_pair_tie {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (a b : K) (hab : a ≠ b) :
    trueProbability ((productPMF (gridPriorities (τ := K) N)).map
      (fun ω => decide (ω a = ω b))) = 1 / (N : ℝ) := by
  have hpair := productPMF_pair (gridPriorities (τ := K) N) a b hab
  have hh := congrArg (fun q : PMF (Fin N × Fin N) =>
    q.map (fun z => decide (z.1 = z.2))) hpair
  simp only [PMF.map_comp, PMF.map_bind] at hh
  change (productPMF (gridPriorities (τ := K) N)).map (fun ω => decide (ω a = ω b)) =
    (gridPriorities N a).bind (fun v => (gridPriorities N b).map (fun w => decide (v = w))) at hh
  rw [hh, trueProbability_bind]
  simp only [trueProbability_map, gridPriorities, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_fin, Bool.decide_iff]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  field_simp

theorem grid_table_ties_bound {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] :
    trueProbability ((productPMF (gridPriorities (τ := K) N)).map
      (fun ω => decide (¬Function.Injective ω))) ≤
        (Fintype.card K : ℝ) ^ 2 / N := by
  classical
  let p := productPMF (gridPriorities (τ := K) N)
  let events : K × K → (K → Fin N) → Bool :=
    fun ab ω => decide (ab.1 ≠ ab.2 ∧ ω ab.1 = ω ab.2)
  have hc : ∀ ω ∈ p.support, decide (¬Function.Injective ω) = true →
      ∃ ab, events ab ω = true := by
    intro ω _ hω
    simp only [Bool.decide_iff, Function.Injective, not_forall] at hω
    obtain ⟨a, b, h⟩ := hω
    push Not at h
    exact ⟨(a, b), by simpa [events] using And.intro h.2 h.1⟩
  have hle := boolean_union_bound p (fun ω => decide (¬Function.Injective ω)) events hc
  calc
    _ ≤ ∑ ab, trueProbability (p.map (events ab)) := hle
    _ ≤ ∑ _ab : K × K, (1 / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro ab _
      by_cases hab : ab.1 = ab.2
      · have he : events ab = Function.const (K → Fin N) false := by
          funext ω
          simp [events, hab]
        rw [he, PMF.map_const, trueProbability_pure]
        simp only [Bool.false_eq_true, ↓reduceIte]
        positivity
      · have he : events ab = fun ω => decide (ω ab.1 = ω ab.2) := by
          funext ω
          simp [events, hab]
        rw [he]
        exact le_of_eq (grid_table_pair_tie N ab.1 ab.2 hab)
    _ = _ := by simp [Fintype.card_prod, pow_two, Nat.cast_mul, div_eq_mul_inv]

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_ClockOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section ClockOrders
variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

theorem iid_table_relabel (ν : PMF V) (σ : Equiv.Perm K) :
    (productPMF (fun _ : K => ν)).map (fun ω => ω ∘ σ.symm) =
      productPMF (fun _ : K => ν) := by
  ext ω
  rw [PMF.map_apply, tsum_fintype]
  have he : ∀ θ : K → V, ω = θ ∘ σ.symm ↔ θ = ω ∘ σ := by
    intro θ
    constructor
    · intro h
      funext k
      simpa only [Function.comp_apply, σ.symm_apply_apply] using (congrFun h (σ k)).symm
    · rintro rfl
      funext k
      simp
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    productPMF_apply, Function.comp_apply]
  exact Equiv.prod_comp σ (fun k => ν (ω k))

theorem clockOrder_enumerates (ω : K → ℕ) :
    Enumerates Finset.univ (clockOrder ω) := by
  have hp := List.mergeSort_perm Finset.univ.toList (fun a b => ω a ≤ ω b)
  refine ⟨hp.nodup_iff.mpr (Finset.nodup_toList _), ?_⟩
  apply Finset.eq_univ_of_forall
  intro k
  simp only [List.mem_toFinset]
  exact hp.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))

omit [DecidableEq K] in
theorem clockOrder_pairwise (ω : K → ℕ) :
    (clockOrder ω).Pairwise (fun a b => ω a ≤ ω b) := by
  let : Std.Total (fun a b : K => ω a ≤ ω b) := ⟨fun a b => le_total _ _⟩
  let : IsTrans K (fun a b : K => ω a ≤ ω b) := ⟨fun _ _ _ => le_trans⟩
  exact List.pairwise_mergeSort' _ _

theorem clockOrder_relabel (ω : K → ℕ) (hω : Function.Injective ω)
    (σ : Equiv.Perm K) : clockOrder (ω ∘ σ.symm) = (clockOrder ω).map σ := by
  let ρ := ω ∘ σ.symm
  let : Std.Antisymm (fun a b : K => ρ a ≤ ρ b) :=
    ⟨fun a b hab hba => σ.symm.injective (hω (le_antisymm hab hba))⟩
  have ha := clockOrder_enumerates ρ
  have hb := enumerates_map_perm (clockOrder_enumerates ω) σ
  have hp : (clockOrder ρ).Perm ((clockOrder ω).map σ) :=
    List.perm_of_nodup_nodup_toFinset_eq ha.1 hb.1 (ha.2.trans hb.2.symm)
  apply hp.eq_of_pairwise' (clockOrder_pairwise ρ)
  rw [List.pairwise_map]
  simpa only [ρ, Function.comp_apply, σ.symm_apply_apply] using clockOrder_pairwise ω

theorem iid_random_relabel (ν : PMF V) :
    (productPMF (fun _ : K => ν)).bind (fun ω =>
      (PMF.uniformOfFintype (Equiv.Perm K)).map (fun σ : Equiv.Perm K => ω ∘ σ.symm)) =
      productPMF (fun _ : K => ν) := by
  change (productPMF (fun _ : K => ν)).bind (fun ω =>
    (PMF.uniformOfFintype (Equiv.Perm K)).bind
      (fun σ => PMF.pure (ω ∘ σ.symm))) = _
  rw [PMF.bind_comm]
  change (PMF.uniformOfFintype (Equiv.Perm K)).bind (fun σ =>
    (productPMF (fun _ : K => ν)).map (fun ω => ω ∘ σ.symm)) = _
  simp only [iid_table_relabel, PMF.bind_const]

theorem clock_order_error (N : ℕ) [NeZero N] (F : List K → Bool) :
    |trueProbability ((productPMF (gridPriorities (τ := K) N)).map
        (fun ω => F (clockOrder (fun k => (ω k).val)))) -
      trueProbability ((orderLaw (Fintype.card K) Finset.univ).map F)| ≤
        (Fintype.card K : ℝ) ^ 2 / N := by
  classical
  let p := productPMF (gridPriorities (τ := K) N)
  let u := PMF.uniformOfFintype (Equiv.Perm K)
  let q := p.bind (fun ω => u.map (fun σ => (ω, σ)))
  let b₁ : (K → Fin N) × Equiv.Perm K → Bool :=
    fun z => F (clockOrder (fun k => (z.1 (z.2.symm k)).val))
  let b₂ : (K → Fin N) × Equiv.Perm K → Bool :=
    fun z => F ((clockOrder (fun k => (z.1 k).val)).map z.2)
  let bad : (K → Fin N) × Equiv.Perm K → Bool :=
    fun z => decide (¬Function.Injective z.1)
  have hagrees : ∀ z ∈ q.support, bad z = false → b₁ z = b₂ z := by
    intro z _ hz
    have hinj : Function.Injective z.1 := by simpa [bad] using hz
    have hinj' : Function.Injective (fun k => (z.1 k).val) :=
      Fin.val_injective.comp hinj
    exact congrArg F (clockOrder_relabel _ hinj' z.2)
  have h₁ : q.map b₁ = p.map (fun ω => F (clockOrder (fun k => (ω k).val))) := by
    have hh := congrArg (fun r : PMF (K → Fin N) =>
      r.map (fun ω => F (clockOrder (fun k => (ω k).val))))
      (iid_random_relabel (K := K) (PMF.uniformOfFintype (Fin N)))
    simp only [q, PMF.map_bind, PMF.map_comp, b₁, Function.comp_def]
    change (p.bind (fun ω => u.map (fun σ : Equiv.Perm K =>
      F (clockOrder (fun k => (ω (σ.symm k)).val))))) =
      p.map (fun ω => F (clockOrder (fun k => (ω k).val)))
    rw [show p = productPMF (fun _ : K => PMF.uniformOfFintype (Fin N)) from rfl]
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, u] using hh
  have h₂ : q.map b₂ = (orderLaw (Fintype.card K) Finset.univ).map F := by
    have hh : ∀ ω : K → Fin N,
        u.map (fun σ : Equiv.Perm K => (clockOrder (fun k => (ω k).val)).map σ) =
        orderLaw (Fintype.card K) Finset.univ := by
      intro ω
      exact uniform_relabel_eq_orderLaw _ le_rfl _ (clockOrder_enumerates _)
    simp only [q, PMF.map_bind, PMF.map_comp, b₂, Function.comp_def]
    have hr : ∀ ω : K → Fin N,
        u.map (fun σ : Equiv.Perm K => F ((clockOrder (fun k => (ω k).val)).map σ)) =
        (orderLaw (Fintype.card K) Finset.univ).map F := by
      intro ω
      simpa only [PMF.map_comp, Function.comp_def] using congrArg (fun r => r.map F) (hh ω)
    simp only [hr, PMF.bind_const]
  have hb : q.map bad = p.map (fun ω => decide (¬Function.Injective ω)) := by
    simp only [q, PMF.map_bind, PMF.map_comp, bad, Function.comp_def]
    change p.bind (fun ω => u.bind (fun _ => PMF.pure (decide (¬Function.Injective ω)))) = _
    simp only [PMF.bind_const]
    rfl
  have hle := boolean_coupling_bound q b₁ b₂ bad hagrees
  rw [h₁, h₂, hb] at hle
  exact hle.trans (grid_table_ties_bound N)

end ClockOrders
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_GeometricVolterraIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem geometric_volterra_identity (a c : ℝ) (k : ℕ) :
    c + a * (∑ j ∈ Finset.range k, c * (1 + a) ^ j) = c * (1 + a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [ih]

theorem discrete_volterra_bound (E : ℕ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (M : ℕ) (hE : ∀ k ≤ M, E k ≤ c + a * ∑ j ∈ Finset.range k, E j)
    (k : ℕ) (hk : k ≤ M) : E k ≤ c * (1 + a) ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    calc
      E k ≤ c + a * ∑ j ∈ Finset.range k, E j := hE k hk
      _ ≤ c + a * ∑ j ∈ Finset.range k, c * (1 + a) ^ j := by
        gcongr with j hj
        exact ih j (Finset.mem_range.mp hj) ((Nat.le_of_lt (Finset.mem_range.mp hj)).trans hk)
      _ = c * (1 + a) ^ k := geometric_volterra_identity a c k

theorem discrete_volterra_exp_bound (E : ℕ → ℝ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (N : ℕ) (hN : 0 < N)
    (hE : ∀ k ≤ N, E k ≤ C / N + (A / N) * ∑ j ∈ Finset.range k, E j)
    (k : ℕ) (hk : k ≤ N) : E k ≤ (C / N) * Real.exp A := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 ≤ A / N := div_nonneg hA hNr.le
  have hh := discrete_volterra_bound E (A / N) (C / N) hd N hE k hk
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hC hNr.le)
  calc
    (1 + A / N) ^ k ≤ (Real.exp (A / N)) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (A / N)
    _ = Real.exp ((k : ℝ) * (A / N)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp A := by
      apply Real.exp_le_exp.mpr
      have hkr : (k : ℝ) ≤ N := by exact_mod_cast hk
      calc
        (k : ℝ) * (A / N) ≤ (N : ℝ) * (A / N) := mul_le_mul_of_nonneg_right hkr hd
        _ = A := by field_simp

theorem integral_cell_error (f : ℝ → ℝ) {a b L : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc a b, |f x - f a| ≤ L * (x - a)) :
    |(∫ x in a..b, f x) - (b - a) * f a| ≤ L * (b - a) ^ 2 := by
  have heq : (∫ x in a..b, f x) - (b - a) * f a = ∫ x in a..b, f x - f a := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [heq, ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => f x - f a) (C := L * (b - a)) (by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact (hLip x ⟨hx.1.le, hx.2⟩).trans
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hL))
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem uniform_grid_quadrature (f : ℝ → ℝ) (hf : Continuous f)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |f x - f y| ≤ L * |x - y|)
    (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    |(∫ x in (0 : ℝ)..((k : ℝ) / N), f x) -
      (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f ((j : ℝ) / N)| ≤ L / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : (∫ x in (0 : ℝ)..((k : ℝ) / N), f x) =
      ∑ j ∈ Finset.range k, ∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), f x := by
    simpa only [Nat.cast_zero, zero_div] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (a := fun j => (j : ℝ) / N) (n := k) (fun _ _ => hf.intervalIntegrable _ _)).symm
  rw [hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range k,
        |(∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), f x) -
          (1 / N) * f ((j : ℝ) / N)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, L * (1 / (N : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast (show j + 1 ≤ N by omega)
      have hja : (j : ℝ) / N ≤ ((j + 1 : ℕ) : ℝ) / N := by
        gcongr; exact_mod_cast (Nat.le_succ j)
      have hdif : (((j + 1 : ℕ) : ℝ) / N) - (j : ℝ) / N = 1 / (N : ℝ) := by
        push_cast; ring
      have he := integral_cell_error f hja hf hL (by
        intro x hx
        have ha0 : (0 : ℝ) ≤ (j : ℝ) / N := by positivity
        have hb1 : (((j + 1 : ℕ) : ℝ) / N) ≤ 1 := by
          rw [div_le_one hNr]; simpa using hjN
        have hh := hLip x ⟨ha0.trans hx.1, hx.2.trans hb1⟩
          ((j : ℝ) / N) ⟨ha0, hja.trans hb1⟩
        simpa only [abs_of_nonneg (sub_nonneg.mpr hx.1)] using hh)
      simpa only [hdif] using he
    _ ≤ L / N := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hkr : (k : ℝ) ≤ N := by exact_mod_cast hk
      calc
        _ ≤ (N : ℝ) * (L * (1 / (N : ℝ)) ^ 2) := by gcongr
        _ = L / N := by field_simp

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_GridCavityError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
open Filter
open scoped BigOperators Topology

section GridApproximation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem messageIntegral_time_lipschitz (H : τ → Finset ι) (e : ι) (T : τ)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |messageIntegral H (cavityLimit H) e T t - messageIntegral H (cavityLimit H) e T s| ≤
      |t - s| := by
  let f : ℝ → ℝ := fun x => ∏ a ∈ (H T).erase e, cavityLimit H a (some T) x
  have hc : Continuous f := continuous_message_integrand H _ (continuous_cavityLimit H) e T
  have hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨Finset.prod_nonneg (fun a _ => (cavityLimit_mem_unit H a (some T) x).1),
      Finset.prod_le_one (fun a _ => (cavityLimit_mem_unit H a (some T) x).1)
        (fun a _ => (cavityLimit_mem_unit H a (some T) x).2)⟩
  simp only [messageIntegral, unitTime_of_mem hs, unitTime_of_mem ht]
  change |(∫ x in (0 : ℝ)..t, f x) - ∫ x in (0 : ℝ)..s, f x| ≤ _
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    ← Real.norm_eq_abs]
  simpa only [one_mul] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := (1 : ℝ))
      (f := f) (fun x _ => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf x).1] using (hf x).2))

theorem cavityLimit_time_lipschitz (H : τ → Finset ι) (e : ι) (p : Option τ)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |cavityLimit H e p t - cavityLimit H e p s| ≤ (Fintype.card τ : ℝ) * |t - s| := by
  rw [cavityLimit_product H e p t, cavityLimit_product H e p s]
  unfold cavityOperator
  have hm : ∀ T u, 1 - messageIntegral H (cavityLimit H) e T u ∈ Set.Icc (0 : ℝ) 1 := by
    intro T u
    have h := messageIntegral_mem_unit H _ (continuous_cavityLimit H) (cavityLimit_mem_unit H) e T u
    constructor <;> linarith [h.1, h.2]
  calc
    _ ≤ ∑ T ∈ messageCandidates H e p,
        |(1 - messageIntegral H (cavityLimit H) e T t) -
          (1 - messageIntegral H (cavityLimit H) e T s)| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun T _ => hm T t) (fun T _ => hm T s)
    _ ≤ ∑ _T ∈ messageCandidates H e p, |t - s| := by
      apply Finset.sum_le_sum
      intro T _
      rw [sub_sub_sub_cancel_left, abs_sub_comm]
      exact messageIntegral_time_lipschitz H e T hs ht
    _ ≤ (Fintype.card τ : ℝ) * |t - s| := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast Finset.card_le_univ (messageCandidates H e p)

theorem cavity_integrand_time_lipschitz (H : τ → Finset ι) (e : ι) (T : τ)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(∏ f ∈ (H T).erase e, cavityLimit H f (some T) t) -
      ∏ f ∈ (H T).erase e, cavityLimit H f (some T) s| ≤
        ((Fintype.card ι : ℝ) * Fintype.card τ) * |t - s| := by
  calc
    _ ≤ ∑ f ∈ (H T).erase e, |cavityLimit H f (some T) t - cavityLimit H f (some T) s| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun f _ => cavityLimit_mem_unit H f (some T) t)
        (fun f _ => cavityLimit_mem_unit H f (some T) s)
    _ ≤ ∑ _f ∈ (H T).erase e, (Fintype.card τ : ℝ) * |t - s| :=
      Finset.sum_le_sum (fun f _ => cavityLimit_time_lipschitz H f (some T) hs ht)
    _ ≤ ((Fintype.card ι : ℝ) * Fintype.card τ) * |t - s| := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      gcongr
      exact_mod_cast Finset.card_le_univ ((H T).erase e)

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem sum_fin_filter_lt_eq_range (N k : ℕ) (hk : k ≤ N) (f : ℕ → ℝ) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), f u.val) =
      ∑ j ∈ Finset.range k, f j := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ j ∈ Finset.range N, if j < k then f j else 0 :=
      Fin.sum_univ_eq_sum_range (fun j => if j < k then f j else 0) N
    _ =
        ∑ j ∈ Finset.range k, if j < k then f j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro j _ hj
      simp only [Finset.mem_range] at hj
      simp only [hj, ↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range.mp hj, ↓reduceIte]

omit [Fintype ι] in

theorem gridMessage_exact_range (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (parent : Option τ) :
    gridMessage H N N k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
          ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T)) := by
  rw [gridMessage_exact H N k hk]
  apply Finset.prod_congr rfl
  intro T _
  congr 2
  exact sum_fin_filter_lt_eq_range N k hk
    (fun j => ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T))

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem uniform_subaverage_mem_unit (N k : ℕ) (hN : 0 < N) (hk : k ≤ N)
    (f : ℕ → ℝ) (hf : ∀ j < k, f j ∈ Set.Icc (0 : ℝ) 1) :
    1 - (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f j ∈ Set.Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 ≤ (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f j :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun j hj => (hf j (Finset.mem_range.mp hj)).1))
  have hs1 : (∑ j ∈ Finset.range k, f j) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj => (hf j (Finset.mem_range.mp hj)).2)
      _ = (k : ℝ) := by simp
      _ ≤ (N : ℝ) := by exact_mod_cast hk
  have hs2 : (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f j ≤ 1 := by
    calc
      _ ≤ (1 / (N : ℝ)) * N := mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 1 := by field_simp
  constructor <;> linarith

omit [Fintype ι] in
theorem gridMessage_mem_unit (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (e : ι) (p : Option τ) : gridMessage H N d k e p ∈ Set.Icc (0 : ℝ) 1 :=
  gridAnswerProbability_mem_unit H N d k {e} p

theorem gridCavityError_nonneg (H : τ → Finset ι) (N : ℕ) [NeZero N] (k : ℕ) :
    0 ≤ gridCavityError H N k := norm_nonneg _

theorem gridCavityError_coord (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (e : ι) (p : Option τ) :
    |gridMessage H N N k e p - cavityLimit H e p ((k : ℝ) / N)| ≤ gridCavityError H N k := by
  exact norm_le_pi_norm (fun ep : ι × Option τ =>
    gridMessage H N N k ep.1 ep.2 - cavityLimit H ep.1 ep.2 ((k : ℝ) / N)) (e, p)

theorem grid_integrand_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (e : ι) (T : τ) :
    |(∏ f ∈ (H T).erase e, gridMessage H N N k f (some T)) -
      ∏ f ∈ (H T).erase e, cavityLimit H f (some T) ((k : ℝ) / N)| ≤
        (Fintype.card ι : ℝ) * gridCavityError H N k := by
  calc
    _ ≤ ∑ f ∈ (H T).erase e,
        |gridMessage H N N k f (some T) - cavityLimit H f (some T) ((k : ℝ) / N)| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun f _ => gridMessage_mem_unit H N N k f (some T))
        (fun f _ => cavityLimit_mem_unit H f (some T) ((k : ℝ) / N))
    _ ≤ ∑ _f ∈ (H T).erase e, gridCavityError H N k :=
      Finset.sum_le_sum (fun f _ => gridCavityError_coord H N k f (some T))
    _ ≤ (Fintype.card ι : ℝ) * gridCavityError H N k := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (gridCavityError_nonneg H N k)
      exact_mod_cast Finset.card_le_univ ((H T).erase e)

theorem grid_message_integral_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (T : τ) :
    |(1 / (N : ℝ)) * (∑ j ∈ Finset.range k,
        ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T)) -
      messageIntegral H (cavityLimit H) e T ((k : ℝ) / N)| ≤
        ((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
          ((Fintype.card ι : ℝ) * Fintype.card τ) / N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let f : ℝ → ℝ := fun s => ∏ a ∈ (H T).erase e, cavityLimit H a (some T) s
  have hc : Continuous f := continuous_message_integrand H _ (continuous_cavityLimit H) e T
  have hquad := uniform_grid_quadrature f hc (by positivity :
      0 ≤ (Fintype.card ι : ℝ) * Fintype.card τ)
    (fun x hx y hy => cavity_integrand_time_lipschitz H e T hy hx) N k hN hk
  have htime : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hNr).mpr (by exact_mod_cast hk)⟩
  have hi : messageIntegral H (cavityLimit H) e T ((k : ℝ) / N) =
      ∫ s in (0 : ℝ)..((k : ℝ) / N), f s := by
    simp only [messageIntegral, unitTime_of_mem htime, f]
  rw [hi]
  calc
    _ ≤ |(1 / (N : ℝ)) * (∑ j ∈ Finset.range k,
        ∏ a ∈ (H T).erase e, gridMessage H N N j a (some T)) -
          (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f ((j : ℝ) / N)| +
        |(1 / (N : ℝ)) * (∑ j ∈ Finset.range k, f ((j : ℝ) / N)) -
          ∫ s in (0 : ℝ)..((k : ℝ) / N), f s| := abs_sub_le _ _ _
    _ ≤ ((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
          ((Fintype.card ι : ℝ) * Fintype.card τ) / N := by
      apply add_le_add _ (by simpa only [abs_sub_comm] using hquad)
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ)),
        ← Finset.sum_sub_distrib]
      calc
        _ ≤ (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
            |(∏ a ∈ (H T).erase e, gridMessage H N N j a (some T)) - f ((j : ℝ) / N)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
            (Fintype.card ι : ℝ) * gridCavityError H N j := by
          gcongr with j hj
          exact grid_integrand_error H N j e T
        _ = _ := by rw [← Finset.mul_sum]; ring

theorem gridCavityError_volterra (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) :
    gridCavityError H N k ≤
      ((Fintype.card τ : ℝ) ^ 2 * Fintype.card ι) / N +
        ((Fintype.card τ : ℝ) * Fintype.card ι / N) *
          ∑ j ∈ Finset.range k, gridCavityError H N j := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 ≤ ((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
      ((Fintype.card ι : ℝ) * Fintype.card τ) / N := by
    have := Finset.sum_nonneg (s := Finset.range k) (fun j _ => gridCavityError_nonneg H N j)
    positivity
  unfold gridCavityError
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro ep
  rw [Real.norm_eq_abs, gridMessage_exact_range H N k hk,
    cavityLimit_product H ep.1 ep.2 ((k : ℝ) / N)]
  unfold cavityOperator
  let g : τ → ℝ := fun T => 1 - (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
    ∏ f ∈ (H T).erase ep.1, gridMessage H N N j f (some T)
  let q : τ → ℝ := fun T => 1 - messageIntegral H (cavityLimit H) ep.1 T ((k : ℝ) / N)
  have hg : ∀ T, g T ∈ Set.Icc (0 : ℝ) 1 := by
    intro T
    apply uniform_subaverage_mem_unit N k hN hk
    intro j _
    exact ⟨Finset.prod_nonneg (fun f _ => (gridMessage_mem_unit H N N j f (some T)).1),
      Finset.prod_le_one (fun f _ => (gridMessage_mem_unit H N N j f (some T)).1)
        (fun f _ => (gridMessage_mem_unit H N N j f (some T)).2)⟩
  have hq : ∀ T, q T ∈ Set.Icc (0 : ℝ) 1 := by
    intro T
    have h := messageIntegral_mem_unit H _ (continuous_cavityLimit H) (cavityLimit_mem_unit H)
      ep.1 T ((k : ℝ) / N)
    change 1 - _ ∈ _
    constructor <;> linarith [h.1, h.2]
  change |(∏ T ∈ messageCandidates H ep.1 ep.2, g T) -
    ∏ T ∈ messageCandidates H ep.1 ep.2, q T| ≤ _
  calc
    _ ≤ ∑ T ∈ messageCandidates H ep.1 ep.2, |g T - q T| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun T _ => hg T) (fun T _ => hq T)
    _ ≤ ∑ _T ∈ messageCandidates H ep.1 ep.2,
        (((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
          ((Fintype.card ι : ℝ) * Fintype.card τ) / N) := by
      apply Finset.sum_le_sum
      intro T _
      dsimp only [g, q]
      rw [sub_sub_sub_cancel_left, abs_sub_comm]
      exact grid_message_integral_error H N k hk ep.1 T
    _ ≤ (Fintype.card τ : ℝ) *
        (((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
          ((Fintype.card ι : ℝ) * Fintype.card τ) / N) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hb
      exact_mod_cast Finset.card_le_univ (messageCandidates H ep.1 ep.2)
    _ = _ := by unfold gridCavityError; ring

theorem gridCavityError_bound (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) :
    gridCavityError H N k ≤
      (((Fintype.card τ : ℝ) ^ 2 * Fintype.card ι) / N) *
        Real.exp ((Fintype.card τ : ℝ) * Fintype.card ι) := by
  exact discrete_volterra_exp_bound (gridCavityError H N)
    ((Fintype.card τ : ℝ) * Fintype.card ι)
    ((Fintype.card τ : ℝ) ^ 2 * Fintype.card ι) (by positivity) (by positivity)
    N (Nat.pos_of_ne_zero (NeZero.ne N)) (gridCavityError_volterra H N) k hk

theorem gridMessage_tendsto_terminal (H : τ → Finset ι) (e : ι) (p : Option τ) :
    Tendsto (fun n : ℕ => gridMessage H (n + 1) (n + 1) (n + 1) e p)
      atTop (𝓝 (cavityLimit H e p 1)) := by
  have hden : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  let C : ℝ := ((Fintype.card τ : ℝ) ^ 2 * Fintype.card ι) *
    Real.exp ((Fintype.card τ : ℝ) * Fintype.card ι)
  have hbound : ∀ n : ℕ,
      ‖gridMessage H (n + 1) (n + 1) (n + 1) e p - cavityLimit H e p 1‖ ≤
        C * (1 / ((n + 1 : ℕ) : ℝ)) := by
    intro n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hx := (gridCavityError_coord H (n + 1) (n + 1) e p).trans
      (gridCavityError_bound H (n + 1) (n + 1) le_rfl)
    simpa only [div_self hn, Real.norm_eq_abs, C, div_eq_mul_inv, one_mul,
      mul_assoc, mul_comm, mul_left_comm] using hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hbound
    (by simpa using tendsto_const_nhds.mul hden)

end GridApproximation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_GridUniformError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section GridRowBounds
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [DecidableEq ι] [DecidableEq τ] in
lemma gridUniformError_nonneg (H : τ → Finset ι) : 0 ≤ gridUniformError H := by
  unfold gridUniformError
  positivity

lemma gridMessage_uniform_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (p : Option τ) :
    |gridMessage H N N k e p - cavityLimit H e p ((k : ℝ)/N)| ≤
      gridUniformError H / N := by
  have h := (gridCavityError_coord H N k e p).trans (gridCavityError_bound H N k hk)
  simpa only [gridUniformError,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

lemma gridCandidateFailure_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (T : τ) :
    |gridCandidateFailure H N k e T -
        (1-messageIntegral H (cavityLimit H) e T ((k : ℝ)/N))| ≤
      ((Fintype.card ι : ℝ)*gridUniformError H +
        (Fintype.card ι : ℝ)*Fintype.card τ)/N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hE : 0 ≤ gridUniformError H / N := div_nonneg (gridUniformError_nonneg H) hN.le
  have hs : (∑ j ∈ Finset.range k, gridCavityError H N j) ≤ gridUniformError H := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, gridUniformError H / N := by
        apply Finset.sum_le_sum
        intro j hj
        have hh := gridCavityError_bound H N j ((Finset.mem_range.mp hj).le.trans hk)
        simpa only [gridUniformError,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
      _ = (k : ℝ) * (gridUniformError H / N) := by simp
      _ ≤ (N : ℝ) * (gridUniformError H / N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hE
      _ = gridUniformError H := by field_simp
  unfold gridCandidateFailure
  rw [sub_sub_sub_cancel_left,abs_sub_comm]
  calc
    _ ≤ ((Fintype.card ι : ℝ)/N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
        ((Fintype.card ι : ℝ)*Fintype.card τ)/N :=
      grid_message_integral_error H N k hk e T
    _ ≤ ((Fintype.card ι : ℝ)/N)*gridUniformError H +
        ((Fintype.card ι : ℝ)*Fintype.card τ)/N := by gcongr
    _ = _ := by ring

lemma gridAnswer_uniform_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (focus : Finset ι) (p : Option τ) :
    |gridAnswerProbability H N N k focus p -
        ∏ e ∈ focus, cavityLimit H e p ((k : ℝ)/N)| ≤
      (focus.card : ℝ)*gridUniformError H/N := by
  rw [gridAnswerProbability_factor]
  calc
    _ ≤ ∑ e ∈ focus, |gridMessage H N N k e p - cavityLimit H e p ((k : ℝ)/N)| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun e _ => gridMessage_mem_unit H N N k e p)
        (fun e _ => cavityLimit_mem_unit H e p _)
    _ ≤ ∑ _e ∈ focus, gridUniformError H/N :=
      Finset.sum_le_sum (fun e _ => gridMessage_uniform_error H N k hk e p)
    _ = _ := by simp; ring

end GridRowBounds
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LevelDeletes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

section TimeScan
variable {ι τ : Type*} [DecidableEq ι] [Fintype τ] [DecidableEq τ]

omit [DecidableEq τ] in

theorem timeScan_mem_iff (H : τ → Finset ι) (ω : τ → ℕ) (E : Finset ι) (k : ℕ) (e : ι) :
    e ∈ timeScan H ω E k ↔ e ∈ E ∧
      ∀ T, ω T < k → e ∈ H T → ¬ (H T).erase e ⊆ timeScan H ω E (ω T) := by
  induction k with
  | zero => simp [timeScan]
  | succ k ih =>
    simp only [timeScan, Finset.mem_sdiff, mem_levelDeletes, not_exists, not_and]
    constructor
    · intro he
      obtain ⟨heE, hePast⟩ := ih.mp he.1
      refine ⟨heE, fun T hTk heT hsub => ?_⟩
      by_cases hlt : ω T < k
      · exact hePast T hlt heT hsub
      · have ht : ω T = k := by omega
        apply he.2 T ht
        · intro f hf
          by_cases hfe : f = e
          · simpa [hfe] using he.1
          · exact (ht ▸ hsub) (Finset.mem_erase.mpr ⟨hfe, hf⟩)
        · exact heT
    · rintro ⟨heE, hePast⟩
      have hek : e ∈ timeScan H ω E k := ih.mpr ⟨heE, fun T hT => hePast T (by omega)⟩
      refine ⟨hek, fun T ht hsub heT => ?_⟩
      apply hePast T (by omega) heT
      rw [ht]
      exact (Finset.erase_subset e (H T)).trans hsub

theorem evaluate_gridQueryDepth_succ (H : τ → Finset ι) (N d k : ℕ)
    (ω : τ → Fin N) (focus : Finset ι) (parent : Option τ) :
    ExposureTree.evaluate ω (gridQueryDepth H N (d + 1) k focus parent) = true ↔
      ∀ e ∈ focus, ∀ T, e ∈ H T → some T ≠ parent → (ω T).val < k →
        ExposureTree.evaluate ω
          (gridQueryDepth H N d (ω T).val ((H T).erase e) (some T)) = false := by
  simp only [gridQueryDepth, ExposureTree.evaluate_bind, ExposureTree.evaluate_exposeLabeled,
    ExposureTree.evaluate_checkNone, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, List.mem_mergeSort, Finset.mem_toList]
  constructor
  · intro h e he T heT hp ht
    have hm : (e, T) ∈ gridCandidates H focus parent := by
      simp [gridCandidates, he, heT, hp]
    have hh := h (e, T) hm
    simpa only [ht, ↓reduceIte] using hh
  · intro h a ha
    have ha' : a.1 ∈ focus ∧ a.1 ∈ H a.2 ∧ some a.2 ≠ parent := by
      simpa [gridCandidates] using ha
    by_cases ht : (ω a.2).val < k
    · simpa only [ht, ↓reduceIte] using h a.1 ha'.1 a.2 ha'.2.1 ha'.2.2 ht
    · simp [ht, ExposureTree.evaluate]

theorem evaluate_gridQueryDepth_iff (H : τ → Finset ι) (N d k : ℕ)
    (ω : τ → Fin N) (E focus : Finset ι) (parent : Option τ)
    (hk : k ≤ d) (hfocus : focus ⊆ E) (hH : ∀ T, H T ⊆ E)
    (hparent : ∀ T, some T = parent → k ≤ (ω T).val) :
    ExposureTree.evaluate ω (gridQueryDepth H N d k focus parent) = true ↔
      focus ⊆ timeScan H (fun T => (ω T).val) E k := by
  induction d generalizing k focus parent with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp only [gridQueryDepth, ExposureTree.evaluate_bind, ExposureTree.evaluate,
      timeScan, true_iff]
    exact hfocus
  | succ d ih =>
    rw [evaluate_gridQueryDepth_succ]
    constructor
    · intro h e he
      apply (timeScan_mem_iff H (fun T => (ω T).val) E k e).mpr
      refine ⟨hfocus he, fun T hTk heT hsub => ?_⟩
      have hp : some T ≠ parent := by
        intro hh
        have := hparent T hh
        omega
      have hf := h e he T heT hp hTk
      have ht := (ih (ω T).val ((H T).erase e) (some T) (by omega)
        ((Finset.erase_subset e (H T)).trans (hH T)) (fun S hS => by cases Option.some.inj hS; rfl)).mpr hsub
      rw [ht] at hf
      contradiction
    · intro hs e he T heT _ hTk
      apply Bool.eq_false_iff.mpr
      intro ht
      have hsub := (ih (ω T).val ((H T).erase e) (some T) (by omega)
        ((Finset.erase_subset e (H T)).trans (hH T)) (fun S hS => by cases Option.some.inj hS; rfl)).mp ht
      exact ((timeScan_mem_iff H (fun T => (ω T).val) E k e).mp (hs he)).2 T hTk heT hsub

end TimeScan
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_HyperScanAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section GenericClockScan
variable {ι τ : Type*} [DecidableEq ι] [Fintype τ] [DecidableEq τ]

omit [Fintype τ] [DecidableEq τ] in
theorem hyperScan_append (H : τ → Finset ι) (G : Finset ι) (as bs : List τ) :
    hyperScan H G (as ++ bs) = hyperScan H (hyperScan H G as) bs :=
  List.foldl_append

omit [DecidableEq ι] [Fintype τ] [DecidableEq τ] in
theorem sorted_filter_lt_succ (ω : τ → ℕ) (as : List τ)
    (hs : as.Pairwise (fun a b => ω a ≤ ω b)) (k : ℕ) :
    as.filter (fun a => ω a < k + 1) =
      as.filter (fun a => ω a < k) ++ as.filter (fun a => ω a = k) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨hle, hs⟩ := List.pairwise_cons.mp hs
    by_cases hlt : ω a < k
    · have hne : ω a ≠ k := by omega
      have hlt' : ω a < k + 1 := by omega
      simp only [List.filter_cons, decide_eq_true hlt, decide_eq_true hlt',
        decide_eq_false hne, Bool.false_eq_true, ↓reduceIte, List.cons_append, ih hs]
    · by_cases heq : ω a = k
      · have hn : as.filter (fun b => ω b < k) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          have h := hle b hb
          simpa only [Bool.decide_iff] using (show ¬ω b < k by omega)
        simp only [List.filter_cons, decide_eq_false hlt, decide_eq_true heq,
          show decide (ω a < k + 1) = true by simp [heq], Bool.false_eq_true, ↓reduceIte,
          ih hs, hn, List.nil_append]
      · have hn : ¬ω a < k + 1 := by omega
        simp only [List.filter_cons, decide_eq_false hlt, decide_eq_false heq,
          decide_eq_false hn, Bool.false_eq_true, ↓reduceIte, ih hs]

omit [DecidableEq ι] in
theorem clockOrder_level_singleton (ω : τ → ℕ) (hω : Function.Injective ω) (T : τ) :
    (clockOrder ω).filter (fun a => ω a = ω T) = [T] := by
  have hd := (clockOrder_enumerates ω).1.filter (fun a => decide (ω a = ω T))
  apply List.perm_singleton.mp
  apply List.perm_of_nodup_nodup_toFinset_eq hd (by simp)
  ext a
  simp only [List.mem_toFinset, List.mem_filter, Bool.decide_iff,
    List.mem_singleton, hω.eq_iff]
  constructor
  · exact And.right
  · intro ha
    exact ⟨(enumerates_mem (clockOrder_enumerates ω) a).mpr (Finset.mem_univ _), ha⟩

omit [DecidableEq τ] in
theorem levelDeletes_one (H : τ → Finset ι) (ω : τ → ℕ)
    (hω : Function.Injective ω) (G : Finset ι) (T : τ) :
    levelDeletes H ω G (ω T) = if H T ⊆ G then H T else ∅ := by
  ext e
  simp only [mem_levelDeletes, hω.eq_iff, exists_eq_left]
  by_cases hs : H T ⊆ G <;> simp [hs]

theorem timeScan_eq_hyperScan_prefix (H : τ → Finset ι) (ω : τ → ℕ)
    (hω : Function.Injective ω) (E : Finset ι) (k : ℕ) :
    timeScan H ω E k =
      hyperScan H E ((clockOrder ω).filter (fun T => ω T < k)) := by
  induction k with
  | zero => simp [timeScan, hyperScan]
  | succ k ih =>
    rw [timeScan, ih, sorted_filter_lt_succ ω _ (clockOrder_pairwise ω) k]
    by_cases he : ∃ T, ω T = k
    · obtain ⟨T, rfl⟩ := he
      rw [clockOrder_level_singleton ω hω T, levelDeletes_one H ω hω]
      rw [hyperScan_append, hyperScan_singleton]
      unfold hyperScanAction
      split_ifs <;> simp
    · have hn : (clockOrder ω).filter (fun T => ω T = k) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro T _
        simpa only [Bool.decide_iff] using (show ¬ω T = k from fun h => he ⟨T,h⟩)
      have hd : ∀ G : Finset ι, levelDeletes H ω G k = ∅ := by
        intro G
        ext e
        simp only [mem_levelDeletes, Finset.notMem_empty, iff_false, not_exists,
          not_and]
        intro T hT
        exact False.elim (he ⟨T, hT⟩)
      rw [hn, List.append_nil, hd, Finset.sdiff_empty]

theorem timeScan_eq_hyperScan (H : τ → Finset ι) (ω : τ → ℕ)
    (hω : Function.Injective ω) (E : Finset ι) (N : ℕ) (hN : ∀ T, ω T < N) :
    timeScan H ω E N = hyperScan H E (clockOrder ω) := by
  rw [timeScan_eq_hyperScan_prefix H ω hω E N]
  congr 1
  apply List.filter_eq_self.mpr
  intro T _
  exact decide_eq_true (hN T)

end GenericClockScan
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Finish
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

theorem pmf_bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem evolve_eq_finish {n : ℕ} (G : Graph n) (k : ℕ) (hk : G.card ≤ k) :
    evolve G k = finish G := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact evolve_stable G G.card l le_rfl

theorem finish_absorbing {n : ℕ} (G : Graph n) (hG : triangles G = ∅) :
    finish G = PMF.pure G := evolve_absorbing G hG G.card

theorem finish_harmonic {n : ℕ} (G : Graph n) :
    finish G = (step G).bind finish := by
  have heq : evolve G (1 + G.card) = (step G).bind (fun H => evolve H G.card) := by
    rw [evolve_add]
    simp [evolve]
  rw [evolve_eq_finish G _ (by omega)] at heq
  rw [heq]
  apply pmf_bind_congr_support
  intro H hH
  exact evolve_eq_finish H G.card (Finset.card_le_card (step_support_subset hH))

theorem scanAction_subset {n : ℕ} (G : Graph n) (t : Finset (Fin n)) :
    scanAction G t ⊆ G := by
  unfold scanAction
  split_ifs
  · exact Finset.sdiff_subset
  · exact Finset.Subset.rfl

theorem triangle_not_mem_delete {n : ℕ} (G : Graph n) (t : Finset (Fin n)) :
    t ∉ triangles (G \ t.powersetCard 2) := by
  intro ht
  have hc : (t.powersetCard 2).card = 3 := by
    simp [(mem_triangles.mp ht).1]
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (t.powersetCard 2).card)
  exact (Finset.mem_sdiff.mp ((mem_triangles.mp ht).2 he)).2 he

theorem triangles_scanAction_subset {n : ℕ} (G : Graph n) (C : Finset (Finset (Fin n)))
    (hC : triangles G ⊆ C) (t : Finset (Fin n)) :
    triangles (scanAction G t) ⊆ C.erase t := by
  intro u hu
  apply Finset.mem_erase.mpr
  refine ⟨?_, hC (triangles_mono (scanAction_subset G t) hu)⟩
  intro heq
  subst u
  by_cases ht : t ∈ triangles G
  · exact triangle_not_mem_delete G t (by simpa [scanAction, ht] using hu)
  · exact ht (triangles_mono (scanAction_subset G t) hu)

theorem finish_mean_uniform_candidates {n : ℕ} (G : Graph n)
    (C : Finset (Finset (Fin n))) (hC : C.Nonempty) (hall : triangles G ⊆ C)
    (f : Graph n → ℝ) :
    pmfMean (PMF.uniformOfFinset C hC) (fun t => pmfMean (finish (scanAction G t)) f) =
      pmfMean (finish G) f := by
  classical
  by_cases hG : (triangles G).Nonempty
  · let w : ℝ := pmfMean (finish G) f
    have hw : ∑ t ∈ triangles G, pmfMean (finish (G \ t.powersetCard 2)) f =
        ((triangles G).card : ℝ) * w := by
      have hh := congrArg (fun p => pmfMean p f) (finish_harmonic G)
      rw [pmfMean_bind, step_mean G _ hG] at hh
      have hpos : (0 : ℝ) < (triangles G).card := by exact_mod_cast hG.card_pos
      have he := (div_eq_iff hpos.ne').mp hh.symm
      simpa only [mul_comm] using he
    rw [pmfMean_uniformOfFinset]
    have hsplit : C = (triangles G) ∪ (C \ triangles G) := by
      exact (Finset.union_sdiff_of_subset hall).symm
    have hsum : ∑ t ∈ C, pmfMean (finish (scanAction G t)) f = (C.card : ℝ) * w := by
      have hdisj : Disjoint (triangles G) (C \ triangles G) := by
        exact Finset.disjoint_left.mpr fun t ht hdiff => (Finset.mem_sdiff.mp hdiff).2 ht
      conv_lhs => rw [hsplit]
      rw [Finset.sum_union hdisj]
      have hfirst : ∑ t ∈ triangles G, pmfMean (finish (scanAction G t)) f =
          ((triangles G).card : ℝ) * w := by
        calc
          _ = ∑ t ∈ triangles G, pmfMean (finish (G \ t.powersetCard 2)) f := by
            apply Finset.sum_congr rfl
            intro t ht
            simp [scanAction, ht]
          _ = _ := hw
      rw [hfirst]
      have hsecond : ∑ t ∈ C \ triangles G, pmfMean (finish (scanAction G t)) f =
          ((C \ triangles G).card : ℝ) * w := by
        calc
          _ = ∑ _t ∈ C \ triangles G, w := Finset.sum_congr rfl fun t ht => by
            simp [scanAction, (Finset.mem_sdiff.mp ht).2, w]
          _ = _ := by simp
      rw [hsecond, Finset.card_sdiff_of_subset hall, Nat.cast_sub (Finset.card_le_card hall)]
      ring
    rw [hsum]
    exact mul_div_cancel_left₀ w (by exact_mod_cast hC.card_pos.ne')
  · have ht : triangles G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    have heq : (fun t => pmfMean (finish (scanAction G t)) f) =
        (fun _ => pmfMean (finish G) f) := by
      funext t
      simp [scanAction, ht]
    rw [heq, pmfMean_const]

theorem pmf_ext_mean {α : Type*} [Fintype α] (p q : PMF α)
    (h : ∀ f : α → ℝ, pmfMean p f = pmfMean q f) : p = q := by
  classical
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp
  simpa [pmfMean] using h (fun b => if b = a then 1 else 0)

theorem scan_mean_eq_finish {n : ℕ} (k : ℕ) (G : Graph n)
    (C : Finset (Finset (Fin n))) (hk : C.card ≤ k) (hall : triangles G ⊆ C)
    (f : Graph n → ℝ) : pmfMean (scanLaw k G C) f = pmfMean (finish G) f := by
  classical
  induction k generalizing G C with
  | zero =>
    have hC : C = ∅ := Finset.card_eq_zero.mp (by omega)
    have ht : triangles G = ∅ := Finset.subset_empty.mp (hC ▸ hall)
    simp [scanLaw, finish_absorbing G ht]
  | succ k ih =>
    by_cases hC : C.Nonempty
    · rw [scanLaw, dite_eq_left hC, pmfMean_bind]
      calc
        _ = pmfMean (PMF.uniformOfFinset C hC)
            (fun t => pmfMean (finish (scanAction G t)) f) := by
          apply pmfMean_congr
          intro t ht
          have htC : t ∈ C := by simpa using ht
          exact ih (scanAction G t) (C.erase t)
            (by rw [Finset.card_erase_of_mem htC]; omega)
            (triangles_scanAction_subset G C hall t)
        _ = _ := finish_mean_uniform_candidates G C hC hall f
    · have hCe : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      have ht : triangles G = ∅ := Finset.subset_empty.mp (hCe ▸ hall)
      simp [scanLaw, hC, finish_absorbing G ht]

theorem scanLaw_eq_finish {n : ℕ} (k : ℕ) (G : Graph n)
    (C : Finset (Finset (Fin n))) (hk : C.card ≤ k) (hall : triangles G ⊆ C) :
    scanLaw k G C = finish G :=
  pmf_ext_mean _ _ (scan_mean_eq_finish k G C hk hall)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_ScanList
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

theorem orderLaw_scanList_eq_scanLaw {n : ℕ} (d : ℕ) (G : Graph n)
    (C : Finset (Finset (Fin n))) :
    (orderLaw d C).map (scanList G) = scanLaw d G C := by
  induction d generalizing G C with
  | zero => simp [orderLaw, scanLaw, scanList, PMF.pure_map]
  | succ d ih =>
    by_cases hC : C.Nonempty
    · simp only [orderLaw, scanLaw, dite_eq_left hC, PMF.map_bind, PMF.map_comp]
      congr 1
      funext t
      exact ih (scanAction G t) (C.erase t)
    · simp [orderLaw, scanLaw, hC, scanList, PMF.pure_map]

theorem uniform_order_scan_eq_finish {n : ℕ} (G : Graph n)
    (C : Finset (Finset (Fin n))) (hall : triangles G ⊆ C) :
    (orderLaw C.card C).map (scanList G) = finish G := by
  rw [orderLaw_scanList_eq_scanLaw, scanLaw_eq_finish _ _ _ le_rfl hall]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ActiveHypergraph
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem activeHypergraph_map {n : ℕ} (G : Graph n) (T : ↥(triangles G)) :
    (activeHypergraph G T).map (edgeEmbedding G) = T.val.powersetCard 2 := by
  ext e
  simp only [Finset.mem_map, activeHypergraph_mem, edgeEmbedding, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · intro he
    exact ⟨⟨e, (mem_triangles.mp T.property).2 he⟩, he, rfl⟩

@[simp] theorem activeHypergraph_card {n : ℕ} (G : Graph n) (T : ↥(triangles G)) :
    (activeHypergraph G T).card = 3 := by
  have hh := congrArg Finset.card (activeHypergraph_map G T)
  simpa only [Finset.card_map, triangle_edge_card T.property] using hh

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleHypergraph
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

theorem triangleHypergraph_subset {n : ℕ} (G : Graph n) (T : Finset (Fin n)) :
    triangleHypergraph G T ⊆ G := by
  unfold triangleHypergraph
  split_ifs with hT
  · exact (mem_triangles.mp hT).2
  · exact Finset.empty_subset _

theorem triangle_hyperScanAction_eq {n : ℕ} (G E : Graph n) (hE : E ⊆ G)
    (T : Finset (Fin n)) :
    hyperScanAction (triangleHypergraph G) E T = scanAction E T := by
  by_cases hT : T ∈ triangles G
  · have hc := (mem_triangles.mp hT).1
    simp only [hyperScanAction, triangleHypergraph, hT, ite_true, scanAction,
      mem_triangles, hc, true_and]
  · have hn : T ∉ triangles E := fun ht => hT (triangles_mono hE ht)
    simp [hyperScanAction, triangleHypergraph, hT, scanAction, hn]

theorem triangle_hyperScan_eq {n : ℕ} (G E : Graph n) (hE : E ⊆ G)
    (as : List (Finset (Fin n))) :
    hyperScan (triangleHypergraph G) E as = scanList E as := by
  induction as generalizing E with
  | nil => rfl
  | cons T as ih =>
    change hyperScan (triangleHypergraph G)
      (hyperScanAction (triangleHypergraph G) E T) as = scanList (scanAction E T) as
    rw [triangle_hyperScanAction_eq G E hE T]
    exact ih _ ((scanAction_subset E T).trans hE)

theorem graph_gridQuery_eq_scan {n : ℕ} (G focus : Graph n) (hf : focus ⊆ G)
    (N : ℕ) (ω : Finset (Fin n) → Fin N) (hω : Function.Injective ω) :
    ExposureTree.evaluate ω (gridQueryDepth (triangleHypergraph G) N N N focus none) =
      decide (focus ⊆ scanList G (clockOrder (fun T => (ω T).val))) := by
  have hs := evaluate_gridQueryDepth_iff (triangleHypergraph G) N N N ω G focus none
    le_rfl hf (triangleHypergraph_subset G) (fun T h => by cases h)
  rw [timeScan_eq_hyperScan (triangleHypergraph G) (fun T => (ω T).val)
    (Fin.val_injective.comp hω) G N (fun T => (ω T).isLt),
    triangle_hyperScan_eq G G (Finset.Subset.refl G)] at hs
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.decide_iff] using hs

theorem graph_grid_exposure_error {n : ℕ} (G focus : Graph n) (hf : focus ⊆ G)
    (N : ℕ) [NeZero N] :
    |focusSurvival G focus - gridAnswerProbability (triangleHypergraph G) N N N focus none| ≤
      2 * (Fintype.card (Finset (Fin n)) : ℝ) ^ 2 / N +
      trueProbability ((ExposureTree.freshRecorded (gridPriorities N)
        (gridQueryDepth (triangleHypergraph G) N N N focus none) ∅).map Prod.snd) := by
  classical
  let H := triangleHypergraph G
  let p := productPMF (gridPriorities (τ := Finset (Fin n)) N)
  let b₁ := fun ω => ExposureTree.evaluate ω (gridQueryDepth H N N N focus none)
  let b₂ := fun ω : Finset (Fin n) → Fin N =>
    decide (focus ⊆ scanList G (clockOrder (fun T => (ω T).val)))
  let C : ℝ := (Fintype.card (Finset (Fin n)) : ℝ) ^ 2 / N
  have h₁ : |trueProbability (p.map b₁) - trueProbability (p.map b₂)| ≤ C := by
    apply (boolean_coupling_bound p b₁ b₂
      (fun ω => decide (¬Function.Injective ω)) ?_).trans (grid_table_ties_bound N)
    intro ω _ hω
    have hinj : Function.Injective ω := Classical.not_not.mp (of_decide_eq_false hω)
    exact graph_gridQuery_eq_scan G focus hf N ω hinj
  have h₂ : |trueProbability (p.map b₂) - focusSurvival G focus| ≤ C := by
    have hh := clock_order_error N (fun as : List (Finset (Fin n)) =>
      decide (focus ⊆ scanList G as))
    have hl := uniform_order_scan_eq_finish G Finset.univ
      (Finset.subset_univ (triangles G))
    have hh' := congrArg (fun r : PMF (Graph n) =>
      r.map (fun E => decide (focus ⊆ E))) hl
    simp only [PMF.map_comp, Function.comp_def, Finset.card_univ] at hh'
    rw [hh'] at hh
    exact hh
  have h₃ := ExposureTree.independent_exposure_error (gridPriorities N)
    (gridQueryDepth H N N N focus none)
  have h₁' : |trueProbability (p.map b₂) - trueProbability (p.map b₁)| ≤ C := by
    rw [abs_sub_comm]
    exact h₁
  have h₂' : |focusSurvival G focus - trueProbability (p.map b₂)| ≤ C := by
    rw [abs_sub_comm]
    exact h₂
  have hsum : |focusSurvival G focus - gridAnswerProbability H N N N focus none| ≤
      C + (C + trueProbability ((ExposureTree.freshRecorded (gridPriorities N)
        (gridQueryDepth H N N N focus none) ∅).map Prod.snd)) := (abs_sub_le (focusSurvival G focus) (trueProbability (p.map b₂))
    (gridAnswerProbability H N N N focus none)).trans
    (add_le_add h₂'
      ((abs_sub_le (trueProbability (p.map b₂)) (trueProbability (p.map b₁))
        (gridAnswerProbability H N N N focus none)).trans
        (add_le_add h₁' h₃)))
  convert hsum using 1 <;> first | rfl | ring

end SharpTerminalLeave

open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_GridCollision
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

section Continuum
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem gridAnswer_tendsto_terminal (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) :
    Tendsto (fun n : ℕ => gridAnswerProbability H (n + 1) (n + 1) (n + 1) focus parent)
      atTop (𝓝 (∏ e ∈ focus, cavityLimit H e parent 1)) := by
  have hh := tendsto_finsetProd focus (fun e _ => gridMessage_tendsto_terminal H e parent)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact gridAnswerProbability_factor H (n + 1) (n + 1) (n + 1) focus parent

omit [Fintype ι] in
theorem gridCollision_mem_unit (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) (n : ℕ) : gridCollision H focus parent n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨trueProbability_nonneg _, trueProbability_le_one _⟩

end Continuum

theorem graph_cavity_error {n : ℕ} (G focus : Graph n) (hf : focus ⊆ G) :
    |focusSurvival G focus - ∏ e ∈ focus, cavityLimit (triangleHypergraph G) e none 1| ≤
      collisionCost (triangleHypergraph G) focus none := by
  let H := triangleHypergraph G
  let C : ℝ := 2 * (Fintype.card (Finset (Fin n)) : ℝ) ^ 2
  let a : ℕ → ℝ := fun k =>
    |focusSurvival G focus - gridAnswerProbability H (k + 1) (k + 1) (k + 1) focus none| -
      C / (k + 1 : ℕ)
  have hden : Tendsto (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0))
  have ha : Tendsto a atTop
      (𝓝 |focusSurvival G focus - ∏ e ∈ focus, cavityLimit H e none 1|) := by
    have hh := (((tendsto_const_nhds (x := focusSurvival G focus)).sub (gridAnswer_tendsto_terminal H focus none)).abs).sub
      ((tendsto_const_nhds (x := C)).mul hden)
    simpa only [a, mul_zero, sub_zero, div_eq_mul_inv, one_mul] using hh
  have he : ∀ᶠ k in atTop, a k ≤ gridCollision H focus none k := by
    apply Filter.Eventually.of_forall
    intro k
    have hh := graph_grid_exposure_error G focus hf (k + 1)
    dsimp only [a, C, H, gridCollision]
    linarith
  have hupp : atTop.IsBoundedUnder (· ≤ ·) (gridCollision H focus none) :=
    Filter.isBoundedUnder_of ⟨1, fun k => (gridCollision_mem_unit H focus none k).2⟩
  have hh := liminf_le_liminf he ha.isBoundedUnder_ge hupp.isCobounded_flip
  rw [ha.liminf_eq] at hh
  exact hh

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MessageCandidatesReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section Reindex
variable {ι τ ι' τ' : Type*} [Fintype ι] [Fintype τ] [Fintype ι'] [Fintype τ']
  [DecidableEq ι] [DecidableEq τ] [DecidableEq ι'] [DecidableEq τ']
  (H : τ → Finset ι) (H' : τ' → Finset ι') (f : ι' ↪ ι) (g : τ' ↪ τ)
  (hH : ∀ T, H (g T) = (H' T).map f)
  (hlocal : ∀ e : ι', ∀ T, f e ∈ H T → ∃ T', g T' = T)
include hH hlocal

omit [Fintype ι] [Fintype ι'] in

theorem messageCandidates_reindex (e : ι') (p : Option τ') :
    messageCandidates H (f e) (p.map g) = (messageCandidates H' e p).map g := by
  ext T
  simp only [messageCandidates, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · rintro ⟨he, hp⟩
    obtain ⟨T', rfl⟩ := hlocal e T he
    refine ⟨T', ⟨?_, ?_⟩, rfl⟩
    · rw [hH] at he
      exact Finset.mem_map.mp he |>.elim (fun _ hz => f.injective hz.2 ▸ hz.1)
    · intro hh
      exact hp (by rw [← hh]; rfl)
  · rintro ⟨T', ⟨he, hp⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hH]
      exact Finset.mem_map.mpr ⟨e, he, rfl⟩
    · intro hh
      apply hp
      cases p with
      | none => contradiction
      | some S =>
        simp only [Option.map_some, Option.some.injEq] at hh ⊢
        exact g.injective hh

omit [Fintype ι] [Fintype ι'] in

theorem cavityDepth_reindex (k : ℕ) (e : ι') (p : Option τ') (t : ℝ) :
    cavityDepth H k (f e) (p.map g) t = cavityDepth H' k e p t := by
  induction k generalizing e p t with
  | zero => rfl
  | succ k ih =>
    simp only [cavityDepth, cavityOperator, messageCandidates_reindex H H' f g hH hlocal,
      Finset.prod_map]
    apply Finset.prod_congr rfl
    intro T _
    congr 1
    unfold messageIntegral
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hH, ← Finset.map_erase, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro e' _
    exact ih e' (some T) s

theorem cavityLimit_reindex (e : ι') (p : Option τ') (t : ℝ) :
    cavityLimit H (f e) (p.map g) t = cavityLimit H' e p t := by
  apply tendsto_nhds_unique (tendsto_cavityDepth H (f e) (p.map g) t)
  convert tendsto_cavityDepth H' e p t using 1
  all_goals try with_reducible_and_instances rfl
  funext k
  exact cavityDepth_reindex H H' f g hH hlocal k e p t

end Reindex
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleHypergraphReindex
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem triangleHypergraph_reindex {n : ℕ} (G : Graph n) (T : ↥(triangles G)) :
    triangleHypergraph G (triangleEmbedding G T) =
      (activeHypergraph G T).map (edgeEmbedding G) := by
  rw [activeHypergraph_map]
  simp [triangleHypergraph, triangleEmbedding, T.property]

theorem triangleHypergraph_active {n : ℕ} (G : Graph n) (e : ↥G)
    (T : Finset (Fin n)) (he : edgeEmbedding G e ∈ triangleHypergraph G T) :
    ∃ T' : ↥(triangles G), triangleEmbedding G T' = T := by
  by_cases hT : T ∈ triangles G
  · exact ⟨⟨T, hT⟩, rfl⟩
  · simp [triangleHypergraph, hT] at he

theorem active_cavity_eq {n : ℕ} (G : Graph n) (e : ↥G)
    (p : Option ↥(triangles G)) (t : ℝ) :
    cavityLimit (triangleHypergraph G) e.val (p.map Subtype.val) t =
      cavityLimit (activeHypergraph G) e p t :=
  cavityLimit_reindex _ _ (edgeEmbedding G) (triangleEmbedding G)
    (triangleHypergraph_reindex G) (triangleHypergraph_active G) e p t

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PowersetCardTriple
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma powersetCard_triple {α : Type*} [DecidableEq α] {u v w : α}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u,v,w} : Finset α).powersetCard 2 = {{u,v},{u,w},{v,w}} := by
  have h2 : ({v,w}:Finset α).powersetCard 2 = {{v,w}} := by
    rw [← Finset.card_pair hvw]
    exact Finset.powersetCard_self _
  rw [Finset.powersetCard_succ_insert (by simp [huv,huw]) 1, h2]
  simp only [Finset.powersetCard_one, Finset.map_insert, Finset.map_singleton, Finset.image_insert,
    Finset.image_singleton, Function.Embedding.coeFn_mk]
  ext s
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma triangle_closure_iff {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    {u,v,w} ∈ triangles G ↔ {u,v} ∈ G := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  obtain ⟨huwG,hvwG⟩ := (mem_commonNeighbors G u v w).mp hw
  rw [mem_triangles, powersetCard_triple huv huw hvw]
  simp [huv,huw,hvw,Finset.insert_subset_iff,Finset.singleton_subset_iff,huwG,hvwG]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TripleFactorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open Filter MeasureTheory
open scoped BigOperators Topology BoundedContinuousFunction
open scoped BigOperators

namespace SharpTerminalLeave

theorem triple_factor_bounds {a b c ε : ℝ}
    (hε : ε ≤ 1 / 2) (ha : a ∈ Set.Icc 0 ε)
    (hb : b ∈ Set.Icc 0 ε) (hc : c ∈ Set.Icc 0 ε) :
    1 / 8 ≤ (1 - a) * (1 - b) * (1 - c) ∧
    (1 - a) * (1 - b) * (1 - c) ≤ 1 ∧
    |1 - (1 - a) * (1 - b) * (1 - c)| ≤ 3 * ε := by
  have ha' : 1 / 2 ≤ 1 - a := by linarith [ha.2]
  have hb' : 1 / 2 ≤ 1 - b := by linarith [hb.2]
  have hc' : 1 / 2 ≤ 1 - c := by linarith [hc.2]
  have hab : 1 / 4 ≤ (1 - a) * (1 - b) := by
    nlinarith [mul_le_mul ha' hb' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith : 0 ≤ 1 - a)]
  have hl : 1 / 8 ≤ (1 - a) * (1 - b) * (1 - c) := by
    nlinarith [mul_le_mul hab hc' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : 0 ≤ (1 - a) * (1 - b))]
  have hab1 : (1 - a) * (1 - b) ≤ 1 := by
    nlinarith [mul_le_mul (by linarith [ha.1] : 1 - a ≤ 1)
      (by linarith [hb.1] : 1 - b ≤ 1) (by linarith : 0 ≤ 1 - b) zero_le_one]
  have hu : (1 - a) * (1 - b) * (1 - c) ≤ 1 := by
    nlinarith [mul_le_mul hab1 (by linarith [hc.1] : 1 - c ≤ 1)
      (by linarith : 0 ≤ 1 - c) zero_le_one]
  refine ⟨hl, hu, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hu)]
  have hx : 0 ≤ a * b * (1 - c) :=
    mul_nonneg (mul_nonneg ha.1 hb.1) (by linarith)
  have hy := mul_nonneg ha.1 hc.1
  have hz := mul_nonneg hb.1 hc.1
  nlinarith [ha.2, hb.2, hc.2]

theorem cavity_summand_taylor {x y a b c δ ε : ℝ}
    (hδ : δ ≤ 1 / 2) (hx : |x| ≤ δ) (hy : |y| ≤ δ)
    (hε : ε ≤ 1 / 2) (ha : a ∈ Set.Icc 0 ε)
    (hb : b ∈ Set.Icc 0 ε) (hc : c ∈ Set.Icc 0 ε) :
    |Real.exp (x + y) / ((1 - a) * (1 - b) * (1 - c)) - 1 - x - y| ≤
      32 * δ ^ 2 + 48 * ε := by
  let P := (1 - a) * (1 - b) * (1 - c)
  have hp := triple_factor_bounds hε ha hb hc
  have hp0 : 0 < P := by dsimp [P]; linarith [hp.1]
  have hδ0 : 0 ≤ δ := (abs_nonneg x).trans hx
  have hε0 : 0 ≤ ε := ha.1.trans ha.2
  have hxy : |x + y| ≤ 2 * δ := (abs_add_le x y).trans (by linarith)
  have he : |Real.exp (x + y) - 1 - (x + y)| ≤ 4 * δ ^ 2 := by
    apply (Real.abs_exp_sub_one_sub_id_le (hxy.trans (by linarith))).trans
    have hh := sq_le_sq.mpr (show |x + y| ≤ |2 * δ| by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hδ0]
      exact hxy)
    nlinarith
  have hlin : |1 + x + y| ≤ 2 := by
    calc
      _ = |1 + (x + y)| := by congr 1; ring
      _ ≤ |(1 : ℝ)| + |x + y| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hPinv : P⁻¹ ≤ 8 := by
    rw [← one_div]
    apply (div_le_iff₀ hp0).mpr
    dsimp [P]
    linarith [hp.1]
  have hPinv0 : 0 ≤ P⁻¹ := inv_nonneg.mpr hp0.le
  calc
    _ = |(Real.exp (x + y) - 1 - (x + y)) * P⁻¹ +
        (1 + x + y) * ((1 - P) * P⁻¹)| := by
      congr 1
      change Real.exp (x + y) / P - 1 - x - y = _
      field_simp [hp0.ne']
      ring
    _ ≤ |Real.exp (x + y) - 1 - (x + y)| * P⁻¹ +
        |1 + x + y| * (|1 - P| * P⁻¹) := by
      simpa only [abs_mul, abs_of_nonneg hPinv0] using abs_add_le
        ((Real.exp (x + y) - 1 - (x + y)) * P⁻¹)
        ((1 + x + y) * ((1 - P) * P⁻¹))
    _ ≤ (4 * δ ^ 2) * 8 + 2 * ((3 * ε) * 8) := by
      apply add_le_add
      · exact mul_le_mul he hPinv hPinv0 (by positivity)
      · exact mul_le_mul hlin
          (mul_le_mul hp.2.2 hPinv hPinv0 (by positivity))
          (mul_nonneg (abs_nonneg _) hPinv0) (by norm_num)
    _ = _ := by ring

theorem cavity_row_error {τ : Type*} (S : Finset τ) (R L : τ → ℝ)
    {D η B : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (hdegree : |(S.card : ℝ) / D - 1| ≤ η)
    (hrow : (S.card : ℝ) / D ≤ 2)
    (hterm : ∀ T ∈ S, |R T - 1 - L T| ≤ B) :
    |1 - (1 / D) * (∑ T ∈ S, R T) + (1 / D) * (∑ T ∈ S, L T)| ≤
      η + 2 * B := by
  have heq : 1 - (1 / D) * (∑ T ∈ S, R T) + (1 / D) * (∑ T ∈ S, L T) =
      -(S.card / D - 1) - (1 / D) * (∑ T ∈ S, (R T - 1 - L T)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  rw [heq]
  calc
    _ ≤ |(S.card : ℝ) / D - 1| + |(1 / D) * (∑ T ∈ S, (R T - 1 - L T))| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (-(S.card / D - 1))
        (-((1 / D) * (∑ T ∈ S, (R T - 1 - L T))))
    _ ≤ η + (1 / D) * (S.card * B) := by
      apply add_le_add hdegree
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hD)]
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hD.le)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hterm)
    _ ≤ η + 2 * B := by
      calc
        _ = η + (S.card / D) * B := by ring
        _ ≤ _ := by linarith [mul_le_mul_of_nonneg_right hrow hB]

end SharpTerminalLeave

open Filter MeasureTheory
open scoped Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_VariationConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open scoped BigOperators Topology BoundedContinuousFunction
open scoped BigOperators
open Filter MeasureTheory
open scoped Topology

namespace SharpTerminalLeave

section Forcing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem variation_of_constants (A : E →L[ℝ] E) (z f : ℝ → E)
    {s : ℝ} (hs : 0 ≤ s) (hz : ContinuousOn z (Set.Icc 0 s))
    (hf : ContinuousOn f (Set.Icc 0 s))
    (hd : ∀ t ∈ Set.Ioo 0 s, HasDerivAt z (-A (z t) + f t) t) :
    z s = NormedSpace.exp ((-s) • A) (z 0) +
      ∫ t in (0 : ℝ)..s, NormedSpace.exp ((t - s) • A) (f t) := by
  let w : ℝ → E := fun t => NormedSpace.exp ((t - s) • A) (z t)
  let g : ℝ → E := fun t => NormedSpace.exp ((t - s) • A) (f t)
  have he : Continuous (fun t : ℝ => NormedSpace.exp ((t - s) • A)) :=
    (differentiable_exp_smul_const ℝ A).continuous.comp
      (continuous_id.sub continuous_const)
  have hw : ContinuousOn w (Set.Icc 0 s) := he.continuousOn.clm_apply hz
  have hg : ContinuousOn g (Set.Icc 0 s) := he.continuousOn.clm_apply hf
  have hw' : ∀ t ∈ Set.Ioo 0 s, HasDerivAt w (g t) t := by
    intro t ht
    have he' := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t - s)).scomp t
      ((hasDerivAt_id t).sub_const s)
    have hh := he'.clm_apply (hd t ht)
    simp only [Function.comp_apply, id_eq, one_smul] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp [g, map_add, map_neg]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hw hw'
    (hg.intervalIntegrable_of_Icc hs)
  simp only [w, sub_self, zero_smul, NormedSpace.exp_zero,
    one_apply_eq_self, zero_sub] at hi
  change z s = _ + ∫ t in (0 : ℝ)..s, g t
  rw [hi]
  abel

theorem forcing_norm_bound (A : E →L[ℝ] E) (z f : ℝ → E)
    {s K d : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hz : ContinuousOn z (Set.Icc 0 s)) (hf : ContinuousOn f (Set.Icc 0 s))
    (hz0 : z 0 = 0)
    (hd : ∀ t ∈ Set.Ioo 0 s, HasDerivAt z (-A (z t) + f t) t)
    (hsem : ∀ u ∈ Set.Icc 0 s, ‖NormedSpace.exp ((-u) • A)‖ ≤ K)
    (hforce : ∀ t ∈ Set.Icc 0 s, ‖f t‖ ≤ d) : ‖z s‖ ≤ K * d * s := by
  rw [variation_of_constants A z f hs hz hf hd, hz0, map_zero, zero_add]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := s) (C := K * d)
    (f := fun t => NormedSpace.exp ((t - s) • A) (f t)) (by
      intro t ht
      have ht0 : t ∈ Set.Ioc 0 s := by simpa only [Set.uIoc_of_le hs] using ht
      have ht' : t ∈ Set.Icc 0 s := ⟨ht0.1.le, ht0.2⟩
      have hu : s - t ∈ Set.Icc 0 s := ⟨sub_nonneg.mpr ht'.2, by linarith [ht'.1]⟩
      have he : ‖NormedSpace.exp ((t - s) • A)‖ ≤ K := by
        simpa only [neg_sub] using hsem (s - t) hu
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul he (hforce t ht') (norm_nonneg _) hK))
  simpa only [sub_zero, abs_of_nonneg hs] using hh

end Forcing

theorem strict_bootstrap {Q : ℝ → ℝ} {S δ : ℝ} (hδ : 0 < δ)
    (hQ : ContinuousOn Q (Set.Icc 0 S)) (hzero : Q 0 ≤ δ)
    (himprove : ∀ t ∈ Set.Icc 0 S,
      (∀ u ∈ Set.Icc 0 t, Q u ≤ δ) → Q t ≤ δ / 2) :
    ∀ t ∈ Set.Icc 0 S, Q t ≤ δ / 2 := by
  let B : Set ℝ := {t | Q t ≤ δ}
  have hclosed : IsClosed (B ∩ Set.Icc 0 S) := by
    simpa only [B, Set.preimage, Set.mem_Iic, Set.inter_comm] using
      hQ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hB : Set.Icc 0 S ⊆ B := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
    intro t ht hp
    have ht' : t ∈ Set.Icc 0 S := ⟨ht.1, ht.2.le⟩
    have him : Q t < δ := lt_of_le_of_lt (himprove t ht' hp) (by linarith)
    have hc := hQ t ht'
    have hI : Set.Icc 0 S ∈ 𝓝[>] t := by
      have hh : Set.Icc t S ∈ 𝓝[≥] t := Icc_mem_nhdsGE ht.2
      exact (nhdsWithin_mono t Set.Ioi_subset_Ici_self)
        (Filter.mem_of_superset hh (Set.Icc_subset_Icc_left ht.1))
    have hc' : ContinuousWithinAt Q (Set.Ioi t) t := hc.mono_of_mem_nhdsWithin hI
    have hsmall : ∀ᶠ u in 𝓝[>] t, Q u < δ := hc' (Iio_mem_nhds him)
    exact hsmall.mono (fun _ hu => hu.le)
  intro t ht
  apply himprove t ht
  intro u hu
  exact hB ⟨hu.1, hu.2.trans ht.2⟩

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_CavityGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open scoped BigOperators Topology BoundedContinuousFunction
open scoped BigOperators
open Filter MeasureTheory
open scoped Topology

namespace SharpTerminalLeave
section CavityStability
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem cavityMessage_derivative_bound (H : τ → Finset ι) {D δ s : ℝ}
    (hD : 0 < D) (hδ : δ ≤ 1 / 2) (hcard : ∀ T, (H T).card = 3)
    (hz : ∀ f, |cavityLog H D f s| ≤ δ)
    (hI : ∀ f T, f ∈ H T → cavityMessage H D f T s ≤ 1 / 2)
    (ht : cavityTime D s ∈ Set.Ioo (0 : ℝ) 1) (e : ι) (T : τ) (he : e ∈ H T) :
    deriv (cavityMessage H D e T) s ≤ 12 / D := by
  rw [(cavityMessage_hasDerivAt H D e T ht).deriv]
  obtain ⟨f, g, hfg, hset, hf, hg⟩ := triangle_children (hcard T) he
  have heq := cavity_triangle_message_summand H D e T hfg hset hf hg ht.2
  have hprod : 1 / 4 ≤ (1 - cavityMessage H D f T s) * (1 - cavityMessage H D g T s) := by
    have h1 : 1 / 2 ≤ 1 - cavityMessage H D f T s := by linarith [hI f T hf]
    have h2 : 1 / 2 ≤ 1 - cavityMessage H D g T s := by linarith [hI g T hg]
    nlinarith [mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith)]
  have he2 : Real.exp (cavityLog H D f s + cavityLog H D g s) ≤ 3 := by
    apply (Real.exp_le_exp.mpr (show cavityLog H D f s + cavityLog H D g s ≤ 1 from
      by linarith [(abs_le.mp (hz f)).2, (abs_le.mp (hz g)).2])).trans
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hb : Real.exp (2 * s) *
      (∏ u ∈ (H T).erase e, cavityLimit H u (some T) (cavityTime D s)) ≤ 12 := by
    rw [heq]
    apply (div_le_iff₀ (by linarith : 0 <
      (1 - cavityMessage H D f T s) * (1 - cavityMessage H D g T s))).mpr
    linarith
  calc
    _ = (Real.exp (2 * s) *
      ∏ u ∈ (H T).erase e, cavityLimit H u (some T) (cavityTime D s)) / D := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hb hD.le

theorem cavityMessage_bound (H : τ → Finset ι) {D δ s : ℝ}
    (hD : 0 < D) (hs : 0 ≤ s) (hδ : δ ≤ 1 / 2) (hcard : ∀ T, (H T).card = 3)
    (hz : ∀ u ∈ Set.Icc 0 s, ∀ f, |cavityLog H D f u| ≤ δ)
    (hI : ∀ u ∈ Set.Icc 0 s, ∀ f T, f ∈ H T → cavityMessage H D f T u ≤ 1 / 2)
    (ht : cavityTime D s < 1) (e : ι) (T : τ) (he : e ∈ H T) :
    cavityMessage H D e T s ≤ 12 * s / D := by
  have hi : ∀ u ∈ Set.Ioo 0 s, cavityTime D u ∈ Set.Ioo (0 : ℝ) 1 := by
    intro u hu
    exact ⟨cavityTime_pos hD hu.1, (cavityTime_mono hD hu.2.le).trans_lt ht⟩
  have hh := (convex_Icc (0 : ℝ) s).image_sub_le_mul_sub_of_deriv_le
    (continuous_cavityMessage H D e T).continuousOn
    (fun u hu => ((cavityMessage_hasDerivAt H D e T (hi u (by simpa using hu))).differentiableAt).differentiableWithinAt)
    (C := 12 / D) (fun u hu => by
      have hu' : u ∈ Set.Ioo 0 s := by simpa only [interior_Icc] using hu
      exact cavityMessage_derivative_bound H hD hδ hcard
        (hz u ⟨hu'.1.le, hu'.2.le⟩) (hI u ⟨hu'.1.le, hu'.2.le⟩) (hi u hu') e T he)
    0 ⟨le_rfl, hs⟩ s ⟨hs, le_rfl⟩ hs
  simpa only [cavityMessage_zero, sub_zero, div_mul_eq_mul_div] using hh

theorem cavityResidual_bound (H : τ → Finset ι) {D δ ε η s : ℝ}
    (hD : 0 < D) (hδ : δ ≤ 1 / 2) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (hη : 0 ≤ η)
    (hcard : ∀ T, (H T).card = 3)
    (hdeg : ∀ e, |((messageCandidates H e none).card : ℝ) / D - 1| ≤ η)
    (hrow : ∀ e, ((messageCandidates H e none).card : ℝ) / D ≤ 2)
    (hz : ∀ e, |cavityLog H D e s| ≤ δ)
    (hI : ∀ e T, e ∈ H T → cavityMessage H D e T s ≤ ε)
    (ht : cavityTime D s < 1) :
    ‖cavityResidual H D s‖ ≤ η + 64 * δ ^ 2 + 96 * ε := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro e
  let R : τ → ℝ := fun T => Real.exp (2 * s) *
    ((∏ f ∈ (H T).erase e, cavityLimit H f (some T) (cavityTime D s)) /
      (1 - cavityMessage H D e T s))
  let L : τ → ℝ := fun T => ∑ f ∈ (H T).erase e, cavityLog H D f s
  have hres : cavityResidual H D s e =
      1 - (1 / D) * (∑ T ∈ messageCandidates H e none, R T) +
        (1 / D) * (∑ T ∈ messageCandidates H e none, L T) := by
    simp only [cavityResidual, Pi.add_apply, cavityVelocity, cavityGenerator_apply, R, L,
      ← Finset.mul_sum]
    ring
  rw [Real.norm_eq_abs, hres]
  have hb := cavity_row_error (messageCandidates H e none) R L hD
    (show 0 ≤ 32 * δ ^ 2 + 48 * ε by positivity) (hdeg e) (hrow e) (by
      intro T hT
      have he : e ∈ H T := (Finset.mem_filter.mp hT).2.1
      obtain ⟨f, g, hfg, hset, hf, hg⟩ := triangle_children (hcard T) he
      have hR := cavity_triangle_summand H D e T hfg hset hf hg ht
      have hL : L T = cavityLog H D f s + cavityLog H D g s := by
        simp only [L, hset, Finset.sum_pair hfg]
      dsimp only [R]
      rw [hR, hL]
      convert cavity_summand_taylor hδ (hz f) (hz g) hε'
        ⟨cavityMessage_nonneg H D e T s, hI e T he⟩
        ⟨cavityMessage_nonneg H D f T s, hI f T hf⟩
        ⟨cavityMessage_nonneg H D g T s, hI g T hg⟩ using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring)
  nlinarith

theorem continuousOn_cavityVelocity (H : τ → Finset ι) {D S : ℝ}
    (hD : 0 < D) (hS : cavityTime D S < 1) :
    ContinuousOn (cavityVelocity H D) (Set.Icc 0 S) := by
  apply continuousOn_pi.mpr
  intro e
  unfold cavityVelocity
  apply continuousOn_const.sub
  apply ContinuousOn.mul
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const D).continuousOn
  · apply continuousOn_finsetSum
    intro T _
    apply ContinuousOn.div
    · apply continuousOn_finsetProd
      intro f _
      exact ((continuous_cavityLimit H f (some T)).comp (continuous_cavityTime D)).continuousOn
    · exact continuousOn_const.sub (continuous_cavityMessage H D e T).continuousOn
    · intro s hs
      exact (cavityLimit_factor_pos H e T ((cavityTime_mono hD hs.2).trans_lt hS)).ne'

theorem continuousOn_cavityLog_vector (H : τ → Finset ι) {D S : ℝ}
    (hD : 0 < D) (hS : cavityTime D S < 1) :
    ContinuousOn (fun s e => cavityLog H D e s) (Set.Icc 0 S) :=
  continuousOn_pi.mpr (continuousOn_cavityLog H hD hS)

theorem continuousOn_cavityResidual (H : τ → Finset ι) {D S : ℝ}
    (hD : 0 < D) (hS : cavityTime D S < 1) :
    ContinuousOn (cavityResidual H D) (Set.Icc 0 S) :=
  (continuousOn_cavityVelocity H hD hS).add
    ((cavityGenerator H D).continuous.comp_continuousOn (continuousOn_cavityLog_vector H hD hS))

theorem cavityLog_provisional_bound (H : τ → Finset ι) {D δ η K s : ℝ}
    (hD : 0 < D) (hs : 0 ≤ s) (hδ : δ ≤ 1 / 2) (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hcard : ∀ T, (H T).card = 3)
    (hdeg : ∀ e, |((messageCandidates H e none).card : ℝ) / D - 1| ≤ η)
    (hrow : ∀ e, ((messageCandidates H e none).card : ℝ) / D ≤ 2)
    (hz : ∀ u ∈ Set.Icc 0 s, ∀ e, |cavityLog H D e u| ≤ δ)
    (hI : ∀ u ∈ Set.Icc 0 s, ∀ e T, e ∈ H T → cavityMessage H D e T u ≤ 1 / 2)
    (ht : cavityTime D s < 1) (hsmall : 12 * s / D ≤ 1 / 2)
    (hsem : ∀ u ∈ Set.Icc 0 s, ‖NormedSpace.exp ((-u) • cavityGenerator H D)‖ ≤ K) :
    ‖fun e => cavityLog H D e s‖ ≤ K * (η + 64 * δ ^ 2 + 1152 * s / D) * s := by
  have hi : ∀ u ∈ Set.Icc 0 s, ∀ e T, e ∈ H T →
      cavityMessage H D e T u ≤ 12 * s / D := by
    intro u hu e T he
    apply (cavityMessage_bound H hD hu.1 hδ hcard
      (fun v hv => hz v ⟨hv.1, hv.2.trans hu.2⟩)
      (fun v hv => hI v ⟨hv.1, hv.2.trans hu.2⟩)
      ((cavityTime_mono hD hu.2).trans_lt ht) e T he).trans
    exact div_le_div_of_nonneg_right (by linarith [hu.2]) hD.le
  have hh := forcing_norm_bound (cavityGenerator H D)
    (fun u e => cavityLog H D e u) (cavityResidual H D) hs hK
    (continuousOn_cavityLog_vector H hD ht) (continuousOn_cavityResidual H hD ht)
    (funext (cavityLog_zero H D)) (by
      intro u hu
      apply hasDerivAt_pi.mpr
      intro e
      convert cavityLog_hasDerivAt H D e
        ⟨cavityTime_pos hD hu.1, (cavityTime_mono hD hu.2.le).trans_lt ht⟩ using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [cavityResidual, cavityVelocity]
      ring) hsem (d := η + 64 * δ ^ 2 + 1152 * s / D) (by
      intro u hu
      have hr := cavityResidual_bound H hD hδ (by positivity : 0 ≤ 12 * s / D)
        hsmall hη hcard hdeg hrow (hz u hu) (hi u hu)
        ((cavityTime_mono hD hu.2).trans_lt ht)
      convert hr using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  exact hh

theorem continuous_cavityIncidentMessages (H : τ → Finset ι) (D : ℝ) :
    Continuous (cavityIncidentMessages H D) := by
  apply continuous_pi
  intro p
  by_cases hp : p.1 ∈ H p.2
  · simpa only [cavityIncidentMessages, ite_eq_left hp] using continuous_cavityMessage H D p.1 p.2
  · simpa only [cavityIncidentMessages, ite_eq_right hp] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

theorem cavityIncidentMessages_norm_iff (H : τ → Finset ι) (D s b : ℝ) (hb : 0 ≤ b) :
    ‖cavityIncidentMessages H D s‖ ≤ b ↔
      ∀ e T, e ∈ H T → cavityMessage H D e T s ≤ b := by
  rw [pi_norm_le_iff_of_nonneg hb]
  constructor
  · intro hh e T he
    simpa only [cavityIncidentMessages, ite_eq_left he, Real.norm_eq_abs,
      abs_of_nonneg (cavityMessage_nonneg H D e T s)] using hh (e, T)
  · intro hh p
    by_cases hp : p.1 ∈ H p.2
    · simpa only [cavityIncidentMessages, ite_eq_left hp, Real.norm_eq_abs,
        abs_of_nonneg (cavityMessage_nonneg H D p.1 p.2 s)] using hh p.1 p.2 hp
    · simpa only [cavityIncidentMessages, ite_eq_right hp, norm_zero] using hb

theorem cavity_strict_continuation (H : τ → Finset ι) {D S δ η K : ℝ}
    (hD : 0 < D) (hS : 0 ≤ S) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hcard : ∀ T, (H T).card = 3)
    (hdeg : ∀ e, |((messageCandidates H e none).card : ℝ) / D - 1| ≤ η)
    (hrow : ∀ e, ((messageCandidates H e none).card : ℝ) / D ≤ 2)
    (ht : cavityTime D S < 1)
    (hsmall : 12 * S / D ≤ 1 / 4)
    (himprove : K * (η + 64 * δ ^ 2 + 1152 * S / D) * S ≤ δ / 2)
    (hsem : ∀ u ∈ Set.Icc 0 S, ‖NormedSpace.exp ((-u) • cavityGenerator H D)‖ ≤ K) :
    ∀ s ∈ Set.Icc 0 S,
      (∀ e, |cavityLog H D e s| ≤ δ / 2) ∧
      (∀ e T, e ∈ H T → cavityMessage H D e T s ≤ 12 * s / D) := by
  let Q : ℝ → ℝ := fun s => max (‖fun e => cavityLog H D e s‖ / δ)
    (2 * ‖cavityIncidentMessages H D s‖)
  have hQ : ContinuousOn Q (Set.Icc 0 S) :=
    ((continuousOn_cavityLog_vector H hD ht).norm.div_const δ).sup
      (continuousOn_const.mul (continuous_cavityIncidentMessages H D).continuousOn.norm)
  have hzero : Q 0 ≤ 1 := by
    simp only [Q, cavityLog_zero, show (fun _ : ι => (0 : ℝ)) = 0 from rfl,
      norm_zero, zero_div, cavityIncidentMessages_zero, mul_zero, max_self, zero_le_one]
  have hdecode : ∀ s, Q s ≤ 1 →
      (∀ e, |cavityLog H D e s| ≤ δ) ∧
      (∀ e T, e ∈ H T → cavityMessage H D e T s ≤ 1 / 2) := by
    intro s hh
    have hm := max_le_iff.mp hh
    constructor
    · have hb : ‖fun e => cavityLog H D e s‖ ≤ δ := by
        exact (div_le_one hδ).mp hm.1
      simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hδ.le).mp hb
    · apply (cavityIncidentMessages_norm_iff H D s _ (by norm_num)).mp
      linarith [hm.2]
  have hboot : ∀ s ∈ Set.Icc 0 S, Q s ≤ 1 / 2 := by
    apply strict_bootstrap (δ := 1) (by norm_num) hQ hzero
    intro s hs hp
    have hz := fun u hu => (hdecode u (hp u hu)).1
    have hI := fun u hu => (hdecode u (hp u hu)).2
    have ht' : cavityTime D s < 1 := (cavityTime_mono hD hs.2).trans_lt ht
    have hsmall' : 12 * s / D ≤ 1 / 4 :=
      (div_le_div_of_nonneg_right (by linarith [hs.2]) hD.le).trans hsmall
    apply max_le_iff.mpr
    constructor
    · apply (div_le_iff₀ hδ).mpr
      have hh := cavityLog_provisional_bound H hD hs.1 hδ' hη hK hcard hdeg hrow hz hI
        ht' (by linarith) (fun u hu => hsem u ⟨hu.1, hu.2.trans hs.2⟩)
      have hforce : η + 64 * δ ^ 2 + 1152 * s / D ≤ η + 64 * δ ^ 2 + 1152 * S / D := by
        have := div_le_div_of_nonneg_right (by linarith [hs.2] : 1152 * s ≤ 1152 * S) hD.le
        linarith
      have hcmp : K * (η + 64 * δ ^ 2 + 1152 * s / D) * s ≤
          K * (η + 64 * δ ^ 2 + 1152 * S / D) * S := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hforce hK) hs.2 hs.1
        positivity
      linarith [hh.trans hcmp, himprove]
    · have hm : ‖cavityIncidentMessages H D s‖ ≤ 12 * s / D := by
        apply (cavityIncidentMessages_norm_iff H D s _
          (div_nonneg (mul_nonneg (by norm_num) hs.1) hD.le)).mpr
        exact cavityMessage_bound H hD hs.1 hδ' hcard hz hI ht'
      linarith
  intro s hs
  have hpre : ∀ u ∈ Set.Icc 0 s, Q u ≤ 1 := fun u hu =>
    (hboot u ⟨hu.1, hu.2.trans hs.2⟩).trans (by norm_num)
  constructor
  · have hh := (max_le_iff.mp (hboot s hs)).1
    have hn : ‖fun e => cavityLog H D e s‖ ≤ δ / 2 := by
      have := (div_le_iff₀ hδ).mp hh
      linarith
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg (by positivity)).mp hn
  · exact cavityMessage_bound H hD hs.1 hδ' hcard
      (fun u hu => (hdecode u (hpre u hu)).1)
      (fun u hu => (hdecode u (hpre u hu)).2)
      ((cavityTime_mono hD hs.2).trans_lt ht)

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem cavityTime_strictMono {D : ℝ} (hD : 0 < D) : StrictMono (cavityTime D) := by
  intro s t hst
  apply div_lt_div_of_pos_right _ (by positivity)
  exact sub_lt_sub_right (Real.exp_lt_exp.mpr (by linarith)) _

theorem cavity_closed_continuation (H : τ → Finset ι) {D S δ η K : ℝ}
    (hD : 0 < D) (hS : 0 < S) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hcard : ∀ T, (H T).card = 3)
    (hdeg : ∀ e, |((messageCandidates H e none).card : ℝ) / D - 1| ≤ η)
    (hrow : ∀ e, ((messageCandidates H e none).card : ℝ) / D ≤ 2)
    (ht : cavityTime D S ≤ 1)
    (hsmall : 12 * S / D ≤ 1 / 4)
    (himprove : K * (η + 64 * δ ^ 2 + 1152 * S / D) * S ≤ δ / 2)
    (hsem : ∀ u ∈ Set.Icc 0 S, ‖NormedSpace.exp ((-u) • cavityGenerator H D)‖ ≤ K) :
    ∀ s ∈ Set.Icc 0 S,
      (∀ e, Real.exp (-s - δ / 2) ≤ cavityLimit H e none (cavityTime D s) ∧
        cavityLimit H e none (cavityTime D s) ≤ Real.exp (-s + δ / 2)) ∧
      (∀ e T, e ∈ H T → cavityMessage H D e T s ≤ 12 * s / D) := by
  have hpre : ∀ s ∈ Set.Ico 0 S,
      (∀ e, Real.exp (-s - δ / 2) ≤ cavityLimit H e none (cavityTime D s) ∧
        cavityLimit H e none (cavityTime D s) ≤ Real.exp (-s + δ / 2)) ∧
      (∀ e T, e ∈ H T → cavityMessage H D e T s ≤ 12 * s / D) := by
    intro s hs
    have ht' : cavityTime D s < 1 := (cavityTime_strictMono hD hs.2).trans_le ht
    have hsmall' : 12 * s / D ≤ 1 / 4 :=
      (div_le_div_of_nonneg_right (by linarith [hs.2]) hD.le).trans hsmall
    have hforce : η + 64 * δ ^ 2 + 1152 * s / D ≤ η + 64 * δ ^ 2 + 1152 * S / D := by
      linarith [div_le_div_of_nonneg_right (by linarith [hs.2] : 1152 * s ≤ 1152 * S) hD.le]
    have hcmp : K * (η + 64 * δ ^ 2 + 1152 * s / D) * s ≤
        K * (η + 64 * δ ^ 2 + 1152 * S / D) * S := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hforce hK) hs.2.le hs.1
      positivity
    have hh := cavity_strict_continuation H hD hs.1 hδ hδ' hη hK hcard hdeg hrow ht'
      hsmall' (hcmp.trans himprove) (fun u hu => hsem u ⟨hu.1, hu.2.trans hs.2.le⟩) s ⟨hs.1, le_rfl⟩
    refine ⟨?_, hh.2⟩
    intro e
    rw [cavityLog_exp H D e ht']
    constructor <;> apply Real.exp_le_exp.mpr <;> linarith [(abs_le.mp (hh.1 e)).1, (abs_le.mp (hh.1 e)).2]
  have hclose {P : ℝ → Prop} (hp : IsClosed {s | P s})
      (hh : ∀ s ∈ Set.Ico 0 S, P s) : ∀ s ∈ Set.Icc 0 S, P s := by
    have hx : closure (Set.Ico 0 S) ⊆ {s | P s} := closure_minimal hh hp
    simpa only [closure_Ico hS.ne, Set.subset_def, Set.mem_ofPred_eq] using hx
  intro s hs
  constructor
  · intro e
    have hc := (continuous_cavityLimit H e none).comp (continuous_cavityTime D)
    constructor
    · exact hclose (isClosed_le (Real.continuous_exp.comp
        (continuous_id.neg.sub continuous_const)) hc) (fun u hu => (hpre u hu).1 e |>.1) s hs
    · exact hclose (isClosed_le hc (Real.continuous_exp.comp
        (continuous_id.neg.add continuous_const))) (fun u hu => (hpre u hu).1 e |>.2) s hs
  · intro e T he
    exact hclose (isClosed_le (continuous_cavityMessage H D e T)
      ((continuous_const.mul continuous_id).div_const D)) (fun u hu => (hpre u hu).2 e T he) s hs

end CavityStability
end SharpTerminalLeave

end

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ActivePairMembership
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma active_messageCandidates_card {n : ℕ} (G : Graph n) (e : G) :
    (messageCandidates (activeHypergraph G) e none).card = triangleDegree G e.val := by
  classical
  have hm : (messageCandidates (activeHypergraph G) e none).map (triangleEmbedding G) =
      incidentTriangles G e.val := by
    ext T
    simp only [Finset.mem_map,messageCandidates,Finset.mem_filter,Finset.mem_univ,
      true_and,activeHypergraph_mem,ne_eq,reduceCtorEq,not_false_eq_true,and_true,
      triangleEmbedding,Function.Embedding.coeFn_mk,incidentTriangles]
    constructor
    · rintro ⟨U,hu,rfl⟩
      exact ⟨U.property,hu⟩
    · rintro ⟨hT,he⟩
      exact ⟨⟨T,hT⟩,he,rfl⟩
  have hh := congrArg Finset.card hm
  simpa only [Finset.card_map,triangleDegree] using hh

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IncidentTriangleThird
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma incidentTriangle_third {n : ℕ} {G : Graph n} {u v : Fin n}
    (huv : u ≠ v) {t : Finset (Fin n)} (ht : t ∈ incidentTriangles G {u,v}) :
    ∃ w ∈ commonNeighbors G u v, t = {u,v,w} ∧ u ≠ w ∧ v ≠ w := by
  obtain ⟨ht,hpair⟩ := Finset.mem_filter.mp ht
  obtain ⟨htcard,htG⟩ := mem_triangles.mp ht
  have hsub : ({u,v} : Finset (Fin n)) ⊆ t := (Finset.mem_powersetCard.mp hpair).1
  have hc : (t \ {u,v}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, htcard, Finset.card_pair huv]
  obtain ⟨w,heq⟩ := Finset.card_eq_one.mp hc
  have hw : w ∈ t \ {u,v} := by rw [heq]; simp
  obtain ⟨hwt,hwuv⟩ := Finset.mem_sdiff.mp hw
  have huw : u ≠ w := by intro h; apply hwuv; simp [h]
  have hvw : v ≠ w := by intro h; apply hwuv; simp [h]
  have htriple : t = {u,v,w} := by
    have hu := Finset.sdiff_union_of_subset hsub
    rw [heq] at hu
    rw [← hu]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hcw : w ∈ commonNeighbors G u v := by
    apply (mem_commonNeighbors G u v w).mpr
    constructor
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair huw⟩
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair hvw⟩
  exact ⟨w,hcw,htriple,huw,hvw⟩

lemma incidentTriangles_eq_image {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    incidentTriangles G {u,v} = (commonNeighbors G u v).image (fun w => {u,v,w}) := by
  have huv : u ≠ v := by
    intro h
    have hh := mem_completeGraph.mp (hG he)
    simp [h] at hh
  ext t
  constructor
  · intro ht
    obtain ⟨w,hw,rfl,_,_⟩ := incidentTriangle_third huv ht
    exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
  · intro ht
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨(triangle_closure_iff hG huv hw).mpr he,?_⟩
    exact Finset.mem_powersetCard.mpr ⟨by simp,Finset.card_pair huv⟩

theorem triangleDegree_eq_codegree {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    triangleDegree G {u,v} = currentCodegree G u v := by
  unfold triangleDegree currentCodegree
  rw [incidentTriangles_eq_image hG he]
  apply Finset.card_image_of_injOn
  intro a ha b _ hab
  change ({u,v,a} : Finset (Fin n)) = {u,v,b} at hab
  have ha' : a ∈ ({u,v,b} : Finset (Fin n)) := by rw [← hab]; simp
  have hnea := commonNeighbors_ne hG ha
  simpa [hnea.1.symm,hnea.2.symm] using ha'

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixHorizon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma prefixHorizon_bounds : ∀ᶠ n : ℕ in atTop,
    0 < prefixHorizon n ∧ prefixHorizon n ≤ Real.log n := by
  filter_upwards [prefix_scales_eventually_pos,eventually_ge_atTop (3 : ℕ)] with n hp hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : prefixD n ≤ n := by
    have hpl := prefixDensity_le_one n
    have hsq : (prefixDensity n)^2 ≤ 1 := by nlinarith [hp.1]
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n)).trans_eq (mul_one _)
  have harg : 1+2*prefixD n ≤ (n : ℝ)^2 := by nlinarith
  have hl := Real.log_le_log (by linarith [hp.2] : 0 < 1+2*prefixD n) harg
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold prefixHorizon
  exact ⟨div_pos (Real.log_pos (by linarith [hp.2])) (by norm_num),by linarith⟩

theorem prefix_bootstrap_numerics {c C₁ : ℝ} (hc : 0 < c) (hC₁ : 0 < C₁) (J : ℕ) :
    ∃ a : ℝ, 0 < a ∧ a < min c (1/1000 : ℝ) ∧ ∀ᶠ n : ℕ in atTop,
      let δ := (n : ℝ)^(-a)
      let S := prefixHorizon n
      let K := C₁*(1+Real.log n)^J
      0 < δ ∧ δ ≤ 1/2 ∧ 0 < S ∧ S ≤ Real.log n ∧
        12*S/prefixD n ≤ 1/4 ∧
        K*((n : ℝ)^(-c)+64*δ^2+1152*S/prefixD n)*S ≤ δ/2 := by
  let a := min c (1/1000 : ℝ)/3
  have ha : 0 < a := div_pos (lt_min hc (by norm_num)) (by norm_num)
  have hac : 2*a ≤ c := by dsimp [a]; linarith [min_le_left c (1/1000 : ℝ)]
  have had : 2*a ≤ (1/1000 : ℝ) := by dsimp [a]; linarith [min_le_right c (1/1000 : ℝ)]
  refine ⟨a,ha,by dsimp [a]; linarith [lt_min hc (by norm_num : (0 : ℝ) < 1/1000)],?_⟩
  have hδ := ((tendsto_rpow_neg_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const
      (by norm_num : (0 : ℝ) < 1/2)
  have hb : 0 < 1/(2434*C₁) := by positivity
  filter_upwards [prefixHorizon_bounds,prefixD_eventual_envelope,prefix_scales_eventually_pos,
    prefixTemplateFactor_subpower (J+2) ha hb,
    prefixTemplateFactor_subpower 1 ha (by norm_num : (0 : ℝ) < 1/48),
    hδ,eventually_ge_atTop (1 : ℕ)] with n hS hD hp hpol hlog hδ hn
  dsimp only
  change (n : ℝ)^(-a) ≤ 1/2 at hδ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hL : 1 ≤ 1+Real.log n := by linarith
  have hna : 0 < (n : ℝ)^a := Real.rpow_pos_of_pos hn0 _
  have hn2a : 0 < (n : ℝ)^(-2*a) := Real.rpow_pos_of_pos hn0 _
  have hDa : (n : ℝ)^a ≤ prefixD n :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : a ≤ (1/1000 : ℝ))).trans hD.1
  have hD2a : (n : ℝ)^(2*a) ≤ prefixD n :=
    (Real.rpow_le_rpow_of_exponent_le hn1 had).trans hD.1
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  have hη : (n : ℝ)^(-c) ≤ (n : ℝ)^(-2*a) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hδsq : ((n : ℝ)^(-a))^2 = (n : ℝ)^(-2*a) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hDinv : 1/prefixD n ≤ (n : ℝ)^(-2*a) := by
    calc
      _ ≤ 1/(n : ℝ)^(2*a) := div_le_div_of_nonneg_left zero_le_one
        (Real.rpow_pos_of_pos hn0 _) hD2a
      _ = _ := by rw [one_div,← Real.rpow_neg hn0.le]; congr 1; ring
  have hSD : prefixHorizon n/prefixD n ≤ (1+Real.log n)*(n : ℝ)^(-2*a) := by
    calc
      _ = prefixHorizon n*(1/prefixD n) := by ring
      _ ≤ (1+Real.log n)*(n : ℝ)^(-2*a) :=
        mul_le_mul (by linarith [hS.2]) hDinv (by positivity) (by linarith)
  have hsmall : 12*prefixHorizon n/prefixD n ≤ 1/4 := by
    have hlog' : 1+Real.log n ≤ (1/48 : ℝ)*(n : ℝ)^a := by
      simpa only [prefixTemplateFactor,Real.rpow_one] using hlog
    apply (div_le_iff₀ hD0).mpr
    nlinarith [hS.2,hDa]
  have hforce : (n : ℝ)^(-c)+64*((n : ℝ)^(-a))^2+
      1152*prefixHorizon n/prefixD n ≤ 1217*(1+Real.log n)*(n : ℝ)^(-2*a) := by
    rw [hδsq]
    have hhd := mul_le_mul_of_nonneg_left hSD (by norm_num : (0 : ℝ) ≤ 1152)
    have hhη := mul_le_mul_of_nonneg_right hL hn2a.le
    rw [mul_div_assoc]
    nlinarith only [hη,hhη,hhd]
  have hpol' : (1+Real.log n)^(J+2) ≤ 1/(2434*C₁)*(n : ℝ)^a := by
    unfold prefixTemplateFactor at hpol
    rw [show (J : ℝ)+2 = ((J+2 : ℕ) : ℝ) by norm_cast,Real.rpow_natCast] at hpol
    exact hpol
  have hm : C₁*(1+Real.log n)^J *
      ((n : ℝ)^(-c)+64*((n : ℝ)^(-a))^2+1152*prefixHorizon n/prefixD n)*
        prefixHorizon n ≤
        1217*C₁*(1+Real.log n)^(J+2)*(n : ℝ)^(-2*a) := by
    calc
      _ ≤ C₁*(1+Real.log n)^J * (1217*(1+Real.log n)*(n : ℝ)^(-2*a)) *
        (1+Real.log n) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hforce (by positivity))
          (by linarith [hS.2]) hS.1.le
        positivity
      _ = _ := by rw [pow_add]; ring
  have hident : (1217*C₁)*(1/(2434*C₁)) = (1/2 : ℝ) := by
    field_simp
    ring
  have hexp : (n : ℝ)^a*(n : ℝ)^(-2*a) = (n : ℝ)^(-a) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  refine ⟨Real.rpow_pos_of_pos hn0 _,hδ,hS.1,hS.2,hsmall,?_⟩
  calc
    _ ≤ 1217*C₁*(1+Real.log n)^(J+2)*(n : ℝ)^(-2*a) := hm
    _ ≤ 1217*C₁*(1/(2434*C₁)*(n : ℝ)^a)*(n : ℝ)^(-2*a) := by
      gcongr
    _ = (n : ℝ)^(-a)/2 := by
      rw [← mul_assoc (1217*C₁),hident,mul_assoc,hexp]
      ring
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_CavityReference
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma goodPrefix_active_degree {n : ℕ} {c C : ℝ} {G : Graph n}
    (h : GoodPrefixGraph n c C G) (hD : 0 < prefixD n) (e : G) :
    |((messageCandidates (activeHypergraph G) e none).card : ℝ)/prefixD n-1| ≤
      (n : ℝ)^(-c) := by
  classical
  rw [active_messageCandidates_card]
  obtain ⟨u,v,huv,hev⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp (h.1 e.property))
  have heG : ({u,v} : Finset (Fin n)) ∈ G := hev ▸ e.property
  rw [hev,triangleDegree_eq_codegree h.1 heG]
  have hcode := h.2.2.2.1 u v huv
  have heq : (currentCodegree G u v : ℝ)/prefixD n-1 =
      ((currentCodegree G u v : ℝ)-prefixD n)/prefixD n := by
    rw [sub_div,div_self hD.ne']
  rw [heq,abs_div,abs_of_pos hD]
  exact (div_le_iff₀ hD).mpr hcode

lemma cavityTime_prefixHorizon {n : ℕ} (hD : 0 < prefixD n) :
    cavityTime (prefixD n) (prefixHorizon n) = 1 := by
  unfold cavityTime prefixHorizon
  rw [show 2*(Real.log (1+2*prefixD n)/2)=Real.log (1+2*prefixD n) by ring,
    Real.exp_log (by linarith : 0 < 1+2*prefixD n)]
  field_simp
  ring

theorem goodPrefix_cavity_continuation {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ a < min c (1/1000 : ℝ) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ s ∈ Set.Icc (0 : ℝ) (prefixHorizon n),
        (∀ e : G, Real.exp (-s-(n : ℝ)^(-a)/2) ≤
            cavityLimit (activeHypergraph G) e none (cavityTime (prefixD n) s) ∧
          cavityLimit (activeHypergraph G) e none (cavityTime (prefixD n) s) ≤
            Real.exp (-s+(n : ℝ)^(-a)/2)) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          cavityMessage (activeHypergraph G) (prefixD n) e T s ≤ 12*s/prefixD n) := by
  obtain ⟨C₁,hC₁,J,hsem⟩ := goodPrefix_cavity_semigroup hc
  obtain ⟨a,ha,hac,hnum⟩ := prefix_bootstrap_numerics hc hC₁ J
  refine ⟨a,ha,hac,?_⟩
  filter_upwards [hsem,hnum,prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)]
    with n hsem hnum hp hn
  intro C G h
  have hD : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  have hδc : (n : ℝ)^(-c) ≤ (n : ℝ)^(-a) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
      (by linarith [(lt_min_iff.mp hac).1])
  apply cavity_closed_continuation (activeHypergraph G)
    (K := C₁*(1+Real.log (n : ℝ))^J) hD hnum.2.2.1 hnum.1 hnum.2.1
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)
    (activeHypergraph_card G) (goodPrefix_active_degree h hD)
  · intro e
    have hh := (abs_le.mp (goodPrefix_active_degree h hD e)).2
    linarith [hnum.2.1]
  · exact (cavityTime_prefixHorizon hD).le
  · exact hnum.2.2.2.2.1
  · exact hnum.2.2.2.2.2
  · intro s hs
    exact hsem C G h s ⟨hs.1,hs.2.trans hnum.2.2.2.1⟩

lemma cavityClock_mem {D t : ℝ} (hD : 0 < D) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cavityClock D t ∈ Set.Icc (0 : ℝ) (Real.log (1+2*D)/2) := by
  have harg : 1 ≤ 1+2*D*t := by nlinarith [ht.1]
  have hlo := Real.log_nonneg harg
  have hhi := Real.log_le_log (by linarith : 0 < 1+2*D*t)
    (by nlinarith [ht.2] : 1+2*D*t ≤ 1+2*D)
  exact ⟨by dsimp [cavityClock]; linarith,by dsimp [cavityClock]; linarith⟩

lemma cavityTime_clock {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    cavityTime D (cavityClock D t) = t := by
  unfold cavityTime cavityClock
  rw [show 2*(Real.log (1+2*D*t)/2)=Real.log (1+2*D*t) by ring,
    Real.exp_log (by nlinarith : 0 < 1+2*D*t)]
  field_simp
  ring

lemma cavityReference_exp {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    cavityReference D t = Real.exp (-cavityClock D t) := by
  rw [cavityReference,Real.rpow_def_of_pos (by nlinarith : 0 < 1+2*D*t)]
  congr 1
  dsimp [cavityClock]
  ring

lemma cavityReference_pos {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    0 < cavityReference D t := by rw [cavityReference_exp hD ht]; positivity

theorem goodPrefix_cavity_relative {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      let δ := (n : ℝ)^(-a)
      let Imax := 12*prefixHorizon n/prefixD n
      Imax ≤ 1/4 ∧ ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ e : G, Real.exp (-δ/2) ≤ cavityLimit (activeHypergraph G) e none t /
            cavityReference (prefixD n) t ∧
          cavityLimit (activeHypergraph G) e none t / cavityReference (prefixD n) t ≤
            Real.exp (δ/2)) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          messageIntegral (activeHypergraph G) (cavityLimit (activeHypergraph G)) e T t ≤ Imax ∧
          Real.exp (-δ/2) ≤ cavityLimit (activeHypergraph G) e (some T) t /
            cavityReference (prefixD n) t ∧
          cavityLimit (activeHypergraph G) e (some T) t / cavityReference (prefixD n) t ≤
            Real.exp (δ/2)/(1-Imax)) := by
  obtain ⟨a,ha,hac,hcont⟩ := goodPrefix_cavity_continuation hc
  obtain ⟨C₁,hC₁,J,_⟩ := goodPrefix_cavity_semigroup hc
  obtain ⟨b,hb,_,hnum⟩ := prefix_bootstrap_numerics hc hC₁ J
  refine ⟨a,ha,?_⟩
  filter_upwards [hcont,hnum,prefix_scales_eventually_pos] with n hcavity hn hp
  dsimp only
  have hD : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  have hI : 12*prefixHorizon n/prefixD n ≤ 1/4 := hn.2.2.2.2.1
  refine ⟨hI,?_⟩
  intro C G h t ht
  let s := cavityClock (prefixD n) t
  have hs : s ∈ Set.Icc (0 : ℝ) (prefixHorizon n) := cavityClock_mem hD ht
  have hst : cavityTime (prefixD n) s = t := cavityTime_clock hD ht.1
  obtain ⟨hq,hmsg⟩ := hcavity C G h s hs
  rw [hst] at hq
  have href := cavityReference_exp hD ht.1
  have href0 := cavityReference_pos hD ht.1
  have helo : Real.exp (-s-(n : ℝ)^(-a)/2) =
      Real.exp (-(n : ℝ)^(-a)/2)*cavityReference (prefixD n) t := by
    rw [href,← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  have hehi : Real.exp (-s+(n : ℝ)^(-a)/2) =
      Real.exp ((n : ℝ)^(-a)/2)*cavityReference (prefixD n) t := by
    rw [href,← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  have hroot (e : G) := hq e
  simp only [helo,hehi] at hroot
  constructor
  · intro e
    exact ⟨(le_div_iff₀ href0).mpr (hroot e).1,(div_le_iff₀ href0).mpr (hroot e).2⟩
  · intro e T he
    let I := messageIntegral (activeHypergraph G) (cavityLimit (activeHypergraph G)) e T t
    have hI0 : 0 ≤ I := (messageIntegral_mem_unit _ _ (continuous_cavityLimit _)
      (cavityLimit_mem_unit _) _ _ _).1
    have hIm : I ≤ 12*prefixHorizon n/prefixD n := by
      have hh := hmsg e T he
      change messageIntegral _ _ _ _ (cavityTime (prefixD n) s) ≤ _ at hh
      rw [hst] at hh
      exact hh.trans (div_le_div_of_nonneg_right (by linarith [hs.2]) hD.le)
    have hIf : 0 < 1-I := by linarith
    have hMax : 0 < 1-12*prefixHorizon n/prefixD n := by linarith
    have ho := cavityLimit_omission (activeHypergraph G) e T he t
    change cavityLimit (activeHypergraph G) e none t =
      cavityLimit (activeHypergraph G) e (some T) t * (1-I) at ho
    have hparent : cavityLimit (activeHypergraph G) e (some T) t =
      cavityLimit (activeHypergraph G) e none t/(1-I) := (eq_div_iff hIf.ne').mpr ho.symm
    refine ⟨hIm,?_,?_⟩
    · apply (le_div_iff₀ href0).mpr
      have hpar0 := (cavityLimit_mem_unit (activeHypergraph G) e (some T) t).1
      have hm : cavityLimit (activeHypergraph G) e none t ≤
          cavityLimit (activeHypergraph G) e (some T) t := by rw [ho]; nlinarith
      exact (hroot e).1.trans hm
    · rw [hparent]
      calc
        _ = (cavityLimit (activeHypergraph G) e none t/cavityReference (prefixD n) t)/(1-I) := by ring
        _ ≤ Real.exp ((n : ℝ)^(-a)/2)/(1-12*prefixHorizon n/prefixD n) :=
          div_le_div₀ (by positivity) ((div_le_iff₀ href0).mpr (hroot e).2) hMax (by linarith)
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_AbsPmfMean
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma abs_pmfMean_le {α : Type*} [Fintype α] (P : PMF α) (f : α → ℝ) :
    |pmfMean P f| ≤ pmfMean P (fun a => |f a|) := by
  unfold pmfMean
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro a _
  rw [abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]

lemma pmfMean_swap {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) (f : α → β → ℝ) :
    pmfMean P (fun a => pmfMean Q (f a)) =
      pmfMean Q (fun b => pmfMean P (fun a => f a b)) := by
  unfold pmfMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma pmfMean_common_error {α : Type*} [Fintype α] (P : PMF α)
    (f err : α → ℝ) (r : ℝ) (h : ∀ a ∈ P.support, |f a-r| ≤ err a) :
    |pmfMean P f-r| ≤ pmfMean P err := by
  rw [← pmfMean_const P r,← pmfMean_sub]
  exact (abs_pmfMean_le P _).trans (pmfMean_mono P h)

lemma relative_error_absolute {a r ε : ℝ} (hr : 0 < r)
    (h : |a/r-1| ≤ ε) : |a-r| ≤ ε*r := by
  have heq : (a/r-1)*r = a-r := by field_simp
  calc
    _ = |(a/r-1)*r| := congrArg abs heq.symm
    _ = |a/r-1| *r := by rw [abs_mul,abs_of_pos hr]
    _ ≤ _ := mul_le_mul_of_nonneg_right h hr.le

lemma product_relative_error {a b r ε : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b)
    (haerr : |a-r| ≤ ε*r) (hberr : |b-r| ≤ ε*r) (hε : 0 ≤ ε) :
    |a*b-r^2| ≤ (2*ε+ε^2)*r^2 := by
  have hbup : b ≤ (1+ε)*r := by
    have := (abs_le.mp hberr).2
    nlinarith
  calc
    _ = |(a-r)*b+r*(b-r)| := by congr 1; ring
    _ ≤ |(a-r)*b|+|r*(b-r)| := abs_add_le _ _
    _ = |a-r| *b+r*|b-r| := by rw [abs_mul,abs_mul,abs_of_nonneg hb,abs_of_nonneg hr]
    _ ≤ (ε*r)*((1+ε)*r)+r*(ε*r) := add_le_add
      (mul_le_mul haerr hbup hb (mul_nonneg hε hr))
      (mul_le_mul_of_nonneg_left hberr hr)
    _ = _ := by ring

lemma focusSurvival_mem_unit {n : ℕ} (G focus : Graph n) :
    focusSurvival G focus ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨trueProbability_nonneg _,trueProbability_le_one _⟩

lemma cavityReference_le_one {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    cavityReference D t ≤ 1 := by
  unfold cavityReference
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith : 1 ≤ 1+2*D*t)
    (by norm_num)

theorem singleton_survival_error {n : ℕ} (G : Graph n) (D ε : ℝ)
    (hD : 0 < D)
    (hrel : ∀ e : G, |cavityLimit (activeHypergraph G) e none 1 /
      cavityReference D 1 - 1| ≤ ε)
    (e : Finset (Fin n)) (he : e ∈ G) :
    |focusSurvival G {e}-cavityReference D 1| ≤
      collisionCost (triangleHypergraph G) {e} none+ε*cavityReference D 1 := by
  classical
  have hc := graph_cavity_error G {e} (Finset.singleton_subset_iff.mpr he)
  rw [Finset.prod_singleton] at hc
  have heq := active_cavity_eq G ⟨e,he⟩ none 1
  simp only [Option.map_none] at heq
  have habs := relative_error_absolute (cavityReference_pos hD (by norm_num)) (hrel ⟨e,he⟩)
  rw [← heq] at habs
  exact (abs_sub_le _ _ _).trans (add_le_add hc habs)

theorem pair_survival_error {n : ℕ} (G : Graph n) (D ε : ℝ)
    (hD : 0 < D) (hε : 0 ≤ ε)
    (hrel : ∀ e : G, |cavityLimit (activeHypergraph G) e none 1 /
      cavityReference D 1 - 1| ≤ ε)
    (e f : Finset (Fin n)) (he : e ∈ G) (hf : f ∈ G) (hef : e ≠ f) :
    |focusSurvival G {e,f}-(cavityReference D 1)^2| ≤
      collisionCost (triangleHypergraph G) {e,f} none+
        (2*ε+ε^2)*(cavityReference D 1)^2 := by
  classical
  have hc := graph_cavity_error G {e,f}
    (by intro a ha; simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> assumption)
  rw [Finset.prod_pair hef] at hc
  have heq := active_cavity_eq G ⟨e,he⟩ none 1
  have hfq := active_cavity_eq G ⟨f,hf⟩ none 1
  simp only [Option.map_none] at heq hfq
  have hr := cavityReference_pos hD (by norm_num : (0 : ℝ) ≤ 1)
  have hea := relative_error_absolute hr (hrel ⟨e,he⟩)
  have hfa := relative_error_absolute hr (hrel ⟨f,hf⟩)
  rw [← heq] at hea
  rw [← hfq] at hfa
  have hh := product_relative_error hr.le
    (cavityLimit_mem_unit (triangleHypergraph G) f none 1).1
    hea hfa hε
  exact (abs_sub_le _ _ _).trans (add_le_add hc hh)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_MapOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

section TraceQuery
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem tracedGridQuery_outcome (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ) :
    ExposureTree.mapOutput Prod.fst (tracedGridQuery H N d k c) =
      gridQueryDepth H N d k c.focus c.parent := by
  induction d generalizing k c with
  | zero => simp only [tracedGridQuery, ExposureTree.mapOutput_bind,
      ExposureTree.mapOutput_done, gridQueryDepth]
  | succ d ih =>
    simp only [tracedGridQuery, ExposureTree.mapOutput_bind, ExposureTree.mapOutput_comp,
      gridQueryDepth]
    congr 1
    funext vals
    change ExposureTree.mapOutput Prod.fst (ExposureTree.checkNoneTrace _) = _
    rw [ExposureTree.checkNoneTrace_outcome, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    split_ifs
    · exact ih _ _
    · rfl

end TraceQuery
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedFailure_eq_one_sub (p : PMF (Bool × Bool)) :
    markedFailure p = 1 - markedSuccess p := by
  unfold markedFailure markedSuccess
  rw [← pmfMean_const p 1, ← pmfMean_sub]
  apply pmfMean_congr
  intro z _
  cases z.1 <;> simp

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ProspectiveFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedGood_bind {α : Type*} [Fintype α] (π : PMF α)
    (p : α → PMF (Bool × Bool)) :
    markedGood (π.bind p) = pmfMean π (fun a => markedGood (p a)) :=
  pmfMean_bind π p _

@[simp] theorem markedGood_no_marks (p : PMF Bool) :
    markedGood (p.map (fun b => (b,true))) = 1 := by
  rw [markedGood,pmfMean_map]
  simp only [↓reduceIte,pmfMean_const]

@[simp] theorem markedSuccess_no_marks (p : PMF Bool) :
    markedSuccess (p.map (fun b => (b,true))) = (p true).toReal := by
  rw [markedSuccess,pmfMean_map]
  simp [pmfMean]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_LegalCollisionPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section CollisionPathSum
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma gridCollision_eq_trace (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) (j : ℕ) :
    gridCollision H focus parent j = tracedCollisionProbability H (j+1) (j+1) (j+1) focus parent := by
  unfold gridCollision trueProbability tracedCollisionProbability
  rw [ExposureTree.freshRecorded_eq_log,PMF.map_comp]
  rw [← tracedGridQuery_outcome H (j+1) (j+1) (j+1) ⟨[],focus,parent⟩,
    ExposureTree.freshLog_mapOutput,PMF.map_comp]
  rfl

end CollisionPathSum

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CardBiUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma disjoint_valid_edge_ne {n : ℕ} {e f : Finset (Fin n)}
    (he : e.card = 2) (hd : Disjoint e f) : e ≠ f := by
  rintro rfl
  have h : e = ∅ := disjoint_self.mp hd
  rw [h,Finset.card_empty] at he
  omega

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EdgeFamilyDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section RootOverlap
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_edgeFamilyDegree (G : Finset (Finset V))
    (hG : ∀ e ∈ G, e.card = 2) : ∑ v, edgeFamilyDegree G v = 2 * G.card := by
  classical
  calc
    _ = ∑ v, ∑ e ∈ G, if v ∈ e then 1 else 0 := by
      simp only [edgeFamilyDegree, Finset.card_filter]
    _ = ∑ e ∈ G, ∑ v, if v ∈ e then 1 else 0 := Finset.sum_comm
    _ = ∑ e ∈ G, e.card := by simp
    _ = _ := by simp only [Finset.sum_congr rfl hG, Finset.sum_const, smul_eq_mul, mul_comm]

theorem uniform_root_vertex (G : Finset (Finset V)) (hne : G.Nonempty) (v : V) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e => if v ∈ e then 1 else 0) =
      (edgeFamilyDegree G v : ℝ) / G.card := by
  rw [pmfMean_uniformOfFinset]
  congr 1
  simp [edgeFamilyDegree]

theorem uniform_root_pair_vertex (G : Finset (Finset V)) (hne : G.Nonempty) (v : V) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if v ∈ e ∧ v ∈ f then 1 else 0)) =
      (edgeFamilyDegree G v : ℝ) ^ 2 / (G.card : ℝ) ^ 2 := by
  have hi (e : Finset V) :
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if v ∈ e ∧ v ∈ f then 1 else 0) =
        (if v ∈ e then 1 else 0) * ((edgeFamilyDegree G v : ℝ) / G.card) := by
    by_cases he : v ∈ e
    · simpa [he] using uniform_root_vertex G hne v
    · simp [he]
  simp_rw [hi]
  rw [pmfMean_mul_const, uniform_root_vertex]
  ring

theorem rootOverlap_le_degree_sum (G : Finset (Finset V)) (hne : G.Nonempty) :
    rootOverlap G hne ≤ (∑ v, (edgeFamilyDegree G v : ℝ) ^ 2) / (G.card : ℝ) ^ 2 := by
  classical
  have hpt (e f : Finset V) :
      (if ¬Disjoint e f then (1 : ℝ) else 0) ≤
        ∑ v : V, if v ∈ e ∧ v ∈ f then (1 : ℝ) else 0 := by
    by_cases h : Disjoint e f
    · simp only [h, not_true_eq_false, ite_false]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    · obtain ⟨v, hv, hv'⟩ := Finset.not_disjoint_iff.mp h
      simp only [h, not_false_eq_true, ite_true]
      have hh := Finset.single_le_sum (f := fun x => if x ∈ e ∧ x ∈ f then (1 : ℝ) else 0)
        (s := Finset.univ) (a := v) (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ v)
      simpa only [hv, hv', and_self, ite_true] using hh
  calc
    rootOverlap G hne ≤ pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        pmfMean (PMF.uniformOfFinset G hne) (fun f =>
          ∑ v : V, if v ∈ e ∧ v ∈ f then (1 : ℝ) else 0)) := by
      apply pmfMean_mono
      intro e _
      apply pmfMean_mono
      intro f _
      exact hpt e f
    _ = _ := by
      simp_rw [pmfMean_sum]
      simp_rw [uniform_root_pair_vertex]
      exact (Finset.sum_div _ _ _).symm

theorem rootOverlap_le_maxDegree (G : Finset (Finset V)) (hne : G.Nonempty)
    (hG : ∀ e ∈ G, e.card = 2) (Δ : ℝ)
    (hΔ : ∀ v, (edgeFamilyDegree G v : ℝ) ≤ Δ) :
    rootOverlap G hne ≤ 2 * Δ / G.card := by
  have hm : (0 : ℝ) < G.card := Nat.cast_pos.mpr hne.card_pos
  have hd : (∑ v, (edgeFamilyDegree G v : ℝ)) = 2 * (G.card : ℝ) := by
    exact_mod_cast sum_edgeFamilyDegree G hG
  have hs : (∑ v, (edgeFamilyDegree G v : ℝ) ^ 2) ≤ Δ * (2 * (G.card : ℝ)) := by
    rw [← hd, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (hΔ v) (show (0 : ℝ) ≤ edgeFamilyDegree G v by positivity)
  calc
    _ ≤ _ := rootOverlap_le_degree_sum G hne
    _ ≤ Δ * (2 * (G.card : ℝ)) / (G.card : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by field_simp

end RootOverlap
end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_AveragedSingletonSurvivalError
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem averaged_singleton_survival_error {n : ℕ} (G : Graph n) (hne : G.Nonempty)
    (D ε : ℝ) (hD : 0 < D)
    (hrel : ∀ e : G, |cavityLimit (activeHypergraph G) e none 1 /
      cavityReference D 1 - 1| ≤ ε) :
    |pmfMean (PMF.uniformOfFinset G hne) (fun e => focusSurvival G {e})-
      cavityReference D 1| ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        collisionCost (triangleHypergraph G) {e} none)+ε*cavityReference D 1 := by
  let P := PMF.uniformOfFinset G hne
  have hh := pmfMean_common_error P (fun e => focusSurvival G {e})
    (fun e => collisionCost (triangleHypergraph G) {e} none+ε*cavityReference D 1)
    (cavityReference D 1) (fun e he => singleton_survival_error G D ε hD hrel e
      ((PMF.mem_support_uniformOfFinset_iff hne e).mp he))
  simpa only [pmfMean_add,pmfMean_const,P] using hh

theorem averaged_pair_survival_error {n : ℕ} (G : Graph n) (hne : G.Nonempty)
    (hG : G ⊆ completeGraph n) (D ε : ℝ) (hD : 0 < D) (hε : 0 ≤ ε)
    (hrel : ∀ e : G, |cavityLimit (activeHypergraph G) e none 1 /
      cavityReference D 1 - 1| ≤ ε) :
    |pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => focusSurvival G {e,f}))-
        (cavityReference D 1)^2| ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        pmfMean (PMF.uniformOfFinset G hne) (fun f => if Disjoint e f then
          collisionCost (triangleHypergraph G) {e,f} none else 0))+
      rootOverlap G hne+(2*ε+ε^2)*(cavityReference D 1)^2 := by
  classical
  let P := PMF.uniformOfFinset G hne
  let A := (2*ε+ε^2)*(cavityReference D 1)^2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let err := fun e f : Finset (Fin n) =>
    (if Disjoint e f then collisionCost (triangleHypergraph G) {e,f} none else 0)+
      (if ¬Disjoint e f then 1 else 0)+A
  have ht (e f : Finset (Fin n)) (he : e ∈ P.support) (hf : f ∈ P.support) :
      |focusSurvival G {e,f}-(cavityReference D 1)^2| ≤ err e f := by
    have heG := (PMF.mem_support_uniformOfFinset_iff hne e).mp he
    have hfG := (PMF.mem_support_uniformOfFinset_iff hne f).mp hf
    by_cases hd : Disjoint e f
    · have hh := pair_survival_error G D ε hD hε hrel e f heG hfG
        (disjoint_valid_edge_ne (mem_completeGraph.mp (hG heG)) hd)
      simpa only [err,hd,not_true_eq_false,ite_true,ite_false,add_zero,A] using hh
    · have hsu := focusSurvival_mem_unit G {e,f}
      have hr := (cavityReference_pos hD (by norm_num : (0 : ℝ) ≤ 1)).le
      have hru := cavityReference_le_one hD (by norm_num : (0 : ℝ) ≤ 1)
      have hsq : (cavityReference D 1)^2 ≤ 1 := by nlinarith
      have hh : |focusSurvival G {e,f}-(cavityReference D 1)^2| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> nlinarith [hsu.1,hsu.2,sq_nonneg (cavityReference D 1)]
      simpa only [err,hd,not_false_eq_true,ite_true,ite_false,zero_add] using
        hh.trans (le_add_of_nonneg_right hA)
  have hh := pmfMean_common_error P
    (fun e => pmfMean P (fun f => focusSurvival G {e,f}))
    (fun e => pmfMean P (err e)) ((cavityReference D 1)^2)
    (fun e he => pmfMean_common_error P (fun f => focusSurvival G {e,f})
      (err e) ((cavityReference D 1)^2) (fun f hf => ht e f he hf))
  simpa only [err,pmfMean_add,pmfMean_const,A,P,rootOverlap] using hh

lemma currentDegree_eq_edgeFamilyDegree {n : ℕ} (G : Graph n)
    (hG : G ⊆ completeGraph n) (u : Fin n) :
    currentDegree G u = edgeFamilyDegree G u := by
  classical
  unfold currentDegree edgeFamilyDegree
  apply Finset.card_bij (fun v _ => ({u,v} : Finset (Fin n)))
  · intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,by simp⟩
  · intro v _ w _ h
    by_cases huv : u = v
    · subst v
      have hw' : w ∈ ({u,u} : Finset (Fin n)) := by rw [h]; simp
      have hwu : w = u := by simpa using hw'
      exact hwu.symm
    · have hv' : v ∈ ({u,w} : Finset (Fin n)) := by rw [← h]; simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
      rcases hv' with h' | h'
      · exact False.elim (huv h'.symm)
      · exact h'
  · intro e he
    obtain ⟨heG,hue⟩ := Finset.mem_filter.mp he
    obtain ⟨a,b,_,heq⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp (hG heG))
    subst e
    simp only [Finset.mem_insert,Finset.mem_singleton] at hue
    rcases hue with rfl | rfl
    · exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heG⟩,rfl⟩
    · refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · simpa only [Finset.pair_comm] using heG
      · exact Finset.pair_comm _ _

theorem goodPrefix_rootOverlap {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
    ∀ hne : G.Nonempty, rootOverlap G hne ≤ 8/(n : ℝ) := by
  have hδ : Tendsto (fun n : ℕ => (n : ℝ)^(-c)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hc).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hδ.eventually_le_const zero_lt_one,prefixDensity_eventual_envelope,
    eventually_ge_atTop (1 : ℕ)] with n hδ hp hn
  intro C G hG hne
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 < prefixDensity n :=
    (Real.rpow_pos_of_pos hn0 _).trans_le hp.1
  have hdeg (v : Fin n) : (edgeFamilyDegree G v : ℝ) ≤ 2*(n : ℝ)*prefixDensity n := by
    have hh := (abs_le.mp (hG.2.2.1 v)).2
    have hmul := mul_le_mul_of_nonneg_right hδ (mul_nonneg hn0.le hp0.le)
    rw [← currentDegree_eq_edgeFamilyDegree G hG.1 v]
    nlinarith
  apply (rootOverlap_le_maxDegree G hne
    (fun e he => mem_completeGraph.mp (hG.1 he)) (2*(n : ℝ)*prefixDensity n) hdeg).trans_eq
  rw [hG.2.1,prefixM]
  field_simp [ne_of_gt hn0,ne_of_gt hp0]
  ring

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_FinishSupportSubset
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem finish_support_subset {n : ℕ} {G H : Graph n}
    (hH : H ∈ (finish G).support) : H ⊆ G :=
  evolve_support_subset G G.card hH

theorem uniform_edge_survival {n : ℕ} {G H : Graph n}
    (hG : G.Nonempty) (hH : H ⊆ G) :
    pmfMean (PMF.uniformOfFinset G hG) (fun e => if e ∈ H then 1 else 0) =
      (H.card : ℝ) / G.card := by
  classical
  rw [pmfMean_uniformOfFinset]
  congr 1
  rw [← Finset.sum_filter]
  have heq : G.filter (fun e => e ∈ H) = H := Finset.filter_mem_eq_inter |>.trans
    (Finset.inter_eq_right.mpr hH)
  simp [heq]

theorem uniform_two_edge_survival {n : ℕ} {G H : Graph n}
    (hG : G.Nonempty) (hH : H ⊆ G) :
    pmfMean (PMF.uniformOfFinset G hG) (fun e =>
      pmfMean (PMF.uniformOfFinset G hG) (fun f =>
        if e ∈ H ∧ f ∈ H then 1 else 0)) =
      (H.card : ℝ) ^ 2 / (G.card : ℝ) ^ 2 := by
  classical
  have hm (e : Finset (Fin n)) :
      pmfMean (PMF.uniformOfFinset G hG)
          (fun f => if e ∈ H ∧ f ∈ H then 1 else 0) =
        (if e ∈ H then 1 else 0) * ((H.card : ℝ) / G.card) := by
    by_cases he : e ∈ H
    · simpa [he] using uniform_edge_survival hG hH
    · simp [he]
  simp_rw [hm]
  rw [pmfMean_mul_const, uniform_edge_survival hG hH]
  ring

theorem terminal_first_edge_moment {n : ℕ} (G : Graph n) (hG : G.Nonempty) :
    pmfMean (finish G) (fun H =>
      pmfMean (PMF.uniformOfFinset G hG) (fun e => if e ∈ H then 1 else 0)) =
      pmfMean (finish G) (fun H => (H.card : ℝ)) / G.card := by
  classical
  calc
    _ = pmfMean (finish G) (fun H => (H.card : ℝ) / G.card) := by
      apply pmfMean_congr
      intro H hH
      exact uniform_edge_survival hG (finish_support_subset hH)
    _ = _ := by simp only [div_eq_mul_inv, pmfMean_mul_const]

theorem terminal_second_edge_moment {n : ℕ} (G : Graph n) (hG : G.Nonempty) :
    pmfMean (finish G) (fun H =>
      pmfMean (PMF.uniformOfFinset G hG) (fun e =>
        pmfMean (PMF.uniformOfFinset G hG) (fun f =>
          if e ∈ H ∧ f ∈ H then 1 else 0))) =
      pmfMean (finish G) (fun H => (H.card : ℝ) ^ 2) / (G.card : ℝ) ^ 2 := by
  classical
  calc
    _ = pmfMean (finish G) (fun H => (H.card : ℝ) ^ 2 / (G.card : ℝ) ^ 2) := by
      apply pmfMean_congr
      intro H hH
      exact uniform_two_edge_survival hG (finish_support_subset hH)
    _ = _ := by simp only [div_eq_mul_inv, pmfMean_mul_const]

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_PmfMeanLiminfTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_liminf_le_of_tendsto_upper {α : Type*} [Fintype α]
    (p : PMF α) (f : α → ℕ → ℝ) (hbound : ∀ a j, 0 ≤ f a j)
    (g : ℕ → ℝ) {L : ℝ} (hg : Tendsto g atTop (𝓝 L))
    (hupper : ∀ᶠ j : ℕ in atTop, pmfMean p (fun a => f a j) ≤ g j) :
    pmfMean p (fun a => Filter.liminf (f a) atTop) ≤ L := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hevent (a : α) : ∀ᶠ j : ℕ in atTop,
      Filter.liminf (f a) atTop - ε ≤ f a j := by
    have hl : atTop.IsBoundedUnder (· ≥ ·) (f a) :=
      Filter.isBoundedUnder_of ⟨0, fun j => hbound a j⟩
    exact (Filter.eventually_lt_of_lt_liminf (sub_lt_self _ hε) hl).mono (fun _ h => h.le)
  have hall : ∀ᶠ j : ℕ in atTop, ∀ a, Filter.liminf (f a) atTop - ε ≤ f a j :=
    Filter.eventually_all.mpr hevent
  have hle : pmfMean p (fun a => Filter.liminf (f a) atTop) - ε ≤ L := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hg
    filter_upwards [hall,hupper] with j hj hU
    have hh := pmfMean_mono p (fun a _ => hj a)
    rw [pmfMean_sub,pmfMean_const] at hh
    exact hh.trans hU
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixMessageEnvelopeSmall
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma prefix_message_envelope_small {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ 12*prefixHorizon n/prefixD n ∧
      12*prefixHorizon n/prefixD n ≤ b := by
  have hpoly := prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/1000)
    (div_pos hb (by norm_num : (0 : ℝ) < 12))
  filter_upwards [prefixHorizon_bounds,prefixD_eventual_envelope,
    prefix_scales_eventually_pos,hpoly] with n hS hD hp hpoly
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  have hpoly' : 1+Real.log n ≤ (b/12)*(n : ℝ)^(1/1000 : ℝ) := by
    simpa only [prefixTemplateFactor,Real.rpow_one] using hpoly
  refine ⟨div_nonneg (mul_nonneg (by norm_num) hS.1.le) hD0.le,?_⟩
  apply (div_le_iff₀ hD0).mpr
  have hbound := mul_le_mul_of_nonneg_left hD.1 hb.le
  nlinarith [hS.2]

lemma prefix_message_envelope_tendsto :
    Tendsto (fun n : ℕ => 12*prefixHorizon n/prefixD n) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [prefix_message_envelope_small zero_lt_one] with n hn
    exact ha.trans_le hn.1
  · intro b hb
    filter_upwards [prefix_message_envelope_small (show 0 < b/2 by linarith)] with n hn
    exact hn.2.trans_lt (by linarith)

theorem goodPrefix_cavity_stability {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ e : G, |cavityLimit (activeHypergraph G) e none t /
            cavityReference (prefixD n) t - 1| ≤ ε) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          |cavityLimit (activeHypergraph G) e (some T) t /
            cavityReference (prefixD n) t - 1| ≤ ε) := by
  obtain ⟨a,ha,hrel⟩ := goodPrefix_cavity_relative hc
  have hδ := (tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlo : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ)^(-a)/2)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp (hδ.neg.div_const 2)
  have hexp : Tendsto (fun n : ℕ => Real.exp ((n : ℝ)^(-a)/2)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp (hδ.div_const 2)
  have hden : Tendsto (fun n : ℕ => 1-12*prefixHorizon n/prefixD n) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub prefix_message_envelope_tendsto
  have hhi : Tendsto (fun n : ℕ => Real.exp ((n : ℝ)^(-a)/2)/
      (1-12*prefixHorizon n/prefixD n)) atTop (𝓝 1) := by
    simpa only [Pi.div_def,div_one] using hexp.div hden one_ne_zero
  filter_upwards [hrel,hlo.eventually_const_le (by linarith : 1-ε < 1),
    hhi.eventually_le_const (by linarith : 1 < 1+ε),
    hexp.eventually_le_const (by linarith : 1 < 1+ε)] with n hrel hlo hhi hexp
  intro C G h t ht
  obtain ⟨hroot,hparent⟩ := hrel.2 C G h t ht
  constructor
  · intro e
    apply abs_le.mpr
    obtain ⟨he1,he2⟩ := hroot e
    constructor <;> linarith
  · intro e T he
    obtain ⟨_,he1,he2⟩ := hparent e T he
    apply abs_le.mpr
    constructor <;> linarith

end SharpTerminalLeave

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_CavityWeight
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma cavityReference_sq {D t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t) :
    cavityReference D t ^ 2 = cavityWeight D t := by
  have hx : 0 ≤ 1+2*D*t := by positivity
  unfold cavityReference cavityWeight
  rw [← Real.rpow_mul_natCast hx]
  norm_num [Real.rpow_neg_one]

lemma cavityWeight_pos {D t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t) :
    0 < cavityWeight D t := by unfold cavityWeight; positivity

lemma cavityWeight_lower {D t : ℝ} (hD : 0 ≤ D) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cavityWeight D 1 ≤ cavityWeight D t := by
  unfold cavityWeight
  have ht0 := ht.1
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [ht.2]

theorem goodPrefix_continuous_rows {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < prefixD n ∧
      ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          messageIntegral (activeHypergraph G) (cavityLimit (activeHypergraph G)) e T t ≤ 1/16) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          (∏ f ∈ (activeHypergraph G T).erase e,
            cavityLimit (activeHypergraph G) f (some T) t) ≤
              (17/16 : ℝ)*cavityWeight (prefixD n) t) := by
  obtain ⟨a,ha,hrel⟩ := goodPrefix_cavity_relative hc
  filter_upwards [goodPrefix_cavity_stability hc (by norm_num : (0 : ℝ) < 1/64),
    hrel,prefix_message_envelope_small (by norm_num : (0 : ℝ) < 1/16),
    prefix_scales_eventually_pos] with n hs hr hi hp
  have hD : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  refine ⟨hD,?_⟩
  intro C G h t ht
  refine ⟨fun e T he => ((hr.2 C G h t ht).2 e T he).1.trans hi.2,?_⟩
  intro e T he
  have hcard : ((activeHypergraph G T).erase e).card = 2 := by
    rw [Finset.card_erase_of_mem he,activeHypergraph_card]
  have href := cavityReference_pos hD ht.1
  have hprod : (∏ f ∈ (activeHypergraph G T).erase e,
      cavityLimit (activeHypergraph G) f (some T) t) ≤
      ((65/64 : ℝ)*cavityReference (prefixD n) t)^2 := by
    calc
      _ ≤ ∏ _f ∈ (activeHypergraph G T).erase e,
          (65/64 : ℝ)*cavityReference (prefixD n) t := by
        apply Finset.prod_le_prod
        · intro f _; exact (cavityLimit_mem_unit _ _ _ _).1
        · intro f hf
          have hh := (abs_le.mp ((hs C G h t ht).2 f T (Finset.mem_of_mem_erase hf))).2
          apply (div_le_iff₀ href).mp
          linarith
      _ = _ := by simp [hcard]
  calc
    _ ≤ ((65/64 : ℝ)*cavityReference (prefixD n) t)^2 := hprod
    _ = (65/64 : ℝ)^2*cavityWeight (prefixD n) t := by
      rw [mul_pow,cavityReference_sq hD.le ht.1]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (cavityWeight_pos hD.le ht.1).le

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_ActiveCavityFactorProduct
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma active_cavity_factor_product {n : ℕ} (G : Graph n) (e : G) (T : triangles G) (t : ℝ) :
    (∏ f ∈ (triangleHypergraph G T.val).erase e.val,
      cavityLimit (triangleHypergraph G) f (some T.val) t) =
    ∏ f ∈ (activeHypergraph G T).erase e, cavityLimit (activeHypergraph G) f (some T) t := by
  change (∏ f ∈ (triangleHypergraph G (triangleEmbedding G T)).erase (edgeEmbedding G e), _) = _
  rw [triangleHypergraph_reindex,← Finset.map_erase,Finset.prod_map]
  apply Finset.prod_congr rfl
  intro f _
  exact active_cavity_eq G f (some T) t

lemma active_messageIntegral {n : ℕ} (G : Graph n) (e : G) (T : triangles G) (t : ℝ) :
    messageIntegral (triangleHypergraph G) (cavityLimit (triangleHypergraph G)) e.val T.val t =
    messageIntegral (activeHypergraph G) (cavityLimit (activeHypergraph G)) e T t := by
  unfold messageIntegral
  apply intervalIntegral.integral_congr
  intro s _
  exact active_cavity_factor_product G e T s

lemma goodPrefix_full_continuous_rows {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < prefixD n ∧
      ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ (e T : Finset (Fin n)), e ∈ triangleHypergraph G T →
        messageIntegral (triangleHypergraph G) (cavityLimit (triangleHypergraph G)) e T t ≤ 1/16 ∧
        (∏ f ∈ (triangleHypergraph G T).erase e,
          cavityLimit (triangleHypergraph G) f (some T) t) ≤
          (17/16 : ℝ)*cavityWeight (prefixD n) t := by
  filter_upwards [goodPrefix_continuous_rows hc] with n hn
  refine ⟨hn.1,?_⟩
  intro C G hG t ht e T he
  have heG := triangleHypergraph_subset G T he
  have hT : T ∈ triangles G := by
    by_contra hT
    simp only [triangleHypergraph,hT,ite_false,Finset.notMem_empty] at he
  let ee : G := ⟨e,heG⟩
  let TT : triangles G := ⟨T,hT⟩
  have heact : ee ∈ activeHypergraph G TT := by
    have hh : edgeEmbedding G ee ∈ (activeHypergraph G TT).map (edgeEmbedding G) := by
      rw [← triangleHypergraph_reindex]
      exact he
    exact Finset.mem_map.mp hh |>.elim (fun _ ha => (edgeEmbedding G).injective ha.2 ▸ ha.1)
  obtain ⟨h1,h2⟩ := hn.2 C G hG t ht
  rw [show e = ee.val from rfl,show T = TT.val from rfl,
    active_messageIntegral,active_cavity_factor_product]
  exact ⟨h1 ee TT heact,h2 ee TT heact⟩

theorem goodPrefix_full_grid_rows {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
        GridRowQuality (triangleHypergraph G) N
          (fun k => cavityWeight (prefixD n) ((k : ℝ)/N)) := by
  filter_upwards [goodPrefix_full_continuous_rows hc] with n hn
  intro C G h
  let H := triangleHypergraph G
  let A : ℝ := (Fintype.card (Finset (Fin n)) : ℝ)*gridUniformError H +
    (Fintype.card (Finset (Fin n)) : ℝ)*Fintype.card (Finset (Fin n))
  let B : ℝ := 2*gridUniformError H
  have hA : Tendsto (fun N : ℕ => A/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hB : Tendsto (fun N : ℕ => B/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall : ∀ᶠ N : ℕ in atTop, A/(N : ℝ) ≤ 1/16 ∧
      B/(N : ℝ) ≤ cavityWeight (prefixD n) 1/16 := by
    filter_upwards [hA.eventually_le_const (by norm_num : (0 : ℝ) < 1/16),
      hB.eventually_le_const (show 0 < cavityWeight (prefixD n) 1/16 from
        div_pos (cavityWeight_pos hn.1.le zero_le_one) (by norm_num))]
      with N ha hb
    exact ⟨ha,hb⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hsmall
  refine ⟨N₀,?_⟩
  intro N _ hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ht (k : ℕ) (hk : k ≤ N) : (k : ℝ)/N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one hNpos).mpr (by exact_mod_cast hk)⟩
  obtain ⟨ha,hb⟩ := hN₀ N hN
  constructor
  · intro k hk e T he
    obtain ⟨hi,_⟩ := hn.2 C G h _ (ht k hk) e T he
    have herr := gridCandidateFailure_error H N k hk e T
    change |gridCandidateFailure H N k e T - _| ≤ A/(N : ℝ) at herr
    have hh := (abs_le.mp herr).1
    dsimp only [H] at hh
    linarith
  · intro k hk e T he
    obtain ⟨_,hp⟩ := hn.2 C G h _ (ht k hk) e T he
    have hT : T ∈ triangles G := by
      by_contra hh
      simp only [triangleHypergraph,hh,ite_false,Finset.notMem_empty] at he
    have hcard : ((H T).erase e).card = 2 := by
      rw [Finset.card_erase_of_mem he]
      simp only [triangleHypergraph,hT,ite_true,Finset.card_powersetCard,(mem_triangles.mp hT).1]
      decide
    have herr := gridAnswer_uniform_error H N k hk ((H T).erase e) (some T)
    rw [hcard] at herr
    have herr' := (abs_le.mp herr).2
    have hbl := cavityWeight_lower hn.1.le (ht k hk)
    dsimp only [B,H] at hb herr'
    linarith

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_CavityWeightLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
open Filter MeasureTheory
open scoped BigOperators Topology

lemma cavityWeight_integral {D : ℝ} (hD : 0 < D) :
    (∫ t in (0 : ℝ)..1, cavityWeight D (unitTime t)) = witnessMu D := by
  have hc : 2*D ≠ 0 := by positivity
  have he : (∫ t in (0 : ℝ)..1, cavityWeight D (unitTime t)) =
      ∫ t in (0 : ℝ)..1, 1/(1+(2*D)*t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [unitTime_of_mem ht,cavityWeight]
  rw [he,intervalIntegral.integral_comp_add_mul (fun x : ℝ => 1/x) hc 1]
  simp only [mul_zero,add_zero,mul_one,smul_eq_mul]
  rw [integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < 1+2*D)]
  simp only [div_one,witnessMu]
  ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_ContinuousCavityWeightClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma continuous_cavityWeight_clip {D : ℝ} (hD : 0 ≤ D) :
    Continuous (fun t => cavityWeight D (unitTime t)) := by
  unfold cavityWeight
  apply continuous_const.div
    (continuous_const.add ((continuous_const.mul continuous_const).mul continuous_unitTime))
  intro t
  have ht := unitTime_nonneg t
  apply ne_of_gt
  change 0 < 1+2*D*unitTime t
  have hh : 0 ≤ 2*D*unitTime t := mul_nonneg (mul_nonneg (by norm_num) hD) ht
  linarith

lemma cavityWeight_lipschitz_cell {D x y : ℝ} (hD : 0 ≤ D)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |cavityWeight D x - cavityWeight D y| ≤ (2*D)*|x-y| := by
  have ha : 1 ≤ 1+2*D*x := le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hD) hx)
  have hb : 1 ≤ 1+2*D*y := le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hD) hy)
  have ha0 : 0 < 1+2*D*x := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < 1+2*D*y := lt_of_lt_of_le zero_lt_one hb
  have hid : 1/(1+2*D*x)-1/(1+2*D*y) =
      (2*D*(y-x))/((1+2*D*x)*(1+2*D*y)) := by
    field_simp
    ring
  unfold cavityWeight
  rw [hid,abs_div,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*D),
    abs_of_pos (mul_pos ha0 hb0),abs_sub_comm y x]
  exact div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le ha hb)

theorem grid_prefixWeight_tendsto {D : ℝ} (hD : 0 < D) :
    Tendsto (fun j : ℕ =>
      prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1))
      atTop (𝓝 (2*witnessMu D)) := by
  have hquad (j : ℕ) :
      |prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1) -
        2*witnessMu D| ≤ 4*D/((j+1 : ℕ) : ℝ) := by
    have hN : 0 < j+1 := Nat.succ_pos j
    have hNr : (0 : ℝ) < (j+1 : ℕ) := by exact_mod_cast hN
    have hh := uniform_grid_quadrature (fun t => cavityWeight D (unitTime t))
      (continuous_cavityWeight_clip hD.le) (show 0 ≤ 2*D by positivity)
      (fun x hx y hy => by
        rw [unitTime_of_mem hx,unitTime_of_mem hy]
        exact cavityWeight_lipschitz_cell hD.le hx.1 hy.1) (j+1) (j+1) hN le_rfl
    rw [div_self (ne_of_gt hNr),cavityWeight_integral hD] at hh
    have heq : (∑ t ∈ Finset.range (j+1), cavityWeight D (unitTime ((t : ℝ)/(j+1 : ℕ)))) =
        ∑ t ∈ Finset.range (j+1), cavityWeight D ((t : ℝ)/(j+1 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [unitTime_of_mem ⟨by positivity,(div_le_one hNr).mpr
        (by exact_mod_cast (Finset.mem_range.mp ht).le)⟩]
    rw [heq] at hh
    have hb := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ = 2*|witnessMu D - (1/((j+1 : ℕ) : ℝ))*
          ∑ t ∈ Finset.range (j+1), cavityWeight D ((t : ℝ)/(j+1 : ℕ))| := by
        unfold prefixWeight
        rw [← Finset.mul_sum]
        rw [show (2 : ℝ) = |(2 : ℝ)| by norm_num, ← abs_mul, ← abs_neg]
        congr 1
        ring
      _ ≤ _ := by
        calc
          _ ≤ 2*(2*D/((j+1 : ℕ) : ℝ)) := hb
          _ = _ := by ring
  have hden : Tendsto (fun j : ℕ => (4*D)/((j+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hh := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (4*D)
    simpa only [Nat.cast_add,Nat.cast_one,mul_comm,one_div,div_eq_mul_inv,one_mul,zero_mul] using hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun j => by rw [Real.norm_eq_abs]; exact hquad j) hden

lemma collision_exponential_identity {D : ℝ} (hD : 0 < D) :
    (1+2*D)^3*Real.exp (45*D*(2*witnessMu D)) = (1+2*D)^48 := by
  have he : 45*D*(2*witnessMu D) = 45*Real.log (1+2*D) := by
    unfold witnessMu
    field_simp
  rw [he,show (45 : ℝ) = (45 : ℕ) by norm_num,Real.exp_nat_mul,
    Real.exp_log (by linarith : 0 < 1+2*D),← pow_add]

lemma collision_power_48_bound {D : ℝ} (hD : 1 ≤ D) :
    (1+2*D)^48/D^50 ≤ (3 : ℝ)^48/D^2 := by
  have hpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hh := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : 0 ≤ 1+2*D) (by linarith : 1+2*D ≤ 3*D) 48)
    (by positivity : 0 ≤ D^50)
  apply hh.trans_eq
  rw [mul_pow,show 50 = 48+2 by norm_num,pow_add]
  field_simp

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_GridCavityWeightLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma grid_cavityWeight_lower {D : ℝ} (hD : 0 ≤ D) (N : ℕ) [NeZero N] :
    ∀ t ≤ N, 1 ≤ (1+2*D)*cavityWeight D ((t : ℝ)/N) := by
  intro t ht
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hmem : (t : ℝ)/N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one hNr).mpr (by exact_mod_cast ht)⟩
  have hh := mul_le_mul_of_nonneg_left (cavityWeight_lower hD hmem)
    (show 0 ≤ 1+2*D by positivity)
  have heq : (1+2*D)*cavityWeight D 1 = 1 := by
    unfold cavityWeight
    rw [mul_one,mul_one_div_cancel (by positivity : 1+2*D ≠ 0)]
  rwa [heq] at hh

lemma grid_collision_majorant_tendsto (K : ℝ) {D : ℝ} (hD : 0 < D) :
    Tendsto (fun j : ℕ => (K*(1+2*D)^3/D^50)*
      Real.exp (45*D*prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*
        cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1)))
      atTop (𝓝 (K*(1+2*D)^48/D^50)) := by
  have hh := (Real.continuous_exp.continuousAt.tendsto.comp
    ((grid_prefixWeight_tendsto hD).const_mul (45*D))).const_mul
    (K*(1+2*D)^3/D^50)
  have he : (K*(1+2*D)^3/D^50)*Real.exp (45*D*(2*witnessMu D)) =
      K*(1+2*D)^48/D^50 := by
    calc
      _ = K*((1+2*D)^3*Real.exp (45*D*(2*witnessMu D)))/D^50 := by ring
      _ = _ := by rw [collision_exponential_identity hD]
  rwa [he] at hh

theorem averaged_disjoint_collisionCost (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ hne : G.Nonempty,
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if Disjoint e f then
        collisionCost (triangleHypergraph G) {e,f} none else 0)) ≤
      65536*(1+2*prefixD n)^48/prefixD n^50 := by
  classical
  filter_upwards [averaged_disjoint_grid_collision c₀ C₀ hc₀,
    goodPrefix_full_grid_rows hc₀,goodPrefix_full_continuous_rows hc₀] with n hfinite hrows hn
  intro G hGood hne
  let D := prefixD n
  let P := PMF.uniformOfFinset G hne
  let PP := P.bind (fun e => P.map (Prod.mk e))
  let f : (Finset (Fin n) × Finset (Fin n)) → ℕ → ℝ := fun ef j =>
    if Disjoint ef.1 ef.2 then gridCollision (triangleHypergraph G) {ef.1,ef.2} none j else 0
  let g : ℕ → ℝ := fun j => (65536*(1+2*D)^3/D^50)*
    Real.exp (45*D*prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*
      cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1))
  have hbound (ef : Finset (Fin n) × Finset (Fin n)) (j : ℕ) : 0 ≤ f ef j := by
    dsimp only [f]
    split_ifs <;> first | exact (gridCollision_mem_unit _ _ _ _).1 | rfl
  obtain ⟨N₀,hN₀⟩ := hrows C₀ G hGood
  have hupper : ∀ᶠ j : ℕ in atTop, pmfMean PP (fun ef => f ef j) ≤ g j := by
    filter_upwards [eventually_ge_atTop N₀] with j hj
    dsimp only [PP]
    rw [pmfMean_bind]
    simp_rw [pmfMean_map]
    have hh := hfinite G hGood hne (j+1)
      (fun t => cavityWeight D ((t : ℝ)/(j+1 : ℕ)))
      (fun t => (cavityWeight_pos hn.1.le (by positivity)).le)
      (hN₀ (j+1) (by omega)) (1+2*D)
      (by dsimp only [D]; linarith [hn.1]) (grid_cavityWeight_lower hn.1.le (j+1))
      (j+1) (j+1) le_rfl le_rfl
    simpa only [gridCollision_eq_trace,P,f,g,D] using hh
  have hh := pmfMean_liminf_le_of_tendsto_upper PP f hbound g
    (grid_collision_majorant_tendsto 65536 hn.1) hupper
  dsimp only [PP] at hh
  rw [pmfMean_bind] at hh
  simp_rw [pmfMean_map] at hh
  have hf (e f' : Finset (Fin n)) : Filter.liminf (f (e,f')) atTop =
      if Disjoint e f' then collisionCost (triangleHypergraph G) {e,f'} none else 0 := by
    by_cases hd : Disjoint e f'
    · simp only [f,hd,ite_true,collisionCost]
    · simp only [f,hd,ite_false,Filter.liminf_const]
  simp_rw [hf] at hh
  exact hh

theorem averaged_singleton_collisionCost (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ hne : G.Nonempty,
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        collisionCost (triangleHypergraph G) {e} none) ≤
      8192*(1+2*prefixD n)^48/prefixD n^50 := by
  classical
  filter_upwards [averaged_singleton_grid_collision c₀ C₀ hc₀,
    goodPrefix_full_grid_rows hc₀,goodPrefix_full_continuous_rows hc₀] with n hfinite hrows hn
  intro G hGood hne
  let D := prefixD n
  let P := PMF.uniformOfFinset G hne
  let f : Finset (Fin n) → ℕ → ℝ := fun e j => gridCollision (triangleHypergraph G) {e} none j
  let g : ℕ → ℝ := fun j => (8192*(1+2*D)^3/D^50)*
    Real.exp (45*D*prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*
      cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1))
  have hbound (e : Finset (Fin n)) (j : ℕ) : 0 ≤ f e j :=
    (gridCollision_mem_unit _ _ _ _).1
  obtain ⟨N₀,hN₀⟩ := hrows C₀ G hGood
  have hupper : ∀ᶠ j : ℕ in atTop, pmfMean P (fun e => f e j) ≤ g j := by
    filter_upwards [eventually_ge_atTop N₀] with j hj
    have hh := hfinite G hGood hne (j+1)
      (fun t => cavityWeight D ((t : ℝ)/(j+1 : ℕ)))
      (fun t => (cavityWeight_pos hn.1.le (by positivity)).le)
      (hN₀ (j+1) (by omega)) (1+2*D)
      (by dsimp only [D]; linarith [hn.1]) (grid_cavityWeight_lower hn.1.le (j+1))
      (j+1) (j+1) le_rfl le_rfl
    simpa only [gridCollision_eq_trace,P,f,g,D] using hh
  exact pmfMean_liminf_le_of_tendsto_upper P f hbound g
    (grid_collision_majorant_tendsto 8192 hn.1) hupper

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_GoodPrefixSurvivalMoments
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem goodPrefix_survival_moments (c C : ℝ) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c C G →
    ∀ hne : G.Nonempty,
      (|pmfMean (PMF.uniformOfFinset G hne) (fun e => focusSurvival G {e})-
        cavityReference (prefixD n) 1| ≤
          8192*(1+2*prefixD n)^48/prefixD n^50+ε*cavityReference (prefixD n) 1) ∧
      (|pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        pmfMean (PMF.uniformOfFinset G hne) (fun f => focusSurvival G {e,f}))-
          (cavityReference (prefixD n) 1)^2| ≤
        65536*(1+2*prefixD n)^48/prefixD n^50+8/(n : ℝ)+
          (2*ε+ε^2)*(cavityReference (prefixD n) 1)^2) := by
  filter_upwards [goodPrefix_cavity_stability hc hε,
    averaged_singleton_collisionCost c C hc,averaged_disjoint_collisionCost c C hc,
    goodPrefix_rootOverlap hc,goodPrefix_full_continuous_rows hc] with n hrel hsingle hpair hover hpos
  intro G hG hne
  have hr := (hrel C G hG 1 ⟨by norm_num,le_rfl⟩).1
  constructor
  · exact (averaged_singleton_survival_error G hne (prefixD n) ε hpos.1 hr).trans
      (add_le_add (hsingle G hG hne) le_rfl)
  · exact (averaged_pair_survival_error G hne hG.1 (prefixD n) ε hpos.1 hε.le hr).trans
      (add_le_add (add_le_add (hpair G hG hne) (hover C G hG hne)) le_rfl)

lemma focusSurvival_singleton_mean {n : ℕ} (G : Graph n) (e : Finset (Fin n)) :
    focusSurvival G {e} = pmfMean (finish G) (fun H => if e ∈ H then 1 else 0) := by
  classical
  unfold focusSurvival
  rw [trueProbability_map]
  simp only [Finset.singleton_subset_iff,decide_eq_true_eq,pmfMean]

lemma focusSurvival_pair_mean {n : ℕ} (G : Graph n) (e f : Finset (Fin n)) :
    focusSurvival G {e,f} = pmfMean (finish G) (fun H => if e ∈ H ∧ f ∈ H then 1 else 0) := by
  classical
  unfold focusSurvival
  rw [trueProbability_map]
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,decide_eq_true_eq,pmfMean]

theorem terminal_first_focus_moment {n : ℕ} (G : Graph n) (hne : G.Nonempty) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e => focusSurvival G {e}) =
      pmfMean (finish G) (fun H => (H.card : ℝ))/(G.card : ℝ) := by
  simp_rw [focusSurvival_singleton_mean]
  rw [pmfMean_swap]
  exact terminal_first_edge_moment G hne

theorem terminal_second_focus_moment {n : ℕ} (G : Graph n) (hne : G.Nonempty) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => focusSurvival G {e,f})) =
      pmfMean (finish G) (fun H => (H.card : ℝ)^2)/(G.card : ℝ)^2 := by
  simp_rw [focusSurvival_pair_mean]
  calc
    _ = pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        pmfMean (finish G) (fun H =>
          pmfMean (PMF.uniformOfFinset G hne) (fun f =>
            if e ∈ H ∧ f ∈ H then 1 else 0))) := by
      apply congrArg
      funext e
      exact pmfMean_swap _ _ _
    _ = pmfMean (finish G) (fun H =>
        pmfMean (PMF.uniformOfFinset G hne) (fun e =>
          pmfMean (PMF.uniformOfFinset G hne) (fun f =>
            if e ∈ H ∧ f ∈ H then 1 else 0))) := pmfMean_swap _ _ _
    _ = _ := terminal_second_edge_moment G hne

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixDTendstoTop
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma prefixD_tendsto_atTop : Tendsto prefixD atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (show ∀ᶠ n : ℕ in atTop, (n : ℝ)^(1/1000 : ℝ) ≤ prefixD n from
      prefixD_eventual_envelope.mono (fun _ h => h.1))
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/1000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixD_inv_tendsto : Tendsto (fun n => 1/prefixD n) atTop (𝓝 (0 : ℝ)) := by
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp prefixD_tendsto_atTop

lemma prefixD_div_n_tendsto : Tendsto (fun n => prefixD n/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hupper : ∀ᶠ n : ℕ in atTop,
      0 ≤ prefixD n/(n : ℝ) ∧ prefixD n/(n : ℝ) ≤ 4*(n : ℝ)^(-(999/1000 : ℝ)) := by
    filter_upwards [prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hn hp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hp
    have hp0 : 0 ≤ prefixD n := le_trans (Real.rpow_nonneg (Nat.cast_nonneg n) _) hn.1
    refine ⟨div_nonneg hp0 hn0.le,?_⟩
    calc
      _ ≤ (4*(n : ℝ)^(1/1000 : ℝ))/(n : ℝ) := div_le_div_of_nonneg_right hn.2 hn0.le
      _ = _ := by
        have hid : (n : ℝ)^(1/1000 : ℝ)/(n : ℝ) =
            (n : ℝ)^(-(999/1000 : ℝ)) := by
          conv_lhs => rhs; rw [← Real.rpow_one (n : ℝ)]
          rw [← Real.rpow_sub hn0]
          norm_num
        rw [mul_div_assoc,hid]
  have hl := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999/1000)).comp
    tendsto_natCast_atTop_atTop).const_mul 4
  exact squeeze_zero' (hupper.mono (fun _ h => h.1)) (hupper.mono (fun _ h => h.2))
    (by simpa using hl)

theorem goodPrefix_relative_l2_bound (c C : ℝ) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c C G →
      pmfMean (finish G) (fun H =>
        ((H.card : ℝ)/((G.card : ℝ)*cavityReference (prefixD n) 1)-1)^2) ≤
      (81920*(3 : ℝ)^49)/prefixD n+8/(n : ℝ)+16*(prefixD n/(n : ℝ))+
        (4*ε+ε^2) := by
  filter_upwards [goodPrefix_survival_moments c C hc hε,
    prefixD_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hm hD hsc hn
  intro G hG
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hD
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : 0 < (G.card : ℝ) := by
    rw [hG.2.1]
    unfold prefixM
    have := hsc.1
    positivity
  have hne : G.Nonempty := Finset.card_pos.mp (by exact_mod_cast hm0)
  obtain ⟨h1,h2⟩ := hm G hG hne
  rw [terminal_first_focus_moment] at h1
  rw [terminal_second_focus_moment] at h2
  let q := cavityReference (prefixD n) 1
  let A := (1+2*prefixD n)^48/prefixD n^50
  have hq : 0 < q := cavityReference_pos hD0 (by norm_num)
  have hq1 : q ≤ 1 := cavityReference_le_one hD0 (by norm_num)
  have hq2 : q^2 = 1/(1+2*prefixD n) := by
    dsimp only [q]
    rw [cavityReference_sq hD0.le (by norm_num)]
    simp only [cavityWeight,mul_one]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAbound : A ≤ (3 : ℝ)^48/prefixD n^2 := collision_power_48_bound hD
  have h1' : |pmfMean (finish G) (fun H => (H.card : ℝ))/(G.card : ℝ)-q| ≤
      8192*A+ε*q := by simpa only [A,q,mul_div_assoc] using h1
  have h2' : |pmfMean (finish G) (fun H => (H.card : ℝ)^2)/(G.card : ℝ)^2-q^2| ≤
      65536*A+8/(n : ℝ)+(2*ε+ε^2)*q^2 := by
    simpa only [A,q,mul_div_assoc] using h2
  have heq : pmfMean (finish G) (fun H =>
      ((H.card : ℝ)/((G.card : ℝ)*q)-1)^2) =
      (pmfMean (finish G) (fun H => (H.card : ℝ)^2)/(G.card : ℝ)^2-q^2)/q^2 -
      2*(pmfMean (finish G) (fun H => (H.card : ℝ))/(G.card : ℝ)-q)/q := by
    rw [pmfMean_sq_sub]
    simp_rw [div_pow,div_eq_mul_inv,pmfMean_mul_const]
    field_simp
    ring
  have hb : pmfMean (finish G) (fun H =>
      ((H.card : ℝ)/((G.card : ℝ)*q)-1)^2) ≤
      (81920*A+8/(n : ℝ))/q^2+(4*ε+ε^2) := by
    rw [heq]
    have hfirst := (abs_le.mp h1').1
    have hsecond := (abs_le.mp h2').2
    have haux : (2*(8192*A+ε*q))/q ≤ (16384*A)/q^2+2*ε := by
      calc
        _ = 16384*A/q+2*ε := by field_simp; ring
        _ ≤ _ := add_le_add
          (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hq)
            (by nlinarith : q^2 ≤ q)) le_rfl
    have hlinear : -2*(pmfMean (finish G) (fun H => (H.card : ℝ))/(G.card : ℝ)-q)/q ≤
        (2*(8192*A+ε*q))/q :=
      div_le_div_of_nonneg_right (by linarith) hq.le
    calc
      _ ≤ (65536*A+8/(n : ℝ)+(2*ε+ε^2)*q^2)/q^2 +
          (2*(8192*A+ε*q))/q := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right hsecond (sq_nonneg q)
        · simpa only [neg_mul,neg_div] using hlinear
      _ ≤ (65536*A+8/(n : ℝ)+(2*ε+ε^2)*q^2)/q^2+
          ((16384*A)/q^2+2*ε) := add_le_add le_rfl haux
      _ = _ := by field_simp; ring
  apply hb.trans
  rw [hq2]
  have hDA : (81920*A)*(1+2*prefixD n) ≤ (81920*(3 : ℝ)^49)/prefixD n := by
    calc
      _ ≤ (81920*((3 : ℝ)^48/prefixD n^2))*(3*prefixD n) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAbound (by norm_num))
          (by linarith) (by positivity) (by positivity)
      _ = _ := by rw [show 49 = 48+1 by norm_num,pow_add,pow_one]; field_simp
  have hraw : (81920*A+8/(n : ℝ))/(1/(1+2*prefixD n)) =
      (81920*A)*(1+2*prefixD n)+8/(n : ℝ)+16*(prefixD n/(n : ℝ)) := by
    field_simp
    ring
  rw [hraw]
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_ContinuationCollisionRemainderTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma continuation_collision_remainder_tendsto :
    Tendsto (fun n : ℕ => (81920*(3 : ℝ)^49)/prefixD n+8/(n : ℝ)+
      16*(prefixD n/(n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  have h1 := prefixD_inv_tendsto.const_mul (81920*(3 : ℝ)^49)
  have h2 := tendsto_one_div_atTop_nhds_zero_nat.const_mul (8 : ℝ)
  have h3 := prefixD_div_n_tendsto.const_mul (16 : ℝ)
  simpa only [mul_one_div,add_zero,mul_zero] using (h1.add h2).add h3

theorem goodPrefix_relative_l2 (c C : ℝ) (hc : 0 < c) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ (G : Graph n), GoodPrefixGraph n c C G →
        pmfMean (finish G) (fun H =>
          ((H.card : ℝ)/((G.card : ℝ)*cavityReference (prefixD n) 1)-1)^2) < δ := by
  intro δ hδ
  let ε := min (δ/10) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεδ : ε ≤ δ/10 := min_le_left _ _
  have hsmall : 4*ε+ε^2 ≤ δ/2 := by nlinarith [sq_nonneg ε]
  filter_upwards [goodPrefix_relative_l2_bound c C hc hε,
    continuation_collision_remainder_tendsto.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ/2))]
      with n hbound hrem
  intro G hG
  exact (hbound G hG).trans_lt (by linarith)

lemma normalization_sq (n : ℕ) : normalization n ^ 2 = (n : ℝ)^3 := by
  unfold normalization
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

lemma normalization_pos {n : ℕ} (hn : 0 < n) : 0 < normalization n := by
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

lemma sharpConstant_pos : 0 < sharpConstant := by
  unfold sharpConstant
  positivity

lemma sharpConstant_sq : sharpConstant^2 = (1/8 : ℝ) := by
  unfold sharpConstant
  rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem prefix_terminal_scale_tendsto :
    Tendsto (fun n => prefixM n*cavityReference (prefixD n) 1/normalization n)
      atTop (𝓝 sharpConstant) := by
  have hinv : Tendsto (fun n => 1 / (4*(1/prefixD n+2))) atTop (𝓝 (1/8 : ℝ)) := by
    have hh := (prefixD_inv_tendsto.add_const (2 : ℝ)).const_mul (4 : ℝ)
    have hh' := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div
      hh (by norm_num : (4*((0 : ℝ)+2)) ≠ 0)
    change Tendsto (fun n => 1/(4*(1/prefixD n+2))) atTop (𝓝 (1/(4*((0 : ℝ)+2)))) at hh'
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hsq : ∀ᶠ n : ℕ in atTop,
      (prefixM n*cavityReference (prefixD n) 1/normalization n)^2 =
        1 / (4*(1/prefixD n+2)) := by
    filter_upwards [prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hp hn
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    have hD0 : 0 < prefixD n := by linarith [hp.2]
    rw [div_pow,mul_pow,normalization_sq,cavityReference_sq hD0.le (by norm_num)]
    simp only [cavityWeight,mul_one]
    unfold prefixM prefixD
    have hp0 := hp.1
    field_simp
    ring
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 ≤ prefixM n*cavityReference (prefixD n) 1/normalization n := by
    filter_upwards [prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hp hn
    have hn0 : 0 < n := by omega
    have hm0 : 0 < prefixM n := by unfold prefixM; have := hp.1; positivity
    have hq0 : 0 < cavityReference (prefixD n) 1 := cavityReference_pos (by linarith [hp.2]) (by norm_num)
    exact (div_pos (mul_pos hm0 hq0) (normalization_pos hn0)).le
  have hl := Real.continuous_sqrt.continuousAt.tendsto.comp hinv
  have hroot : Real.sqrt (1/8 : ℝ) = sharpConstant := by
    rw [← sharpConstant_sq,Real.sqrt_sq sharpConstant_pos.le]
  rw [hroot] at hl
  apply hl.congr'
  filter_upwards [hsq,hpos] with n he hp
  dsimp only [Function.comp_def]
  rw [← he,Real.sqrt_sq hp]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_PmfMeanAffineSq
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma pmfMean_affine_sq_bound {α : Type*} [Fintype α] (P : PMF α)
    (f : α → ℝ) (a b : ℝ) :
    pmfMean P (fun x => (a*f x+b)^2) ≤ 2*a^2*pmfMean P (fun x => (f x)^2)+2*b^2 := by
  calc
    _ ≤ pmfMean P (fun x => (2*a^2)*(f x)^2+2*b^2) := by
      apply pmfMean_mono
      intro x _
      nlinarith [sq_nonneg (a*f x-b)]
    _ = _ := by rw [pmfMean_add,pmfMean_const_mul,pmfMean_const]

theorem goodPrefix_normalized_l2 (c C : ℝ) (hc : 0 < c) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ (G : Graph n), GoodPrefixGraph n c C G →
        pmfMean (finish G) (fun H => (normalizedLeave n H-sharpConstant)^2) < δ := by
  intro δ hδ
  let s : ℕ → ℝ := fun n => prefixM n*cavityReference (prefixD n) 1/normalization n
  have hs : Tendsto s atTop (𝓝 sharpConstant) := prefix_terminal_scale_tendsto
  have hs2 : ∀ᶠ n : ℕ in atTop, s n ^ 2 ≤ 1 := by
    have hh := hs.pow 2
    rw [sharpConstant_sq] at hh
    exact (hh.eventually (gt_mem_nhds (by norm_num : (1/8 : ℝ) < 1))).mono (fun _ h => h.le)
  have hbias : Tendsto (fun n => 2*(s n-sharpConstant)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((hs.sub_const sharpConstant).pow 2).const_mul (2 : ℝ)
  filter_upwards [goodPrefix_relative_l2 c C hc (δ/4) (by positivity),hs2,
    hbias.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ/2)),
    prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hr hsqr hb hp hn
  intro G hG
  have hn0 : 0 < n := by omega
  have hnorm : 0 < normalization n := normalization_pos hn0
  have hm0 : 0 < (G.card : ℝ) := by rw [hG.2.1]; unfold prefixM; have := hp.1; positivity
  have hq : 0 < cavityReference (prefixD n) 1 :=
    cavityReference_pos (by linarith [hp.2]) (by norm_num)
  let f : Graph n → ℝ := fun H => (H.card : ℝ)/((G.card : ℝ)*cavityReference (prefixD n) 1)-1
  have heq : (fun H => (normalizedLeave n H-sharpConstant)^2) =
      (fun H => (s n*f H+(s n-sharpConstant))^2) := by
    funext H
    congr 1
    dsimp only [s,f,normalizedLeave]
    rw [← hG.2.1]
    field_simp [ne_of_gt hm0, ne_of_gt hq, ne_of_gt hnorm]
    ring
  have hnon : 0 ≤ pmfMean (finish G) (fun H => f H^2) := pmfMean_nonneg _ (fun _ _ => sq_nonneg _)
  rw [heq]
  calc
    _ ≤ 2*(s n)^2*pmfMean (finish G) (fun H => f H^2)+2*(s n-sharpConstant)^2 :=
      pmfMean_affine_sq_bound _ f _ _
    _ ≤ 2*pmfMean (finish G) (fun H => f H^2)+2*(s n-sharpConstant)^2 := by
      have hh := mul_le_mul_of_nonneg_right hsqr hnon
      nlinarith
    _ < δ := by have hh := hr G hG; change pmfMean (finish G) (fun H => f H^2) < δ/4 at hh; linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EvolveBindFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma evolve_bind_finish {n : ℕ} (G : Graph n) (k : ℕ) :
    (evolve G k).bind finish = finish G := by
  induction k with
  | zero => simp only [evolve,PMF.pure_bind]
  | succ k ih =>
    rw [evolve,PMF.bind_bind]
    have hh : (fun H : Graph n => (step H).bind finish) = finish := by
      funext H
      exact (finish_harmonic H).symm
    rw [hh,ih]

lemma terminalLaw_prefix_disintegration (n : ℕ) :
    terminalLaw n = (prefixLaw n).bind finish := by
  rw [prefixLaw,evolve_bind_finish]
  apply evolve_eq_finish
  simp only [completeGraph,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin,le_refl]

lemma normalizedLeave_error_envelope {n : ℕ} (hn : 0 < n) {H : Graph n}
    (hH : H ⊆ completeGraph n) :
    (normalizedLeave n H-sharpConstant)^2 ≤ 2*(n : ℝ)+1 := by
  have hcard : (H.card : ℝ) ≤ (n : ℝ)^2 := by
    have hh := (Finset.card_le_card hH).trans
      (show (completeGraph n).card ≤ n^2 by
        simpa only [completeGraph,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
          using Nat.choose_le_pow n 2)
    exact_mod_cast hh
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnorm := normalization_pos hn
  have hsq : (normalizedLeave n H)^2 ≤ (n : ℝ) := by
    unfold normalizedLeave
    rw [div_pow,normalization_sq]
    calc
      _ ≤ ((n : ℝ)^2)^2/(n : ℝ)^3 := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg H.card) hcard 2) (by positivity)
      _ = _ := by field_simp
  have ha := sharpConstant_sq
  nlinarith [sq_nonneg (normalizedLeave n H+sharpConstant)]

theorem main_l2_prefix_failure_bound_oai (c C : ℝ) (hc : 0 < c) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      expectation n (fun H => (normalizedLeave n H-sharpConstant)^2) ≤
        δ+(2*(n : ℝ)+1)*prefixFailure n c C := by
  classical
  intro δ hδ
  filter_upwards [goodPrefix_normalized_l2 c C hc δ hδ,eventually_ge_atTop (1 : ℕ)] with n hg hn
  have hn0 : 0 < n := by omega
  change pmfMean (terminalLaw n) (fun H => (normalizedLeave n H-sharpConstant)^2) ≤ _
  rw [terminalLaw_prefix_disintegration,pmfMean_bind]
  calc
    _ ≤ pmfMean (prefixLaw n) (fun G => δ+(2*(n : ℝ)+1)*
          (if GoodPrefixGraph n c C G then 0 else 1)) := by
      apply pmfMean_mono
      intro G hG
      by_cases hgood : GoodPrefixGraph n c C G
      · simp only [ite_eq_left hgood,mul_zero,add_zero]
        exact (hg G hgood).le
      · simp only [ite_eq_right hgood,mul_one]
        have hsub : G ⊆ completeGraph n := evolve_support_subset _ _ hG
        have hh : pmfMean (finish G) (fun H => (normalizedLeave n H-sharpConstant)^2) ≤
            2*(n : ℝ)+1 := by
          rw [← pmfMean_const (finish G) (2*(n : ℝ)+1)]
          apply pmfMean_mono
          intro H hH
          exact normalizedLeave_error_envelope hn0 ((finish_support_subset hH).trans hsub)
        linarith
    _ = _ := by rw [pmfMean_add,pmfMean_const,pmfMean_const_mul]; rfl

end SharpTerminalLeave

end

end OAI
end

theorem solution : type_of% @OAI.SharpTerminalLeave.main_l2_prefix_failure_bound_oai := @OAI.SharpTerminalLeave.main_l2_prefix_failure_bound_oai

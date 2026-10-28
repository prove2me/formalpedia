-- Prove2me | solution 1 for OAI.HyperbolicCoding.block_recoding_small_cost_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:15:27.215156+00:00
-- url     : https://prove2.me/submissions/ef38a814-7de2-438c-9a2c-426031fb66f7

import Mathlib
import Definitions.Def_OAIQ44C000
import Definitions.Def_OAIQ44C001

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_LiftGrid
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open Set Finset
open scoped BigOperators

lemma shannon_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) (hm : ∑ a,p a≤1) : 0 ≤ shannon p := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg (hp a) ((Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)).trans hm)

lemma shannon_bound {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) (hm : ∑ a,p a=1) : shannon p≤Real.log (Fintype.card α) := by
  have hc : 0<(Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh := shannon_le_cross p (fun _ => (Fintype.card α : ℝ)⁻¹) hp
    (fun _ => (inv_pos.mpr hc).le) (fun _ _ => inv_ne_zero hc.ne') (by simp [hm,hc.ne'])
  rw [←Finset.sum_mul,hm,one_mul,Real.log_inv,neg_neg] at hh
  exact hh

lemma matrix_super_row {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) :
    shannon (fun a => ∑ b,p a b)≤ shannon (fun ab : α×β => p ab.1 ab.2) := by
  have hh (a : α) (b : β) : -p a b*Real.log (∑ j,p a j)≤Real.negMulLog (p a b) := by
    by_cases he : p a b=0
    · simp [he]
    have hpos : 0<p a b := lt_of_le_of_ne (hp a b) (Ne.symm he)
    have hlog := Real.log_le_log hpos (matrix_le_row p hp a b)
    exact mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr (hp a b))
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hh a b))
  simp only [neg_mul,←Finset.sum_mul,Finset.sum_neg_distrib] at hs
  simpa only [shannon,Fintype.sum_prod_type,Real.negMulLog,neg_mul,Finset.sum_neg_distrib] using hs

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_ObservableEntropy
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_pair_swap (p : Ω → α) (q : Ω → β) :
    obs μ (fun x => (p x,q x))=obs μ (fun x => (q x,p x)) := by
  simp only [obs,shannon,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => congrArg Real.negMulLog (mass_joint_swap μ p q a b)))

lemma obs_pair_ge_left (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ p ≤ obs μ (fun x => (p x,q x)) := by
  have h := matrix_super_row (fun a b => mass μ (fun x => (p x,q x)) (a,b))
    (fun a b => mass_nonneg μ _ _)
  simpa only [obs,Prod.mk.eta,←mass_joint_row μ p q hp hq] using h
lemma obs_pair_ge_right (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ q ≤ obs μ (fun x => (p x,q x)) := by
  rw [obs_pair_swap]
  exact obs_pair_ge_left μ q p hq hp

omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma mass_pair_function [DecidableEq β] (p : Ω → α) (g : α → β) (a : α) (b : β) :
    mass μ (fun x => (p x,g (p x))) (a,b)=if g a=b then mass μ p a else 0 := by
  classical
  by_cases h : g a=b
  · rw [ite_eq_left h]
    unfold mass
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
    exact ⟨And.left,fun hp => ⟨hp,hp ▸ h⟩⟩
  · rw [ite_eq_right h]
    have he : ((fun x => (p x,g (p x))) ⁻¹' {(a,b)})=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ((congrArg g (Prod.mk.inj hx).1).symm.trans (Prod.mk.inj hx).2)
    simp only [mass,he,measure_empty,ENNReal.toReal_zero]
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_pair_function (p : Ω → α) (g : α → β) :
    obs μ (fun x => (p x,g (p x)))=obs μ p := by
  classical
  simp only [obs,shannon,Fintype.sum_prod_type,mass_pair_function]
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite Real.negMulLog,Real.negMulLog_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
lemma obs_factor (p : Ω → α) (g : α → β) (hp : Measurable p) (hg : Measurable (g ∘ p)) :
    obs μ (g ∘ p) ≤ obs μ p := by
  have h := obs_pair_ge_right μ p (g ∘ p) hp hg
  simpa only [Function.comp_def,obs_pair_function] using h

lemma sum_mass_mul_integral (p : Ω → α) (hp : Measurable p) (g : α → ℝ) :
    ∑ a,mass μ p a*g a=∫ x,g (p x) ∂μ := by
  classical
  have he (x : Ω) : (∑ a : α,(p ⁻¹' {a}).indicator (fun _ => g a) x)=g (p x) := by
    simp only [indicator_apply,mem_preimage,mem_singleton_iff,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [←show (fun x => ∑ a : α,(p ⁻¹' {a}).indicator (fun _ => g a) x)=(fun x => g (p x)) from funext he]
  rw [integral_finsetSum _ (fun a _ => (integrable_const _).indicator (hp (measurableSet_singleton a)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_indicator (hp (measurableSet_singleton a)),integral_const,Measure.real,Measure.restrict_apply_univ]
  rfl

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ ζ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ζ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace ζ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] [MeasurableSingletonClass ζ]

omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [Fintype γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma mass_triple_assoc (p : Ω → α) (q : Ω → β) (r : Ω → γ) (a : α) (b : β) (c : γ) :
    mass μ (fun x => (p x,(q x,r x))) (a,(b,c))=
      mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_assoc]
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma obs_triple_assoc (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    obs μ (fun x => (p x,(q x,r x)))=obs μ (fun x => ((p x,q x),r x)) := by
  simpa only [Function.comp_def,Equiv.prodAssoc_apply] using obs_equiv μ (fun x => ((p x,q x),r x)) (Equiv.prodAssoc α β γ)

lemma obs_strong_subadd (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    obs μ (fun x => (p x,(q x,r x)))+obs μ q ≤
      obs μ (fun x => (p x,q x))+obs μ (fun x => (q x,r x)) := by
  let P : α → β → γ → ℝ := fun a b c => mass μ (fun x => (p x,(q x,r x))) (a,(b,c))
  have hrow (a : α) (b : β) : ∑ c,P a b c=mass μ (fun x => (p x,q x)) (a,b) := by
    simp only [P,mass_triple_assoc]
    exact (mass_joint_row μ _ r (hp.prodMk hq) hr (a,b)).symm
  have hcol (b : β) (c : γ) : ∑ a,P a b c=mass μ (fun x => (q x,r x)) (b,c) :=
    (mass_joint_col μ p _ hp (hq.prodMk hr) (b,c)).symm
  have htotal (b : β) : ∑ a,∑ c,P a b c=mass μ q b := by
    simp only [hrow]
    exact (mass_joint_col μ p q hp hq b).symm
  have hb (b : β) := matrix_subadd (fun a c => P a b c) (fun a c => mass_nonneg μ _ _)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hb b)
  simp only [shannon,Fintype.sum_prod_type,hrow,hcol,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  simp only [←mass_joint_col μ p q hp hq] at hh
  rw [Finset.sum_comm (f:=fun b a => ∑ c,Real.negMulLog (P a b c)),
    Finset.sum_comm (f:=fun b a => Real.negMulLog (mass μ (fun x => (p x,q x)) (a,b)))] at hh
  have h : obs μ (fun x => (p x,(q x,r x))) ≤
      obs μ (fun x => (p x,q x))+obs μ (fun x => (q x,r x))-obs μ q := by
    simpa only [obs,shannon,Fintype.sum_prod_type] using hh
  linarith

lemma cond_le_obs [IsProbabilityMeasure μ] (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q ≤ obs μ p := sub_le_iff_le_add.mpr (obs_pair_subadd_prob μ p q hp hq)
lemma cond_pair_right (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    cond μ p (fun x => (q x,r x)) ≤ cond μ p q := by
  have h := obs_strong_subadd μ p q r hp hq hr
  dsimp [cond]
  linarith
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma cond_pair_swap_right (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    cond μ p (fun x => (q x,r x))=cond μ p (fun x => (r x,q x)) := by
  have he : obs μ (fun x => (p x,(r x,q x)))=obs μ (fun x => (p x,(q x,r x))) := by
    simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.prodComm_apply,Prod.swap_prod_mk] using
      obs_equiv μ (fun x => (p x,(q x,r x))) (Equiv.prodCongr (Equiv.refl α) (Equiv.prodComm β γ))
  unfold cond
  rw [he,obs_pair_swap μ q r]

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma cond_chain (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    cond μ (fun x => (p x,r x)) q=cond μ p q+cond μ r (fun x => (p x,q x)) := by
  have h1 := obs_pair_swap μ (fun x => (p x,r x)) q
  have h2 := obs_triple_assoc μ q p r
  have h3 := obs_pair_swap μ (fun x => (q x,p x)) r
  have h4 := cond_pair_swap_right μ r q p
  unfold cond at *
  have h5 := obs_pair_swap μ p q
  linarith
lemma cond_factor_right (p : Ω → α) (q : Ω → β) (g : β → γ)
    (hp : Measurable p) (hq : Measurable q) :
    cond μ p q ≤ cond μ p (g ∘ q) := by
  have hg : Measurable (g ∘ q) := (measurable_of_countable g).comp hq
  have h := cond_pair_right μ p (g ∘ q) q hp hg hq
  have he0 : cond μ p (fun x => (q x,g (q x)))=cond μ p q := by
    unfold cond
    dsimp only
    rw [obs_triple_assoc]
    rw [show obs μ (fun x => ((p x,q x),g (q x)))=obs μ (fun x => (p x,q x)) from
      obs_pair_function μ (fun x => (p x,q x)) (fun v : α×β => g v.2)]
    rw [obs_pair_function μ q g]
  have he : cond μ p (fun x => (g (q x),q x))=cond μ p q :=
    (cond_pair_swap_right μ p (g ∘ q) q).trans he0
  calc
    cond μ p q = cond μ p (fun x => (g (q x),q x)) := he.symm
    _ ≤ cond μ p (g ∘ q) := h

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma obs_nonneg (p : Ω → α) (hp : Measurable p) : 0 ≤ obs μ p := by
  apply shannon_nonneg _ (mass_nonneg μ p)
  rw [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
lemma obs_bound [Nonempty α] (p : Ω → α) (hp : Measurable p) : obs μ p ≤ Real.log (Fintype.card α) := by
  apply shannon_bound _ (mass_nonneg μ p)
  rw [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_const [Nonempty α] (a : α) : obs μ (fun _ : Ω => a)=0 := by
  classical
  have he (b : α) : mass μ (fun _ : Ω => a) b=if a=b then 1 else 0 := by
    unfold mass
    by_cases h : a=b
    · subst b; simp
    · have hs : (fun _ : Ω => a) ⁻¹' {b}=∅ := by ext x; simp [h]
      simp [hs,h]
  simp only [obs,shannon,he,apply_ite Real.negMulLog,Real.negMulLog_one,Real.negMulLog_zero,ite_self,Finset.sum_const_zero]

lemma obs_word_bddBelow (f : Ω → Ω) (hf : Measurable f) (p : Ω → α) (hp : Measurable p) :
    BddBelow (Set.range (fun n : ℕ => obs μ (word f p n)/(n : ℝ))) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  exact div_nonneg (obs_nonneg μ _ (word_measurable f hf p hp n)) (Nat.cast_nonneg n)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma rate_eq_lim (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    rate μ f p=(obs_word_subadd μ f hf p hp).lim := by
  rw [Subadditive.lim]; rfl
lemma rate_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    Tendsto (fun n : ℕ => obs μ (word f p n)/(n : ℝ)) atTop (𝓝 (rate μ f p)) := by
  rw [rate_eq_lim μ f hf p hp]
  exact (obs_word_subadd μ f hf p hp).tendsto_lim (obs_word_bddBelow μ f hf.measurable p hp)
lemma rate_nonneg (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    0 ≤ rate μ f p :=
  ge_of_tendsto' (rate_tendsto μ f hf p hp) (fun n => div_nonneg
    (obs_nonneg μ _ (word_measurable f hf.measurable p hp n)) (Nat.cast_nonneg n))

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ReverseFano
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

lemma cond_factor_left (p : Ω → α) (q : Ω → β) (g : α → γ)
    (hp : Measurable p) (hq : Measurable q) : cond μ (g ∘ p) q ≤ cond μ p q := by
  unfold cond
  apply sub_le_sub_right
  exact obs_factor μ (fun x => (p x,q x)) (fun v : α×β => (g v.1,v.2))
    (hp.prodMk hq) (((measurable_of_countable g).comp hp).prodMk hq)

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_IntegerDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma LawClose.symm {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε) : LawClose ν μ ε := by
  intro D hD
  rw [abs_sub_comm]
  exact h D hD

lemma LawClose.triangle {μ ν κ : Measure X} {ε δ : ℝ}
    (h : LawClose μ ν ε) (h' : LawClose ν κ δ) : LawClose μ κ (ε+δ) := by
  intro D hD
  exact (abs_sub_le (μ.real D) (ν.real D) (κ.real D)).trans (add_le_add (h D hD) (h' D hD))

lemma LawClose.map {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε)
    {f : X → Y} (hf : Measurable f) : LawClose (μ.map f) (ν.map f) ε := by
  intro D hD
  simp only [Measure.real,Measure.map_apply hf hD]
  exact h _ (hD.preimage hf)

lemma real_prod_apply (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D : Set (X×Y)} (hD : MeasurableSet D) :
    (μ.prod ν).real D=∫ x,ν.real ((Prod.mk x) ⁻¹' D) ∂μ := by
  rw [Measure.real,Measure.prod_apply hD]
  exact (integral_toReal (measurable_measure_prodMk_left hD).aemeasurable
    (Filter.Eventually.of_forall (fun _ => measure_lt_top ν _))).symm

lemma integrable_real_section (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {D : Set (X×Y)} (hD : MeasurableSet D) :
    Integrable (fun x => ν.real ((Prod.mk x) ⁻¹' D)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_measure_prodMk_left hD).ennreal_toReal.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one)

lemma LawClose.prod_same_left (μ : Measure X) [IsProbabilityMeasure μ]
    {ν η : Measure Y} [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    {ε : ℝ} (h : LawClose ν η ε) : LawClose (μ.prod ν) (μ.prod η) ε := by
  intro D hD
  rw [real_prod_apply μ ν hD,real_prod_apply μ η hD,
    ←integral_sub (integrable_real_section μ ν hD) (integrable_real_section μ η hD)]
  calc
    _≤∫ x,|ν.real ((Prod.mk x) ⁻¹' D)-η.real ((Prod.mk x) ⁻¹' D)| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (fun x => ν.real ((Prod.mk x) ⁻¹' D)-η.real ((Prod.mk x) ⁻¹' D)))
    _≤∫ _x : X,ε ∂μ := integral_mono_ae
      ((integrable_real_section μ ν hD).sub (integrable_real_section μ η hD)).abs
      (integrable_const ε) (Filter.Eventually.of_forall (fun x => h _ (hD.preimage measurable_prodMk_left)))
    _=ε := by simp

lemma LawClose.prod_same_right {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) (η : Measure Y) [IsProbabilityMeasure η] :
    LawClose (μ.prod η) (ν.prod η) ε := by
  simpa only [Measure.prod_swap] using (h.prod_same_left η).map measurable_swap

lemma LawClose.prod {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η κ : Measure Y} [IsProbabilityMeasure η] [IsProbabilityMeasure κ]
    {ε δ : ℝ} (h : LawClose μ ν ε) (h' : LawClose η κ δ) :
    LawClose (μ.prod η) (ν.prod κ) (ε+δ) :=
  (h.prod_same_right η).triangle (h'.prod_same_left ν)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ReverseTailProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma LawClose.mono {μ ν : Measure X} {ε δ : ℝ} (h : LawClose μ ν ε) (hεδ : ε≤δ) :
    LawClose μ ν δ := fun D hD => (h D hD).trans hεδ

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteMaximalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem finite_maximal_coupling_equal_mass {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (heq : ∑ a,p a=∑ a,q a) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=p a) ∧ (∀ b,∑ a,r a b=q b) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))=∑ a,max (p a-q a) 0 := by
  classical
  let d : A → ℝ := fun a => min (p a) (q a)
  let u : A → ℝ := fun a => p a-d a
  let v : A → ℝ := fun a => q a-d a
  let t : ℝ := ∑ a,u a
  have hd (a) : 0≤d a := le_min (hp a) (hq a)
  have hu (a) : 0≤u a := sub_nonneg.mpr (min_le_left _ _)
  have hv (a) : 0≤v a := sub_nonneg.mpr (min_le_right _ _)
  have ht : 0≤t := Finset.sum_nonneg (fun a _ => hu a)
  have htv : ∑ a,v a=t := by
    dsimp only [t,u,v]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,heq]
  have huv (a) : u a*v a=0 := by
    rcases le_total (p a) (q a) with ha | ha
    · simp only [u,v,d,min_eq_left ha,sub_self,zero_mul]
    · simp only [u,v,d,min_eq_right ha,sub_self,mul_zero]
  have hmax (a) : u a=max (p a-q a) 0 := by
    rcases le_total (p a) (q a) with ha | ha
    · simp only [u,d,min_eq_left ha,sub_self,max_eq_right (sub_nonpos.mpr ha)]
    · simp only [u,d,min_eq_right ha,max_eq_left (sub_nonneg.mpr ha)]
  by_cases ht0 : t=0
  · have hu0 (a) : u a=0 := by
      have hh := Finset.single_le_sum (fun b _ => hu b) (Finset.mem_univ a)
      change u a≤t at hh
      rw [ht0] at hh
      exact le_antisymm hh (hu a)
    have hv0 (a) : v a=0 := by
      have hh := Finset.single_le_sum (fun b _ => hv b) (Finset.mem_univ a)
      rw [htv,ht0] at hh
      exact le_antisymm hh (hv a)
    refine ⟨fun a b => if a=b then p a else 0,?_,?_,?_,?_⟩
    · intro a b
      dsimp only
      split_ifs
      · exact hp a
      · exact le_rfl
    · intro a; simp
    · intro b
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      have h1 := hu0 b
      have h2 := hv0 b
      dsimp [u,v] at h1 h2
      linarith
    · have he (a b : A) : (if a=b then p a else 0)*(if a=b then (0 : ℝ) else 1)=0 := by
        by_cases h : a=b <;> simp [h]
      simp_rw [he]
      simp only [Finset.sum_const_zero]
      rw [←show (∑ a,u a)=(∑ a,max (p a-q a) 0) from Finset.sum_congr rfl (fun a _ => hmax a)]
      exact ht0.symm
  · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
    let r : A → A → ℝ := fun a b => (if a=b then d a else 0)+u a*v b/t
    have hr (a b) : 0 ≤ r a b := by
      dsimp only [r]
      exact add_nonneg (by split_ifs; exact hd a; exact le_rfl) (div_nonneg (mul_nonneg (hu a) (hv b)) ht)
    have hrow (a) : ∑ b,r a b=p a := by
      simp only [r,Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
        ←Finset.sum_div,←Finset.mul_sum,htv,mul_div_cancel_right₀ _ ht0]
      dsimp only [u]
      ring
    have hcol (b) : ∑ a,r a b=q b := by
      simp only [r,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
        ←Finset.sum_div,←Finset.sum_mul]
      change d b+t*v b/t=q b
      rw [mul_div_cancel_left₀ _ ht0]
      dsimp only [v]
      ring
    refine ⟨r,hr,hrow,hcol,?_⟩
    have hoff (a b) : r a b*(if a=b then 0 else 1)=u a*v b/t := by
      by_cases hab : a=b
      · subst b; simp [huv]
      · simp only [r,ite_eq_right hab,zero_add,mul_one]
    simp_rw [hoff]
    simp only [←Finset.sum_div,←Finset.mul_sum,htv,mul_div_cancel_right₀ _ ht0]
    exact Finset.sum_congr rfl (fun a _ => hmax a)

theorem finite_maximal_coupling {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hp1 : ∑ a,p a=1) (hq1 : ∑ a,q a=1) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=p a) ∧ (∀ b,∑ a,r a b=q b) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))=∑ a,max (p a-q a) 0 :=
  finite_maximal_coupling_equal_mass p q hp hq (hp1.trans hq1.symm)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators ENNReal

lemma positive_mass_difference_le {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) :
    (∑ a,max (μ.real {a}-ν.real {a}) 0)≤ε := by
  classical
  let D := Finset.univ.filter (fun a : A => ν.real {a}≤μ.real {a})
  have hm (a : A) : max (μ.real {a}-ν.real {a}) 0=
      if ν.real {a}≤μ.real {a} then μ.real {a}-ν.real {a} else 0 := by
    split_ifs with ha
    · exact max_eq_left (sub_nonneg.mpr ha)
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_ge ha))
  have he : (∑ a,max (μ.real {a}-ν.real {a}) 0)=μ.real D-ν.real D := by
    simp_rw [hm]
    rw [←Finset.sum_filter]
    change (∑ a∈D,(μ.real {a}-ν.real {a}))=_
    rw [Finset.sum_sub_distrib,sum_measureReal_singleton,sum_measureReal_singleton]
  rw [he]
  exact (le_abs_self _).trans (h D D.measurableSet)

theorem finite_coupling_of_lawClose {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=μ.real {a}) ∧ (∀ b,∑ a,r a b=ν.real {b}) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))≤ε := by
  obtain ⟨r,hr,hrow,hcol,herr⟩ := finite_maximal_coupling (fun a => μ.real {a}) (fun a => ν.real {a})
    (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
    (by simp)
    (by simp)
  exact ⟨r,hr,hrow,hcol,herr.le.trans (positive_mass_difference_le μ ν h)⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ}

lemma comp_cost_le (r : MatrixCoupling p q) (t : MatrixCoupling q s)
    (d : A → B → ℝ) (e : B → C → ℝ) (f : A → C → ℝ)
    (htri : ∀ a b c,f a c≤d a b+e b c) :
    (r.comp t).cost f ≤ r.cost d+t.cost e := by
  unfold cost comp
  simp only [Finset.sum_mul]
  calc
    _≤∑ a,∑ c,∑ b,glueWeight r t a b c*(d a b+e b c) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun c _ =>
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (htri a b c) (glueWeight_nonneg r t a b c))))
    _=(∑ a,∑ c,∑ b,glueWeight r t a b c*d a b)+
        (∑ a,∑ c,∑ b,glueWeight r t a b c*e b c) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _=(∑ a,∑ b,r.weight a b*d a b)+(∑ b,∑ c,t.weight b c*e b c) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        simp only [←Finset.sum_mul,glueWeight_row]
      · rw [Finset.sum_comm]
        calc
          _ = ∑ c,∑ b,∑ a,glueWeight r t a b c*e b c := by
            apply Finset.sum_congr rfl
            intro c _
            exact Finset.sum_comm
          _ = ∑ c,∑ b,t.weight b c*e b c := by simp only [←Finset.sum_mul,glueWeight_col]
          _ = _ := Finset.sum_comm

end MatrixCoupling
end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

lemma integrable_finite_observation (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) (g : A → ℝ) : Integrable (fun x => g (p x)) μ := by
  classical
  apply Integrable.of_bound ((measurable_of_countable g).comp hp).aestronglyMeasurable (∑ a,|g a|)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun a _ => abs_nonneg (g a)) (Finset.mem_univ _))

lemma information_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) : Integrable (information μ p) μ :=
  integrable_finite_observation μ p hp (fun a : A => -Real.log (mass μ p a))

lemma integral_information (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) : (∫ x,information μ p x ∂μ)=obs μ p := by
  simp only [information]
  rw [←sum_mass_mul_integral μ p hp (fun a => -Real.log (mass μ p a))]
  simp only [obs,shannon,Real.negMulLog,mul_neg,neg_mul]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma ae_mass_positive (μ : Measure X) [IsFiniteMeasure μ] (p : X → A) :
    ∀ᵐ x ∂μ,0 < mass μ p (p x) := by
  have hzero (a : A) : ∀ᵐ x ∂μ,mass μ p a=0 → p x≠a := by
    by_cases ha : mass μ p a=0
    · have hm : μ (p ⁻¹' {a})=0 := by
        apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.zero_ne_top).mp
        exact ha
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hm] with x hx _h
      exact hx
    · exact ae_of_all _ (fun _ h => (ha h).elim)
  filter_upwards [ae_all_iff.mpr hzero] with x hx
  exact lt_of_le_of_ne (mass_nonneg μ p _) (Ne.symm (fun h => hx (p x) h rfl))

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ} {t : D → ℝ}

lemma diagonal_cost (p : A → ℝ) (hp : ∀ a,0≤p a) (d : A → A → ℝ)
    (hd : ∀ a,d a a=0) : (diagonal p hp).cost d=0 := by
  classical
  unfold cost diagonal
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,hd,mul_zero,Finset.sum_const_zero]

lemma product_cost (r : MatrixCoupling p q) (u : MatrixCoupling s t)
    (hp : ∑ a,p a=1) (hs : ∑ c,s c=1) (d : A → B → ℝ) (e : C → D → ℝ) :
    (r.product u).cost (fun ac bd => d ac.1 bd.1+e ac.2 bd.2)=r.cost d+u.cost e := by
  unfold cost product
  simp only [Fintype.sum_prod_type,mul_add,Finset.sum_add_distrib]
  congr 1
  · calc
      _ = ∑ a,∑ c,∑ b,r.weight a b*d a b*(∑ v,u.weight c v) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ a,∑ c,∑ b,r.weight a b*d a b*s c := by simp only [u.row]
      _ = ∑ a,∑ b,r.weight a b*d a b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        simp only [←Finset.mul_sum,hs,mul_one]
  · calc
      _ = ∑ a,∑ c,(∑ b,r.weight a b)*(∑ v,u.weight c v*e c v) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ a,∑ c,p a*(∑ v,u.weight c v*e c v) := by simp only [r.row]
      _ = ∑ c,∑ v,u.weight c v*e c v := by
        rw [Finset.sum_comm]
        simp only [←Finset.sum_mul,hp,one_mul]

section Observations
variable [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma observations_cost (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (d : A → B → ℝ) : (observations μ p q hp hq).cost d=∫ x,d (p x) (q x) ∂μ := by
  change (∑ a,∑ b,mass μ (fun x => (p x,q x)) (a,b)*d a b)=_
  simpa only [Fintype.sum_prod_type] using
    sum_mass_mul_integral μ (fun x => (p x,q x)) (hp.prodMk hq) (fun ab => d ab.1 ab.2)

end Observations
end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal Topology

lemma continuous_cdf_atomless (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  have hc : Continuous (fun a : ℝ => ∫ _x in Iic a,(1 : ℝ) ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro a
    have h := ((integrable_const (1 : ℝ)).integrableOn : IntegrableOn (fun _x : ℝ => (1 : ℝ)) (Iic (a+1)) ν)
    exact (h.continuousOn_Iic_primitive_Iic a (by simp)).continuousAt (Iic_mem_nhds (by linarith))
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ,←cdf_eq_real] using hc

theorem exists_event_real_mass {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    ∃ E : Set X,MeasurableSet E ∧ μ.real E=t := by
  by_cases ht0 : t=0
  · exact ⟨∅,MeasurableSet.empty,by simp [ht0]⟩
  by_cases hte : t=1
  · exact ⟨univ,MeasurableSet.univ,by simp [hte]⟩
  let b : X → ℝ := embeddingReal X
  have hb : MeasurableEmbedding b := measurableEmbedding_embeddingReal X
  let ν := μ.map b
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : NullSingletonClass ν := by
    constructor
    intro y
    rw [show ν=μ.map b from rfl,Measure.map_apply hb.measurable (measurableSet_singleton y)]
    by_cases hy : ∃ x,b x=y
    · obtain ⟨x,rfl⟩ := hy
      have hs : b ⁻¹' {b x}={x} := by
        ext z
        exact hb.injective.eq_iff
      simp only [hs,measure_singleton]
    · have hs : b ⁻¹' {y}=∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hy ⟨x,hx⟩)
      simp only [hs,measure_empty]
  have hs := isPreconnected_univ.intermediate_value_Ioo (s:=Set.univ)
    (show (atBot : Filter ℝ)≤𝓟 Set.univ by simp) (show (atTop : Filter ℝ)≤𝓟 Set.univ by simp)
    (continuous_cdf_atomless ν).continuousOn (tendsto_cdf_atBot ν) (tendsto_cdf_atTop ν)
    (show t∈Ioo (0 : ℝ) 1 from ⟨lt_of_le_of_ne ht (Ne.symm ht0),lt_of_le_of_ne ht1 hte⟩)
  obtain ⟨r,_hr,hrt⟩ := hs
  refine ⟨b ⁻¹' Iic r,measurableSet_Iic.preimage hb.measurable,?_⟩
  rw [←map_measureReal_apply hb.measurable measurableSet_Iic]
  exact (cdf_eq_real ν r).symm.trans hrt

theorem exists_subset_real_mass {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {S : Set X} (hS : MeasurableSet S) {t : ℝ} (ht : 0≤t) (htS : t≤μ.real S) :
    ∃ E : Set X,MeasurableSet E ∧ E⊆S ∧ μ.real E=t := by
  by_cases ht0 : t=0
  · exact ⟨∅,MeasurableSet.empty,empty_subset _,by simp [ht0]⟩
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hSr : 0<μ.real S := htpos.trans_le htS
  have hS0 : μ S≠0 := by
    intro h
    simp only [Measure.real,h,ENNReal.toReal_zero] at hSr
    exact lt_irrefl _ hSr
  let ν : Measure X := (μ S)⁻¹ • μ.restrict S
  have : IsProbabilityMeasure ν := by
    constructor
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    exact ENNReal.inv_mul_cancel hS0 (measure_ne_top μ S)
  have : NullSingletonClass ν := by
    constructor
    intro x
    have hz : μ ({x}∩S)=0 := measure_mono_null inter_subset_left (measure_singleton x)
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply (measurableSet_singleton x),hz,mul_zero]
  obtain ⟨T,hT,hTm⟩ := exists_event_real_mass ν (div_nonneg ht hSr.le) ((div_le_one hSr).mpr htS)
  refine ⟨S∩T,hS.inter hT,inter_subset_left,?_⟩
  have he : ν.real T=μ.real (S∩T)/μ.real S := by
    simp only [ν,Measure.real,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hT,
      ENNReal.toReal_mul,ENNReal.toReal_inv,inter_comm T S,div_eq_mul_inv]
    ring
  rw [he] at hTm
  exact (div_left_inj' hSr.ne').mp hTm

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_AtomlessFinitePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem exists_disjoint_cuts (s : Finset A) (w : A → ℝ) (hw : ∀ a,0≤w a)
    {S : Set X} (hS : MeasurableSet S) (hsum : (∑ a∈s,w a)≤μ.real S) :
    ∃ E : A → Set X,(∀ a∈s,MeasurableSet (E a) ∧ E a⊆S ∧ μ.real (E a)=w a) ∧
      (∀ a∈s,∀ b∈s,a≠b → Disjoint (E a) (E b)) := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty => exact ⟨fun _ => ∅,by simp,by simp⟩
  | @insert a s ha ih =>
    have hsumnonneg : 0≤∑ b∈s,w b := Finset.sum_nonneg (fun b _ => hw b)
    rw [Finset.sum_insert ha] at hsum
    obtain ⟨D,hD,hDS,hDm⟩ := exists_subset_real_mass μ hS (hw a) (by linarith)
    have hrem : (∑ b∈s,w b)≤μ.real (S\D) := by
      rw [measureReal_sdiff hDS hD,hDm]
      linarith
    obtain ⟨F,hF,hFd⟩ := ih (hS.diff hD) hrem
    refine ⟨fun b => if b=a then D else F b,?_,?_⟩
    · intro b hb
      by_cases hba : b=a
      · subst b
        simpa using And.intro hD (And.intro hDS hDm)
      · have hbs : b∈s := (Finset.mem_insert.mp hb).resolve_left hba
        simpa only [ite_eq_right hba] using And.intro (hF b hbs).1
          (And.intro ((hF b hbs).2.1.trans sdiff_subset) (hF b hbs).2.2)
    · intro b hb c hc hbc
      by_cases hba : b=a
      · subst b
        have hca : c≠a := Ne.symm hbc
        have hcs := (Finset.mem_insert.mp hc).resolve_left hca
        simp only [ite_eq_right hca]
        exact disjoint_left.mpr (fun x hxD hxF => ((hF c hcs).2.1 hxF).2 hxD)
      · by_cases hca : c=a
        · subst c
          have hbs := (Finset.mem_insert.mp hb).resolve_left hba
          simp only [ite_eq_right hba]
          exact disjoint_left.mpr (fun x hxF hxD => ((hF b hbs).2.1 hxF).2 hxD)
        · simp only [ite_eq_right hba,ite_eq_right hca]
          exact hFd b ((Finset.mem_insert.mp hb).resolve_left hba) c
            ((Finset.mem_insert.mp hc).resolve_left hca) hbc

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set

lemma exists_measurable_coloring {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Nonempty A] (s : Finset A) (E : A → Set X)
    (hm : ∀ a∈s,MeasurableSet (E a))
    (hd : ∀ a∈s,∀ b∈s,a≠b → Disjoint (E a) (E b)) :
    ∃ q : X → A,Measurable q ∧ ∀ a∈s,∀ x∈E a,q x=a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary A,measurable_const,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨q,hq,hqa⟩ := ih (fun b hb => hm b (Finset.mem_insert_of_mem hb))
      (fun b hb c hc => hd b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc))
    let q' : X → A := (E a).piecewise (fun _ => a) q
    refine ⟨q',measurable_const.piecewise (hm a (Finset.mem_insert_self _ _)) hq,?_⟩
    intro b hb x hx
    by_cases hba : b=a
    · subst b
      exact Set.piecewise_eq_of_mem _ _ _ hx
    · have hbs := (Finset.mem_insert.mp hb).resolve_left hba
      have hxa : x∉E a := fun hxa => (hd b hb a (Finset.mem_insert_self _ _) hba).le_bot ⟨hx,hxa⟩
      exact (Set.piecewise_eq_of_notMem _ _ _ hxa).trans (hqa b hbs x hx)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem exists_finite_random_variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [Nonempty A]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {S : Set X} (hS : MeasurableSet S) (w : A → ℝ) (hw : ∀ a,0≤w a)
    (hwS : ∑ a,w a=μ.real S) :
    ∃ q : X → A,Measurable q ∧ ∀ a,μ.real (S∩q ⁻¹' {a})=w a := by
  classical
  obtain ⟨E,hE,hEd⟩ := exists_disjoint_cuts μ Finset.univ w hw hS hwS.le
  have hm (a : A) := (hE a (Finset.mem_univ a)).1
  have hsub (a : A) := (hE a (Finset.mem_univ a)).2.1
  have he (a : A) := (hE a (Finset.mem_univ a)).2.2
  have hd : Pairwise (Function.onFun Disjoint E) := fun a b hab =>
    hEd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  obtain ⟨q,hq,hqa⟩ := exists_measurable_coloring Finset.univ E
    (fun a _ => hm a) (fun a _ b _ => hd (i:=a) (j:=b))
  have hUm : MeasurableSet (⋃ a,E a) := MeasurableSet.iUnion hm
  have hUS : (⋃ a,E a)⊆S := iUnion_subset hsub
  have hUr : μ.real (⋃ a,E a)=μ.real S := by
    rw [measureReal_iUnion_fintype hd hm]
    simp_rw [he]
    exact hwS
  have hz : μ (S\⋃ a,E a)=0 := (measureReal_eq_zero_iff).mp (by
    rw [measureReal_sdiff hUS hUm,hUr,sub_self])
  have hAE : ∀ᵐ x ∂μ,x∈S → ∃ a,x∈E a := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx hxS
    by_contra hh
    apply hx
    exact ⟨hxS,by simpa only [mem_iUnion,not_exists] using hh⟩
  refine ⟨q,hq,fun a => ?_⟩
  have hEq : (S∩q ⁻¹' {a} : Set X) =ᵐ[μ] E a := by
    filter_upwards [hAE] with x hx
    apply propext
    constructor
    · rintro ⟨hxS,hxq⟩
      obtain ⟨b,hxb⟩ := hx hxS
      have hba : b=a := (hqa b (Finset.mem_univ b) x hxb).symm.trans hxq
      change x∈E a
      exact hba ▸ hxb
    · intro hxa
      exact ⟨hsub a hxa,hqa a (Finset.mem_univ a) x hxa⟩
  exact (measureReal_congr hEq).trans (he a)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [MeasurableSingletonClass B] in
theorem realize_finite_coupling (p : X → A) (hp : Measurable p)
    (r : A → B → ℝ) (hr : ∀ a b,0 ≤ r a b) (hrow : ∀ a,∑ b,r a b=mass μ p a) :
    ∃ q : X → B,Measurable q ∧ ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=r a b := by
  have hh (a : A) : ∃ q : X → B,Measurable q ∧
      ∀ b,μ.real ((p ⁻¹' {a})∩q ⁻¹' {b})=r a b :=
    exists_finite_random_variable μ (hp (measurableSet_singleton a)) (r a) (hr a) (hrow a)
  choose q hq hqr using hh
  let q' : X → B := fun x => q (p x) x
  have hq' : Measurable q' := (measurable_from_prod_countable_right
    (f:=fun ax : A×X => q ax.1 ax.2) hq).comp (hp.prodMk measurable_id)
  refine ⟨q',hq',fun a b => ?_⟩
  have hset : (fun x => (p x,q' x)) ⁻¹' {(a,b)}=(p ⁻¹' {a})∩q a ⁻¹' {b} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,mem_inter_iff,q']
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
  simpa only [mass,hset,Measure.real] using hqr a b

omit [StandardBorelSpace X] [NullSingletonClass μ] in
lemma repaint_error_eq_sum [DecidableEq A] (p q : X → A) (hp : Measurable p) (hq : Measurable q) :
    μ.real {x | p x≠q x}=(∑ a,∑ b,mass μ (fun x => (p x,q x)) (a,b)*(if a=b then 0 else 1)) := by
  classical
  let g : A×A → ℝ := fun ab => if ab.1=ab.2 then 0 else 1
  have hs := sum_mass_mul_integral μ (fun x => (p x,q x)) (hp.prodMk hq) g
  rw [Fintype.sum_prod_type] at hs
  have hi : (∫ x,g (p x,q x) ∂μ)=μ.real {x | p x≠q x} := by
    have he : (fun x => g (p x,q x))={x | p x≠q x}.indicator (fun _x : X => (1 : ℝ)) := by
      funext x
      by_cases hx : p x=q x <;> simp [g,hx]
    have hD : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
    rw [he]
    change (∫ x,{x | p x≠q x}.indicator (fun _x : X => (1 : ℝ)) x ∂μ)=_
    rw [integral_indicator hD]
    simp
  exact hi.symm.trans hs.symm

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set
open scoped BigOperators
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsFiniteMeasure μ]

omit [Fintype A] [Fintype C] in
lemma mass_triple_first_third (p : X → A) (q : X → B) (r : X → C)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (a : A) (c : C) :
    mass μ (fun x => (p x,r x)) (a,c)=
      ∑ b,mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  rw [mass_joint_row μ (fun x => (p x,r x)) q (hp.prodMk hr) hq (a,c)]
  apply Finset.sum_congr rfl
  intro b _hb
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
  tauto

omit [Fintype B] [Fintype C] in
lemma mass_triple_second_third (p : X → A) (q : X → B) (r : X → C)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (b : B) (c : C) :
    mass μ (fun x => (q x,r x)) (b,c)=
      ∑ a,mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  rw [mass_joint_row μ (fun x => (q x,r x)) p (hq.prodMk hr) hp (b,c)]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
  tauto

end StandardMapEntropy.Entropy
end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

theorem copy_independent_of_finite_past (p : X → A) (q : X → B)
    (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (hclose : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    ∃ q' : X → B,Measurable q' ∧ μ.map q'=μ.map q ∧
      μ.map (fun x => (p x,q' x))=(μ.map p).prod (μ.map q) ∧
      μ.real {x | q x≠q' x}≤ε := by
  classical
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (fun x => (p x,q x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  let u : A → B → ℝ := fun a b => mass μ (fun x => (p x,q x)) (a,b)
  let v : A → B → ℝ := fun a b => mass μ p a*mass μ q b
  have hu (a b) : 0≤u a b := mass_nonneg _ _ _
  have hv (a b) : 0≤v a b := mul_nonneg (mass_nonneg _ _ _) (mass_nonneg _ _ _)
  have hrow (a) : ∑ b,u a b=∑ b,v a b := by
    rw [←mass_joint_row μ p q hp hq]
    dsimp only [v]
    rw [←Finset.mul_sum,mass_sum μ q hq]
    simp
  have hc (a) := finite_maximal_coupling_equal_mass (u a) (v a) (hu a) (hv a) (hrow a)
  choose r hr hrrow hrcol hrerr using hc
  obtain ⟨q',hq',hqq'⟩ := realize_finite_coupling μ (fun x => (p x,q x))
    (hp.prodMk hq) (fun ab c => r ab.1 ab.2 c) (fun ab c => hr ab.1 ab.2 c)
    (fun ab => hrrow ab.1 ab.2)
  have hpair (a b) : mass μ (fun x => (p x,q' x)) (a,b)=v a b := by
    rw [mass_triple_first_third μ p q q' hp hq hq']
    simpa only [hqq'] using hrcol a b
  have hprod (a b) : ((μ.map p).prod (μ.map q)).real {(a,b)}=v a b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hmap : μ.map (fun x => (p x,q' x))=(μ.map p).prod (μ.map q) := by
    apply Measure.ext_of_singleton
    rintro ⟨a,b⟩
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [←Measure.real,map_measureReal_apply (hp.prodMk hq') (measurableSet_singleton (a,b))]
    exact (hpair a b).trans (hprod a b).symm
  have hmarg : μ.map q'=μ.map q := by
    apply Measure.ext_of_singleton
    intro b
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [←Measure.real,←Measure.real,map_measureReal_apply hq' (measurableSet_singleton b),
      map_measureReal_apply hq (measurableSet_singleton b)]
    change mass μ q' b=mass μ q b
    rw [mass_joint_col μ p q' hp hq']
    simp_rw [hpair]
    dsimp only [v]
    rw [←Finset.sum_mul,mass_sum μ p hp]
    simp
  refine ⟨q',hq',hmarg,hmap,?_⟩
  rw [repaint_error_eq_sum μ q q' hq hq']
  simp_rw [mass_triple_second_third μ p q q' hp hq hq',hqq',Finset.sum_mul]
  have herr : (∑ a,∑ b,∑ c,r a b c*(if b=c then (0 : ℝ) else 1))≤ε := by
    simp_rw [hrerr]
    have hh := positive_mass_difference_le (μ.map (fun x => (p x,q x)))
      ((μ.map p).prod (μ.map q)) hclose
    rw [Fintype.sum_prod_type] at hh
    have hu' (a b) : (μ.map (fun x => (p x,q x))).real {(a,b)}=u a b :=
      map_measureReal_apply (hp.prodMk hq) (measurableSet_singleton (a,b))
    simpa only [hu',hprod] using hh
  calc
    _=(∑ b,∑ a,∑ c,r a b c*(if b=c then (0 : ℝ) else 1)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _=(∑ a,∑ b,∑ c,r a b c*(if b=c then (0 : ℝ) else 1)) := Finset.sum_comm
    _≤ε := herr

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma symbolCost_self {E : Type*} (a : E) : symbolCost a a=0 := by simp [symbolCost]
lemma symbolCost_triangle {E : Type*} (a b c : E) : symbolCost a c≤ symbolCost a b+symbolCost b c := by
  classical
  by_cases h1 : a=b <;> by_cases h2 : b=c <;> by_cases h3 : a=c <;> simp_all [symbolCost]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

lemma reindex_cost (r : MatrixCoupling p q) (e : C ≃ A) (f : D ≃ B) (d : A → B → ℝ) :
    (r.reindex e f).cost (fun a b => d (e a) (f b))=r.cost d := by
  change (∑ a,∑ b,r.weight (e a) (f b)*d (e a) (f b))=∑ a,∑ b,r.weight a b*d a b
  have hf (a : C) := f.sum_comp (fun b => r.weight (e a) b*d (e a) b)
  simp_rw [hf]
  exact e.sum_comp (fun a => ∑ b,r.weight a b*d a b)

end MatrixCoupling

lemma nameCost_self {E : Type*} {n : ℕ} (a : Fin n → E) : nameCost a a=0 := by
  simp [nameCost,symbolCost_self]
lemma nameCost_triangle {E : Type*} {n : ℕ} (a b c : Fin n → E) :
    nameCost a c≤nameCost a b+nameCost b c := by
  simp only [nameCost,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => symbolCost_triangle _ _ _)

section Copy
variable [StandardBorelSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

theorem coupling_step (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (t : A → ℝ) (r : MatrixCoupling (mass μ p) t)
    (d : A → A → ℝ) (hdiag : ∀ a,d a a=0) (htri : ∀ a b c,d a c≤d a b+d b c)
    {ε : ℝ}
    (hclose : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    ∃ s : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*t ba.2),
      s.cost (fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2)≤ε+r.cost d := by
  classical
  obtain ⟨q',hq',_hm,hjoint,herr⟩ := copy_independent_of_finite_past μ p q hp hq hclose
  have hmass (b : B) (a : A) : mass μ (fun x => (q' x,p x)) (b,a)=mass μ q b*mass μ p a := by
    have hh := congrArg (fun M : Measure (A×B) => M.real {(a,b)}) hjoint
    rw [map_measureReal_apply (hp.prodMk hq') (measurableSet_singleton (a,b))] at hh
    have hprod : ((μ.map p).prod (μ.map q)).real {(a,b)}=mass μ p a*mass μ q b := by
      rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
      rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
        map_measureReal_apply hq (measurableSet_singleton b)]
      rfl
    rw [hprod] at hh
    have he : mass μ (fun x => (q' x,p x)) (b,a)=mass μ (fun x => (p x,q' x)) (a,b) := by
      unfold mass
      congr 2
      ext x
      simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_comm]
    exact he.trans (hh.trans (mul_comm _ _))
  let R := MatrixCoupling.observations μ (fun x => (q x,p x)) (fun x => (q' x,p x))
    (hq.prodMk hp) (hq'.prodMk hp)
  let R' : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*mass μ p ba.2) := {
    weight := R.weight
    nonneg := R.nonneg
    row := R.row
    col := fun ba => (R.col ba).trans (hmass ba.1 ba.2) }
  let S := (MatrixCoupling.diagonal (mass μ q) (mass_nonneg μ q)).product r
  let cost : (B×A) → (B×A) → ℝ := fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2
  have hR : R'.cost cost≤ε := by
    change R.cost cost≤ε
    rw [MatrixCoupling.observations_cost]
    change (∫ x,symbolCost (q x) (q' x)+d (p x) (p x) ∂μ)≤ε
    simp only [hdiag,add_zero]
    have he : (∫ x,symbolCost (q x) (q' x) ∂μ)=μ.real {x | q x≠q' x} := by
      rw [←sum_mass_mul_integral μ (fun x => (q x,q' x)) (hq.prodMk hq')
        (fun ab => symbolCost ab.1 ab.2),Fintype.sum_prod_type]
      exact (repaint_error_eq_sum μ q q' hq hq').symm
    rwa [he]
  have hS : S.cost cost=r.cost d := by
    rw [MatrixCoupling.product_cost]
    · rw [MatrixCoupling.diagonal_cost _ _ symbolCost symbolCost_self,zero_add]
    · simp only [mass_sum μ q hq,measure_univ,ENNReal.toReal_one]
    · simp only [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
  refine ⟨R'.comp S,?_⟩
  have h := MatrixCoupling.comp_cost_le R' S cost cost cost (fun a b c => by
    dsimp [cost]
    have h1 := symbolCost_triangle a.1 b.1 c.1
    have h2 := htri a.2 b.2 c.2
    linarith)
  exact h.trans (by rw [hS]; linarith)

end Copy
end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_SequentialChunkCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma finiteName_measurable (q : ℕ → X → A) (hq : ∀ i,Measurable (q i)) (i n : ℕ) :
    Measurable (finiteName q i n) := Measurable.of_eval (fun index => hq (i+index))

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma finiteName_cons (q : ℕ → X → A) (i n : ℕ) (x : X) :
    finiteName q i (n+1) x=Fin.cons (q i x) (finiteName q (i+1) n x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [finiteName]
  · simp [finiteName,Nat.add_comm,Nat.add_left_comm]

omit [StandardBorelSpace X] [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [Nonempty A] [IsProbabilityMeasure μ] [NullSingletonClass μ] in
lemma independentNameWeights_cons (q : ℕ → X → A) (i n : ℕ) (w : Fin (n+1) → A) :
    independentNameWeights μ q i (n+1) w=
      mass μ (q i) (w 0)*independentNameWeights μ q (i+1) n (Fin.tail w) := by
  rw [independentNameWeights,Fin.prod_univ_succ]
  simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Fin.tail,independentNameWeights]
  congr 2
  funext j
  congr 2
  omega

omit [StandardBorelSpace X] [IsProbabilityMeasure μ] [NullSingletonClass μ] in
lemma mass_equiv_inverse {B C : Type*} [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    (p : X → B) (e : B ≃ C) (c : C) : mass μ (e ∘ p) c=mass μ p (e.symm c) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Function.comp_apply,←Equiv.eq_symm_apply]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma nameCost_split {n : ℕ} (v w : Fin (n+1) → A) :
    nameCost v w=symbolCost (v 0) (w 0)+nameCost (Fin.tail v) (Fin.tail w) := by
  rw [nameCost,Fin.sum_univ_succ]
  rfl

theorem sequential_chunk_coupling (q : ℕ → X → A) (hq : ∀ i,Measurable (q i))
    {ε : ℝ}
    (hremote : ∀ i n : ℕ,LawClose
      (μ.map (fun x => (finiteName q (i+1) n x,q i x)))
      ((μ.map (finiteName q (i+1) n)).prod (μ.map (q i))) ε) :
    ∀ i n : ℕ,∃ r : MatrixCoupling (mass μ (finiteName q i n)) (independentNameWeights μ q i n),
      r.cost nameCost≤(n : ℝ)*ε := by
  intro i n
  induction n generalizing i with
  | zero =>
    have hm (w : Fin 0 → A) : mass μ (finiteName q i 0) w=1 := by
      have he : (finiteName q i 0) ⁻¹' {w}=univ := by
        ext x
        simp only [mem_preimage,mem_singleton_iff,mem_univ,iff_true]
        funext j
        exact j.elim0
      simp [mass,he]
    let r : MatrixCoupling (mass μ (finiteName q i 0)) (independentNameWeights μ q i 0) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun w => by simp [hm]
      col := fun w => by simp [independentNameWeights] }
    refine ⟨r,?_⟩
    simp [MatrixCoupling.cost,nameCost]
  | succ n ih =>
    obtain ⟨r,hr⟩ := ih (i+1)
    obtain ⟨s,hs⟩ := coupling_step μ (finiteName q (i+1) n) (q i)
      (finiteName_measurable q hq (i+1) n) (hq i)
      (independentNameWeights μ q (i+1) n) r nameCost nameCost_self nameCost_triangle (hremote i n)
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := s.reindex e.symm e.symm
    have hm (w : Fin (n+1) → A) :
        mass μ (fun x => (q i x,finiteName q (i+1) n x)) (e.symm w)=mass μ (finiteName q i (n+1)) w := by
      rw [←mass_equiv_inverse μ _ e w]
      congr 1
      funext x
      exact (finiteName_cons q i n x).symm
    have hw (w : Fin (n+1) → A) :
        mass μ (q i) (e.symm w).1*independentNameWeights μ q (i+1) n (e.symm w).2=
          independentNameWeights μ q i (n+1) w := (independentNameWeights_cons μ q i n w).symm
    let R : MatrixCoupling (mass μ (finiteName q i (n+1))) (independentNameWeights μ q i (n+1)) := {
      weight := t.weight
      nonneg := t.nonneg
      row := fun w => (t.row w).trans (hm w)
      col := fun w => (t.col w).trans (hw w) }
    have hcost : R.cost nameCost=s.cost (fun a b => symbolCost a.1 b.1+nameCost a.2 b.2) := by
      change t.cost nameCost=_
      have he : (nameCost : (Fin (n+1) → A) → (Fin (n+1) → A) → ℝ)=
          (fun v w => symbolCost (e.symm v).1 (e.symm w).1+nameCost (e.symm v).2 (e.symm w).2) := by
        funext v w
        exact nameCost_split v w
      rw [he]
      exact MatrixCoupling.reindex_cost s e.symm e.symm
        (fun a b : A×(Fin n → A) => symbolCost a.1 b.1+nameCost a.2 b.2)
    refine ⟨R,?_⟩
    rw [hcost]
    calc
      _≤ε+r.cost nameCost := hs
      _≤ε+(n : ℝ)*ε := by linarith
      _=((n+1 : ℕ) : ℝ)*ε := by push_cast; ring

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal
variable {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma lawClose_pair_factor_left (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) (hc : Measurable c) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (c (p x),q x))) ((μ.map (c ∘ p)).prod (μ.map q)) ε := by
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hh := h.map (hc.prodMap measurable_id)
  rw [Measure.map_map (hc.prodMap measurable_id) (hp.prodMk hq)] at hh
  rw [←Measure.map_prod_map _ _ hc measurable_id,Measure.map_map hc hp,Measure.map_id] at hh
  exact hh

omit [IsProbabilityMeasure μ] in
lemma map_observation_comp (T : X → X) (hT : MeasurePreserving T μ μ)
    (p : X → A) (hp : Measurable p) : μ.map (p ∘ T)=μ.map p := by
  rw [←Measure.map_map hp hT.measurable,hT.map_eq]

omit [IsProbabilityMeasure μ] in
lemma lawClose_pair_comp (T : X → X) (hT : MeasurePreserving T μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (p (T x),q (T x))))
      ((μ.map (p ∘ T)).prod (μ.map (q ∘ T))) ε := by
  rw [map_observation_comp μ T hT p hp,map_observation_comp μ T hT q hq]
  have he : (fun x => (p (T x),q (T x)))=(fun x => (p x,q x)) ∘ T := rfl
  rw [he,map_observation_comp μ T hT _ (hp.prodMk hq)]
  exact h

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma chunkObservation_measurable (f : X → X) (p : X → A)
    (hf : Measurable f) (hp : Measurable p) (k g i : ℕ) :
    Measurable (chunkObservation f p k g i) :=
  (word_measurable f hf p hp k).comp (hf.iterate _)

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma selectChunks_word (f : X → X) (p : X → A) (k g n : ℕ) (x : X) :
    selectChunks k g n (word f p (n*(k+g)) x)=
      finiteName (chunkObservation f p k g) 0 n x := by
  funext j r
  change p (f^[j.val*(k+g)+r.val] x)=p (f^[r.val] (f^[(0+j.val)*(k+g)] x))
  rw [←Function.iterate_add_apply]
  congr 2
  simp only [Nat.zero_add]
  omega

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma chunkName_translate (f : X → X) (p : X → A) (k g i n : ℕ) (x : X) :
    finiteName (chunkObservation f p k g) 0 n (f^[i*(k+g)] x)=
      finiteName (chunkObservation f p k g) i n x := by
  funext j r
  change p (f^[r.val] (f^[(0+j.val)*(k+g)] (f^[i*(k+g)] x)))=
    p (f^[r.val] (f^[(i+j.val)*(k+g)] x))
  simp only [←Function.iterate_add_apply]
  congr 2
  ring

theorem stationary_chunk_coupling (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (k g : ℕ) {ε : ℝ}
    (hremote : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) ε) :
    ∀ n : ℕ,∃ r : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (fun w : Fin n → Fin k → A => ∏ j,mass μ (word f p k) (w j)),
      r.cost nameCost≤(n : ℝ)*ε := by
  have hq := chunkObservation_measurable f p hf.measurable hp k g
  have hc : ∀ i n : ℕ,LawClose
      (μ.map (fun x => (finiteName (chunkObservation f p k g) (i+1) n x,
        chunkObservation f p k g i x)))
      ((μ.map (finiteName (chunkObservation f p k g) (i+1) n)).prod
        (μ.map (chunkObservation f p k g i))) ε := by
    intro i n
    have hs : Measurable (selectChunks (A:=A) k g n) :=
      Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => measurable_pi_apply _))
    have h := lawClose_pair_factor_left μ _ _ (selectChunks k g n)
      ((word_measurable f hf.measurable p hp _).comp (hf.measurable.iterate _))
      (word_measurable f hf.measurable p hp k) hs (hremote (n*(k+g)))
    have hh := lawClose_pair_comp μ (f^[i*(k+g)]) (hf.iterate _) _ _
      (hs.comp ((word_measurable f hf.measurable p hp _).comp (hf.measurable.iterate _)))
      (word_measurable f hf.measurable p hp k) h
    have he (x : X) : selectChunks k g n
        (word f p (n*(k+g)) (f^[k+g] (f^[i*(k+g)] x)))=
          finiteName (chunkObservation f p k g) (i+1) n x := by
      rw [selectChunks_word,←Function.iterate_add_apply]
      rw [show k+g+i*(k+g)=(i+1)*(k+g) by ring]
      exact chunkName_translate f p k g (i+1) n x
    simp only [Function.comp_def,he] at hh
    exact hh
  intro n
  obtain ⟨r,hr⟩ := sequential_chunk_coupling μ _ hq hc 0 n
  have hw (w : Fin n → Fin k → A) :
      independentNameWeights μ (chunkObservation f p k g) 0 n w=
        ∏ j,mass μ (word f p k) (w j) := by
    apply Finset.prod_congr rfl
    intro j _
    have hh := congrArg (fun ν : Measure (Fin k → A) => ν.real {w j})
      (map_observation_comp μ _ (hf.iterate ((0+j.val)*(k+g)))
        (word f p k) (word_measurable f hf.measurable p hp k))
    rw [map_measureReal_apply ((word_measurable f hf.measurable p hp k).comp
      (hf.measurable.iterate _)) (measurableSet_singleton _),
      map_measureReal_apply (word_measurable f hf.measurable p hp k) (measurableSet_singleton _)] at hh
    exact hh
  let R : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (fun w : Fin n → Fin k → A => ∏ j,mass μ (word f p k) (w j)) := {
    weight := r.weight
    nonneg := r.nonneg
    row := r.row
    col := fun w => (r.col w).trans (hw w) }
  exact ⟨R,hr⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

lemma expectation_product (w f : B → A → ℝ) :
    finiteExpectation (productWeights w) (fun D => ∏ b,f b (D b))=
      ∏ b,∑ a,w b a*f b a := by
  simp only [finiteExpectation,productWeights,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun b a => w b a*f b a)).symm

omit [Fintype A] in
lemma product_one_coordinate (b : B) (f : A → ℝ) (D : B → A) :
    (∏ i,if i=b then f (D i) else 1)=f (D b) := by
  simp

lemma expectation_coordinate (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1)
    (b : B) (f : A → ℝ) :
    finiteExpectation (productWeights w) (fun D => f (D b))=∑ a,w b a*f a := by
  have h := expectation_product w (fun i a => if i=b then f a else 1)
  simp only [product_one_coordinate] at h
  rw [h]
  have hh (i : B) : (∑ a,w i a*(if i=b then f a else 1))=
      if i=b then ∑ a,w b a*f a else 1 := by
    by_cases hi : i=b
    · subst i; simp
    · simp [hi,hw]
  simp_rw [hh]
  simp

section Linear
variable {E I : Type*} [Fintype E] [Fintype I] (v : E → ℝ)
lemma finiteExpectation_sum (F : I → E → ℝ) :
    finiteExpectation v (fun x => ∑ i,F i x)=∑ i,finiteExpectation v (F i) := by
  simp only [finiteExpectation,Finset.mul_sum]
  exact Finset.sum_comm
end Linear
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A : Type*} [Fintype A]
namespace MatrixCoupling
variable {p q : A → ℝ}

lemma symm_cost (r : MatrixCoupling p q) (d : A → A → ℝ) (hd : ∀ a b,d a b=d b a) :
    r.symm.cost d=r.cost d := by
  unfold cost symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hd]

end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators

lemma symbolCost_comm {A : Type*} (a b : A) : symbolCost a b=symbolCost b a := by
  classical
  simp only [symbolCost,eq_comm]
lemma nameCost_comm {A : Type*} {n : ℕ} (a b : Fin n → A) : nameCost a b=nameCost b a := by
  simp only [nameCost,symbolCost_comm]

lemma coupling_of_observation_lawClose {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map p) (ν.map q) ε) :
    ∃ R : MatrixCoupling (mass μ p) (mass ν q),R.cost symbolCost≤ε := by
  classical
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨r,hr,hrow,hcol,hcost⟩ := finite_coupling_of_lawClose (μ.map p) (ν.map q) h
  let R : MatrixCoupling (mass μ p) (mass ν q) := {
    weight := r
    nonneg := hr
    row := fun a => (hrow a).trans (map_measureReal_apply hp (measurableSet_singleton a))
    col := fun a => (hcol a).trans (map_measureReal_apply hq (measurableSet_singleton a)) }
  exact ⟨R,hcost⟩

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ChunkNameCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
lemma symbolCost_le_one {A : Type*} (a b : A) : symbolCost a b≤1 := by
  unfold symbolCost
  split <;> norm_num
lemma nameCost_le_card {A : Type*} {n : ℕ} (v w : Fin n → A) : nameCost v w≤(n : ℝ) := by
  calc
    _≤∑ _i : Fin n,(1 : ℝ) := Finset.sum_le_sum (fun i _ => symbolCost_le_one _ _)
    _=_ := by simp
lemma nameCost_le_chunkCost {A : Type*} {n : ℕ} (v w : Fin n → A) :
    nameCost v w≤(n : ℝ)*symbolCost v w := by
  classical
  by_cases h : v=w
  · subst w; simp only [nameCost_self,symbolCost_self,mul_zero,le_refl]
  · simpa only [symbolCost,ite_eq_right h,mul_one] using nameCost_le_card v w

theorem nameCost_le_retained_chunks {A : Type*} (k g n : ℕ)
    (v w : Fin (n*(k+g)) → A) :
    nameCost v w≤(k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ) := by
  have he : nameCost v w=∑ j : Fin n,∑ r : Fin (k+g),
      symbolCost (v (finProdFinEquiv (j,r))) (w (finProdFinEquiv (j,r))) := by
    rw [nameCost,←Equiv.sum_comp finProdFinEquiv (fun i => symbolCost (v i) (w i)),Fintype.sum_prod_type]
  rw [he]
  have hb (j : Fin n) : (∑ r : Fin (k+g),
      symbolCost (v (finProdFinEquiv (j,r))) (w (finProdFinEquiv (j,r))))≤
      (k : ℝ)*symbolCost (selectChunks k g n v j) (selectChunks k g n w j)+(g : ℝ) := by
    rw [Fin.sum_univ_add]
    have hp : (∑ r : Fin k,symbolCost (v (finProdFinEquiv (j,Fin.castAdd g r)))
        (w (finProdFinEquiv (j,Fin.castAdd g r))))=
        nameCost (selectChunks k g n v j) (selectChunks k g n w j) := by
      apply Finset.sum_congr rfl
      intro r _
      unfold selectChunks
      congr 2 <;> apply Fin.ext <;> dsimp [finProdFinEquiv] <;> ring
    have hg : (∑ r : Fin g,symbolCost (v (finProdFinEquiv (j,Fin.natAdd k r)))
        (w (finProdFinEquiv (j,Fin.natAdd k r))))≤(g : ℝ) := by
      calc
        _≤∑ _r : Fin g,(1 : ℝ) := Finset.sum_le_sum (fun r _ => symbolCost_le_one _ _)
        _=_ := by simp
    rw [hp]
    have hc := nameCost_le_chunkCost (selectChunks k g n v j) (selectChunks k g n w j)
    linarith
  calc
    _≤∑ j : Fin n,((k : ℝ)*symbolCost (selectChunks k g n v j) (selectChunks k g n w j)+(g : ℝ)) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _=_ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,nameCost]
      norm_cast

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
namespace MatrixCoupling
variable {A B : Type*} [Fintype A] [Fintype B] {p : A → ℝ} {q : B → ℝ}
lemma cost_mono (r : MatrixCoupling p q) (d e : A → B → ℝ) (h : ∀ a b,d a b≤e a b) :
    r.cost d ≤ r.cost e :=
  Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
    mul_le_mul_of_nonneg_left (h a b) (r.nonneg a b)))
lemma cost_affine (r : MatrixCoupling p q) (hp : ∑ a,p a=1) (K C : ℝ) (d : A → B → ℝ) :
    r.cost (fun a b => K*d a b+C)=K*r.cost d+C := by
  unfold cost
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · simp only [←Finset.sum_mul,r.row,hp,one_mul]
end MatrixCoupling

variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

theorem lift_observation_transport (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    (c : A → B) (S : MatrixCoupling (mass μ (c ∘ p)) (mass ν (c ∘ q)))
    (d : B → B → ℝ) (hdiag : ∀ b,d b b=0) (htri : ∀ a b c,d a c≤d a b+d b c) :
    ∃ R : MatrixCoupling (mass μ p) (mass ν q),R.cost (fun a b => d (c a) (c b))≤S.cost d := by
  have hc : Measurable c := measurable_of_countable c
  let P := MatrixCoupling.observations μ p (c ∘ p) hp (hc.comp hp)
  let Q := MatrixCoupling.observations ν (c ∘ q) q (hc.comp hq) hq
  have hP : P.cost (fun a b => d (c a) b)=0 := by
    rw [MatrixCoupling.observations_cost]
    simp only [Function.comp_apply,hdiag,integral_zero]
  have hQ : Q.cost (fun a b => d a (c b))=0 := by
    rw [MatrixCoupling.observations_cost]
    simp only [Function.comp_apply,hdiag,integral_zero]
  refine ⟨(P.comp S).comp Q,?_⟩
  have h1 := MatrixCoupling.comp_cost_le P S (fun a b => d (c a) b) d
    (fun a b => d (c a) b) (fun a b v => htri (c a) b v)
  have h2 := MatrixCoupling.comp_cost_le (P.comp S) Q (fun a b => d (c a) b)
    (fun a b => d a (c b)) (fun a b => d (c a) (c b)) (fun a b v => htri (c a) b (c v))
  rw [hP,zero_add] at h1
  rw [hQ,add_zero] at h2
  exact h2.trans h1

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set
open scoped BigOperators ENNReal
variable {X A B C D : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma cond_factor_chain (q : X → B) (r : X → A) (d : B → D)
    (hq : Measurable q) (hr : Measurable r) :
    cond μ q r=cond μ (d ∘ q) r+cond μ q (fun x => (d (q x),r x)) := by
  have hd : Measurable (d ∘ q) := (measurable_of_countable d).comp hq
  have he : cond μ (fun x => (d (q x),q x)) r=cond μ q r := by
    apply le_antisymm
    · exact cond_factor_left μ q r (fun b => (d b,b)) hq hr
    · exact cond_factor_left μ (fun x => (d (q x),q x)) r Prod.snd (hd.prodMk hq) hr
  rw [←he,cond_chain]
  rfl

theorem conditional_defect_data_processing (p : X → A) (q : X → B)
    (c : A → C) (d : B → D) (hp : Measurable p) (hq : Measurable q) :
    cond μ (d ∘ q) (c ∘ p)-cond μ (d ∘ q) p≤
      cond μ q (c ∘ p)-cond μ q p := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  have hd : Measurable (d ∘ q) := (measurable_of_countable d).comp hq
  have h1 := cond_factor_chain μ q (c ∘ p) d hq hc
  have h2 := cond_factor_chain μ q p d hq hp
  have h3 := cond_factor_right μ q (fun x => (d (q x),p x))
    (fun v : D×A => (v.1,c v.2)) hq (hd.prodMk hp)
  change cond μ q (fun x => (d (q x),p x))≤
    cond μ q (fun x => (d (q x),c (p x))) at h3
  simp only [Function.comp_def] at h1 h2 ⊢
  linarith

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open scoped BigOperators

lemma log_ratio_hellinger_bound {p q : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hs : p≠0 → q≠0) : 2*p-2*Real.sqrt p*Real.sqrt q≤p*(Real.log p-Real.log q) := by
  by_cases hp0 : p=0
  · simp [hp0]
  have hp' : 0<p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0<q := lt_of_le_of_ne hq (Ne.symm (hs hp0))
  have ha : 0<Real.sqrt p := Real.sqrt_pos.mpr hp'
  have hb : 0<Real.sqrt q := Real.sqrt_pos.mpr hq'
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb ha)) (mul_nonneg (by norm_num : (0 : ℝ)≤2) hp)
  rw [Real.log_div hb.ne' ha.ne',Real.log_sqrt hq,Real.log_sqrt hp] at hh
  have hr : p*(Real.sqrt q/Real.sqrt p)=Real.sqrt p*Real.sqrt q := by
    calc
      _=(Real.sqrt p*Real.sqrt p)*(Real.sqrt q/Real.sqrt p) :=
        congrArg (fun t : ℝ => t*(Real.sqrt q/Real.sqrt p)) (Real.mul_self_sqrt hp).symm
      _=_ := by field_simp
  have he : 2*p*(Real.sqrt q/Real.sqrt p-1)=2*Real.sqrt p*Real.sqrt q-2*p := by
    calc
      _=2*(p*(Real.sqrt q/Real.sqrt p))-2*p := by ring
      _=_ := by rw [hr]; ring
  rw [he] at hh
  nlinarith

theorem finite_pinsker_sq {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hp1 : ∑ a,p a=1) (hq1 : ∑ a,q a=1) (hs : ∀ a,p a≠0 → q a≠0) :
    (∑ a,|p a-q a|)^2≤4*relativeInformation p q := by
  let u : A → ℝ := fun a => Real.sqrt (p a)-Real.sqrt (q a)
  let v : A → ℝ := fun a => Real.sqrt (p a)+Real.sqrt (q a)
  have hu (a) : (u a)^2=p a+q a-2*Real.sqrt (p a)*Real.sqrt (q a) := by
    dsimp [u]
    nlinarith [Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
  have huv (a) : |p a-q a|=|u a| * v a := by
    have he : p a-q a=u a*v a := by
      dsimp [u,v]
      nlinarith [Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
    rw [he,abs_mul,abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hH : (∑ a,(u a)^2) ≤ relativeInformation p q := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => log_ratio_hellinger_bound (hp a) (hq a) (hs a))
    have he : (∑ a,(u a)^2)=(∑ a,(2*p a-2*Real.sqrt (p a)*Real.sqrt (q a))) := by
      simp_rw [hu]
      rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hp1,hq1,Finset.sum_sub_distrib,←Finset.mul_sum,hp1]
      norm_num
    rw [he]
    exact hh
  have hV : (∑ a,(v a)^2)≤4 := by
    have hv (a) : (v a)^2≤2*p a+2*q a := by
      dsimp [v]
      nlinarith [sq_nonneg (u a),hu a,Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
    calc
      _≤∑ a,(2*p a+2*q a) := Finset.sum_le_sum (fun a _ => hv a)
      _=4 := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hp1,hq1]; norm_num
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ) (fun a => |u a|) v
  simp only [sq_abs] at hc
  simp_rw [huv]
  calc
    _≤(∑ a,(u a)^2)*(∑ a,(v a)^2) := hc
    _≤(∑ a,(u a)^2)*4 := mul_le_mul_of_nonneg_left hV (Finset.sum_nonneg (fun a _ => sq_nonneg (u a)))
    _≤4*relativeInformation p q := by nlinarith [hH]

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ConditionalRefinementInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] in
lemma mass_factor_le (p : X → A) (g : A → B) (a : A) :
    mass μ p a≤ mass μ (g ∘ p) (g a) := by
  unfold mass
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono
  intro x hx
  exact congrArg g hx

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [IsProbabilityMeasure μ] in
lemma refinementCopyWeights_nonneg (p : X → A) (q : X → B) (c : A → C) (a : A) (b : B) :
    0 ≤ refinementCopyWeights μ p q c a b :=
  div_nonneg (mul_nonneg (mass_nonneg _ _ _) (mass_nonneg _ _ _)) (mass_nonneg _ _ _)

omit [Fintype C] in
lemma refinementCopyWeights_row (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) (a : A) :
    (∑ b,refinementCopyWeights μ p q c a b)=mass μ p a := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  by_cases hz : mass μ (c ∘ p) (c a)=0
  · have hp0 : mass μ p a=0 := le_antisymm ((mass_factor_le μ p c a).trans (le_of_eq hz)) (mass_nonneg _ _ _)
    simp only [refinementCopyWeights,hp0,zero_mul,zero_div,Finset.sum_const_zero]
  · have hrow : (∑ b,mass μ (fun x => (c (p x),q x)) (c a,b))=mass μ (c ∘ p) (c a) :=
      (mass_joint_row μ (c ∘ p) q hc hq (c a)).symm
    simp only [refinementCopyWeights,←Finset.sum_div,←Finset.mul_sum,hrow,mul_div_cancel_right₀ _ hz]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] in
lemma refinementCopyWeights_support (p : X → A) (q : X → B) (c : A → C) (a : A) (b : B)
    (h : mass μ (fun x => (p x,q x)) (a,b)≠0) : refinementCopyWeights μ p q c a b≠0 := by
  have hu : 0 < mass μ (fun x => (p x,q x)) (a,b) := lt_of_le_of_ne (mass_nonneg _ _ _) (Ne.symm h)
  have hp : 0 < mass μ p a := hu.trans_le (mass_factor_le μ (fun x => (p x,q x)) Prod.fst (a,b))
  have hcb : 0 < mass μ (fun x => (c (p x),q x)) (c a,b) :=
    hu.trans_le (mass_factor_le μ (fun x => (p x,q x)) (fun ab => (c ab.1,ab.2)) (a,b))
  have hc : 0 < mass μ (c ∘ p) (c a) := hp.trans_le (mass_factor_le μ p c a)
  exact ne_of_gt (div_pos (mul_pos hp hcb) hc)

theorem refinement_relativeInformation (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) :
    relativeInformation (fun ab : A×B => mass μ (fun x => (p x,q x)) ab)
      (fun ab => refinementCopyWeights μ p q c ab.1 ab.2)=
        cond μ q (c ∘ p)-cond μ q p := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  let pq : X → A×B := fun x => (p x,q x)
  let cq : X → C×B := fun x => (c (p x),q x)
  have hpq : Measurable pq := hp.prodMk hq
  have hcq : Measurable cq := hc.prodMk hq
  unfold relativeInformation
  rw [sum_mass_mul_integral μ pq hpq]
  have he : (fun x => Real.log (mass μ pq (pq x))-
      Real.log (refinementCopyWeights μ p q c (p x) (q x)))=ᵐ[μ]
      (fun x => -information μ pq x+information μ p x+information μ cq x-information μ (c ∘ p) x) := by
    filter_upwards [ae_mass_positive μ p,ae_mass_positive μ cq,ae_mass_positive μ (c ∘ p)] with x hx hcx hcpx
    dsimp only [refinementCopyWeights,information,pq,cq,Function.comp_apply] at *
    rw [Real.log_div (mul_pos hx hcx).ne' hcpx.ne',Real.log_mul hx.ne' hcx.ne']
    ring
  rw [integral_congr_ae he]
  rw [integral_sub (f:=fun x => -information μ pq x+information μ p x+information μ cq x)
    (g:=fun x => information μ (c ∘ p) x) (((information_integrable μ pq hpq).neg.add (information_integrable μ p hp)).add
    (information_integrable μ cq hcq)) (information_integrable μ (c ∘ p) hc)]
  rw [integral_add (f:=fun x => -information μ pq x+information μ p x) (g:=fun x => information μ cq x) ((information_integrable μ pq hpq).neg.add (information_integrable μ p hp))
      (information_integrable μ cq hcq),integral_add (f:=fun x => -information μ pq x) (g:=fun x => information μ p x) (information_integrable μ pq hpq).neg
      (information_integrable μ p hp),integral_neg]
  simp only [integral_information μ pq hpq,integral_information μ p hp,
    integral_information μ cq hcq,integral_information μ (c ∘ p) hc]
  unfold cond
  rw [obs_pair_swap μ q (c ∘ p),obs_pair_swap μ q p]
  dsimp only [pq,cq,Function.comp_apply]
  ring

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma finite_l1_le_two_of_lawClose {ε : ℝ} (h : LawClose μ ν ε) :
    (∑ a,|μ.real {a}-ν.real {a}|)≤2*ε := by
  have he (a : A) : |μ.real {a}-ν.real {a}|=
      max (μ.real {a}-ν.real {a}) 0+max (ν.real {a}-μ.real {a}) 0 := by
    rcases le_total (μ.real {a}) (ν.real {a}) with ha|ha
    · rw [abs_of_nonpos (sub_nonpos.mpr ha),max_eq_right (sub_nonpos.mpr ha),max_eq_left (sub_nonneg.mpr ha)]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr ha),max_eq_left (sub_nonneg.mpr ha),max_eq_right (sub_nonpos.mpr ha)]
      ring
  simp_rw [he,Finset.sum_add_distrib]
  linarith [positive_mass_difference_le μ ν h,positive_mass_difference_le ν μ h.symm]

lemma lawClose_of_finite_l1 {ε : ℝ} (h : (∑ a,|μ.real {a}-ν.real {a}|)≤ε) : LawClose μ ν ε := by
  classical
  intro D _hD
  let S : Finset A := Finset.univ.filter (fun a => a∈D)
  have he : (S : Set A)=D := by ext a; simp [S]
  have hμ : μ.real D=∑ a∈S,μ.real {a} := by rw [←he]; exact (sum_measureReal_singleton S).symm
  have hν : ν.real D=∑ a∈S,ν.real {a} := by rw [←he]; exact (sum_measureReal_singleton S).symm
  rw [hμ,hν,←Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ h)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _ => abs_nonneg _)

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma sum_mass_factor_mul (p : X → A) (hp : Measurable p) (c : A → C) (F : C → ℝ) :
    (∑ a,mass μ p a*F (c a))=∑ d,mass μ (c ∘ p) d*F d := by
  calc
    _ = ∫ x, (F ∘ c) (p x) ∂μ := sum_mass_mul_integral μ p hp (F ∘ c)
    _ = _ := (sum_mass_mul_integral μ (c ∘ p)
      ((measurable_of_countable c).comp hp) F).symm

omit [MeasurableSingletonClass B] in
lemma refinement_distance_eq (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (_ : Measurable q) :
    (∑ a,∑ b,|refinementCopyWeights μ p q c a b-mass μ p a*mass μ q b|)=
      ∑ d,∑ b,|mass μ (fun x => (c (p x),q x)) (d,b)-mass μ (c ∘ p) d*mass μ q b| := by
  have he (a : A) (b : B) : |refinementCopyWeights μ p q c a b-mass μ p a*mass μ q b|=
      mass μ p a*|mass μ (fun x => (c (p x),q x)) (c a,b)/mass μ (c ∘ p) (c a)-mass μ q b| := by
    unfold refinementCopyWeights
    rw [mul_div_assoc,←mul_sub,abs_mul,abs_of_nonneg (mass_nonneg μ p a)]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hec (b : B) := sum_mass_factor_mul μ p hp c
    (fun d => |mass μ (fun x => (c (p x),q x)) (d,b)/mass μ (c ∘ p) d-mass μ q b|)
  simp_rw [hec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  let u := mass μ (c ∘ p) d
  let v := mass μ (fun x => (c (p x),q x)) (d,b)
  have hu : 0≤u := mass_nonneg _ _ _
  have hv : 0≤v := mass_nonneg _ _ _
  have hvu : v≤u := mass_factor_le μ (fun x => (c (p x),q x)) Prod.fst (d,b)
  change u*|v/u-mass μ q b|=|v-u*mass μ q b|
  by_cases hu0 : u=0
  · have hv0 : v=0 := le_antisymm (hvu.trans (le_of_eq hu0)) hv
    simp [hu0,hv0]
  · calc
      _ = |u*(v/u-mass μ q b)| := by rw [abs_mul,abs_of_nonneg hu]
      _ = _ := by congr 1; rw [mul_sub,mul_div_cancel₀ _ hu0]

theorem lawClose_of_coarse_independence (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose (μ.map (fun x => (c (p x),q x)))
      ((μ.map (c ∘ p)).prod (μ.map q)) ε)
    (hdef : 4*(cond μ q (c ∘ p)-cond μ q p)≤δ^2) :
    LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) (δ+2*ε) := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (c ∘ p)) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (fun x => (p x,q x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (fun x => (c (p x),q x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  let u : A×B → ℝ := fun ab => mass μ (fun x => (p x,q x)) ab
  let v : A×B → ℝ := fun ab => refinementCopyWeights μ p q c ab.1 ab.2
  have hu1 : (∑ ab,u ab)=1 := by simp only [u,mass_sum μ _ (hp.prodMk hq),measure_univ,ENNReal.toReal_one]
  have hv1 : (∑ ab,v ab)=1 := by
    rw [Fintype.sum_prod_type]
    simp only [v,refinementCopyWeights_row μ p q c hp hq,mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
  have hpen := finite_pinsker_sq u v (fun _ => mass_nonneg _ _ _)
    (fun ab => refinementCopyWeights_nonneg μ p q c ab.1 ab.2) hu1 hv1
    (fun ab => refinementCopyWeights_support μ p q c ab.1 ab.2)
  have hinfo : relativeInformation u v=cond μ q (c ∘ p)-cond μ q p :=
    refinement_relativeInformation μ p q c hp hq
  rw [hinfo] at hpen
  have hUV : (∑ ab,|u ab-v ab|)≤δ := by nlinarith [hpen.trans hdef]
  have hmap (a : A) (b : B) : (μ.map (fun x => (p x,q x))).real {(a,b)}=u (a,b) :=
    map_measureReal_apply (hp.prodMk hq) (measurableSet_singleton (a,b))
  have hmapC (d : C) (b : B) : (μ.map (fun x => (c (p x),q x))).real {(d,b)}=
      mass μ (fun x => (c (p x),q x)) (d,b) :=
    map_measureReal_apply (hc.prodMk hq) (measurableSet_singleton (d,b))
  have hprod (a : A) (b : B) : ((μ.map p).prod (μ.map q)).real {(a,b)}=mass μ p a*mass μ q b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hprodC (d : C) (b : B) : ((μ.map (c ∘ p)).prod (μ.map q)).real {(d,b)}=
      mass μ (c ∘ p) d*mass μ q b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hc (measurableSet_singleton d),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hcoarse := finite_l1_le_two_of_lawClose _ _ hclose
  rw [Fintype.sum_prod_type] at hcoarse
  simp only [hmapC,hprodC] at hcoarse
  have hVP : (∑ ab : A×B,|v ab-mass μ p ab.1*mass μ q ab.2|)≤2*ε := by
    rw [Fintype.sum_prod_type]
    exact (refinement_distance_eq μ p q c hp hq).le.trans hcoarse
  apply lawClose_of_finite_l1
  rw [Fintype.sum_prod_type]
  simp only [hmap,hprod]
  rw [Fintype.sum_prod_type] at hUV hVP
  calc
    _≤∑ a,∑ b,(|u (a,b)-v (a,b)|+|v (a,b)-mass μ p a*mass μ q b|) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => abs_sub_le _ _ _))
    _=(∑ a,∑ b,|u (a,b)-v (a,b)|)+(∑ a,∑ b,|v (a,b)-mass μ p a*mass μ q b|) := by simp only [Finset.sum_add_distrib]
    _≤δ+2*ε := add_le_add hUV hVP

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [MeasurableSpace B]

lemma independence_law_stable (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : X → B) (p' : Y → A) (q' : Y → B)
    (hp : Measurable p) (hq : Measurable q) (hp' : Measurable p') (hq' : Measurable q')
    {ε δ : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) (ν.map (fun y => (p' y,q' y))) δ)
    (hi : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (ν.map (fun y => (p' y,q' y))) ((ν.map p').prod (ν.map q')) (ε+3*δ) := by
  have hleft := h.map measurable_fst
  have hright := h.map measurable_snd
  rw [Measure.map_map measurable_fst (hp.prodMk hq),Measure.map_map measurable_fst (hp'.prodMk hq')] at hleft
  rw [Measure.map_map measurable_snd (hp.prodMk hq),Measure.map_map measurable_snd (hp'.prodMk hq')] at hright
  change LawClose (μ.map p) (ν.map p') δ at hleft
  change LawClose (μ.map q) (ν.map q') δ at hright
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map p') := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map q') := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  convert h.symm.triangle (hi.triangle (hleft.prod hright)) using 1 <;> first | rfl | ring

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FiniteBinCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma wordPack_apply (f : Ω → Ω) (p : Ω → α) (n m : ℕ) (x : Ω) :
    wordPack n m (word f p (n*m) x)=word (f^[m]) (word f p m) n x := by
  funext i j
  simp only [wordPack,Equiv.trans_apply,Equiv.curry_apply,word]
  change p (f^[j.val+m*i.val] x)=p (f^[j.val] ((f^[m])^[i.val] x))
  rw [Function.iterate_add_apply,Function.iterate_mul]

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_IidFiniteWindowApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

 theorem coupling_step_finite (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (t : A → ℝ) (r : MatrixCoupling (mass μ p) t)
    (d : A → A → ℝ) (hdiag : ∀ a,d a a=0) (htri : ∀ a b c,d a c≤d a b+d b c)
    {ε : ℝ}
    (hclose : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    ∃ s : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*t ba.2),
      s.cost (fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2)≤ε+r.cost d := by
  classical
  let u : A → B → ℝ := fun a b => mass μ (fun x => (p x,q x)) (a,b)
  let v : A → B → ℝ := fun a b => mass μ p a*mass μ q b
  have hrow (a) : ∑ b,u a b=∑ b,v a b := by
    rw [←mass_joint_row μ p q hp hq]
    dsimp only [v]
    rw [←Finset.mul_sum,mass_sum μ q hq]
    simp
  have hc (a) := finite_maximal_coupling_equal_mass (u a) (v a)
    (fun b => mass_nonneg μ _ _) (fun b => mul_nonneg (mass_nonneg μ _ _) (mass_nonneg μ _ _)) (hrow a)
  choose w hw hwrow hwcol hwerr using hc
  let R : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*mass μ p ba.2) := {
    weight := fun ba ca => if ba.2=ca.2 then w ba.2 ba.1 ca.1 else 0
    nonneg := fun ba ca => by split
                              · exact hw _ _ _
                              · exact le_rfl
    row := fun ba => by
      simp only [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      rw [hwrow]
      exact mass_joint_swap μ p q ba.2 ba.1
    col := fun ca => by
      simp only [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rw [hwcol]
      exact mul_comm _ _ }
  let S := (MatrixCoupling.diagonal (mass μ q) (mass_nonneg μ q)).product r
  let cost : (B×A) → (B×A) → ℝ := fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2
  have hR : R.cost cost≤ε := by
    have he : R.cost cost=∑ a,∑ b,∑ c,w a b c*symbolCost b c := by
      simp only [MatrixCoupling.cost,R,cost,Fintype.sum_prod_type]
      have hh (b : B) (a : A) (c : B) :
          (∑ a', (if a=a' then w a b c else 0)*(symbolCost b c+d a a'))=
            w a b c*symbolCost b c := by
        simp [ite_mul,hdiag]
      simp only [hh]
      rw [Finset.sum_comm]
    rw [he]
    have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
    have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
    have : IsProbabilityMeasure (μ.map (fun x => (p x,q x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
    have hprod (a : A) (b : B) : ((μ.map p).prod (μ.map q)).real {(a,b)}=v a b := by
      rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
      rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
        map_measureReal_apply hq (measurableSet_singleton b)]
      rfl
    have hsum : (∑ a,∑ b,max (u a b-v a b) 0)≤ε := by
      have h := positive_mass_difference_le _ _ hclose
      rw [Fintype.sum_prod_type] at h
      have hu (a : A) (b : B) : (μ.map (fun x => (p x,q x))).real {(a,b)}=u a b :=
        map_measureReal_apply (hp.prodMk hq) (measurableSet_singleton (a,b))
      simpa only [hu,hprod] using h
    apply le_trans _ hsum
    apply Finset.sum_le_sum
    intro a _
    simpa only [symbolCost] using (hwerr a).le
  have hS : S.cost cost=r.cost d := by
    rw [MatrixCoupling.product_cost]
    · rw [MatrixCoupling.diagonal_cost _ _ symbolCost symbolCost_self,zero_add]
    · simpa using mass_sum μ q hq
    · simpa using mass_sum μ p hp
  refine ⟨R.comp S,?_⟩
  have h := MatrixCoupling.comp_cost_le R S cost cost cost (fun a b c => by
    dsimp [cost]
    have h1 := symbolCost_triangle a.1 b.1 c.1
    have h2 := htri a.2 b.2 c.2
    linarith)
  exact h.trans (by rw [hS]; linarith)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

variable (μ : Measure X)

lemma obs_finiteName_zero [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [StandardBorelSpace X] [Nonempty A] [IsProbabilityMeasure μ]
    (q : ℕ → X → A) (i : ℕ) : obs μ (finiteName q i 0)=0 := by
  have heq : finiteName q i 0=(fun _ => (fun j : Fin 0 => j.elim0 : Fin 0 → A)) := by
    funext x j
    exact j.elim0
  rw [heq,obs_const]

lemma independentNameWeights_cons_finite [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [StandardBorelSpace X] [Nonempty A] [IsProbabilityMeasure μ]
    (q : ℕ → X → A) (i n : ℕ) (w : Fin (n+1) → A) :
    independentNameWeights μ q i (n+1) w=
      mass μ (q i) (w 0)*independentNameWeights μ q (i+1) n (Fin.tail w) := by
  rw [independentNameWeights,Fin.prod_univ_succ]
  simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Fin.tail,independentNameWeights]
  congr 2
  funext j
  congr 2
  omega

lemma mass_equiv_inverse_finite [StandardBorelSpace X] [IsProbabilityMeasure μ]
    {C D : Type*} [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]
    (p : X → C) (e : C ≃ D) (d : D) : mass μ (e ∘ p) d=mass μ p (e.symm d) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Function.comp_apply,← Equiv.eq_symm_apply]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem sequential_coupling_budgets (q : ℕ → X → A) (hq : ∀ i,Measurable (q i))
    (N : ℕ) (b : ℕ → ℝ)
    (hremote : ∀ i n : ℕ,i+n+1≤N → LawClose
      (μ.map (fun x => (finiteName q (i+1) n x,q i x)))
      ((μ.map (finiteName q (i+1) n)).prod (μ.map (q i))) (b i)) :
    ∀ i n : ℕ,i+n≤N → ∃ R : MatrixCoupling (mass μ (finiteName q i n)) (independentNameWeights μ q i n),
      R.cost nameCost≤∑ j : Fin n,b (i+j.val) := by
  intro i n hi
  induction n generalizing i with
  | zero =>
    have hm (w : Fin 0 → A) : mass μ (finiteName q i 0) w=1 := by
      have he : (finiteName q i 0) ⁻¹' {w}=univ := by
        ext x
        simp only [mem_preimage,mem_singleton_iff,mem_univ,iff_true]
        funext j
        exact j.elim0
      simp [mass,he]
    let R : MatrixCoupling (mass μ (finiteName q i 0)) (independentNameWeights μ q i 0) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun w => by simp [hm]
      col := fun w => by simp [independentNameWeights] }
    refine ⟨R,?_⟩
    simp [MatrixCoupling.cost,nameCost]
  | succ n ih =>
    obtain ⟨r,hr⟩ := ih (i+1) (by omega)
    have hc := hremote i n hi
    obtain ⟨s,hs⟩ := coupling_step_finite μ (finiteName q (i+1) n) (q i)
      (finiteName_measurable q hq (i+1) n) (hq i)
      (independentNameWeights μ q (i+1) n) r nameCost nameCost_self nameCost_triangle hc
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := s.reindex e.symm e.symm
    have hm (w : Fin (n+1) → A) :
        mass μ (fun x => (q i x,finiteName q (i+1) n x)) (e.symm w)=mass μ (finiteName q i (n+1)) w := by
      rw [←mass_equiv_inverse_finite μ _ e w]
      congr 1
      funext x
      exact (finiteName_cons q i n x).symm
    have hw (w : Fin (n+1) → A) :
        mass μ (q i) (e.symm w).1*independentNameWeights μ q (i+1) n (e.symm w).2=
          independentNameWeights μ q i (n+1) w := (independentNameWeights_cons_finite μ q i n w).symm
    let R : MatrixCoupling (mass μ (finiteName q i (n+1))) (independentNameWeights μ q i (n+1)) := {
      weight := t.weight
      nonneg := t.nonneg
      row := fun w => (t.row w).trans (hm w)
      col := fun w => (t.col w).trans (hw w) }
    have hcost : R.cost nameCost=s.cost (fun a b => symbolCost a.1 b.1+nameCost a.2 b.2) := by
      change t.cost nameCost=_
      have he : (nameCost : (Fin (n+1) → A) → (Fin (n+1) → A) → ℝ)=
          (fun v w => symbolCost (e.symm v).1 (e.symm w).1+nameCost (e.symm v).2 (e.symm w).2) := by
        funext v w
        exact nameCost_split v w
      rw [he]
      exact MatrixCoupling.reindex_cost s e.symm e.symm
        (fun a b : A×(Fin n → A) => symbolCost a.1 b.1+nameCost a.2 b.2)
    refine ⟨R,?_⟩
    rw [hcost,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    have he : (∑ j : Fin n,b (i+(j.val+1)))=∑ j : Fin n,b (i+1+j.val) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      omega
    rw [he]
    exact hs.trans (add_le_add (le_refl _) hr)

lemma finiteName_entropy_chain (q : ℕ → X → A) (i n : ℕ) :
    obs μ (finiteName q i n)=∑ j : Fin n,StandardMapEntropy.Entropy.cond μ
      (q (i+j.val)) (finiteName q (i+j.val+1) (n-j.val-1)) := by
  induction n generalizing i with
  | zero => simp [obs_finiteName_zero]
  | succ n ih =>
    have he : obs μ (finiteName q i (n+1))=
        StandardMapEntropy.Entropy.cond μ (q i) (finiteName q (i+1) n)+obs μ (finiteName q (i+1) n) := by
      let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
      have heq : finiteName q i (n+1)=e ∘ (fun x => (q i x,finiteName q (i+1) n x)) :=
        funext (finiteName_cons q i n)
      rw [heq,obs_equiv]
      unfold StandardMapEntropy.Entropy.cond
      ring
    rw [he,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Nat.sub_zero,Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hl : n+1-(j.val+1)-1=n-j.val-1 := by omega
    have hi : i+1+j.val=i+(j.val+1) := by omega
    simp only [hi]
    exact congrArg (fun m => StandardMapEntropy.Entropy.cond μ (q (i+(j.val+1)))
      (finiteName q (i+(j.val+1)+1) m)) hl.symm
end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_CoarseConditionalBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]

theorem coarse_conditional_budget (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (q : X → B) (c : A → C) (d : B → D)
    (hp : Measurable p) (hq : Measurable q) {ε τ : ℝ} (hτ : 0<τ)
    (hclose : LawClose (μ.map (fun x => (c (p x),d (q x))))
      ((μ.map (c ∘ p)).prod (μ.map (d ∘ q))) ε) :
    LawClose (μ.map (fun x => (p x,d (q x)))) ((μ.map p).prod (μ.map (d ∘ q)))
      ((StandardMapEntropy.Entropy.cond μ q (c ∘ p)-StandardMapEntropy.Entropy.cond μ q p)/τ+τ+2*ε) := by
  let Δ := StandardMapEntropy.Entropy.cond μ q (c ∘ p)-StandardMapEntropy.Entropy.cond μ q p
  have hΔ : 0≤Δ := sub_nonneg.mpr (cond_factor_right μ q p c hq hp)
  have hdata := conditional_defect_data_processing μ p q c d hp hq
  have hδ : 0≤Δ/τ+τ := by positivity
  have hsq : 4*Δ≤(Δ/τ+τ)^2 := by
    have he : (Δ/τ)*τ=Δ := div_mul_cancel₀ _ hτ.ne'
    nlinarith [sq_nonneg (Δ/τ-τ)]
  exact lawClose_of_coarse_independence μ p (d ∘ q) c hp
    ((measurable_of_countable d).comp hq) hδ hclose ((by linarith :
      4*(StandardMapEntropy.Entropy.cond μ (d ∘ q) (c ∘ p)-
        StandardMapEntropy.Entropy.cond μ (d ∘ q) p)≤4*Δ).trans hsq)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem finite_local_entropy_bridge (q : ℕ → X → B) (hq : ∀ i,Measurable (q i))
    (d : B → A) (N : ℕ) (C : ℕ → Type*) [∀ i,Fintype (C i)]
    [∀ i,MeasurableSpace (C i)] [∀ i,MeasurableSingletonClass (C i)]
    (c : (i : ℕ) → (Fin (N-i-1) → B) → C i) (ε : ℕ → ℝ) {τ : ℝ} (hτ : 0<τ)
    (hlocal : ∀ i : ℕ,i<N → LawClose
      (μ.map (fun x => (c i (finiteName q (i+1) (N-i-1) x),d (q i x))))
      ((μ.map (c i ∘ finiteName q (i+1) (N-i-1))).prod (μ.map (d ∘ q i))) (ε i)) :
    ∃ R : MatrixCoupling (mass μ (finiteName (fun i => d ∘ q i) 0 N))
        (independentNameWeights μ (fun i => d ∘ q i) 0 N),
      R.cost nameCost≤
        ((∑ j : Fin N,StandardMapEntropy.Entropy.cond μ (q j.val)
          (c j.val ∘ finiteName q (j.val+1) (N-j.val-1)))-obs μ (finiteName q 0 N))/τ+
        (N : ℝ)*τ+2*∑ j : Fin N,ε j.val := by
  let b : ℕ → ℝ := fun i =>
    (StandardMapEntropy.Entropy.cond μ (q i) (c i ∘ finiteName q (i+1) (N-i-1))-
      StandardMapEntropy.Entropy.cond μ (q i) (finiteName q (i+1) (N-i-1)))/τ+τ+2*ε i
  have hremote : ∀ i n : ℕ,i+n+1≤N → LawClose
      (μ.map (fun x => (finiteName (fun i => d ∘ q i) (i+1) n x,d (q i x))))
      ((μ.map (finiteName (fun i => d ∘ q i) (i+1) n)).prod (μ.map (d ∘ q i))) (b i) := by
    intro i n hi
    have hh := coarse_conditional_budget μ (finiteName q (i+1) (N-i-1)) (q i) (c i) d
      (finiteName_measurable q hq (i+1) (N-i-1)) (hq i) hτ (hlocal i (by omega))
    let r : (Fin (N-i-1) → B) → (Fin n → A) := fun w j => d (w ⟨j.val,by omega⟩)
    have hf := lawClose_pair_factor_left μ (finiteName q (i+1) (N-i-1)) (d ∘ q i) r
      (finiteName_measurable q hq _ _) ((measurable_of_countable d).comp (hq i))
      (measurable_of_countable r) hh
    exact hf
  obtain ⟨R,hR⟩ := sequential_coupling_budgets μ (fun i => d ∘ q i)
    (fun i => (measurable_of_countable d).comp (hq i)) N b hremote 0 N (by omega)
  refine ⟨R,hR.trans_eq ?_⟩
  simp only [b,Nat.zero_add,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hc := finiteName_entropy_chain μ q 0 N
  simp only [Nat.zero_add] at hc
  rw [←Finset.sum_div,Finset.sum_sub_distrib,←hc,←Finset.mul_sum]
end HyperbolicCoding

end
section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]
    (p : I → A → ℝ) (q : I → B → ℝ)

lemma piCoupling_cost (R : ∀ i,MatrixCoupling (p i) (q i))
    (hp : ∀ i,∑ a,p i a=1) (d : I → A → B → ℝ) :
    (piCoupling p q R).cost (fun a b => ∑ i,d i (a i) (b i))=∑ i,(R i).cost (d i) := by
  classical
  let e : (I → A×B) ≃ ((I → A)×(I → B)) := {
    toFun := fun w => (fun i => (w i).1,fun i => (w i).2)
    invFun := fun w i => (w.1 i,w.2 i)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hw : ∀ i,∑ ab : A×B,(R i).weight ab.1 ab.2=1 := by
    intro i
    rw [Fintype.sum_prod_type]
    simp only [(R i).row,hp]
  change (∑ a : I → A,∑ b : I → B,(∏ i,(R i).weight (a i) (b i))*(∑ i,d i (a i) (b i)))=_
  rw [←Fintype.sum_prod_type (f := fun ab : (I → A)×(I → B) =>
    (∏ i,(R i).weight (ab.1 i) (ab.2 i))*(∑ i,d i (ab.1 i) (ab.2 i))),←e.sum_comp]
  change finiteExpectation (productWeights (fun i (ab : A×B) => (R i).weight ab.1 ab.2))
    (fun w => ∑ i,d i (w i).1 (w i).2)=_
  rw [finiteExpectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectation_coordinate _ hw i (fun ab : A×B => d i ab.1 ab.2),Fintype.sum_prod_type]
  rfl
end HyperbolicCoding.MatrixCoupling

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

 theorem nonstationary_conditional_transport
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    {chunkLength : ℕ}
    (q : ℕ → Y → B) (hq : ∀ i,Measurable (q i)) (d : B → Fin chunkLength → A)
    (g n : ℕ) (C : ℕ → Type*) [∀ i,Fintype (C i)] [∀ i,MeasurableSpace (C i)]
    [∀ i,MeasurableSingletonClass (C i)]
    (c : (i : ℕ) → (Fin (n-i-1) → B) → C i) (ε δ : ℕ → ℝ) {ρ τ : ℝ} (hτ : 0<τ)
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[chunkLength+g] x),word f p chunkLength x)))
      ((μ.map (fun x => word f p M (f^[chunkLength+g] x))).prod (μ.map (word f p chunkLength))) ρ)
    (hlaw : ∀ j : Fin n,LawClose (μ.map (word f p chunkLength)) (ν.map (d ∘ q j.val)) (δ j.val))
    (hlocal : ∀ i : ℕ,i<n → LawClose
      (ν.map (fun x => (c i (finiteName q (i+1) (n-i-1) x),d (q i x))))
      ((ν.map (c i ∘ finiteName q (i+1) (n-i-1))).prod (ν.map (d ∘ q i))) (ε i)) :
    ∃ R : MatrixCoupling (mass μ (finiteName (chunkObservation f p chunkLength g) 0 n))
      (mass ν (finiteName (fun i => d ∘ q i) 0 n)),
      R.cost nameCost≤(n : ℝ)*(ρ+τ)+(∑ j : Fin n,δ j.val)+2*(∑ j : Fin n,ε j.val)+
        ((∑ j : Fin n,StandardMapEntropy.Entropy.cond ν (q j.val)
          (c j.val ∘ finiteName q (j.val+1) (n-j.val-1)))-obs ν (finiteName q 0 n))/τ := by
  classical
  obtain ⟨RP,hRP⟩ := stationary_chunk_coupling μ f hf p hp chunkLength g hP n
  obtain ⟨RQ,hRQ⟩ := finite_local_entropy_bridge ν q hq d n C c ε hτ hlocal
  have hcoups (j : Fin n) := coupling_of_observation_lawClose μ ν (word f p chunkLength) (d ∘ q j.val)
    (word_measurable f hf.measurable p hp chunkLength) ((measurable_of_countable d).comp (hq j.val)) (hlaw j)
  choose r hr using hcoups
  let S := MatrixCoupling.piCoupling (fun _ : Fin n => mass μ (word f p chunkLength))
    (fun j : Fin n => mass ν (d ∘ q j.val)) r
  have hS : S.cost nameCost≤∑ j : Fin n,δ j.val := by
    change (MatrixCoupling.piCoupling _ _ r).cost (fun a b => ∑ j : Fin n,symbolCost (a j) (b j))≤_
    rw [MatrixCoupling.piCoupling_cost (d := fun _ => symbolCost)]
    · exact Finset.sum_le_sum (fun j _ => hr j)
    · intro j
      simpa using mass_sum μ (word f p chunkLength) (word_measurable f hf.measurable p hp chunkLength)
  have hw (w : Fin n → Fin chunkLength → A) :
      independentNameWeights ν (fun i => d ∘ q i) 0 n w=∏ j,mass ν (d ∘ q j.val) (w j) := by
    simp only [independentNameWeights,Nat.zero_add]
  let RQ' : MatrixCoupling (mass ν (finiteName (fun i => d ∘ q i) 0 n))
      (fun w : Fin n → Fin chunkLength → A => ∏ j,mass ν (d ∘ q j.val) (w j)) := {
    weight := RQ.weight
    nonneg := RQ.nonneg
    row := RQ.row
    col := fun w => (RQ.col w).trans (hw w) }
  refine ⟨(RP.comp S).comp RQ'.symm,?_⟩
  have h1 := MatrixCoupling.comp_cost_le RP S nameCost nameCost nameCost nameCost_triangle
  have h2 := MatrixCoupling.comp_cost_le (RP.comp S) RQ'.symm nameCost nameCost nameCost nameCost_triangle
  rw [MatrixCoupling.symm_cost RQ' nameCost nameCost_comm] at h2
  have he : RQ'.cost nameCost=RQ.cost nameCost := rfl
  rw [he] at h2
  nlinarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty A]

lemma fullBlock_measurable
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (s n : ℕ) (q : Y → Fin (n*s) → A) (hq : Measurable q) (i : ℕ) :
    Measurable (fullBlock s n q i) := by
  classical
  unfold fullBlock
  by_cases hi : i<n
  · simp only [hi,dite_true]
    exact (measurable_of_countable (fun w : Fin (n*s) → A => wordPack n s w ⟨i,hi⟩)).comp hq
  · simp only [hi,dite_false]
    exact measurable_const

lemma fullBlock_name
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (s n : ℕ) (q : Y → Fin (n*s) → A) :
    finiteName (fullBlock s n q) 0 n=wordPack n s ∘ q := by
  funext x j
  simp only [finiteName,Nat.zero_add,fullBlock,j.isLt,dite_true,Function.comp_apply]

lemma fullBlock_prefix_name
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A) :
    finiteName (fun i => (fun w : Fin (k+g) → A => fun a : Fin k => w (a.castAdd g)) ∘
      fullBlock (k+g) n q i) 0 n=selectChunks k g n ∘ q := by
  funext x j a
  simp only [finiteName,Nat.zero_add,Function.comp_apply,fullBlock,j.isLt,dite_true,
    wordPack,Equiv.trans_apply,Equiv.curry_apply]
  change q x (finProdFinEquiv (j,a.castAdd g))=selectChunks k g n (q x) j a
  unfold selectChunks
  congr 1
  apply Fin.ext
  dsimp [finProdFinEquiv]
  ring

theorem nonstationary_conditional_word_transport
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A) (hq : Measurable q)
    (C : ℕ → Type*) [∀ i,Fintype (C i)] [∀ i,MeasurableSpace (C i)]
    [∀ i,MeasurableSingletonClass (C i)]
    (c : (i : ℕ) → (Fin (n-i-1) → Fin (k+g) → A) → C i)
    (ε δ : ℕ → ℝ) {ρ τ : ℝ} (hτ : 0<τ)
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) ρ)
    (hlaw : ∀ j : Fin n,LawClose (μ.map (word f p k))
      (ν.map ((fun w : Fin (k+g) → A => fun a : Fin k => w (a.castAdd g)) ∘
        fullBlock (k+g) n q j.val)) (δ j.val))
    (hlocal : ∀ i : ℕ,i<n → LawClose
      (ν.map (fun x => (c i (finiteName (fullBlock (k+g) n q) (i+1) (n-i-1) x),
        fun a : Fin k => fullBlock (k+g) n q i x (a.castAdd g))))
      ((ν.map (c i ∘ finiteName (fullBlock (k+g) n q) (i+1) (n-i-1))).prod
        (ν.map ((fun w : Fin (k+g) → A => fun a : Fin k => w (a.castAdd g)) ∘
          fullBlock (k+g) n q i))) (ε i)) :
    ∃ R : MatrixCoupling (mass μ (word f p (n*(k+g)))) (mass ν q),
      R.cost nameCost≤(k : ℝ)*((n : ℝ)*(ρ+τ)+(∑ j : Fin n,δ j.val)+
        2*(∑ j : Fin n,ε j.val)+((∑ j : Fin n,StandardMapEntropy.Entropy.cond ν
          (fullBlock (k+g) n q j.val)
          (c j.val ∘ finiteName (fullBlock (k+g) n q) (j.val+1) (n-j.val-1)))-obs ν q)/τ)+
          (n*g : ℕ) := by
  obtain ⟨S,hS⟩ := nonstationary_conditional_transport μ ν f hf p hp (fullBlock (k+g) n q)
    (fullBlock_measurable (k+g) n q hq)
    (fun w : Fin (k+g) → A => fun a : Fin k => w (a.castAdd g)) g n C c ε δ hτ hP hlaw hlocal
  have hPsel : selectChunks k g n ∘ word f p (n*(k+g))=
      finiteName (chunkObservation f p k g) 0 n := funext (selectChunks_word f p k g n)
  let S' : MatrixCoupling (mass μ (selectChunks k g n ∘ word f p (n*(k+g))))
      (mass ν (selectChunks k g n ∘ q)) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun w => by rw [hPsel]; exact S.row w
    col := fun w => by rw [←fullBlock_prefix_name k g n q]; exact S.col w }
  obtain ⟨R,hR⟩ := lift_observation_transport μ ν (word f p (n*(k+g))) q
    (word_measurable f hf.measurable p hp _) hq
    (selectChunks k g n) S' nameCost nameCost_self nameCost_triangle
  have he : obs ν (finiteName (fullBlock (k+g) n q) 0 n)=obs ν q := by
    rw [fullBlock_name]
    exact obs_equiv ν q (wordPack n (k+g))
  rw [he] at hS
  refine ⟨R,?_⟩
  have hmass : (∑ v,mass μ (word f p (n*(k+g))) v)=1 := by
    simpa using mass_sum μ _ (word_measurable f hf.measurable p hp _)
  have hbd := R.cost_mono nameCost
    (fun v w => (k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ))
    (nameCost_le_retained_chunks k g n)
  rw [R.cost_affine hmass] at hbd
  exact hbd.trans (add_le_add (mul_le_mul_of_nonneg_left (hR.trans hS) (Nat.cast_nonneg k)) (le_refl _))
end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteConditionalLawTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A B D : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSpace D]

lemma independence_joint_test [Fintype B] [MeasurableSingletonClass B]
    [Fintype D] [MeasurableSingletonClass D] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (d : A → D) {δ ε : ℝ}
    (hlaw : LawClose (μ.map (fun x => (p x,r x))) (ν.map (fun y => (q y,s y))) δ)
    (hremote : LawClose (μ.map (fun x => (r x,d (p x))))
      ((μ.map r).prod (μ.map (d ∘ p))) ε) :
    LawClose (ν.map (fun y => (s y,d (q y)))) ((ν.map s).prod (ν.map (d ∘ q))) (ε+3*δ) := by
  have hd : Measurable (fun z : A×B => (z.2,d z.1)) :=
    measurable_snd.prodMk ((measurable_of_countable d).comp measurable_fst)
  have hh := hlaw.map hd
  rw [Measure.map_map hd (hp.prodMk hr),Measure.map_map hd (hq.prodMk hs)] at hh
  exact independence_law_stable μ ν r (d ∘ p) s (d ∘ q) hr
    ((measurable_of_countable d).comp hp) hs ((measurable_of_countable d).comp hq) hh hremote
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {Y A B : Type*} [Nonempty A]

lemma wordPack_symm_coord {A : Type*} (n s : ℕ) (w : Fin n → Fin s → A)
    (i : Fin n) (a : Fin s) : (wordPack n s).symm w (finProdFinEquiv (i,a))=w i a := by
  have hh := congrFun (congrFun ((wordPack n s).apply_symm_apply w) i) a
  exact hh

lemma fullBlock_packed [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (s n : ℕ) (V : Y → Fin n → Fin s → A) (i : Fin n) :
    fullBlock s n (fun x => (wordPack n s).symm (V x)) i.val=fun x => V x i := by
  funext x
  simp only [fullBlock,i.isLt,dite_true,Equiv.apply_symm_apply]

lemma fullBlock_local_future [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (s n L i : ℕ) (h : i+L<n)
    (V : Y → Fin n → Fin s → A) :
    suffixPrefix n L i h ∘ finiteName (fullBlock s n (fun x => (wordPack n s).symm (V x)))
      (i+1) (n-i-1)=vectorFuture n L i h ∘ V := by
  funext x a
  simp only [Function.comp_apply,suffixPrefix,finiteName,vectorFuture,fullBlock]
  have hi : i+1+a.val<n := by omega
  simp only [hi,dite_true,Equiv.apply_symm_apply]

lemma vectorFuture_inside_block (M J L : ℕ) (I : Fin M) (j : Fin J) (hj : j.val+L<J)
    (V : Fin M → Fin J → B) :
    vectorFuture (M*J) L (finProdFinEquiv (I,j)).val (block_inner_future_lt M J L I j hj)
      ((wordPack M J).symm V)=vectorFuture J L j.val hj (V I) := by
  funext a
  unfold vectorFuture
  have he : (⟨(finProdFinEquiv (I,j)).val+1+a.val,by
      have hh := block_inner_future_lt M J L I j hj
      omega⟩ : Fin (M*J))=finProdFinEquiv (I,⟨j.val+1+a.val,by omega⟩) := by
    apply Fin.ext
    dsimp [finProdFinEquiv]
    ring
  rw [he,wordPack_symm_coord]

lemma fullBlock_nested_head [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (I : Fin M) (j : Fin J) :
    fullBlock s (M*J) (fun x => (wordPack (M*J) s).symm ((wordPack M J).symm (V x)))
      (finProdFinEquiv (I,j)).val=fun x => V x I j := by
  rw [fullBlock_packed]
  funext x a
  exact congrFun (wordPack_symm_coord M J (V x) I j) a

lemma fullBlock_nested_future [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (M J s L : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (I : Fin M) (j : Fin J) (hj : j.val+L<J) :
    suffixPrefix (M*J) L (finProdFinEquiv (I,j)).val (block_inner_future_lt M J L I j hj) ∘
      finiteName (fullBlock s (M*J) (fun x => (wordPack (M*J) s).symm ((wordPack M J).symm (V x))))
        ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1)=
      fun x => vectorFuture J L j.val hj (V x I) := by
  rw [fullBlock_local_future]
  funext x
  exact vectorFuture_inside_block M J L I j hj (V x)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma map_word_coordinate [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (J : ℕ) (j : Fin J) :
    μ.map (fun x => word f p J x j)=μ.map p := by
  change μ.map (p ∘ f^[j.val])=μ.map p
  rw [←Measure.map_map hp (hf.measurable.iterate _),(hf.iterate j.val).map_eq]

lemma map_word_head_future [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (J L : ℕ) (j : Fin J) (hj : j.val+L<J) :
    μ.map (fun x => (word f p J x j,vectorFuture J L j.val hj (word f p J x)))=
      μ.map (fun x => (p x,word f p L (f x))) := by
  have hF : Measurable (fun x => (p x,word f p L (f x))) :=
    hp.prodMk ((word_measurable f hf.measurable p hp L).comp hf.measurable)
  have he : (fun x => (word f p J x j,vectorFuture J L j.val hj (word f p J x)))=
      (fun x => (p x,word f p L (f x))) ∘ f^[j.val] := by
    funext x
    apply Prod.ext
    · rfl
    · funext a
      simp only [vectorFuture,word,Function.comp_apply]
      rw [←Function.iterate_succ_apply' f j.val x,←Function.iterate_add_apply]
      congr 2
      omega
  rw [he,←Measure.map_map hF (hf.measurable.iterate _),(hf.iterate j.val).map_eq]

lemma block_law_head_test [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y)
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (J : ℕ) (V : Y → Fin J → A) (hV : Measurable V) {δ : ℝ}
    (hlaw : LawClose (μ.map (word f p J)) (ν.map V) δ) (j : Fin J) :
    LawClose (μ.map p) (ν.map (fun y => V y j)) δ := by
  have hh := hlaw.map (measurable_pi_apply j)
  rw [Measure.map_map (measurable_pi_apply j) (word_measurable f hf.measurable p hp J),
    Measure.map_map (measurable_pi_apply j) hV] at hh
  change LawClose (μ.map (fun x => word f p J x j)) (ν.map (fun y => V y j)) δ at hh
  rw [map_word_coordinate μ f hf p hp J j] at hh
  exact hh

lemma block_law_local_test [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y)
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (J L : ℕ) (V : Y → Fin J → A) (hV : Measurable V) {δ : ℝ}
    (hlaw : LawClose (μ.map (word f p J)) (ν.map V) δ)
    (j : Fin J) (hj : j.val+L<J) :
    LawClose (μ.map (fun x => (p x,word f p L (f x))))
      (ν.map (fun y => (V y j,vectorFuture J L j.val hj (V y)))) δ := by
  let d : (Fin J → A) → A×(Fin L → A) := fun w => (w j,vectorFuture J L j.val hj w)
  have hd : Measurable d := measurable_of_countable d
  have hh := hlaw.map hd
  rw [Measure.map_map hd (word_measurable f hf.measurable p hp J),Measure.map_map hd hV] at hh
  change LawClose (μ.map (fun x => (word f p J x j,vectorFuture J L j.val hj (word f p J x)))) _ _ at hh
  rw [map_word_head_future μ f hf p hp J L j hj] at hh
  exact hh

lemma remote_law_as_blocks [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L : ℕ) {ρ : ℝ}
    (hremote : LawClose (μ.map (fun x => (word f p (L*(k+g)) (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p (L*(k+g)) (f^[k+g] x))).prod (μ.map (word f p k))) ρ) :
    LawClose (μ.map (fun x => (word (f^[k+g]) (word f p (k+g)) L (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word (f^[k+g]) (word f p (k+g)) L (f^[k+g] x))).prod
        (μ.map (word f p k))) ρ := by
  have hh := lawClose_pair_factor_left μ (fun x => word f p (L*(k+g)) (f^[k+g] x))
    (word f p k) (wordPack L (k+g))
    ((word_measurable f hf.measurable p hp _).comp (hf.measurable.iterate _))
    (word_measurable f hf.measurable p hp k) (measurable_of_countable _) hremote
  simpa only [Function.comp_def,wordPack_apply] using hh
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {Y A B : Type*} [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma lawClose_one (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    LawClose μ ν 1 := by
  intro D _
  apply abs_le.mpr
  constructor <;> linarith [measureReal_nonneg (μ:=μ) (s:=D),measureReal_nonneg (μ:=ν) (s:=D),
    measureReal_le_one (μ:=μ) (s:=D),measureReal_le_one (μ:=ν) (s:=D)]

lemma extendedCoarse_at [Nonempty B] (M J L : ℕ) (i : Fin (M*J)) :
    extendedCoarse (B:=B) M J L i.val=insideCoarse M J L i := by
  funext w
  simp only [extendedCoarse,i.isLt,dite_true]

lemma insideCoarse_good [Nonempty B] (M J L : ℕ) (I : Fin M) (j : Fin J) (hj : j.val+L<J) :
    insideCoarse (B:=B) M J L (finProdFinEquiv (I,j))=
      suffixPrefix (M*J) L (finProdFinEquiv (I,j)).val (block_inner_future_lt M J L I j hj) := by
  funext w
  simp only [insideCoarse,Equiv.symm_apply_apply,hj,dite_true]

lemma boundary_count_le (J L : ℕ) :
    (∑ j : Fin J,if j.val+L<J then (0 : ℝ) else 1)≤(L : ℝ) := by
  classical
  let S : Finset (Fin J) := Finset.univ.filter (fun j => ¬j.val+L<J)
  let F : S → Fin L := fun j => ⟨j.val.val+L-J,by
    have hj : ¬j.val.val+L<J := (Finset.mem_filter.mp j.property).2
    have hJ := j.val.isLt
    omega⟩
  have hF : Function.Injective F := by
    intro i j hij
    have hi : ¬i.val.val+L<J := (Finset.mem_filter.mp i.property).2
    have hj : ¬j.val.val+L<J := (Finset.mem_filter.mp j.property).2
    have he := congrArg Fin.val hij
    apply Subtype.ext
    apply Fin.ext
    dsimp [F] at he
    omega
  have hcard : S.card≤L := by
    simpa using Fintype.card_le_of_injective F hF
  have he : (∑ j : Fin J,if j.val+L<J then (0 : ℝ) else 1)=(S.card : ℝ) := by
    dsimp [S]
    rw [←Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all
  rw [he]
  exact_mod_cast hcard

lemma boundaryLoss_sum_le (M J L : ℕ) :
    (∑ i : Fin (M*J),boundaryLoss M J L i)≤(M*L : ℕ) := by
  rw [←Equiv.sum_comp finProdFinEquiv (boundaryLoss M J L),Fintype.sum_prod_type]
  simp only [boundaryLoss,Equiv.symm_apply_apply]
  calc
    _≤∑ _I : Fin M,(L : ℝ) := Finset.sum_le_sum (fun _ _ => boundary_count_le J L)
    _=_ := by simp
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma nestedOutput_measurable [StandardBorelSpace Y] [Nonempty A]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (hV : Measurable V) : Measurable (nestedOutput M J s V) :=
  (measurable_of_countable (fun v => (wordPack (M*J) s).symm ((wordPack M J).symm v))).comp hV

lemma nestedOutput_head [StandardBorelSpace Y] [Nonempty A]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (I : Fin M) (j : Fin J) :
    fullBlock s (M*J) (nestedOutput M J s V) (finProdFinEquiv (I,j)).val=fun x => V x I j :=
  fullBlock_nested_head M J s V I j

lemma nestedOutput_future [StandardBorelSpace Y] [Nonempty A]
    (M J s L : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (I : Fin M) (j : Fin J) (hj : j.val+L<J) :
    extendedCoarse (B:=Fin s → A) M J L (finProdFinEquiv (I,j)).val ∘
      finiteName (fullBlock s (M*J) (nestedOutput M J s V))
        ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1)=
      fun x => vectorFuture J L j.val hj (V x I) := by
  rw [extendedCoarse_at,insideCoarse_good M J L I j hj]
  exact fullBlock_nested_future M J s L V I j hj

theorem block_recoding_word_transport [StandardBorelSpace Y] [Nonempty A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L M J : ℕ) (V : Y → Fin M → Fin J → Fin (k+g) → A) (hV : Measurable V)
    {ρ τ δ H : ℝ} (hρ : 0≤ρ) (hτ : 0<τ) (hδ : 0≤δ) (hH : 0≤H)
    (hP : ∀ T : ℕ,LawClose
      (μ.map (fun x => (word f p T (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p T (f^[k+g] x))).prod (μ.map (word f p k))) ρ)
    (hlaw : ∀ I : Fin M,LawClose
      (μ.map (word (f^[k+g]) (word f p (k+g)) J)) (ν.map (fun y => V y I)) δ)
    (htest : ∀ (q : Y → Fin (k+g) → A) (r : Y → Fin L → Fin (k+g) → A),
      Measurable q → Measurable r →
      LawClose (μ.map (fun x => (word f p (k+g) x,
        word (f^[k+g]) (word f p (k+g)) L (f^[k+g] x))))
        (ν.map (fun y => (q y,r y))) δ → StandardMapEntropy.Entropy.cond ν q r≤H) :
    ∃ R : MatrixCoupling (mass μ (word f p ((M*J)*(k+g))))
        (mass ν (nestedOutput M J (k+g) V)),
      R.cost nameCost≤(k : ℝ)*((M*J : ℕ)*(3*ρ+τ+7*δ)+2*(M*L : ℕ)+
        (((M*J : ℕ)*H+(M*L : ℕ)*Real.log (Fintype.card (Fin (k+g) → A)))-
          obs ν (nestedOutput M J (k+g) V))/τ)+(M*J*g : ℕ) := by
  classical
  let q := nestedOutput M J (k+g) V
  have hq : Measurable q := nestedOutput_measurable M J (k+g) V hV
  let c := extendedCoarse (B:=Fin (k+g) → A) M J L
  let ε : ℕ → ℝ := fun i => ρ+3*δ+if hi : i<M*J then boundaryLoss M J L ⟨i,hi⟩ else 0
  have he (i : Fin (M*J)) : ε i.val=ρ+3*δ+boundaryLoss M J L i := by
    simp only [ε,i.isLt,dite_true]
  let d : (Fin (k+g) → A) → Fin k → A := fun w a => w (a.castAdd g)
  have hd : Measurable d := measurable_of_countable d
  have hw := word_measurable f hf.measurable p hp (k+g)
  have hpref : d ∘ word f p (k+g)=word f p k := by funext x a; rfl
  have hpref' (x : X) : d (word f p (k+g) x)=word f p k x := congrFun hpref x
  have hhead (i : Fin (M*J)) : LawClose (μ.map (word f p k))
      (ν.map (d ∘ fullBlock (k+g) (M*J) q i.val)) δ := by
    obtain ⟨⟨I,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    have hh := block_law_head_test μ ν (f^[k+g]) (hf.iterate _) (word f p (k+g)) hw J
      (fun y => V y I) ((measurable_pi_apply I).comp hV) (hlaw I) j
    have hh' := hh.map hd
    have hvij : Measurable (fun y => V y I j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply I).comp hV)
    rw [Measure.map_map hd hw,Measure.map_map hd hvij,hpref] at hh'
    simpa only [q,nestedOutput_head] using hh'
  have hremote := remote_law_as_blocks μ f hf p hp k g L (hP (L*(k+g)))
  have hpair (I : Fin M) (j : Fin J) (hj : j.val+L<J) :=
    block_law_local_test μ ν (f^[k+g]) (hf.iterate _) (word f p (k+g)) hw J L
      (fun y => V y I) ((measurable_pi_apply I).comp hV) (hlaw I) j hj
  have hlocal (i : ℕ) (hi : i<M*J) : LawClose
      (ν.map (fun x => (c i (finiteName (fullBlock (k+g) (M*J) q) (i+1) (M*J-i-1) x),
        d (fullBlock (k+g) (M*J) q i x))))
      ((ν.map (c i ∘ finiteName (fullBlock (k+g) (M*J) q) (i+1) (M*J-i-1))).prod
        (ν.map (d ∘ fullBlock (k+g) (M*J) q i))) (ε i) := by
    let a : Fin (M*J) := ⟨i,hi⟩
    change LawClose _ _ (ε a.val)
    rw [he]
    obtain ⟨⟨I,j⟩,ha⟩ := finProdFinEquiv.surjective a
    have hiv : i=(finProdFinEquiv (I,j)).val := congrArg Fin.val ha.symm
    subst i
    by_cases hj : j.val+L<J
    · have hh := independence_joint_test μ ν (word f p (k+g))
        (fun x => word (f^[k+g]) (word f p (k+g)) L (f^[k+g] x))
        (fun y => V y I j) (fun y => vectorFuture J L j.val hj (V y I)) hw
        ((word_measurable (f^[k+g]) (hf.measurable.iterate _) (word f p (k+g)) hw L).comp
          (hf.measurable.iterate _))
        ((measurable_pi_apply j).comp ((measurable_pi_apply I).comp hV))
        ((measurable_of_countable (vectorFuture J L j.val hj)).comp ((measurable_pi_apply I).comp hV)) d (hpair I j hj)
        (by simpa only [hpref,hpref'] using hremote)
      have hb : boundaryLoss M J L a=0 := by rw [←ha]; simp only [boundaryLoss,Equiv.symm_apply_apply,hj,ite_true]
      rw [hb,add_zero]
      change LawClose (ν.map (fun x => ((c _ ∘ _) x,d (fullBlock _ _ q _ x)))) _ _
      simpa only [c,q,nestedOutput_future M J (k+g) L V I j hj,nestedOutput_head]
        using hh
    · have hm1 : Measurable (finiteName (fullBlock (k+g) (M*J) q) ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1)) := finiteName_measurable _ (fun i => fullBlock_measurable _ _ q hq i) _ _
      have hmc : Measurable (c (finProdFinEquiv (I,j)).val ∘ finiteName (fullBlock (k+g) (M*J) q) ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1)) := (measurable_of_countable _).comp hm1
      have hmd : Measurable (d ∘ fullBlock (k+g) (M*J) q (finProdFinEquiv (I,j)).val) := hd.comp (fullBlock_measurable _ _ q hq _)
      have hmp : Measurable (fun x => (c (finProdFinEquiv (I,j)).val (finiteName (fullBlock (k+g) (M*J) q) ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1) x), d (fullBlock (k+g) (M*J) q (finProdFinEquiv (I,j)).val x))) := hmc.prodMk hmd
      haveI := Measure.isProbabilityMeasure_map (μ := ν) hmc.aemeasurable
      haveI := Measure.isProbabilityMeasure_map (μ := ν) hmd.aemeasurable
      haveI := Measure.isProbabilityMeasure_map (μ := ν) hmp.aemeasurable
      apply (lawClose_one _ _).mono
      have hb : boundaryLoss M J L a=1 := by rw [←ha]; simp only [boundaryLoss,Equiv.symm_apply_apply,hj,ite_false]
      rw [hb]
      linarith
  have hcond (i : Fin (M*J)) : StandardMapEntropy.Entropy.cond ν
      (fullBlock (k+g) (M*J) q i.val)
      (c i.val ∘ finiteName (fullBlock (k+g) (M*J) q) (i.val+1) (M*J-i.val-1))≤
      H+boundaryLoss M J L i*Real.log (Fintype.card (Fin (k+g) → A)) := by
    obtain ⟨⟨I,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    by_cases hj : j.val+L<J
    · simp only [boundaryLoss,Equiv.symm_apply_apply,hj,ite_true,zero_mul,add_zero]
      change StandardMapEntropy.Entropy.cond ν _ (extendedCoarse M J L _ ∘ _)≤H
      rw [nestedOutput_future M J (k+g) L V I j hj,nestedOutput_head]
      exact htest _ _ ((measurable_pi_apply j).comp ((measurable_pi_apply I).comp hV))
        ((measurable_of_countable (vectorFuture J L j.val hj)).comp ((measurable_pi_apply I).comp hV)) (hpair I j hj)
    · simp only [boundaryLoss,Equiv.symm_apply_apply,hj,ite_false,one_mul]
      have hh := cond_le_obs ν (fullBlock (k+g) (M*J) q (finProdFinEquiv (I,j)).val)
        (c (finProdFinEquiv (I,j)).val ∘ finiteName (fullBlock (k+g) (M*J) q)
          ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1))
        (fullBlock_measurable _ _ q hq _)
        ((measurable_of_countable (c (finProdFinEquiv (I,j)).val)).comp
          (finiteName_measurable _ (fullBlock_measurable _ _ q hq)
            ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1)))
      have hb := obs_bound ν (fullBlock (k+g) (M*J) q (finProdFinEquiv (I,j)).val)
        (fullBlock_measurable _ _ q hq _)
      linarith
  obtain ⟨R,hR⟩ := nonstationary_conditional_word_transport μ ν f hf p hp k g (M*J) q hq
    (fun _ => Fin L → Fin (k+g) → A) c ε (fun _ => δ) hτ hP hhead hlocal
  refine ⟨R,hR.trans ?_⟩
  have hlog : 0≤Real.log (Fintype.card (Fin (k+g) → A)) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α:=Fin (k+g) → A))
  have hcs : (∑ i : Fin (M*J),StandardMapEntropy.Entropy.cond ν
      (fullBlock (k+g) (M*J) q i.val)
      (c i.val ∘ finiteName (fullBlock (k+g) (M*J) q) (i.val+1) (M*J-i.val-1)))≤
      (M*J : ℕ)*H+(M*L : ℕ)*Real.log (Fintype.card (Fin (k+g) → A)) := by
    calc
      _≤∑ i : Fin (M*J),(H+boundaryLoss M J L i*Real.log (Fintype.card (Fin (k+g) → A))) :=
        Finset.sum_le_sum (fun i _ => hcond i)
      _=(M*J : ℕ)*H+(∑ i : Fin (M*J),boundaryLoss M J L i)*Real.log (Fintype.card (Fin (k+g) → A)) := by
        rw [Finset.sum_add_distrib,←Finset.sum_mul]; simp
      _≤_ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (boundaryLoss_sum_le M J L) hlog)
  have hes : (∑ i : Fin (M*J),ε i.val)≤(M*J : ℕ)*(ρ+3*δ)+(M*L : ℕ) := by
    simp only [he,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hh := boundaryLoss_sum_le M J L
    nlinarith
  apply add_le_add _ (le_refl _)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
  have hh := div_le_div_of_nonneg_right (sub_le_sub_right hcs (obs ν q)) hτ.le
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp only [q] at hh ⊢
  nlinarith
end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ActualFiniteRecodingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding

lemma recoding_deficit_scalar {n j s L C a hr O : ℝ}
    (hn : 0≤n) (hB : 2+L*C≤j*a^2)
    (hO : n*j*s*hr-2*(n*j)*a^2-2*n≤O) :
    n*j*(s*hr+a^2)+n*L*C-O≤4*(n*j)*a^2 := by
  have h₁ := mul_le_mul_of_nonneg_left hB hn
  nlinarith only [h₁,hO]

lemma recoding_wb_cost_scalar {c n j k g L a δ D : ℝ}
    (hn : 0≤n) (hj : 0≤j) (hk : 0≤k) (hg : 0≤g) (ha : 0<a)
    (hδ : δ≤a) (hB : 2*L≤j*a) (hgap : g≤a*k)
    (hD : D≤4*(n*j)*a^2)
    (hc : c≤k*(n*j*(3*a+a+7*δ)+2*(n*L)+D/a)+n*j*g) :
    c≤17*a*(n*j*(k+g)) := by
  have hdiv : D/a≤4*(n*j)*a := (div_le_iff₀ ha).mpr (by nlinarith only [hD])
  have h₁ := mul_le_mul_of_nonneg_left hδ (mul_nonneg hn hj)
  have h₂ := mul_le_mul_of_nonneg_left hB hn
  have h₃ := mul_le_mul_of_nonneg_left hgap (mul_nonneg hn hj)
  have hinside : n*j*(3*a+a+7*δ)+2*(n*L)+D/a≤16*a*(n*j) := by
    nlinarith only [hdiv,h₁,h₂]
  have h₄ := mul_le_mul_of_nonneg_left hinside hk
  have h₅ := mul_nonneg (mul_nonneg (mul_nonneg hn hj) hg) ha.le
  nlinarith only [hc,h₃,h₄,h₅]
end HyperbolicCoding
end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

lemma block_recoding_small_cost_q44_oai [StandardBorelSpace X] [StandardBorelSpace Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (r : X → A) (hr : Measurable r)
    (k g L n J : ℕ) (V : Y → Fin n → Fin J → Fin (k+g) → A) (hV : Measurable V)
    {a δ : ℝ} (ha : 0<a) (hδ₀ : 0≤δ) (hδ : δ≤a)
    (hgap : (g : ℝ)≤a*k) (hB₁ : 2+(L : ℝ)*Real.log (Fintype.card (Fin (k+g) → A))≤(J : ℝ)*a^2)
    (hB₂ : 2*(L : ℝ)≤(J : ℝ)*a)
    (hremote : ∀ T : ℕ,LawClose
      (μ.map (fun x => (word e r T (e^[k+g] x),word e r k x)))
      ((μ.map (fun x => word e r T (e^[k+g] x))).prod (μ.map (word e r k))) a)
    (hlaw : ∀ I : Fin n,LawClose
      (μ.map (word (e^[k+g]) (word e r (k+g)) J)) (ν.map (fun y => V y I)) δ)
    (htest : ∀ (q : Y → Fin (k+g) → A) (v : Y → Fin L → Fin (k+g) → A),
      Measurable q → Measurable v →
      LawClose (μ.map (fun x => (word e r (k+g) x,
        word (e^[k+g]) (word e r (k+g)) L (e^[k+g] x))))
        (ν.map (fun y => (q y,v y))) δ → StandardMapEntropy.Entropy.cond ν q v≤
          (k+g : ℕ)*rate μ e r+a^2)
    (hentropy : ((n*J)*(k+g) : ℕ)*rate μ e r-2*(n*J : ℕ)*a^2-2*(n : ℝ)≤
      obs ν (nestedOutput n J (k+g) V)) :
    ∃ R : MatrixCoupling (mass μ (word e r ((n*J)*(k+g))))
        (mass ν (nestedOutput n J (k+g) V)),
      R.cost nameCost≤17*a*((n*J)*(k+g) : ℕ) := by
  have hH : 0≤(k+g : ℕ)*rate μ e r+a^2 := by
    have := rate_nonneg μ e he r hr
    positivity
  obtain ⟨R,hR⟩ := block_recoding_word_transport μ ν e he r hr k g L n J V hV
    ha.le ha hδ₀ hH hremote hlaw htest
  refine ⟨R,?_⟩
  have hD : (n*J : ℕ)*((k+g : ℕ)*rate μ e r+a^2)+(n*L : ℕ)*Real.log (Fintype.card (Fin (k+g) → A))-
      obs ν (nestedOutput n J (k+g) V)≤4*(n*J : ℕ)*a^2 := by
    push_cast at hentropy ⊢
    exact recoding_deficit_scalar (Nat.cast_nonneg n) hB₁ hentropy
  push_cast at hR hD ⊢
  exact recoding_wb_cost_scalar (Nat.cast_nonneg n) (Nat.cast_nonneg J) (Nat.cast_nonneg k)
    (Nat.cast_nonneg g) ha hδ hB₂ hgap hD hR
end HyperbolicCoding

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.HyperbolicCoding.block_recoding_small_cost_q44_oai.{u_1, u_2, u_3} := @OAI.HyperbolicCoding.block_recoding_small_cost_q44_oai.{u_1, u_2, u_3}

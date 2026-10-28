-- Prove2me | solution 1 for OAI.HyperbolicCoding.fixed_decoder_arbitrary_tests_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:15:28.616596+00:00
-- url     : https://prove2.me/submissions/4845af27-e30a-4666-afbe-ab337f9953c7

import Mathlib
import Definitions.Def_OAIQ44C000
import Definitions.Def_OAIQ44C001
import Theorems.Thm_OAI_HyperbolicCoding_actual_fixed_window_rate_copy_q44
import Theorems.Thm_OAI_HyperbolicCoding_block_recoding_small_cost_q44

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

lemma shannon_scale {α : Type*} [Fintype α] (p : α → ℝ) (c : ℝ) :
    shannon (fun a => c*p a)=c*shannon p+(∑ a,p a)*Real.negMulLog c := by
  simp only [shannon,Real.negMulLog_mul,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

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

lemma cond_nonneg (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) : 0 ≤ cond μ p q :=
  sub_nonneg.mpr (obs_pair_ge_right μ p q hp hq)
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

lemma cond_pair_subadd (p : Ω → α) (q : Ω → β) (r : Ω → γ) (s : Ω → ζ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (hs : Measurable s) :
    cond μ (fun x => (p x,r x)) (fun x => (q x,s x)) ≤ cond μ p q+cond μ r s := by
  rw [cond_chain]
  apply add_le_add (cond_pair_right μ p q s hp hq hs)
  exact cond_factor_right μ r (fun x => (p x,(q x,s x))) (fun v : α×(β×ζ) => v.2.2) hr (hp.prodMk (hq.prodMk hs))

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

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_word_zero (f : Ω → Ω) (p : Ω → α) : obs μ (word f p 0)=0 := by
  have he : word f p 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  rw [he,obs_const]

omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_equiv_left (p : Ω → α) (q : Ω → β)
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (e : α ≃ γ) :
    cond μ (e ∘ p) q=cond μ p q := by
  have h := obs_equiv μ (fun x => (p x,q x)) (Equiv.prodCongr e (Equiv.refl β))
  unfold cond
  rw [show obs μ (fun x => ((e ∘ p) x,q x))=obs μ (fun x => (p x,q x)) from
    by simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply] using h]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_equiv_right (p : Ω → α) (q : Ω → β)
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (e : β ≃ γ) :
    cond μ p (e ∘ q)=cond μ p q := by
  have h := obs_equiv μ (fun x => (p x,q x)) (Equiv.prodCongr (Equiv.refl α) e)
  unfold cond
  rw [show obs μ (fun x => (p x,(e ∘ q) x))=obs μ (fun x => (p x,q x)) from
    by simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply] using h,
    obs_equiv μ q e]

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
lemma rate_le_div (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p)
    {n : ℕ} (hn : n≠0) : rate μ f p≤obs μ (word f p n)/(n : ℝ) := by
  rw [rate_eq_lim μ f hf p hp]
  exact (obs_word_subadd μ f hf p hp).lim_le_div (obs_word_bddBelow μ f hf.measurable p hp) hn

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_TailNameSaturation
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

omit [IsProbabilityMeasure μ] in
lemma cond_word_future_eq (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n m : ℕ) :
    cond μ (word f p n) (fun x => word f p m (f^[n] x))=
      obs μ (word f p (n+m))-obs μ (word f p m) := by
  unfold cond
  rw [←obs_word_split μ f p n m]
  exact congrArg (fun t => obs μ (word f p (n+m))-t)
    (obs_comp_preserving μ (f^[n]) (hf.iterate n) (word f p m) (word_measurable f hf.measurable p hp m))

omit [IsProbabilityMeasure μ] in
lemma entropy_increment_eq (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    obs μ (word f p (m+1))-obs μ (word f p m)=
      cond μ p (fun x => word f p m (f x)) := by
  have h := cond_word_future_eq μ f hf p hp 1 m
  rw [Nat.add_comm 1 m] at h
  have he : (Equiv.funUnique (Fin 1) α) ∘ word f p 1=p := by
    funext x; rfl
  rw [←cond_equiv_left μ (word f p 1) (fun x => word f p m (f^[1] x))
    (Equiv.funUnique (Fin 1) α),he] at h
  simpa only [Function.iterate_one] using h.symm

lemma entropy_increment_antitone (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) :
    Antitone (fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [entropy_increment_eq μ f hf p hp,entropy_increment_eq μ f hf p hp]
  exact cond_factor_right μ p (fun x => word f p (m+1) (f x))
    (fun v : Fin (m+1) → α => fun i : Fin m => v i.castSucc) hp
    ((word_measurable f hf.measurable p hp (m+1)).comp hf.measurable)

lemma entropy_increment_nonneg (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    0≤obs μ (word f p (m+1))-obs μ (word f p m) := by
  rw [entropy_increment_eq μ f hf p hp]
  exact cond_nonneg μ p _ hp ((word_measurable f hf.measurable p hp m).comp hf.measurable)

lemma entropy_increment_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) :
    Tendsto (fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)) atTop (𝓝 (rate μ f p)) := by
  let d := fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)
  have hbd : BddBelow (Set.range d) := ⟨0,by rintro _ ⟨m,rfl⟩; exact entropy_increment_nonneg μ f hf p hp m⟩
  have hd := tendsto_atTop_ciInf (entropy_increment_antitone μ f hf p hp) hbd
  have hs (n : ℕ) : ∑ j ∈ Finset.range n,d j=obs μ (word f p n) := by
    induction n with
    | zero => simp only [Finset.range_zero,Finset.sum_empty,obs_word_zero]
    | succ n ih => rw [Finset.sum_range_succ,ih]; dsimp [d]; ring
  change Tendsto d atTop (𝓝 (⨅ i,d i)) at hd
  have hh := hd.cesaro
  simp only [hs,←div_eq_inv_mul] at hh
  have he := tendsto_nhds_unique hh (rate_tendsto μ f hf p hp)
  rwa [he] at hd

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
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_word_pair (f : Ω → Ω) (p : Ω → α) (q : Ω → β) (n : ℕ) :
    obs μ (word f (fun x => (p x,q x)) n)=obs μ (fun x => (word f p n x,word f q n x)) :=
  (obs_equiv μ (word f (fun x => (p x,q x)) n) (wordPairEquiv n)).symm

lemma rate_pair_ge_left (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    rate μ f p ≤ rate μ f (fun x => (p x,q x)) := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf p hp)
    (rate_tendsto μ f hf (fun x => (p x,q x)) (hp.prodMk hq))
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [obs_word_pair]
  exact div_le_div_of_nonneg_right (obs_pair_ge_left μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)) (Nat.cast_nonneg n)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma inverse_iterate_forward_sub (e : Ω ≃ᵐ Ω) {M i : ℕ} (hi : i≤M) (x : Ω) :
    e.symm^[i] (e^[M] x)=e^[M-i] x := by
  have hx : e^[M] x=e^[i] (e^[M-i] x) := by
    rw [←Function.iterate_add_apply,show i+(M-i)=M from by omega]
  rw [hx]
  exact (show Function.LeftInverse (e.symm : Ω → Ω) e from e.symm_apply_apply).iterate i _

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_RohlinSinaiFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal symmDiff

namespace HyperbolicCoding

lemma law_distance_le_disagreement {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (κ : Measure Ω) [IsFiniteMeasure κ] {p q : Ω → Y}
    (hp : Measurable p) (hq : Measurable q) {D : Set Y} (hD : MeasurableSet D) :
    |(κ.map p).real D-(κ.map q).real D|≤κ.real {w | p w≠q w} := by
  simp only [Measure.real,Measure.map_apply hp hD,Measure.map_apply hq hD]
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hD.preimage hp).nullMeasurableSet (hD.preimage hq).nullMeasurableSet).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro w hw he
  have hh : (w∈p ⁻¹' D)=(w∈q ⁻¹' D) := by simp only [mem_preimage,he]
  simp only [Set.mem_symmDiff,hh,and_not_self,or_self] at hw

end HyperbolicCoding

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
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X : Type*} [MeasurableSpace X]

lemma integerIterate_add (e : X ≃ᵐ X) (m n : ℤ) (x : X) :
    integerIterate e (m+n) x=integerIterate e m (integerIterate e n x) := by
  simp only [integerIterate,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma integerIterate_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : integerIterate e n x=e^[n] x := by
  simp only [integerIterate,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma orbitName_shift {A : Type*} (e : X ≃ᵐ X) (α : X → A) (x : X) :
    orbitName e α (e x)=fun i => orbitName e α x (i+1) := by
  funext i
  simp only [orbitName,integerIterate_add,integerIterate_one]

end HyperbolicCoding

end
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X A : Type*} [MeasurableSpace X]

lemma iterateEquiv_apply (e : X ≃ᵐ X) (n : ℕ) (x : X) : iterateEquiv e n x=e^[n] x := by
  change ((e.toEquiv^n) x)=_
  rw [Equiv.Perm.coe_pow]
  rfl

end HyperbolicCoding

end
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

lemma measurable_remotePair {T S : X → X} {α : X → A}
    (hT : Measurable T) (hS : Measurable S) (hα : Measurable α) (n : ℕ) :
    Measurable (remotePair T S α n) :=
  (measurable_tailName hS hα n).prodMk (measurable_tailName hT hα n)

lemma stationary_tail_law (μ : Measure X) {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} (hα : Measurable α) (n : ℕ) :
    μ.map (tailName T α n)=μ.map (tailName T α 0) := by
  have heq : tailName T α n=(tailName T α 0) ∘ T^[n] := by
    funext x i
    simp only [tailName,Function.comp_apply,Nat.add_zero,←Function.iterate_add_apply]
  rw [heq,←Measure.map_map (measurable_tailName hT.measurable hα 0) (hT.measurable.iterate n),
    (hT.iterate n).map_eq]

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
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma symbolCost_self {E : Type*} (a : E) : symbolCost a a=0 := by simp [symbolCost]
lemma symbolCost_nonneg {E : Type*} (a b : E) : 0≤ symbolCost a b := by unfold symbolCost; split <;> norm_num
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

lemma nameCost_triangle {E : Type*} {n : ℕ} (a b c : Fin n → E) :
    nameCost a c≤nameCost a b+nameCost b c := by
  simp only [nameCost,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => symbolCost_triangle _ _ _)
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
open MeasureTheory Set
open scoped ENNReal
variable {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma lawClose_pair_swap (p : X → A) (q : X → B)
    (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (q x,p x))) ((μ.map q).prod (μ.map p)) ε := by
  have hh := h.map measurable_swap
  rw [Measure.map_map measurable_swap (hp.prodMk hq),Measure.prod_swap] at hh
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
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

lemma productWeights_sum (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1) :
    ∑ D,productWeights w D=1 := by
  unfold productWeights
  rw [←Fintype.prod_sum]
  simp only [hw,Finset.prod_const_one]

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

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
variable (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (α : X → A) (hα : Measurable α)

include he hα
lemma finite_remote_lawClose {n : ℕ} {ε : ℝ}
    (h : LawClose (μ.map (remotePair e e.symm α n)) (remoteProductLaw μ e e.symm α) ε)
    (f : (ℕ → A) → B) (g : (ℕ → A) → C) (hf : Measurable f) (hg : Measurable g) :
    LawClose (μ.map (fun x => (f (tailName e.symm α n x),g (tailName e α n x))))
      ((μ.map (fun x => f (tailName e.symm α n x))).prod
        (μ.map (fun x => g (tailName e α n x)))) ε := by
  have hh := h.map (hf.prodMap hg)
  rw [Measure.map_map (hf.prodMap hg) (measurable_remotePair e.measurable e.symm.measurable hα n)] at hh
  have hmf : (μ.map (tailName e.symm α 0)).map f=μ.map (fun x => f (tailName e.symm α n x)) := by
    rw [←stationary_tail_law μ (he.symm e) hα n,Measure.map_map hf
      (measurable_tailName e.symm.measurable hα n)]
    rfl
  have hmg : (μ.map (tailName e α 0)).map g=μ.map (fun x => g (tailName e α n x)) := by
    rw [←stationary_tail_law μ he hα n,Measure.map_map hg
      (measurable_tailName e.measurable hα n)]
    rfl
  unfold remoteProductLaw at hh
  rw [←Measure.map_prod_map _ _ hf hg,hmf,hmg] at hh
  exact hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype A] [MeasurableSingletonClass A] in
theorem weakBernoulli_forward_blocks (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → A) (hα : Measurable α) (hwb : WeakBernoulliProcess μ e α)
    {ε : ℝ} (hε : 0<ε) : ∃ g : ℕ,∀ k M : ℕ,LawClose
      (μ.map (fun x => (word e α M (e^[k+g] x),word e α k x)))
      ((μ.map (fun x => word e α M (e^[k+g] x))).prod (μ.map (word e α k))) ε := by
  obtain ⟨N,hN⟩ := (hwb ε hε).exists
  refine ⟨2*N,?_⟩
  intro k M
  let P : (ℕ → A) → (Fin k → A) := fun w i => w (k-i.val)
  let Q : (ℕ → A) → (Fin M → A) := fun w i => w i.val
  have hP : Measurable P := Measurable.of_eval (fun index => measurable_pi_apply (k-index.val))
  have hQ : Measurable Q := Measurable.of_eval (fun index => measurable_pi_apply index.val)
  have hfin := finite_remote_lawClose μ e he α hα hN P Q hP hQ
  have hp : Measurable (fun x => P (tailName e.symm α N x)) :=
    hP.comp (measurable_tailName e.symm.measurable hα N)
  have hq : Measurable (fun x => Q (tailName e α N x)) :=
    hQ.comp (measurable_tailName e.measurable hα N)
  have hcomp := lawClose_pair_comp μ (e^[k+N]) (he.iterate (k+N)) _ _ hp hq hfin
  have hswap := lawClose_pair_swap μ _ _ (hp.comp (he.measurable.iterate (k+N)))
    (hq.comp (he.measurable.iterate (k+N))) hcomp
  have hp' (x : X) : P (tailName e.symm α N (e^[k+N] x))=word e α k x := by
    funext i
    change α (e.symm^[(k-i.val)+N] (e^[k+N] x))=α (e^[i.val] x)
    rw [inverse_iterate_forward_sub e (by omega)]
    congr 2
    omega
  have hq' (x : X) : Q (tailName e α N (e^[k+N] x))=word e α M (e^[k+2*N] x) := by
    funext i
    change α (e^[i.val+N] (e^[k+N] x))=α (e^[i.val] (e^[k+2*N] x))
    rw [←Function.iterate_add_apply,←Function.iterate_add_apply]
    congr 2
    omega
  simpa only [Function.comp_def,hp',hq'] using hswap

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped ENNReal Topology BigOperators
variable {A X Y : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma continuous_shannon : Continuous (shannon (α:=A)) := by
  unfold shannon
  fun_prop

theorem finite_entropy_continuity (μ : Measure A) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ ν : Measure A,LawClose μ ν δ →
      |shannon (fun a => μ.real {a})-shannon (fun a => ν.real {a})|<ε := by
  obtain ⟨η,hη,hcont⟩ := Metric.continuousAt_iff.mp (continuous_shannon (A:=A)).continuousAt ε hε
  refine ⟨η/2,half_pos hη,?_⟩
  intro ν hν
  have hd : dist (fun a => ν.real {a}) (fun a => μ.real {a})<η := by
    apply (dist_pi_lt_iff hη).mpr
    intro a
    rw [Real.dist_eq,abs_sub_comm]
    exact (hν {a} (measurableSet_singleton a)).trans_lt (half_lt_self hη)
  simpa only [Real.dist_eq,abs_sub_comm] using hcont hd

lemma obs_eq_entropy_map (μ : Measure X) (p : X → A) (hp : Measurable p) :
    obs μ p=shannon (fun a => (μ.map p).real {a}) := by
  unfold obs
  congr 1
  funext a
  exact (map_measureReal_apply hp (measurableSet_singleton a)).symm

end StandardMapEntropy.Entropy

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

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteProductVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]
namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

omit [DecidableEq B] in
lemma conditionalAssignment_nonneg (r : MatrixCoupling p q) (b : B) (a : A) :
    0 ≤ r.conditionalAssignment b a := by
  unfold conditionalAssignment
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (r.nonneg a b) (r.right_nonneg b)

omit [DecidableEq B] in
lemma conditionalAssignment_sum (r : MatrixCoupling p q) (b : B) :
    ∑ a,r.conditionalAssignment b a=1 := by
  unfold conditionalAssignment
  by_cases hq : q b=0
  · simp [hq]
  · simp only [hq,ite_false,←Finset.sum_div,r.col,div_self hq]

omit [DecidableEq B] in
lemma mul_conditionalAssignment (r : MatrixCoupling p q) (a : A) (b : B) :
    q b*r.conditionalAssignment b a=r.weight a b := by
  unfold conditionalAssignment
  by_cases hq : q b=0
  · have hr : r.weight a b=0 := le_antisymm (by simpa only [hq] using r.le_right a b) (r.nonneg a b)
    simp [hq,hr]
  · simp only [hq,ite_false]
    exact mul_div_cancel₀ _ hq

end MatrixCoupling
end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_TypicalWordCodebook
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma productWordWeight_sum (p : A → ℝ) (hp : ∑ a,p a=1) (n : ℕ) :
    (∑ w : Fin n → A,productWordWeight p n w)=1 :=
  productWeights_sum (fun _ : Fin n => p) (fun _ => hp)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

lemma finiteWeightLaw_singleton (p : A → ℝ) (a : A) :
    finiteWeightLaw p {a}=ENNReal.ofReal (p a) := by
  classical
  simp [finiteWeightLaw,Measure.finsetSum_apply,Measure.smul_apply,Pi.single_apply]

omit [MeasurableSingletonClass A] in
lemma finiteWeightLaw_probability (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :
    IsProbabilityMeasure (finiteWeightLaw p) := by
  constructor
  simp only [finiteWeightLaw,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_univ _),mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a),hs,ENNReal.ofReal_one]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_iterate (w : ℤ → A) (n : ℕ) (i : ℤ) :
    (iidShift^[n]) w i=w (i+n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (iidShift^[n]) w (i+1)=_
    rw [ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_preserving (β : Measure A) [IsProbabilityMeasure β] :
    MeasurePreserving (iidShift (A:=A)) (Measure.infinitePi (fun _ : ℤ => β))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
  refine ⟨iidShift.measurable,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j : ℤ => by omega)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_word_eq (n : ℕ) (w : ℤ → A) :
    word iidShift (fun z : ℤ → A => z 0) n w=fun i : Fin n => w i.val := by
  funext i
  change (iidShift^[i.val]) w 0=_
  rw [iidShift_iterate,zero_add]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_word_law (β : Measure A) [IsProbabilityMeasure β] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℤ => β)).map (word iidShift (fun z : ℤ → A => z 0) n)=
      Measure.pi (fun _ : Fin n => β) := by
  have hi : Function.Injective (fun i : Fin n => (i.val : ℤ)) := by
    intro i j h
    apply Fin.ext
    change (i.val : ℤ)=(j.val : ℤ) at h
    exact Int.ofNat_inj.mp h
  simpa only [funext (iid_word_eq (A:=A) n),Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P:=fun _ : ℤ => β) hi)

lemma iid_word_mass (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (n : ℕ) (w : Fin n → A) :
    mass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p))
      (word iidShift (fun z : ℤ → A => z 0) n) w=productWordWeight p n w := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  change (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)).real
    ((word iidShift (fun z : ℤ → A => z 0) n) ⁻¹' {w})=_
  rw [←map_measureReal_apply (word_measurable iidShift iidShift.measurable _
    (measurable_pi_apply 0) n) (measurableSet_singleton w)]
  rw [iid_word_law,Measure.real,Measure.pi_singleton]
  simp only [finiteWeightLaw_singleton,ENNReal.toReal_prod,ENNReal.toReal_ofReal (hp _),productWordWeight]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory ProbabilityTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma shannon_product_weights {B : Type*} [Fintype B] (p : A → ℝ) (q : B → ℝ)
    (hp : ∑ a,p a=1) (hq : ∑ b,q b=1) :
    shannon (fun ab : A×B => p ab.1*q ab.2)=shannon p+shannon q := by
  simp only [shannon,Fintype.sum_prod_type,Real.negMulLog_mul,Finset.sum_add_distrib]
  simp only [←Finset.sum_mul,←Finset.mul_sum,hp,hq,one_mul]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma shannon_productWordWeight (p : A → ℝ) (hs : ∑ a,p a=1) (n : ℕ) :
    shannon (productWordWeight p n)=(n : ℝ)*weightEntropy p := by
  classical
  have hdef : shannon p=weightEntropy p := by
    unfold shannon weightEntropy
    apply Finset.sum_congr rfl
    intro a _
    simp [Real.negMulLog]
  induction n with
  | zero => simp [shannon,productWordWeight]
  | succ n ih =>
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    have he : (∑ w : Fin (n+1) → A,Real.negMulLog (productWordWeight p (n+1) w))=
        ∑ ab : A×(Fin n → A),Real.negMulLog (p ab.1*productWordWeight p n ab.2) := by
      rw [←Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro ab _
      congr 1
      simp [productWordWeight,Fin.prod_univ_succ,e]
    rw [shannon,he]
    change shannon (fun ab : A×(Fin n → A) => p ab.1*productWordWeight p n ab.2)=_
    rw [shannon_product_weights p _ hs (productWordWeight_sum p hs n),hdef,ih]
    push_cast
    ring

theorem iid_rate [DecidableEq A] (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :
    rate (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) iidShift
      (fun w : ℤ → A => w 0)=weightEntropy p := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  have hword (n : ℕ) : obs (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p))
      (word iidShift (fun w : ℤ → A => w 0) n)=(n : ℝ)*weightEntropy p := by
    rw [obs,funext (iid_word_mass p hp hs n)]
    exact shannon_productWordWeight p hs n
  have ht := rate_tendsto (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) iidShift
    (iidShift_preserving _) (fun w : ℤ → A => w 0) (measurable_pi_apply 0)
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hword,mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory ProbabilityTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma weight_le_one (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) (a : A) : p a≤1 := by
  rw [←hs]
  exact Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma weightEntropy_zero_of_one (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    {a : A} (ha : p a=1) : weightEntropy p=0 := by
  classical
  have hzer : ∑ b∈Finset.univ.erase a,p b=0 := by
    have hh := Finset.sum_erase_add (s:=Finset.univ) p (Finset.mem_univ a)
    rw [hs,ha] at hh
    linarith
  have hb (b : A) (hba : b≠a) : p b=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp hzer b (by simp [hba])
  unfold weightEntropy
  apply Finset.sum_eq_zero
  intro b _
  by_cases hba : b=a
  · simp [hba,ha]
  · simp [hb b hba]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma positive_weightEntropy_max_bound (p : A → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (hh : 0 < weightEntropy p) :
    ∃ c : ℝ,0 ≤ c ∧ c < 1 ∧ ∀ a,p a ≤ c := by
  classical
  have : Nonempty A := by
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp at hs
  obtain ⟨a,ha,hamax⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  refine ⟨p a,hp a,?_,fun b => hamax b (Finset.mem_univ b)⟩
  apply lt_of_le_of_ne (weight_le_one p hp hs a)
  intro he
  have hz := weightEntropy_zero_of_one p hp hs he
  linarith

theorem iid_nullSingleton [DecidableEq A] (p : A → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (hh : 0 < weightEntropy p) :
    NullSingletonClass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  let μ := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)
  obtain ⟨c,hc,hc1,hbound⟩ := positive_weightEntropy_max_bound p hp hs hh
  constructor
  intro w
  have hb (n : ℕ) : μ.real {w} ≤ c^n := by
    have hsub : ({w} : Set (ℤ → A))⊆
        (word iidShift (fun y : ℤ → A => y 0) n) ⁻¹' {word iidShift (fun y : ℤ → A => y 0) n w} := by
      rintro y rfl
      rfl
    have h := measureReal_mono (μ:=μ) hsub
    change μ.real {w}≤ mass μ (word iidShift (fun y : ℤ → A => y 0) n)
      (word iidShift (fun y : ℤ → A => y 0) n w) at h
    have himass := iid_word_mass p hp hs n (word iidShift (fun y : ℤ → A => y 0) n w)
    change mass μ _ _=_ at himass
    rw [himass] at h
    apply h.trans
    calc
      productWordWeight p n _ ≤ ∏ _i : Fin n,c := Finset.prod_le_prod
        (fun _ _ => hp _) (fun _ _ => hbound _)
      _=c^n := by simp
  have hz : μ.real {w}=0 := le_antisymm
    (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1) hb) ENNReal.toReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top μ _)

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_LocallyFiniteLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma rate_equiv (f : Ω → Ω) (p : Ω → α) (e : α ≃ β) : rate μ f (e ∘ p)=rate μ f p := by
  have he (n : ℕ) : obs μ (word f (e ∘ p) n)=obs μ (word f p n) := by
    have hword : word f (e ∘ p) n=(Equiv.piCongrRight (fun _ : Fin n => e)) ∘ word f p n := rfl
    rw [hword,obs_equiv]
  simp only [rate,he]
end StandardMapEntropy.Entropy

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
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_word_pack (f : Ω → Ω) (p : Ω → α) (n m : ℕ) :
    obs μ (word (f^[m]) (word f p m) n)=obs μ (word f p (n*m)) := by
  have h := obs_equiv μ (word f p (n*m)) (wordPack n m)
  simpa only [Function.comp_def,wordPack_apply] using h
lemma rate_power_word (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) (m : ℕ) (hm : 0 < m) :
    rate μ (f^[m]) (word f p m)=(m : ℝ)*rate μ f p := by
  have ht : Tendsto (fun n : ℕ => n*m) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hm) tendsto_id
  have h := ((rate_tendsto μ f hf p hp).comp ht).const_mul (m : ℝ)
  have h' : Tendsto (fun n : ℕ => obs μ (word (f^[m]) (word f p m) n)/(n : ℝ))
      atTop (𝓝 ((m : ℝ)*rate μ f p)) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [obs_word_pack]
    dsimp only [Function.comp_def]
    have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
    have hm0 : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
  exact tendsto_nhds_unique (rate_tendsto μ (f^[m]) (hf.iterate m) (word f p m)
    (word_measurable f hf.measurable p hp m)) h'

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_FiniteCouplingRealization
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
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [MeasurableSingletonClass B] in
theorem realize_finite_coupling_finite (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (p : X → A) (hp : Measurable p) (t : B → ℝ) (R : MatrixCoupling (mass μ p) t) :
    ∃ q : X → B,Measurable q ∧ ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=R.weight a b := by
  have hh (a : A) : ∃ q : X → B,Measurable q ∧
      ∀ b,μ.real ((p ⁻¹' {a})∩q ⁻¹' {b})=R.weight a b :=
    exists_finite_random_variable μ (hp (measurableSet_singleton a)) (R.weight a) (R.nonneg a) (R.row a)
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

omit [StandardBorelSpace X] in
lemma finite_symbolCost_integral (μ : Measure X) [IsFiniteMeasure μ]
    (p q : X → A) (hp : Measurable p) (hq : Measurable q) :
    (∫ x,symbolCost (p x) (q x) ∂μ)=μ.real {x | p x≠q x} := by
  have hm : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
  have he : (fun x => symbolCost (p x) (q x))={x | p x≠q x}.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : p x=q x <;> simp [symbolCost,hx]
  rw [he]
  change (∫ x,{x | p x≠q x}.indicator (fun _ : X => (1 : ℝ)) x ∂μ)=_
  rw [integral_indicator hm]
  simp

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
variable {X I A : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Countable I] [MeasurableSpace A]

attribute [local instance] OAI.HyperbolicCoding.disjointIndexOptionMeasurableSpace
local instance disjointIndexOptionMeasurableSingletonClass : MeasurableSingletonClass (Option I) :=
  ⟨fun _ => trivial⟩

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] in
lemma disjointIndex_some (s : I → Set X) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (x : X) (i : I) : disjointIndex s x=some i ↔ x∈s i := by
  classical
  unfold disjointIndex
  split_ifs with h
  · constructor
    · intro he
      have hi : h.choose=i := Option.some.inj he
      exact hi ▸ h.choose_spec
    · intro hx
      congr 1
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) h.choose_spec hx
  · have hx : x∉s i := fun hx => h ⟨i,hx⟩
    simp [hx]

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] in
lemma disjointIndex_none (s : I → Set X) (x : X) :
    disjointIndex s x=none ↔ x∉⋃ i,s i := by
  classical
  simp only [disjointIndex]
  split_ifs with h
  · have hx : x∈⋃ i,s i := mem_iUnion.mpr h
    simp [hx]
  · have hx : x∉⋃ i,s i := by simpa only [mem_iUnion] using h
    simp [hx]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_disjointIndex (s : I → Set X) (hs : ∀ i,MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) : Measurable (disjointIndex s) := by
  apply measurable_to_countable'
  intro i
  cases i with
  | none =>
    have he : (disjointIndex s) ⁻¹' {none}=(⋃ i,s i)ᶜ := by
      ext x
      exact disjointIndex_none s x
    rw [he]
    exact (MeasurableSet.iUnion hs).compl
  | some i =>
    have he : (disjointIndex s) ⁻¹' {some i}=s i := by
      ext x
      exact disjointIndex_some s hd x i
    rw [he]
    exact hs i

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
  [MeasurableSpace A] in
lemma disjointPaste_on (s : I → Set X) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : I → X → A) (f₀ : X → A) {i : I} {x : X} (hx : x∈s i) :
    disjointPaste s f f₀ x=f i x := by
  unfold disjointPaste
  rw [(disjointIndex_some s hd x i).mpr hx]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_disjointPaste (s : I → Set X) (hs : ∀ i,MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (f : I → X → A)
    (hf : ∀ i,Measurable (f i)) (f₀ : X → A) (hf₀ : Measurable f₀) :
    Measurable (disjointPaste s f f₀) := by
  let F : Option I×X → A := fun ix => match ix.1 with
    | none => f₀ ix.2
    | some i => f i ix.2
  have hF : Measurable F := measurable_from_prod_countable_right (fun i => by
    cases i
    · exact hf₀
    · exact hf _)
  exact hF.comp ((measurable_disjointIndex s hs hd).prodMk measurable_id)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X : Type*} [MeasurableSpace X]

lemma measurableSet_entryLevel {T : X → X} (hT : Measurable T) {B : Set X}
    (hB : MeasurableSet B) (n : ℕ) : MeasurableSet (entryLevel T B n) := by
  have heq : entryLevel T B n=(T^[n] ⁻¹' B) ∩ ⋂ j : ℕ,⋂ (_ : j<n),(T^[j] ⁻¹' B)ᶜ := by
    ext x
    simp only [entryLevel,mem_ofPred_eq,mem_inter_iff,mem_iInter,mem_compl_iff,mem_preimage]
  rw [heq]
  exact (hB.preimage (hT.iterate n)).inter
    (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ => (hB.preimage (hT.iterate j)).compl)))

omit [MeasurableSpace X] in
lemma entryLevel_disjoint (T : X → X) (B : Set X) {n m : ℕ} (hnm : n≠m) :
    Disjoint (entryLevel T B n) (entryLevel T B m) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hnm with h|h
  · exact hy.2 n h hx.1
  · exact hx.2 m h hy.1

omit [MeasurableSpace X] in
lemma mem_entryLevel_iterate {T : X → X} {B : Set X} {n i : ℕ} (hi : i≤n)
    {x : X} (hx : x∈entryLevel T B n) : T^[i] x∈entryLevel T B (n-i) := by
  constructor
  · simpa only [←Function.iterate_add_apply,Nat.sub_add_cancel hi] using hx.1
  · intro j hj
    rw [←Function.iterate_add_apply]
    exact hx.2 (j+i) (by omega)

lemma mem_entryLevel_back (e : X ≃ᵐ X) {B : Set X} {n j : ℕ} {x : X}
    (hx : x∈entryLevel e B n) (hpast : ∀ i : ℕ, (0 < i) → (i ≤ j) → e.symm^[i] x∉B) :
    e.symm^[j] x∈entryLevel e B (n+j) := by
  have hi : Function.LeftInverse (e : X → X) e.symm := e.apply_symm_apply
  constructor
  · rw [Function.iterate_add_apply,hi.iterate j x]
    exact hx.1
  · intro l hl
    by_cases hj : j≤l
    · have heq : l=(l-j)+j := by omega
      rw [heq,Function.iterate_add_apply,hi.iterate j x]
      exact hx.2 (l-j) (by omega)
    · have hlj : j=l+(j-l) := by omega
      rw [hlj,Function.iterate_add_apply,hi.iterate l]
      exact hpast (j-l) (by omega) (by omega)

lemma ae_exists_entry {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) {B : Set X} (hB : MeasurableSet B) (hBp : 0<μ B) :
    ∀ᵐ x ∂μ,∃ n : ℕ,x∈entryLevel T B n := by
  classical
  let H : Set X := ⋃ n : ℕ,T^[n] ⁻¹' B
  have hH : MeasurableSet H := MeasurableSet.iUnion (fun n => hB.preimage (hT.measurable.iterate n))
  have hsub : T ⁻¹' H⊆H := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n+1,by simpa only [mem_preimage,Function.iterate_succ_apply] using hn⟩
  have heq : T ⁻¹' H =ᵐ[μ] H := ae_eq_of_ae_subset_of_measure_ge
    (Filter.Eventually.of_forall hsub) (hT.toMeasurePreserving.measure_preimage hH.nullMeasurableSet).ge
    (hH.preimage hT.measurable).nullMeasurableSet (measure_ne_top μ H)
  have hp : 0<μ H := hBp.trans_le (measure_mono (fun x hx => mem_iUnion.mpr ⟨0,hx⟩))
  have hfull : ∀ᵐ x ∂μ,x∈H := by
    rcases hT.quasiErgodic.ae_mem_or_ae_notMem₀ hH.nullMeasurableSet heq with hh|hh
    · exact hh
    · have : μ H=0 := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
      exact (hp.ne' this).elim
  filter_upwards [hfull] with x hx
  have hex : ∃ n : ℕ,T^[n] x∈B := mem_iUnion.mp hx
  exact ⟨Nat.find hex,Nat.find_spec hex,fun j hj => Nat.find_min hex hj⟩

lemma measurableSet_entryTowerBase (e : X ≃ᵐ X) {B : Set X} (hB : MeasurableSet B) (N : ℕ) :
    MeasurableSet (entryTowerBase e B N) :=
  MeasurableSet.iUnion (fun _ => measurableSet_entryLevel e.measurable hB _)

lemma entryTower_disjoint (e : X ≃ᵐ X) (B : Set X) {N : ℕ} (hN : 0<N)
    (i j : Fin N) (hij : i≠j) :
    Disjoint ((e^[i.val]) '' entryTowerBase e B N) ((e^[j.val]) '' entryTowerBase e B N) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy,rfl⟩ ⟨z,hz,heq⟩
  obtain ⟨q,hq⟩ := mem_iUnion.mp hy
  obtain ⟨r,hr⟩ := mem_iUnion.mp hz
  have hqi : i.val≤q*N+(N-1) := by omega
  have hrj : j.val ≤ r*N+(N-1) := by omega
  have hx := mem_entryLevel_iterate hqi hq
  have hz := mem_entryLevel_iterate hrj hr
  rw [heq] at hz
  have he : q*N+(N-1)-i.val=r*N+(N-1)-j.val := by
    by_contra hne
    exact Set.disjoint_left.mp (entryLevel_disjoint e B hne) hx hz
  have hi : (q*N+(N-1)-i.val)%N=N-1-i.val := by
    rw [Nat.add_sub_assoc (by omega : i.val≤N-1),Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  have hj : (r*N+(N-1)-j.val)%N=N-1-j.val := by
    rw [Nat.add_sub_assoc (by omega : j.val≤N-1),Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  have hh := congrArg (fun n => n%N) he
  rw [hi,hj] at hh
  exact hij (Fin.ext (by omega))

lemma entryTower_covers (e : X ≃ᵐ X) (B : Set X) {N : ℕ} (hN : 0<N) {x : X}
    (hx : ∃ n : ℕ,x∈entryLevel e B n)
    (hpast : ∀ i : ℕ, (0 < i) → (i < N) → e.symm^[i] x∉B) :
    x∈⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N := by
  obtain ⟨n,hn⟩ := hx
  let j := N-1-n%N
  have hj : j<N := by dsimp [j]; omega
  have hnum : n+j=(n/N)*N+(N-1) := by
    have hd := Nat.mod_add_div n N
    have hm := Nat.mod_lt n hN
    rw [Nat.mul_comm] at hd
    dsimp [j]
    omega
  apply mem_iUnion.mpr
  refine ⟨⟨j,hj⟩,e.symm^[j] x,?_,?_⟩
  · apply mem_iUnion.mpr
    refine ⟨n/N,?_⟩
    rw [←hnum]
    exact mem_entryLevel_back e hn (fun i hi hij => hpast i hi (hij.trans_lt hj))
  · exact (show Function.LeftInverse (e : X → X) e.symm from e.apply_symm_apply).iterate j x

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X]

lemma measurableSet_iterate_image (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U) (j : ℕ) :
    MeasurableSet ((e^[j]) '' U) := by
  have hh := (iterateEquiv e j).measurableSet_image.mpr hU
  simpa only [funext (iterateEquiv_apply e j)] using hh

lemma entryTower_error {μ : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : Ergodic e μ) {B : Set X} (hB : MeasurableSet B) (hBp : 0<μ B)
    {N : ℕ} (hN : 0<N) :
    μ (⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N)ᶜ≤(N : ℝ≥0∞)*μ B := by
  classical
  have hc : (⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N)ᶜ ≤ᵐ[μ]
      (⋃ j : Fin N,(e.symm^[j.val]) ⁻¹' B) := by
    filter_upwards [ae_exists_entry he hB hBp] with x hx hnot
    by_contra hbad
    apply hnot
    apply entryTower_covers e B hN hx
    intro i _hi hiN hmem
    exact hbad (mem_iUnion.mpr ⟨⟨i,hiN⟩,hmem⟩)
  calc
    _≤μ (⋃ j : Fin N,(e.symm^[j.val]) ⁻¹' B) := measure_mono_ae hc
    _≤∑' j : Fin N,μ ((e.symm^[j.val]) ⁻¹' B) := measure_iUnion_le _
    _=(N : ℝ≥0∞)*μ B := by
      simp only [((he.toMeasurePreserving.symm e).iterate _).measure_preimage hB.nullMeasurableSet,
        tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma exists_small_positive_marker [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] {δ : ℝ≥0∞} (hδ : 0<δ) :
    ∃ B : Set X,MeasurableSet B ∧ 0<μ B ∧ μ B<δ := by
  obtain ⟨x,hx⟩ := μ.nonempty_support (by exact NeZero.ne μ)
  obtain ⟨B,hxB,hBm,hB⟩ := (Set.singleton x).exists_isOpen_lt_of_lt δ (by simpa using hδ : μ {x}<δ)
  exact ⟨B,hBm.measurableSet,(μ.mem_support_iff_forall x).mp hx B (hBm.mem_nhds (hxB (mem_singleton x))),hB⟩

theorem exists_rohlin_tower [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular]
    (e : X ≃ᵐ X) (he : Ergodic e μ) {N : ℕ} (hN : 0<N) {ε : ℝ} (hε : 0<ε) :
    ∃ U : Set X,MeasurableSet U ∧
      (∀ i j : Fin N,i≠j → Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) ∧
      μ (⋃ j : Fin N,(e^[j.val]) '' U)ᶜ<ENNReal.ofReal ε := by
  have hNc : (N : ℝ≥0∞)≠0 := by exact_mod_cast hN.ne'
  have hNf : (N : ℝ≥0∞)≠⊤ := by simp
  have hd : 0<ENNReal.ofReal ε/(N : ℝ≥0∞) := ENNReal.div_pos (ENNReal.ofReal_pos.mpr hε).ne' hNf
  obtain ⟨B,hB,hBp,hBs⟩ := exists_small_positive_marker μ hd
  refine ⟨entryTowerBase e B N,measurableSet_entryTowerBase e hB N,entryTower_disjoint e B hN,?_⟩
  apply (entryTower_error e he hB hBp hN).trans_lt
  rw [mul_comm]
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl hNc) (Or.inl hNf)).mp hBs

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma measurable_paintTower (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    {B : X → (Fin N → A)} (hB : Measurable B) {p : X → A} (hp : Measurable p) :
    Measurable (paintTower e U N B p) :=
  measurable_disjointPaste (fun i : Fin N => (e^[i.val]) '' U) (fun i => measurableSet_iterate_image e hU i.val) hd _
    (fun i => ((measurable_pi_apply i).comp hB).comp (e.symm.measurable.iterate i.val)) _ hp

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma paintTower_level (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (B : X → (Fin N → A)) (p : X → A) {x : X} (hx : x∈U) (i : Fin N) :
    paintTower e U N B p (e^[i.val] x)=B x i := by
  unfold paintTower
  rw [disjointPaste_on _ hd _ _ (mem_image_of_mem _ hx)]
  rw [(show Function.LeftInverse e.symm (e : X → X) from e.symm_apply_apply).iterate i.val x]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma paintTower_word (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (B : X → (Fin N → A)) (p : X → A) {x : X} (hx : x∈U) :
    word e (paintTower e U N B p) N x=B x := by
  funext i
  exact paintTower_level e U N hd B p hx i

lemma measure_iterate_image (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (U : Set X) (i : ℕ) : μ ((e^[i]) '' U)=μ U := by
  have hmp : MeasurePreserving (iterateEquiv e i).symm μ μ :=
    (show MeasurePreserving (iterateEquiv e i) μ μ from by
      simpa only [funext (iterateEquiv_apply e i)] using he.iterate i).symm _
  have hset : (e^[i]) '' U=(iterateEquiv e i).symm ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (iterateEquiv e i).symm ((iterateEquiv e i) y)∈U
      simpa only [MeasurableEquiv.symm_apply_apply] using hy
    · intro hx
      refine ⟨(iterateEquiv e i).symm x,hx,?_⟩
      exact (iterateEquiv e i).apply_symm_apply x
  rw [hset]
  exact hmp.measure_preimage_equiv U

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_PhaseAveraging
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
variable {X A B I : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B] [Fintype I]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] in
lemma map_restrict_image_equiv (μ : Measure X) (f : X ≃ᵐ X) (hf : MeasurePreserving f μ μ)
    (U : Set X) (p : X → A) (hp : Measurable p) :
    (μ.restrict (f '' U)).map p=(μ.restrict U).map (p ∘ f) := by
  have hh := hf.restrict_image_emb f.measurableEmbedding U
  rw [←hh.map_eq,Measure.map_map hp f.measurable]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] in
lemma map_restrict_finite_iUnion (μ : Measure X) (S : I → Set X)
    (hS : ∀ i,MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (p : X → A) (hp : Measurable p) :
    (μ.restrict (⋃ i,S i)).map p=∑ i,(μ.restrict (S i)).map p := by
  rw [Measure.restrict_iUnion hd hS,Measure.map_sum hp.aemeasurable,Measure.sum_fintype]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
lemma tower_measure (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    μ (⋃ i : Fin N,(e^[i.val]) '' U)=(N : ℝ≥0∞)*μ U := by
  rw [measure_iUnion hd (fun i => measurableSet_iterate_image e hU i.val),tsum_fintype]
  simp only [measure_iterate_image μ e he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_ScaledFiniteCoupling
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
variable {X A B : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]

lemma nameCost_nonneg {E : Type*} {n : ℕ} (a b : Fin n → E) : 0≤nameCost a b :=
  Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A] in
lemma wordWindow_word (f : X → X) (p : X → A) {n m : ℕ} (i : ℕ) (hi : i+m≤n) (x : X) :
    wordWindow i hi (word f p n x)=word f p m (f^[i] x) := by
  funext j
  simp only [wordWindow,word,Function.iterate_add_apply]

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_DecodedTowerCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open scoped BigOperators
variable {A C : Type*} {k t r : ℕ}

lemma prefixNameCost_modify (F : C → A) (a : Fin k → C) (b d : Fin (k+t) → A) :
    prefixNameCost F a d ≤ prefixNameCost F a b+nameCost b d := by
  have htri : prefixNameCost F a d ≤ prefixNameCost F a b+
      ∑ i : Fin k,symbolCost (b (Fin.castAdd t i)) (d (Fin.castAdd t i)) := by
    unfold prefixNameCost
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun _ _ => symbolCost_triangle _ _ _)
  apply htri.trans
  apply add_le_add_right
  rw [nameCost,Fin.sum_univ_add]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _))

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

omit [StandardBorelSpace X] [Nonempty A] in
lemma word_disagreement_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p q : X → A)
    (hp : Measurable p) (hq : Measurable q) (m : ℕ) :
    μ.real {x | word f p m x≠word f q m x}≤(m : ℝ)*μ.real {x | p x≠q x} := by
  have hset : {x | word f p m x≠word f q m x}=
      ⋃ i : Fin m,(f^[i.val]) ⁻¹' {x | p x≠q x} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion,mem_preimage]
    constructor
    · intro hx
      by_contra hn
      apply hx
      funext i
      have hh : ∀ i : Fin m,p (f^[i.val] x)=q (f^[i.val] x) := by simpa using hn
      exact hh i
    · rintro ⟨i,hi⟩ h
      exact hi (congrFun h i)
  rw [hset]
  apply (measureReal_iUnion_fintype_le _).trans
  have hE : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
  have he (i : Fin m) : μ.real ((f^[i.val]) ⁻¹' {x | p x≠q x})=μ.real {x | p x≠q x} := by
    rw [Measure.real,Measure.real,(hf.iterate i.val).measure_preimage hE.nullMeasurableSet]
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,le_refl]

omit [StandardBorelSpace X] [Nonempty A] in
lemma word_lawClose_of_repaint (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p q : X → A)
    (hp : Measurable p) (hq : Measurable q) (m : ℕ) :
    LawClose (μ.map (word f p m)) (μ.map (word f q m)) ((m : ℝ)*μ.real {x | p x≠q x}) := by
  intro D hD
  exact (law_distance_le_disagreement μ (word_measurable f hf.measurable p hp m)
    (word_measurable f hf.measurable q hq m) hD).trans (word_disagreement_le μ f hf p q hp hq m)

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_SanitizedTowerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators
variable {X A C : Type*} {k t : ℕ} [MeasurableSpace X]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma normalizedPrefixCost_modify (F : C → A) (a : Fin k → C) (b d : Fin (k+t) → A) :
    normalizedPrefixCost F a d ≤ normalizedPrefixCost F a b+nameCost b d/(k+t : ℕ) := by
  rw [normalizedPrefixCost,normalizedPrefixCost,←add_div]
  exact div_le_div_of_nonneg_right (prefixNameCost_modify F a b d) (Nat.cast_nonneg _)

omit [MeasurableSpace X] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma prefixNameCost_word_factor (f : X → X) (p : X → C) (F : C → A) (x : X) :
    prefixNameCost (k:=k) (t:=t) F (word f p k x) (word f (F ∘ p) (k+t) x)=0 := by
  simp [prefixNameCost,word,symbolCost]

theorem lift_prefix_transport (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : Measurable f) (p : X → C) (hp : Measurable p) (F : C → A)
    {v : (Fin (k+t) → A) → ℝ}
    (S : MatrixCoupling (mass μ (word f (F ∘ p) (k+t))) v) :
    ∃ R : MatrixCoupling (mass μ (word f p k)) v,
      R.cost (normalizedPrefixCost F)≤S.cost nameCost/(k+t : ℕ) := by
  have hF : Measurable F := measurable_of_finite F
  let P := MatrixCoupling.observations μ (word f p k) (word f (F ∘ p) (k+t))
    (word_measurable f hf p hp k) (word_measurable f hf _ (hF.comp hp) (k+t))
  have hP : P.cost (normalizedPrefixCost F)=0 := by
    rw [MatrixCoupling.observations_cost]
    simp only [normalizedPrefixCost,prefixNameCost_word_factor,zero_div,integral_zero]
  refine ⟨P.comp S,?_⟩
  have hc := P.comp_cost_le S (normalizedPrefixCost F)
    (fun a b => nameCost a b/(k+t : ℕ)) (normalizedPrefixCost F)
    (normalizedPrefixCost_modify F)
  rw [hP,zero_add] at hc
  have he : S.cost (fun a b => nameCost a b/(k+t : ℕ))=S.cost nameCost/(k+t : ℕ) := by
    simp only [MatrixCoupling.cost,mul_div_assoc,Finset.sum_div]
  exact hc.trans_eq he

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_FullEntropyCopySequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] in
lemma FiniteRateSupremum.upper {μ : Measure X} [IsProbabilityMeasure μ] {f : X → X} {h : ℝ}
    (H : FiniteRateSupremum μ f h)
    {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (p : X → C) (hp : Measurable p) : rate μ f p≤h := by
  have hc : Fintype.card C-1+1=Fintype.card C := Nat.sub_add_cancel Fintype.card_pos
  let e : C ≃ Fin (Fintype.card C-1+1) := (Fintype.equivFin C).trans (finCongr hc.symm)
  have he := H.1 (Fintype.card C-1) (e ∘ p) ((measurable_of_finite e).comp hp)
  rwa [rate_equiv] at he

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal NNReal Topology
variable {X A : Type*} [MeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma word_law_of_iid_factor (μ : Measure X) (e : X ≃ᵐ X) (p : X → A)
    (_hp : Measurable p) (β : Measure A) [IsProbabilityMeasure β]
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)))
    (n : ℕ) : μ.map (word e p n)=Measure.pi (fun _ : Fin n => β) := by
  have heq : word iidShift (fun w : ℤ → A => w 0) n ∘ orbitName e p=word e p n := by
    funext x i
    rw [Function.comp_apply,iid_word_eq]
    exact congrArg p (integerIterate_nat e i.val x)
  have hm := congrArg (fun ν => ν.map (word iidShift (fun w : ℤ → A => w 0) n)) hcode.map_eq
  rw [Measure.map_map (word_measurable iidShift iidShift.measurable _ (measurable_pi_apply 0) n)
    hcode.measurable,heq,iid_word_law] at hm
  exact hm

lemma rate_of_iid_factor [DecidableEq A] (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hcode : MeasurePreserving (orbitName e p) μ
      (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))) :
    rate μ e p=weightEntropy β := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hword (n : ℕ) : obs μ (word e p n)=(n : ℝ)*weightEntropy β := by
    have hmass : mass μ (word e p n)=productWordWeight β n := by
      funext w
      change μ.real ((word e p n) ⁻¹' {w})=_
      rw [←map_measureReal_apply (word_measurable e e.measurable p hp n) (measurableSet_singleton w),
        word_law_of_iid_factor μ e p hp (finiteWeightLaw β) hcode,
        Measure.real,Measure.pi_singleton]
      simp only [finiteWeightLaw_singleton,ENNReal.toReal_prod,ENNReal.toReal_ofReal (hβ _),
        productWordWeight]
    rw [obs,hmass]
    exact shannon_productWordWeight β hβsum n
  apply tendsto_nhds_unique (rate_tendsto μ e he p hp)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hword,mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')]

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_RelativeFiniteRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma finite_map_eq_of_mass (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (h : ∀ a,mass μ p a=mass ν q a) :
    μ.map p=ν.map q := by
  apply Measure.ext_of_singleton
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [Measure.map_apply hp (measurableSet_singleton a),Measure.map_apply hq (measurableSet_singleton a)]
  exact h a

omit [StandardBorelSpace X] [StandardBorelSpace Y] [Fintype A] in
lemma mass_eq_of_map_eq (μ : Measure X) (ν : Measure Y) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (h : μ.map p=ν.map q) (a : A) :
    mass μ p a=mass ν q a := by
  have hh := congrArg (fun ξ : Measure A => (ξ {a}).toReal) h
  simpa only [Measure.map_apply hp (measurableSet_singleton a),
    Measure.map_apply hq (measurableSet_singleton a),mass] using hh

omit [StandardBorelSpace X] in
lemma relative_finite_realization (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (p : X → A) (α : X → B) (q : Y → A)
    (hp : Measurable p) (hα : Measurable α) (hq : Measurable q)
    (hfirst : μ.map p=ν.map q) :
    ∃ b : Y → B,Measurable b ∧
      ν.map (fun y => (q y,b y))=μ.map (fun x => (p x,α x)) := by
  let S := MatrixCoupling.observations μ p α hp hα
  let R : MatrixCoupling (mass ν q) (mass μ α) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun a => (S.row a).trans (mass_eq_of_map_eq μ ν p q hp hq hfirst a)
    col := S.col }
  obtain ⟨b,hb,hR⟩ := realize_finite_coupling_finite ν q hq (mass μ α) R
  refine ⟨b,hb,finite_map_eq_of_mass ν μ _ _ (hq.prodMk hb) (hp.prodMk hα) ?_⟩
  rintro ⟨a,c⟩
  exact hR a c

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma map_restrict_factor (μ : Measure X) (ν : Measure Y)
    (π : X → Y) (hπ : MeasurePreserving π μ ν) {U : Set Y} (hU : MeasurableSet U) :
    (μ.restrict (π ⁻¹' U)).map π=ν.restrict U := by
  rw [←hπ.map_eq,Measure.restrict_map hπ.measurable hU]

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] in
lemma factor_iterate (e : X → X) (f : Y → Y) (π : X → Y)
    (h : ∀ x,π (e x)=f (π x)) (i : ℕ) (x : X) : π (e^[i] x)=f^[i] (π x) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',h,ih,Function.iterate_succ_apply']

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma factor_word (e : X → X) (f : Y → Y) (π : X → Y)
    (h : ∀ x,π (e x)=f (π x)) (p : Y → A) (n : ℕ) :
    word e (p ∘ π) n=word f p n ∘ π := by
  funext x j
  exact congrArg p (factor_iterate e f π h j.val x)

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma factor_tower_level (e : X ≃ᵐ X) (f : Y ≃ᵐ Y) (π : X → Y)
    (h : ∀ x,π (e x)=f (π x)) (U : Set Y) (i : ℕ) :
    (e^[i]) '' (π ⁻¹' U)=π ⁻¹' ((f^[i]) '' U) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨π z,hz,(factor_iterate e f π h i z).symm⟩
  · rintro ⟨y,hy,hxy⟩
    let z := (iterateEquiv e i).symm x
    have hzx : e^[i] z=x := (iterateEquiv e i).apply_symm_apply x
    refine ⟨z,?_,hzx⟩
    have hh : f^[i] (π z)=f^[i] y := by rw [←factor_iterate e f π h,hzx,hxy]
    have hz := (iterateEquiv f i).injective hh
    change π z∈U
    rwa [hz]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [StandardBorelSpace X] in
lemma relative_tower_base_copy (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (e : X ≃ᵐ X) (f : Y ≃ᵐ Y) (π : X → Y) (hπ : MeasurePreserving π μ ν)
    (hcomm : ∀ x,π (e x)=f (π x))
    (p : Y → A) (α : X → B) (hp : Measurable p) (hα : Measurable α)
    {U : Set Y} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((f^[i.val]) '' U) ((f^[j.val]) '' U))) :
    ∃ b : Y → B,Measurable b ∧
      (ν.restrict U).map (word f (fun y => (p y,b y)) N)=
      (μ.restrict (π ⁻¹' U)).map (word e (fun x => (p (π x),α x)) N) := by
  let V := π ⁻¹' U
  have hV : MeasurableSet V := hπ.measurable hU
  have hP : Measurable (word e (p ∘ π) N) :=
    word_measurable e e.measurable _ (hp.comp hπ.measurable) N
  have hQ : Measurable (word f p N) := word_measurable f f.measurable p hp N
  have hA : Measurable (word e α N) := word_measurable e e.measurable α hα N
  have hfirst : (μ.restrict V).map (word e (p ∘ π) N)=(ν.restrict U).map (word f p N) := by
    rw [factor_word e f π hcomm p N,←Measure.map_map hQ hπ.measurable,map_restrict_factor μ ν π hπ hU]
  obtain ⟨C,hC,hjoint⟩ := relative_finite_realization (μ.restrict V) (ν.restrict U)
    (word e (p ∘ π) N) (word e α N) (word f p N) hP hA hQ hfirst
  let b := paintTower f U N C (fun _ => Classical.arbitrary B)
  have hb : Measurable b := measurable_paintTower f hU N hd hC measurable_const
  refine ⟨b,hb,?_⟩
  let zip : (Fin N → A) × (Fin N → B) → (Fin N → A×B) := fun ab i => (ab.1 i,ab.2 i)
  have hzip : Measurable zip := measurable_of_finite zip
  have heq : (ν.restrict U).map (word f (fun y => (p y,b y)) N)=
      (ν.restrict U).map (zip ∘ fun y => (word f p N y,C y)) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hU] with y hy
    have hh : word f b N y=C y := paintTower_word f U N hd C _ hy
    funext i
    exact congrArg (fun c => (p (f^[i.val] y),c i)) hh
  rw [heq,←Measure.map_map hzip (hQ.prodMk hC),hjoint,
    Measure.map_map hzip (hP.prodMk hA)]
  rfl

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma equal_base_level_laws (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y ≃ᵐ Y) (hf : MeasurePreserving f ν ν)
    (V : Set X) (U : Set Y) (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {N m : ℕ} (hbase : (μ.restrict V).map (word e p N)=(ν.restrict U).map (word f q N))
    (i : ℕ) (hi : i+m≤N) :
    (μ.restrict ((e^[i]) '' V)).map (word e p m)=
      (ν.restrict ((f^[i]) '' U)).map (word f q m) := by
  have heI : MeasurePreserving (iterateEquiv e i) μ μ := by
    simpa only [funext (iterateEquiv_apply e i)] using he.iterate i
  have hfI : MeasurePreserving (iterateEquiv f i) ν ν := by
    simpa only [funext (iterateEquiv_apply f i)] using hf.iterate i
  have hpw := word_measurable e e.measurable p hp m
  have hqw := word_measurable f f.measurable q hq m
  change (μ.restrict ((iterateEquiv e i) '' V)).map (word e p m)=
    (ν.restrict ((iterateEquiv f i) '' U)).map (word f q m)
  rw [map_restrict_image_equiv μ (iterateEquiv e i) heI V _ hpw,
    map_restrict_image_equiv ν (iterateEquiv f i) hfI U _ hqw]
  have hcomp (g : X ≃ᵐ X) : word g p m ∘ iterateEquiv g i=wordWindow i hi ∘ word g p N := by
    funext x
    exact (wordWindow_word g p i hi x).symm
  rw [hcomp e]
  have hcomp' : word f q m ∘ iterateEquiv f i=wordWindow i hi ∘ word f q N := by
    funext y
    exact (wordWindow_word f q i hi y).symm
  rw [hcomp',←Measure.map_map (measurable_of_countable (wordWindow (A:=A) i hi))
    (word_measurable e e.measurable p hp N),hbase,
    Measure.map_map (measurable_of_countable (wordWindow (A:=A) i hi))
    (word_measurable f f.measurable q hq N)]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] [StandardBorelSpace Y] [Fintype A] [MeasurableSingletonClass A] in
lemma lawClose_of_common_restriction (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    {V : Set X} {U : Set Y} (_ : MeasurableSet V) (_ : MeasurableSet U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    (hc : (μ.restrict V).map p=(ν.restrict U).map q) :
    LawClose (μ.map p) (ν.map q) (μ.real Vᶜ+ν.real Uᶜ) := by
  intro D hD
  rw [map_measureReal_apply hp hD,map_measureReal_apply hq hD]
  have hcommon := congrArg (fun ξ : Measure A => (ξ D).toReal) hc
  simp only [Measure.map_apply hp hD,Measure.map_apply hq hD,
    Measure.restrict_apply (hp hD),Measure.restrict_apply (hq hD)] at hcommon
  change μ.real ((p ⁻¹' D)∩V)=ν.real ((q ⁻¹' D)∩U) at hcommon
  have hp₀ : μ.real ((p ⁻¹' D)∩V)≤μ.real (p ⁻¹' D) := measureReal_mono inter_subset_left
  have hq₀ : ν.real ((q ⁻¹' D)∩U)≤ν.real (q ⁻¹' D) := measureReal_mono inter_subset_left
  have hp₁ : μ.real (p ⁻¹' D)≤μ.real ((p ⁻¹' D)∩V)+μ.real Vᶜ := by
    apply (measureReal_mono (μ:=μ) (show p ⁻¹' D⊆((p ⁻¹' D)∩V)∪Vᶜ by
      intro x hx; by_cases hv : x∈V
      · exact Or.inl ⟨hx,hv⟩
      · exact Or.inr hv)).trans
    exact measureReal_union_le _ _
  have hq₁ : ν.real (q ⁻¹' D)≤ν.real ((q ⁻¹' D)∩U)+ν.real Uᶜ := by
    apply (measureReal_mono (μ:=ν) (show q ⁻¹' D⊆((q ⁻¹' D)∩U)∪Uᶜ by
      intro x hx; by_cases hu : x∈U
      · exact Or.inl ⟨hx,hu⟩
      · exact Or.inr hu)).trans
    exact measureReal_union_le _ _
  rw [abs_le]
  constructor <;> linarith [measureReal_nonneg (μ:=μ) (s:=Vᶜ),measureReal_nonneg (μ:=ν) (s:=Uᶜ)]

omit [StandardBorelSpace X] in
lemma tower_disjoint_mono (e : X ≃ᵐ X) (V : Set X) {N M : ℕ} (hm : M≤N)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V))) :
    Pairwise (fun i j : Fin M => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) := by
  intro i j hij
  apply hd (i:=⟨i.val,i.isLt.trans_le hm⟩) (j:=⟨j.val,j.isLt.trans_le hm⟩)
  intro hh
  exact hij (Fin.ext (congrArg (fun z : Fin N => z.val) hh))

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma equal_base_interior_laws (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y ≃ᵐ Y) (hf : MeasurePreserving f ν ν)
    {V : Set X} {U : Set Y} (hV : MeasurableSet V) (hU : MeasurableSet U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {N m : ℕ}
    (hdV : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)))
    (hdU : Pairwise (fun i j : Fin N => Disjoint ((f^[i.val]) '' U) ((f^[j.val]) '' U)))
    (hbase : (μ.restrict V).map (word e p N)=(ν.restrict U).map (word f q N)) :
    (μ.restrict (⋃ i : Fin (N-m),(e^[i.val]) '' V)).map (word e p m)=
    (ν.restrict (⋃ i : Fin (N-m),(f^[i.val]) '' U)).map (word f q m) := by
  rw [map_restrict_finite_iUnion μ (fun i : Fin (N-m) => (e^[i.val]) '' V) (fun i => measurableSet_iterate_image e hV i.val)
    (tower_disjoint_mono e V (Nat.sub_le N m) hdV) _ (word_measurable e e.measurable p hp m),
    map_restrict_finite_iUnion ν (fun i : Fin (N-m) => (f^[i.val]) '' U) (fun i => measurableSet_iterate_image f hU i.val)
    (tower_disjoint_mono f U (Nat.sub_le N m) hdU) _ (word_measurable f f.measurable q hq m)]
  apply Finset.sum_congr rfl
  intro i _
  exact equal_base_level_laws μ ν e he f hf V U p q hp hq hbase i.val (by omega)

omit [StandardBorelSpace X] in
lemma tower_interior_compl_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    {N m : ℕ} (hN : 0<N) (hm : m≤N)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    μ.real (⋃ i : Fin (N-m),(e^[i.val]) '' U)ᶜ≤
      μ.real (⋃ i : Fin N,(e^[i.val]) '' U)ᶜ+(m : ℝ)/(N : ℝ) := by
  have hc := congrArg ENNReal.toReal (tower_measure μ e he hU (N-m)
    (tower_disjoint_mono e U (Nat.sub_le N m) hd))
  have ht := congrArg ENNReal.toReal (tower_measure μ e he hU N hd)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_sub hm] at hc ht
  change μ.real (⋃ i : Fin (N-m),(e^[i.val]) '' U)=((N : ℝ)-m)*μ.real U at hc
  change μ.real (⋃ i : Fin N,(e^[i.val]) '' U)=(N : ℝ)*μ.real U at ht
  have hC := measureReal_add_measureReal_compl (μ:=μ)
    (MeasurableSet.iUnion (fun i : Fin (N-m) => measurableSet_iterate_image e hU i.val))
  have hT := measureReal_add_measureReal_compl (μ:=μ)
    (MeasurableSet.iUnion (fun i : Fin N => measurableSet_iterate_image e hU i.val))
  have hu : μ.real univ=1 := by simp [Measure.real]
  rw [hu,hc] at hC
  rw [hu,ht] at hT
  have hmass : (N : ℝ)*μ.real U≤1 := by
    linarith [measureReal_nonneg (μ:=μ) (s:=(⋃ i : Fin N,(e^[i.val]) '' U)ᶜ)]
  have hbound : (m : ℝ)*μ.real U≤(m : ℝ)/(N : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg m)]
  linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
  [TopologicalSpace Y] [SecondCountableTopology Y] [OpensMeasurableSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [StandardBorelSpace X] in
theorem relative_measurable_graph_approx (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] [NullSingletonClass ν] [ν.OuterRegular]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (f : Y ≃ᵐ Y) (hf : Ergodic f ν)
    (π : X → Y) (hπ : MeasurePreserving π μ ν) (hcomm : ∀ x,π (e x)=f (π x))
    (p : Y → A) (α : X → B) (hp : Measurable p) (hα : Measurable α)
    (m : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ b : Y → B,Measurable b ∧
      LawClose (μ.map (word e (fun x => (p (π x),α x)) m))
        (ν.map (word f (fun y => (p y,b y)) m)) ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (m : ℝ) (4*(m : ℝ)/ε)+1)
  have hNm : m<N := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) (by linarith : max (m : ℝ) (4*(m : ℝ)/ε)<N))
  have hNp : 0<N := lt_of_le_of_lt (Nat.zero_le m) hNm
  have hfrac : (m : ℝ)/(N : ℝ)<ε/4 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hNp)).mpr
    have hh : 4*(m : ℝ)/ε<(N : ℝ) := by linarith [le_max_right (m : ℝ) (4*(m : ℝ)/ε)]
    have hh' := (div_lt_iff₀ hε).mp hh
    linarith
  obtain ⟨U,hU,hdU,hcover⟩ := exists_rohlin_tower ν f hf hNp (show 0<ε/4 by positivity)
  let V := π ⁻¹' U
  have hV : MeasurableSet V := hπ.measurable hU
  have hlevels (i : ℕ) : (e^[i]) '' V=π ⁻¹' ((f^[i]) '' U) := factor_tower_level e f π hcomm U i
  have hdV : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) := by
    intro i j hij
    rw [hlevels,hlevels]
    exact (hdU i j hij).preimage π
  obtain ⟨b,hb,hbase⟩ := relative_tower_base_copy μ ν e f π hπ hcomm p α hp hα hU N hdU
  refine ⟨b,hb,?_⟩
  have hi := equal_base_interior_laws μ ν e he f hf.toMeasurePreserving hV hU
    (fun x => (p (π x),α x)) (fun y => (p y,b y)) ((hp.comp hπ.measurable).prodMk hα)
    (hp.prodMk hb) (m:=m) hdV hdU hbase.symm
  have hc := lawClose_of_common_restriction μ ν
    (MeasurableSet.iUnion (fun i : Fin (N-m) => measurableSet_iterate_image e hV i.val))
    (MeasurableSet.iUnion (fun i : Fin (N-m) => measurableSet_iterate_image f hU i.val))
    _ _ (word_measurable e e.measurable _ ((hp.comp hπ.measurable).prodMk hα) m)
    (word_measurable f f.measurable _ (hp.prodMk hb) m) hi
  have hcU : ν.real (⋃ i : Fin N,(f^[i.val]) '' U)ᶜ<ε/4 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr hcover
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hunion : (⋃ i : Fin N,(e^[i.val]) '' V)=π ⁻¹' (⋃ i : Fin N,(f^[i.val]) '' U) := by
    simp only [hlevels,preimage_iUnion]
  have hcV : μ.real (⋃ i : Fin N,(e^[i.val]) '' V)ᶜ=ν.real (⋃ i : Fin N,(f^[i.val]) '' U)ᶜ := by
    rw [hunion,←preimage_compl]
    exact congrArg ENNReal.toReal (hπ.measure_preimage
      (MeasurableSet.iUnion (fun i : Fin N => measurableSet_iterate_image f hU i.val)).compl.nullMeasurableSet)
  have h₁ := tower_interior_compl_bound μ e he hV hNp hNm.le hdV
  have h₂ := tower_interior_compl_bound ν f hf.toMeasurePreserving hU hNp hNm.le hdU
  exact hc.mono (by linarith)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators symmDiff
variable {X : Type*} [mX : MeasurableSpace X]

lemma finite_sigma_set_approx (μ : Measure X) [IsFiniteMeasure μ]
    (m : ℕ → MeasurableSpace X) (hm : Monotone m) (hgen : ‹MeasurableSpace X›=⨆ n,m n)
    {s : Set X} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0<ε) :
    ∃ n : ℕ,∃ t : Set X,MeasurableSet[m n] t ∧ μ (t ∆ s)<ε := by
  let C : Set (Set X) := {t | ∃ n,MeasurableSet[m n] t}
  have hC : IsSetRing C := {
    empty_mem := ⟨0,@MeasurableSet.empty X (m 0)⟩
    union_mem := by
      rintro s t ⟨i,hi⟩ ⟨j,hj⟩
      exact ⟨max i j,((hm (le_max_left _ _)) _ hi).union ((hm (le_max_right _ _)) _ hj)⟩
    sdiff_mem := by
      rintro s t ⟨i,hi⟩ ⟨j,hj⟩
      exact ⟨max i j,((hm (le_max_left _ _)) _ hi).diff ((hm (le_max_right _ _)) _ hj)⟩ }
  have he : (⨆ n,m n)=MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · apply iSup_le
      intro n t ht
      exact MeasurableSpace.measurableSet_generateFrom ⟨n,ht⟩
    · apply MeasurableSpace.generateFrom_le
      rintro t ⟨n,ht⟩
      exact (le_iSup m n) _ ht
  have hc : ∃ D : Set (Set X),D.Countable ∧ D⊆C ∧ μ (⋃₀ D)ᶜ=0 := by
    refine ⟨{univ},countable_singleton _,?_,?_⟩
    · intro t ht
      rcases mem_singleton_iff.mp ht with rfl
      exact ⟨0,@MeasurableSet.univ X (m 0)⟩
    · simp
  obtain ⟨t,⟨n,hn⟩,ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hc
    (hgen.trans he) hs hε
  exact ⟨n,t,hn,ht⟩

theorem finite_factor_approx (μ : Measure X) [IsProbabilityMeasure μ]
    (F : ℕ → Type*) [∀ n,Fintype (F n)] [∀ n,MeasurableSpace (F n)]
    [∀ n,MeasurableSingletonClass (F n)] (f : (n : ℕ) → X → F n)
    (hm : Monotone (fun n => MeasurableSpace.comap (f n) inferInstance))
    (hgen : ‹MeasurableSpace X›=⨆ n,MeasurableSpace.comap (f n) inferInstance)
    {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ,∃ D : F N → A,μ.real {x | D (f N x)≠p x}<ε := by
  classical
  let δ := ε/((Fintype.card A : ℝ)+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  have ha (a : A) := finite_sigma_set_approx μ
    (fun n => MeasurableSpace.comap (f n) inferInstance) hm hgen
    (hp (measurableSet_singleton a)) (ENNReal.ofReal_pos.mpr hδ)
  choose n t ht hclose using ha
  let N := Finset.univ.sup n
  have hn (a : A) : n a≤N := Finset.le_sup (Finset.mem_univ a)
  have ht' (a : A) : MeasurableSet[MeasurableSpace.comap (f N) inferInstance] (t a) :=
    (hm (hn a)) _ (ht a)
  have hu (a : A) := MeasurableSpace.measurableSet_comap.mp (ht' a)
  choose U hUm hUt using hu
  let D : F N → A := fun y => if h : ∃ a,y∈U a then h.choose else Classical.ofNonempty
  have hbad : {x | D (f N x)≠p x}⊆⋃ a : A,t a ∆ (p ⁻¹' {a}) := by
    intro x hx
    by_contra hn
    have hnot (a : A) : x∉t a ∆ (p ⁻¹' {a}) := by
      intro ha
      exact hn (mem_iUnion.mpr ⟨a,ha⟩)
    have he (a : A) : f N x∈U a ↔ p x=a := by
      have hiff : x∈t a ↔ x∈p ⁻¹' {a} := by
        have hh := hnot a
        simp only [mem_symmDiff] at hh
        tauto
      rw [←hUt a] at hiff
      exact hiff
    have hex : ∃ a,f N x∈U a := ⟨p x,(he _).mpr rfl⟩
    exact hx (by simpa only [D,dite_eq_left hex] using ((he hex.choose).mp hex.choose_spec).symm)
  have hc (a : A) : μ.real (t a ∆ (p ⁻¹' {a}))≤δ := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr (hclose a)
    rw [ENNReal.toReal_ofReal hδ.le] at hh
    exact hh.le
  refine ⟨N,D,lt_of_le_of_lt ((measureReal_mono hbad).trans
    ((measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun a _ => hc a)))) ?_⟩
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have he : ((Fintype.card A : ℝ)+1)*δ=ε := mul_div_cancel₀ ε (ne_of_gt (by positivity))
  nlinarith

end HyperbolicCoding

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
open scoped BigOperators ENNReal
variable {A B : Type*} [MeasurableSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

lemma measurable_centeredWindow [Fintype A] [MeasurableSingletonClass A]
    (N : ℕ) : Measurable (centeredWindow (A:=A) N) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma centeredWindow_comap_monotone [Fintype A] [MeasurableSingletonClass A] :
    Monotone (fun N => MeasurableSpace.comap (centeredWindow (A:=A) N) inferInstance) := by
  intro N M hNM
  let r : (Fin (2*M+1) → A) → (Fin (2*N+1) → A) :=
    fun v i => v ⟨i.val+(M-N),by omega⟩
  have hm : Measurable[MeasurableSpace.comap (centeredWindow (A:=A) M) inferInstance]
      (centeredWindow (A:=A) M) := measurable_iff_comap_le.mpr le_rfl
  have hh := (measurable_of_countable r).comp hm
  have heq : r ∘ centeredWindow (A:=A) M=centeredWindow N := by
    funext w i
    dsimp [r,centeredWindow]
    congr 1
    omega
  rw [heq] at hh
  exact measurable_iff_comap_le.mp hh

lemma centeredWindow_generates [Fintype A] [MeasurableSingletonClass A] :
    (inferInstance : MeasurableSpace (ℤ → A))=
      ⨆ N,MeasurableSpace.comap (centeredWindow (A:=A) N) inferInstance := by
  let m := ⨆ N,MeasurableSpace.comap (centeredWindow (A:=A) N) inferInstance
  apply le_antisymm
  · have hi (i : ℤ) : @Measurable (ℤ → A) A m inferInstance (fun w => w i) := by
      let N := i.natAbs
      let j : Fin (2*N+1) := ⟨(i+N).toNat,by
        have h₁ := (Int.le_natAbs (a:=i))
        have h₂ : -i≤(i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a:=-i))
        dsimp [N]
        omega⟩
      have hN : @Measurable (ℤ → A) (Fin (2*N+1) → A) m inferInstance (centeredWindow N) :=
        measurable_iff_comap_le.mpr
          (le_iSup (fun n => MeasurableSpace.comap (centeredWindow (A:=A) n) inferInstance) N)
      have hh := (measurable_pi_apply j).comp hN
      have heq : (fun w => centeredWindow (A:=A) N w j)=(fun w => w i) := by
        funext w
        dsimp [centeredWindow,j,N]
        congr 1
        have h₂ : -i≤(i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a:=-i))
        omega
      exact heq ▸ hh
    have hid : @Measurable (ℤ → A) (ℤ → A) m MeasurableSpace.pi id := Measurable.of_eval hi
    simpa only [MeasurableSpace.comap_id] using measurable_iff_comap_le.mp hid
  · apply iSup_le
    intro N
    exact measurable_iff_comap_le.mp (measurable_centeredWindow N)

theorem iid_finite_window_approx [Fintype A] [MeasurableSingletonClass A]
    (ν : Measure (ℤ → A)) [IsProbabilityMeasure ν]
    (b : (ℤ → A) → B) (hb : Measurable b) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ,∃ D : (Fin (2*N+1) → A) → B,
      ν.real {w | D (centeredWindow N w)≠b w}<ε :=
  finite_factor_approx ν (fun N => Fin (2*N+1) → A) centeredWindow
    centeredWindow_comap_monotone centeredWindow_generates b hb hε
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators
variable {X Y A : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSingletonClass A]

lemma mass_comp_factor [StandardBorelSpace X] [StandardBorelSpace Y] [Fintype A]
    (μ : Measure X) (ν : Measure Y) (π : X → Y)
    (hπ : MeasurePreserving π μ ν) (p : Y → A) (hp : Measurable p) :
    mass μ (p ∘ π)=mass ν p := by
  funext a
  unfold mass
  exact congrArg ENNReal.toReal (hπ.measure_preimage (hp (measurableSet_singleton a)).nullMeasurableSet)

lemma rate_of_factor [StandardBorelSpace X] [StandardBorelSpace Y] [Fintype A]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (e : X → X) (f : Y → Y) (hf : Measurable f)
    (π : X → Y) (hπ : MeasurePreserving π μ ν) (hcomm : ∀ x,π (e x)=f (π x))
    (p : Y → A) (hp : Measurable p) : rate μ e (p ∘ π)=rate ν f p := by
  have hh (n : ℕ) : obs μ (word e (p ∘ π) n)=obs ν (word f p n) := by
    rw [factor_word e f π hcomm p n]
    unfold obs
    rw [mass_comp_factor μ ν π hπ _ (word_measurable f hf p hp n)]
  unfold rate
  simp only [hh]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

theorem relative_iid_window_graph
    [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : Ergodic e μ) (p : X → A) (_hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0<weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α) (m : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,
      LawClose (μ.map (word e (fun x => (p x,α x)) m))
        ((Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)).map
          (word iidShift (fun y : ℤ → A => (y 0,D (centeredWindow R y))) m)) ε ∧
      rate (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) iidShift
        (fun y : ℤ → A => (y 0,D (centeredWindow R y)))=weightEntropy β := by
  classical
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  let : NullSingletonClass ν := iid_nullSingleton β hβ hβsum hβentropy
  have hcomm : ∀ x,orbitName e p (e x)=iidShift (orbitName e p x) := fun x => orbitName_shift e p x
  have hf : Ergodic iidShift ν := hcode.ergodic_of_ergodic_semiconj he iidShift.measurable hcomm
  have hp0 : (fun x => orbitName e p x 0)=p := by funext x; simp [orbitName,integerIterate]
  obtain ⟨b,hb,hbLaw⟩ := relative_measurable_graph_approx μ ν e he.toMeasurePreserving iidShift hf
    (orbitName e p) hcode hcomm (fun w : ℤ → A => w 0) α (measurable_pi_apply 0) hα m (half_pos hε)
  obtain ⟨R,D,hD⟩ := iid_finite_window_approx ν b hb (show 0<ε/(2*((m : ℝ)+1)) by positivity)
  have hDmeas : Measurable (fun y : ℤ → A => D (centeredWindow R y)) :=
    (measurable_of_countable D).comp (measurable_centeredWindow R)
  have hpaint : ν.real {y | (y 0,b y)≠(y 0,D (centeredWindow R y))}<ε/(2*((m : ℝ)+1)) := by
    convert hD using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext y
    simp only [Set.mem_ofPred_eq,ne_eq,Prod.mk.injEq,true_and]
    exact ne_comm
  have hLaw := word_lawClose_of_repaint ν iidShift hf.toMeasurePreserving
    (fun y : ℤ → A => (y 0,b y)) (fun y : ℤ → A => (y 0,D (centeredWindow R y)))
    ((measurable_pi_apply 0).prodMk hb) ((measurable_pi_apply 0).prodMk hDmeas) m
  refine ⟨R,D,?_,?_⟩
  · have htrans := hbLaw.triangle hLaw
    change LawClose (μ.map (word e (fun x => (p x,α x)) m)) _ _ at htrans
    apply htrans.mono
    have hm0 : (0 : ℝ)≤ m := Nat.cast_nonneg m
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ)<2*((m : ℝ)+1))).mp hpaint
    have hn0 := measureReal_nonneg (μ:=ν) (s:={y | (y 0,b y)≠(y 0,D (centeredWindow R y))})
    nlinarith
  · have hfac := rate_of_factor μ ν e iidShift iidShift.measurable (orbitName e p) hcode hcomm
      (fun y : ℤ → A => (y 0,D (centeredWindow R y))) ((measurable_pi_apply 0).prodMk hDmeas)
    have hu := H.upper ((fun y : ℤ → A => (y 0,D (centeredWindow R y))) ∘ orbitName e p)
      (((measurable_pi_apply 0).prodMk hDmeas).comp hcode.measurable)
    rw [hfac] at hu
    apply le_antisymm hu
    have hl := rate_pair_ge_left ν iidShift hf.toMeasurePreserving (fun y : ℤ → A => y 0)
      (fun y => D (centeredWindow R y)) (measurable_pi_apply 0) hDmeas
    rwa [iid_rate β hβ hβsum] at hl
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

variable (μ : Measure X)

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

lemma conditional_entropy_law_test_uniform [Fintype B] [MeasurableSingletonClass B]
    (μ : Measure X) (p : X → A) (r : X → B)
    (hp : Measurable p) (hr : Measurable r) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (Y : Type u) [MeasurableSpace Y] (ν : Measure Y)
      (q : Y → A) (s : Y → B),Measurable q → Measurable s →
      LawClose (μ.map (fun x => (p x,r x))) (ν.map (fun y => (q y,s y))) δ →
      |StandardMapEntropy.Entropy.cond μ p r-StandardMapEntropy.Entropy.cond ν q s|<ε := by
  obtain ⟨δ₁,hδ₁,h₁⟩ := finite_entropy_continuity (μ.map (fun x => (p x,r x)))
    (show 0<ε/2 by positivity)
  obtain ⟨δ₂,hδ₂,h₂⟩ := finite_entropy_continuity (μ.map r) (show 0<ε/2 by positivity)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,?_⟩
  intro Y mY ν q s hq hs hlaw
  have hm := hlaw.map measurable_snd
  rw [Measure.map_map measurable_snd (hp.prodMk hr),
    Measure.map_map measurable_snd (hq.prodMk hs)] at hm
  have hh₁ := h₁ (ν.map (fun y => (q y,s y))) (hlaw.mono (min_le_left _ _))
  have hh₂ := h₂ (ν.map s) (hm.mono (min_le_right _ _))
  rw [←obs_eq_entropy_map μ (fun x => (p x,r x)) (hp.prodMk hr),
    ←obs_eq_entropy_map ν (fun y => (q y,s y)) (hq.prodMk hs)] at hh₁
  rw [←obs_eq_entropy_map μ r hr,←obs_eq_entropy_map ν s hs] at hh₂
  unfold StandardMapEntropy.Entropy.cond
  have he : obs μ (fun x => (p x,r x))-obs μ r-
      (obs ν (fun y => (q y,s y))-obs ν s)=
      (obs μ (fun x => (p x,r x))-obs ν (fun y => (q y,s y)))-(obs μ r-obs ν s) := by ring
  rw [he]
  exact (abs_sub _ _).trans_lt (by linarith)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {Y A B : Type*} [Nonempty A]

lemma wordPack_apply_coord {A : Type*} (n s : ℕ) (w : Fin (n*s) → A)
    (i : Fin n) (a : Fin s) : wordPack n s w i a=w (finProdFinEquiv (i,a)) := rfl

lemma nameCost_wordPack {A : Type*} (n s : ℕ) (v w : Fin (n*s) → A) :
    nameCost v w=∑ i : Fin n,nameCost (wordPack n s v i) (wordPack n s w i) := by
  rw [nameCost,←Equiv.sum_comp finProdFinEquiv (fun i => symbolCost (v i) (w i)),Fintype.sum_prod_type]
  rfl

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

lemma eventually_conditional_single_test [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℕ in atTop,StandardMapEntropy.Entropy.cond μ p
      (fun x => word f p L (f x)) < rate μ f p+ε := by
  have hh := (entropy_increment_tendsto μ f hf p hp).eventually
    (gt_mem_nhds (show rate μ f p < rate μ f p+ε by linarith))
  simpa only [entropy_increment_eq μ f hf p hp] using hh

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteVectorEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma cond_vector_subadd [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (N : ℕ) (p : X → Fin N → A) (q : X → Fin N → B)
    (hp : Measurable p) (hq : Measurable q) :
    StandardMapEntropy.Entropy.cond μ p q≤∑ i : Fin N,
      StandardMapEntropy.Entropy.cond μ (fun x => p x i) (fun x => q x i) := by
  induction N with
  | zero =>
    have h1 : p=fun _ => (fun i : Fin 0 => i.elim0 : Fin 0 → A) := by
      funext x i
      exact i.elim0
    have h2 : q=fun _ => (fun i : Fin 0 => i.elim0 : Fin 0 → B) := by
      funext x i
      exact i.elim0
    rw [h1,h2]
    simp [StandardMapEntropy.Entropy.cond,obs_const]
  | succ N ih =>
    let eA : (A×(Fin N → A)) ≃ (Fin (N+1) → A) := Fin.consEquiv (fun _ => A)
    let eB : (B×(Fin N → B)) ≃ (Fin (N+1) → B) := Fin.consEquiv (fun _ => B)
    have h1 : p=eA ∘ (fun x => (p x 0,Fin.tail (p x))) := by
      funext x
      exact (Fin.consEquiv (fun _ => A)).apply_symm_apply (p x) |>.symm
    have h2 : q=eB ∘ (fun x => (q x 0,Fin.tail (q x))) := by
      funext x
      exact (Fin.consEquiv (fun _ => B)).apply_symm_apply (q x) |>.symm
    have hp0 := (measurable_pi_apply 0).comp hp
    have hq0 := (measurable_pi_apply 0).comp hq
    have hpt : Measurable (fun x => Fin.tail (p x)) := Measurable.of_eval
      (fun i => (measurable_pi_apply i.succ).comp hp)
    have hqt : Measurable (fun x => Fin.tail (q x)) := Measurable.of_eval
      (fun i => (measurable_pi_apply i.succ).comp hq)
    have hb := cond_pair_subadd μ (fun x => p x 0) (fun x => q x 0)
      (fun x => Fin.tail (p x)) (fun x => Fin.tail (q x)) hp0 hq0 hpt hqt
    have hi := ih (fun x => Fin.tail (p x)) (fun x => Fin.tail (q x)) hpt hqt
    rw [h1,h2,cond_equiv_left,cond_equiv_right]
    rw [Fin.sum_univ_succ]
    exact hb.trans (add_le_add (le_refl _) hi)

lemma shannon_productVector [MeasurableSpace A] [MeasurableSingletonClass A]
    (N : ℕ) (p : Fin N → A → ℝ) (hs : ∀ i,∑ a,p i a=1) :
    shannon (fun w : Fin N → A => ∏ i,p i (w i))=∑ i,shannon (p i) := by
  induction N with
  | zero => simp [shannon]
  | succ N ih =>
    let e : (A×(Fin N → A)) ≃ (Fin (N+1) → A) := Fin.consEquiv (fun _ => A)
    have he : shannon (fun w : Fin (N+1) → A => ∏ i,p i (w i))=
        shannon (fun aw : A×(Fin N → A) => p 0 aw.1*∏ i,p i.succ (aw.2 i)) := by
      unfold shannon
      rw [←Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro aw _
      congr 1
      simp [e,Fin.prod_univ_succ]
    have hm : (∑ w : Fin N → A,∏ i,p i.succ (w i))=1 :=
      productWeights_sum (fun i : Fin N => p i.succ) (fun i => hs i.succ)
    rw [he,shannon_product_weights (p 0) (fun w : Fin N → A => ∏ i,p i.succ (w i))
      (hs 0) hm,ih _ (fun i => hs i.succ),Fin.sum_univ_succ]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X)

lemma mass_factor_sum [MeasurableSpace A] [MeasurableSingletonClass A]
    [IsProbabilityMeasure μ] [DecidableEq C] (p : X → A) (hp : Measurable p) (c : A → C) (z : C) :
    mass μ (c ∘ p) z=∑ a,if c a=z then mass μ p a else 0 := by
  classical
  have h := sum_mass_factor_mul μ p hp c (fun v => if v=z then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h.symm

lemma cond_eq_channel_average [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [IsProbabilityMeasure μ]
    (p : X → A) (q : X → B)
    (K : A → B → ℝ) (hK : ∀ a,∑ b,K a b=1)
    (hjoint : ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=mass μ p a*K a b) :
    StandardMapEntropy.Entropy.cond μ q p=∑ a,mass μ p a*shannon (K a) := by
  have hs (a : A) : (∑ b,Real.negMulLog (mass μ p a*K a b))=
      mass μ p a*shannon (K a)+Real.negMulLog (mass μ p a) := by
    change shannon (fun b => mass μ p a*K a b)=_
    simpa only [hK,one_mul] using shannon_scale (K a) (mass μ p a)
  rw [StandardMapEntropy.Entropy.cond,obs_pair_swap μ q p]
  simp only [obs,shannon,Fintype.sum_prod_type,hjoint]
  change (∑ a,∑ b,Real.negMulLog (mass μ p a*K a b))-
    (∑ a,Real.negMulLog (mass μ p a))=_
  simp only [hs,Finset.sum_add_distrib,shannon]
  ring

lemma product_channel_coordinate [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [IsProbabilityMeasure μ]
    (N : ℕ) (p : X → Fin N → A) (q : X → Fin N → B)
    (hp : Measurable p) (hq : Measurable q) (K : Fin N → A → B → ℝ)
    (hK : ∀ i a,∑ b,K i a b=1)
    (hjoint : ∀ v w,mass μ (fun x => (p x,q x)) (v,w)=
      mass μ p v*∏ i,K i (v i) (w i)) (i : Fin N) (a : A) (b : B) :
    mass μ (fun x => (p x i,q x i)) (a,b)=mass μ (fun x => p x i) a*K i a b := by
  classical
  have he := mass_factor_sum μ (fun x => (p x,q x)) (hp.prodMk hq)
    (fun vw : (Fin N → A)×(Fin N → B) => (vw.1 i,vw.2 i)) (a,b)
  change mass μ (fun x => (p x i,q x i)) (a,b)=_ at he
  rw [he]
  simp only [Fintype.sum_prod_type,hjoint,Prod.mk.injEq]
  have hr (v : Fin N → A) :
      (∑ w : Fin N → B,if v i=a ∧ w i=b then mass μ p v*∏ j,K j (v j) (w j) else 0)=
      (if v i=a then mass μ p v else 0)*K i a b := by
    by_cases hv : v i=a
    · simp only [hv,true_and,ite_true]
      have hec := expectation_coordinate (fun j => K j (v j)) (fun j => hK j (v j)) i
        (fun z => if z=b then 1 else 0)
      simp only [finiteExpectation,productWeights,mul_ite,mul_one,mul_zero,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hec
      calc
        _ = mass μ p v*(∑ w : Fin N → B,if w i=b then ∏ j,K j (v j) (w j) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          split_ifs <;> simp
        _ = _ := by rw [hec,hv]
    · simp only [hv,false_and,ite_false,Finset.sum_const_zero,zero_mul]
  simp only [hr,←Finset.sum_mul]
  have hm := mass_factor_sum μ p hp (fun v : Fin N → A => v i) a
  exact congrArg (fun t : ℝ => t*K i a b) hm.symm

theorem product_channel_entropy_lower [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [IsProbabilityMeasure μ]
    (N : ℕ) (p : X → Fin N → A) (q : X → Fin N → B)
    (hp : Measurable p) (hq : Measurable q) (K : Fin N → A → B → ℝ)
    (hK : ∀ i a,∑ b,K i a b=1)
    (hjoint : ∀ v w,mass μ (fun x => (p x,q x)) (v,w)=
      mass μ p v*∏ i,K i (v i) (w i)) :
    obs μ p+(∑ i : Fin N,(obs μ (fun x => q x i)-obs μ (fun x => p x i)))≤obs μ q := by
  have hfull := cond_eq_channel_average μ p q (fun v w => ∏ i,K i (v i) (w i))
    (fun v => productWeights_sum (fun i => K i (v i)) (fun i => hK i (v i))) hjoint
  have hr : StandardMapEntropy.Entropy.cond μ q p=∑ i : Fin N,
      StandardMapEntropy.Entropy.cond μ (fun x => q x i) (fun x => p x i) := by
    rw [hfull]
    simp_rw [shannon_productVector _ _ (fun i => hK i _),Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [cond_eq_channel_average μ (fun x => p x i) (fun x => q x i) (K i) (hK i)
      (product_channel_coordinate μ N p q hp hq K hK hjoint i)]
    exact sum_mass_factor_mul μ p hp (fun v : Fin N → A => v i) (fun a => shannon (K i a))
  have hsub := cond_vector_subadd μ N p q hp hq
  have hid : obs μ p-obs μ q=StandardMapEntropy.Entropy.cond μ p q-
      StandardMapEntropy.Entropy.cond μ q p := by
    rw [StandardMapEntropy.Entropy.cond,StandardMapEntropy.Entropy.cond,obs_pair_swap μ q p]
    ring
  have hi (i : Fin N) : obs μ (fun x => q x i)-obs μ (fun x => p x i)=
      StandardMapEntropy.Entropy.cond μ (fun x => q x i) (fun x => p x i)-
        StandardMapEntropy.Entropy.cond μ (fun x => p x i) (fun x => q x i) := by
    unfold StandardMapEntropy.Entropy.cond
    rw [obs_pair_swap μ (fun x => q x i) (fun x => p x i)]
    ring
  simp only [hi,Finset.sum_sub_distrib]
  rw [hr] at hid
  linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSpace B] [Fintype B]

lemma mass_finiteWeightLaw_id [MeasurableSingletonClass A] (P : A → ℝ) (hP : ∀ a,0≤P a) (a : A) :
    mass (finiteWeightLaw P) id a=P a := by
  simp only [mass,preimage_id,finiteWeightLaw_singleton,ENNReal.toReal_ofReal (hP a)]

lemma finiteChannelLaw_probability [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (N : ℕ) (P : (Fin N → A) → ℝ)
    (hP : ∀ v,0≤P v) (hPs : ∑ v,P v=1) (K : Fin N → A → B → ℝ)
    (hK : ∀ i a b,0≤K i a b) (hKs : ∀ i a,∑ b,K i a b=1) :
    IsProbabilityMeasure (finiteChannelLaw N P K) := by
  apply finiteWeightLaw_probability
  · intro vw
    exact mul_nonneg (hP _) (Finset.prod_nonneg (fun i _ => hK _ _ _))
  · simp only [Fintype.sum_prod_type,←Finset.mul_sum]
    have he (v : Fin N → A) : (∑ w : Fin N → B,∏ i,K i (v i) (w i))=1 :=
      productWeights_sum (fun i => K i (v i)) (fun i => hKs i (v i))
    simp only [he,mul_one,hPs]

lemma finiteChannelLaw_pair_mass [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (N : ℕ) (P : (Fin N → A) → ℝ)
    (hP : ∀ v,0≤P v) (K : Fin N → A → B → ℝ) (hK : ∀ i a b,0≤K i a b)
    (v : Fin N → A) (w : Fin N → B) :
    mass (finiteChannelLaw N P K) (fun vw => (vw.1,vw.2)) (v,w)=P v*∏ i,K i (v i) (w i) := by
  exact mass_finiteWeightLaw_id _ (fun vw => mul_nonneg (hP _)
    (Finset.prod_nonneg (fun i _ => hK _ _ _))) (v,w)

lemma finiteChannelLaw_input_mass [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (N : ℕ) (P : (Fin N → A) → ℝ)
    (hP : ∀ v,0≤P v) (K : Fin N → A → B → ℝ) (hK : ∀ i a b,0≤K i a b)
    (hKs : ∀ i a,∑ b,K i a b=1) (v : Fin N → A) :
    mass (finiteChannelLaw N P K) Prod.fst v=P v := by
  have : IsFiniteMeasure (finiteChannelLaw N P K) := finiteWeightLaw_finite _
  rw [mass_joint_row _ Prod.fst Prod.snd measurable_fst measurable_snd]
  simp only [finiteChannelLaw_pair_mass N P hP K hK,←Finset.mul_sum]
  have he : (∑ w : Fin N → B,∏ i,K i (v i) (w i))=1 :=
    productWeights_sum (fun i => K i (v i)) (fun i => hKs i (v i))
  rw [he,mul_one]

theorem finiteChannelLaw_entropy [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (N : ℕ) (P : (Fin N → A) → ℝ)
    (hP : ∀ v,0≤P v) (hPs : ∑ v,P v=1) (K : Fin N → A → B → ℝ)
    (hK : ∀ i a b,0≤K i a b) (hKs : ∀ i a,∑ b,K i a b=1) :
    shannon P+(∑ i : Fin N,(obs (finiteChannelLaw N P K) (fun vw => vw.2 i)-
      obs (finiteChannelLaw N P K) (fun vw => vw.1 i)))≤
      obs (finiteChannelLaw N P K) Prod.snd := by
  have := finiteChannelLaw_probability N P hP hPs K hK hKs
  have hh := product_channel_entropy_lower (finiteChannelLaw N P K) N Prod.fst Prod.snd
    measurable_fst measurable_snd K hKs (by
      intro v w
      rw [finiteChannelLaw_pair_mass N P hP K hK,finiteChannelLaw_input_mass N P hP K hK hKs])
  have he : obs (finiteChannelLaw N P K) Prod.fst=shannon P := by
    unfold obs
    congr 1
    funext v
    exact finiteChannelLaw_input_mass N P hP K hK hKs v
  rw [he] at hh
  exact hh
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype A] [Fintype B]

lemma channel_joint_l1 [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (K : A → B → ℝ) (hK : ∀ a b,0≤K a b) (hKs : ∀ a,∑ b,K a b=1)
    (hμ : ∀ a b,mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*K a b)
    (hν : ∀ a b,mass ν (fun x => (q x,s x)) (a,b)=mass ν q a*K a b) :
    (∑ ab : A×B,|mass μ (fun x => (p x,r x)) ab-mass ν (fun x => (q x,s x)) ab|)=
      ∑ a,|mass μ p a-mass ν q a| := by
  simp only [Fintype.sum_prod_type,hμ,hν,←sub_mul,abs_mul,abs_of_nonneg (hK _ _),
    ←Finset.mul_sum,hKs,mul_one]

lemma channel_joint_lawClose [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (K : A → B → ℝ) (hK : ∀ a b,0≤K a b) (hKs : ∀ a,∑ b,K a b=1)
    (hμ : ∀ a b,mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*K a b)
    (hν : ∀ a b,mass ν (fun x => (q x,s x)) (a,b)=mass ν q a*K a b)
    {δ : ℝ} (hlaw : LawClose (μ.map p) (ν.map q) δ) :
    LawClose (μ.map (fun x => (p x,r x))) (ν.map (fun x => (q x,s x))) (2*δ) := by
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (fun x => (p x,r x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map (fun x => (q x,s x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hmass (a : A) : (μ.map p).real {a}=mass μ p a :=
    map_measureReal_apply hp (measurableSet_singleton a)
  have hmass' (a : A) : (ν.map q).real {a}=mass ν q a :=
    map_measureReal_apply hq (measurableSet_singleton a)
  have hj (ab : A×B) : (μ.map (fun x => (p x,r x))).real {ab}=
      mass μ (fun x => (p x,r x)) ab := map_measureReal_apply (hp.prodMk hr) (measurableSet_singleton ab)
  have hj' (ab : A×B) : (ν.map (fun x => (q x,s x))).real {ab}=
      mass ν (fun x => (q x,s x)) ab := map_measureReal_apply (hq.prodMk hs) (measurableSet_singleton ab)
  have hh := finite_l1_le_two_of_lawClose _ _ hlaw
  simp only [hmass,hmass'] at hh
  apply lawClose_of_finite_l1
  simp only [hj,hj']
  rw [channel_joint_l1 μ ν p r q s K hK hKs hμ hν]
  exact hh

lemma channel_output_lawClose [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (K : A → B → ℝ) (hK : ∀ a b,0≤K a b) (hKs : ∀ a,∑ b,K a b=1)
    (hμ : ∀ a b,mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*K a b)
    (hν : ∀ a b,mass ν (fun x => (q x,s x)) (a,b)=mass ν q a*K a b)
    {δ : ℝ} (hlaw : LawClose (μ.map p) (ν.map q) δ) :
    LawClose (μ.map r) (ν.map s) (2*δ) := by
  have hh := (channel_joint_lawClose μ ν p r q s hp hr hq hs K hK hKs hμ hν hlaw).map measurable_snd
  simpa only [Measure.map_map measurable_snd (hp.prodMk hr),
    Measure.map_map measurable_snd (hq.prodMk hs),Function.comp_def] using hh

lemma channel_cost_stability [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (K : A → B → ℝ) (hK : ∀ a b,0≤K a b) (hKs : ∀ a,∑ b,K a b=1)
    (hμ : ∀ a b,mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*K a b)
    (hν : ∀ a b,mass ν (fun x => (q x,s x)) (a,b)=mass ν q a*K a b)
    {δ M : ℝ} (hM : 0≤M) (hlaw : LawClose (μ.map p) (ν.map q) δ)
    (d : A → B → ℝ) (hd : ∀ a b,|d a b|≤M) :
    (MatrixCoupling.observations ν q s hq hs).cost d≤
      (MatrixCoupling.observations μ p r hp hr).cost d+2*δ*M := by
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hl1 := finite_l1_le_two_of_lawClose _ _ hlaw
  have he (a : A) : (μ.map p).real {a}=mass μ p a := map_measureReal_apply hp (measurableSet_singleton a)
  have he' (a : A) : (ν.map q).real {a}=mass ν q a := map_measureReal_apply hq (measurableSet_singleton a)
  simp only [he,he'] at hl1
  have hdiff : (∑ ab : A×B,(mass ν (fun x => (q x,s x)) ab-mass μ (fun x => (p x,r x)) ab)*d ab.1 ab.2)≤2*δ*M := by
    calc
      _≤∑ ab : A×B,|mass μ (fun x => (p x,r x)) ab-mass ν (fun x => (q x,s x)) ab| * M := by
        apply Finset.sum_le_sum
        intro ab _
        calc
          _≤|(mass ν (fun x => (q x,s x)) ab-mass μ (fun x => (p x,r x)) ab)*d ab.1 ab.2| := le_abs_self _
          _≤_ := by rw [abs_mul,abs_sub_comm]; exact mul_le_mul_of_nonneg_left (hd _ _) (abs_nonneg _)
      _=(∑ a,|mass μ p a-mass ν q a|)*M := by
        rw [←Finset.sum_mul,channel_joint_l1 μ ν p r q s K hK hKs hμ hν]
      _≤_ := mul_le_mul_of_nonneg_right hl1 hM
  simp only [sub_mul,Finset.sum_sub_distrib,Fintype.sum_prod_type] at hdiff
  change (∑ a,∑ b,mass ν (fun x => (q x,s x)) (a,b)*d a b)≤
    (∑ a,∑ b,mass μ (fun x => (p x,r x)) (a,b)*d a b)+2*δ*M
  linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

lemma recodingKernel_nonneg (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r) (a : A) (b : B) :
    0 ≤ recodingKernel μ p r hp hr a b := by
  classical
  exact (MatrixCoupling.observations μ r p hr hp).conditionalAssignment_nonneg a b

lemma recodingKernel_sum (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r) (a : A) :
    ∑ b,recodingKernel μ p r hp hr a b=1 := by
  classical
  exact (MatrixCoupling.observations μ r p hr hp).conditionalAssignment_sum a

lemma recodingKernel_joint (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r) (a : A) (b : B) :
    mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*recodingKernel μ p r hp hr a b := by
  classical
  have hh := (MatrixCoupling.observations μ r p hr hp).mul_conditionalAssignment b a
  exact (mass_joint_swap μ p r a b).trans hh.symm

lemma recodingLaw_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q) :
    IsProbabilityMeasure (recodingLaw μ p r hp hr ν N Q) := by
  apply finiteChannelLaw_probability N (mass ν Q) (mass_nonneg _ _) (by simpa using mass_sum ν Q hQ)
  · intro i
    exact recodingKernel_nonneg μ p r hp hr
  · intro i
    exact recodingKernel_sum μ p r hp hr

lemma recodingLaw_input_mass (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (v : Fin N → A) :
    mass (recodingLaw μ p r hp hr ν N Q) Prod.fst v=mass ν Q v :=
  finiteChannelLaw_input_mass N (mass ν Q) (mass_nonneg _ _)
    (fun _ => recodingKernel μ p r hp hr) (fun _ => recodingKernel_nonneg μ p r hp hr)
    (fun _ => recodingKernel_sum μ p r hp hr) v

lemma recodingLaw_input_coordinate (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    (i : Fin N) (a : A) :
    mass (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.1 i) a=mass ν (fun y => Q y i) a := by
  classical
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  have hh := mass_factor_sum (recodingLaw μ p r hp hr ν N Q) Prod.fst measurable_fst
    (fun v : Fin N → A => v i) a
  have hh' := mass_factor_sum ν Q hQ (fun v : Fin N → A => v i) a
  simp only [recodingLaw_input_mass] at hh
  exact hh.trans hh'.symm

lemma recodingLaw_joint_coordinate (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    (i : Fin N) (a : A) (b : B) :
    mass (recodingLaw μ p r hp hr ν N Q) (fun vw => (vw.1 i,vw.2 i)) (a,b)=
      mass (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.1 i) a*recodingKernel μ p r hp hr a b := by
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  apply product_channel_coordinate (recodingLaw μ p r hp hr ν N Q) N Prod.fst Prod.snd
    measurable_fst measurable_snd (fun _ => recodingKernel μ p r hp hr)
    (fun _ => recodingKernel_sum μ p r hp hr) _ i a b
  intro v w
  rw [recodingLaw_input_mass]
  exact finiteChannelLaw_pair_mass N (mass ν Q) (mass_nonneg _ _)
    (fun _ => recodingKernel μ p r hp hr) (fun _ => recodingKernel_nonneg μ p r hp hr) v w

lemma recodingLaw_input_law (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    (i : Fin N) :
    (recodingLaw μ p r hp hr ν N Q).map (fun vw => vw.1 i)=ν.map (fun y => Q y i) := by
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  apply Measure.ext_of_singleton
  intro a
  have hl : Measurable (fun vw : (Fin N → A)×(Fin N → B) => vw.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hr' : Measurable (fun y => Q y i) := (measurable_pi_apply i).comp hQ
  rw [Measure.map_apply hl (measurableSet_singleton a),Measure.map_apply hr' (measurableSet_singleton a)]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact recodingLaw_input_coordinate μ p r hp hr ν N Q hQ i a

lemma recodingLaw_output_lawClose (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    (i : Fin N) {δ : ℝ} (hlaw : LawClose (μ.map p) (ν.map (fun y => Q y i)) δ) :
    LawClose (μ.map r) ((recodingLaw μ p r hp hr ν N Q).map (fun vw => vw.2 i)) (2*δ) := by
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  apply channel_output_lawClose μ (recodingLaw μ p r hp hr ν N Q) p r
    (fun vw => vw.1 i) (fun vw => vw.2 i) hp hr
    ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd)
    (recodingKernel μ p r hp hr) (recodingKernel_nonneg μ p r hp hr)
    (recodingKernel_sum μ p r hp hr) (recodingKernel_joint μ p r hp hr)
    (recodingLaw_joint_coordinate μ p r hp hr ν N Q hQ i)
  rw [recodingLaw_input_law μ p r hp hr ν N Q hQ i]
  exact hlaw
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
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma observations_vector_cost [Nonempty B] (μ : Measure X) [IsProbabilityMeasure μ]
    (N : ℕ) (P : X → Fin N → A) (Q : X → Fin N → B) (hP : Measurable P) (hQ : Measurable Q)
    (d : A → B → ℝ) :
    (MatrixCoupling.observations μ P Q hP hQ).cost (fun v w => ∑ i,d (v i) (w i))=
      ∑ i : Fin N,(MatrixCoupling.observations μ (fun x => P x i) (fun x => Q x i)
        ((measurable_pi_apply i).comp hP) ((measurable_pi_apply i).comp hQ)).cost d := by
  simp only [MatrixCoupling.observations_cost]
  exact integral_finsetSum _ (fun i _ => integrable_finite_observation μ
    (fun x => (P x i,Q x i)) (((measurable_pi_apply i).comp hP).prodMk
      ((measurable_pi_apply i).comp hQ)) (fun ab => d ab.1 ab.2))

lemma recodingLaw_entropy_lower [Nonempty B] (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    {η : ℝ}
    (hin : ∀ i : Fin N,obs ν (fun y => Q y i)≤obs μ p+η)
    (hout : ∀ i : Fin N,obs μ r-η≤obs (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.2 i)) :
    obs ν Q+(N : ℝ)*(obs μ r-obs μ p-2*η)≤
      obs (recodingLaw μ p r hp hr ν N Q) Prod.snd := by
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  have hh := finiteChannelLaw_entropy N (mass ν Q) (mass_nonneg _ _)
    (by simpa using mass_sum ν Q hQ) (fun _ => recodingKernel μ p r hp hr)
    (fun _ => recodingKernel_nonneg μ p r hp hr) (fun _ => recodingKernel_sum μ p r hp hr)
  change obs ν Q+(∑ i : Fin N,(obs (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.2 i)-
    obs (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.1 i)))≤_ at hh
  apply le_trans _ hh
  apply add_le_add (le_refl _)
  calc
    _=∑ _i : Fin N,(obs μ r-obs μ p-2*η) := by simp; ring
    _≤_ := by
      apply Finset.sum_le_sum
      intro i _
      have he : obs (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.1 i)=obs ν (fun y => Q y i) := by
        unfold obs
        congr 1
        funext a
        exact recodingLaw_input_coordinate μ p r hp hr ν N Q hQ i a
      rw [he]
      linarith [hin i,hout i]

lemma recodingLaw_transport_cost [Nonempty B] (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    {δ M : ℝ} (hM : 0≤M) (hlaw : ∀ i : Fin N,LawClose (μ.map p) (ν.map (fun y => Q y i)) δ)
    (d : A → B → ℝ) (hd : ∀ a b,|d a b|≤M) :
    ∃ R : MatrixCoupling (mass ν Q) (mass (recodingLaw μ p r hp hr ν N Q) Prod.snd),
      R.cost (fun v w => ∑ i,d (v i) (w i))≤
        (N : ℝ)*((MatrixCoupling.observations μ p r hp hr).cost d+2*δ*M) := by
  let ξ := recodingLaw μ p r hp hr ν N Q
  have : IsProbabilityMeasure ξ := recodingLaw_probability μ p r hp hr ν N Q hQ
  let S := MatrixCoupling.observations ξ Prod.fst Prod.snd measurable_fst measurable_snd
  let R : MatrixCoupling (mass ν Q) (mass ξ Prod.snd) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun v => (S.row v).trans (recodingLaw_input_mass μ p r hp hr ν N Q v)
    col := S.col }
  refine ⟨R,?_⟩
  change S.cost (fun v w => ∑ i,d (v i) (w i))≤_
  rw [observations_vector_cost]
  calc
    _≤∑ _i : Fin N,((MatrixCoupling.observations μ p r hp hr).cost d+2*δ*M) := by
      apply Finset.sum_le_sum
      intro i _
      apply channel_cost_stability μ ξ p r (fun vw => vw.1 i) (fun vw => vw.2 i) hp hr
        ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd)
        (recodingKernel μ p r hp hr) (recodingKernel_nonneg μ p r hp hr)
        (recodingKernel_sum μ p r hp hr) (recodingKernel_joint μ p r hp hr)
        (recodingLaw_joint_coordinate μ p r hp hr ν N Q hQ i) hM _ d hd
      change LawClose (μ.map p) ((recodingLaw μ p r hp hr ν N Q).map (fun vw => vw.1 i)) δ
      rw [recodingLaw_input_law μ p r hp hr ν N Q hQ i]
      exact hlaw i
    _=_ := by simp; ring
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*}

lemma nestedPack_word [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (f : X → X) (p : X → A) (M J s : ℕ) (x : X) :
    nestedPack M J s (word f p ((M*J)*s) x)=
      word (f^[J*s]) (word (f^[s]) (word f p s) J) M x := by
  funext I j a
  simp only [nestedPack,Equiv.trans_apply,wordPack_apply_coord,word]
  change p (f^[a.val+s*(j.val+J*I.val)] x)=_
  simp only [←Function.iterate_mul,←Function.iterate_add_apply]
  congr 2
  ring

lemma obs_nestedPack_word [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (p : X → A) (M J s : ℕ) :
    obs μ (word (f^[J*s]) (word (f^[s]) (word f p s) J) M)=
      obs μ (word f p ((M*J)*s)) := by
  simpa only [Function.comp_def,nestedPack_word] using
    obs_equiv μ (word f p ((M*J)*s)) (nestedPack M J s)

lemma obs_nestedOutput [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A) :
    obs ν (nestedOutput M J s V)=obs ν V :=
  obs_equiv ν V (nestedPack M J s).symm

lemma fineWordCost_sum [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (J s : ℕ) (v w : Fin J → Fin s → A) :
    fineWordCost J s v w=∑ j,nameCost (v j) (w j) := by
  simp only [fineWordCost,nameCost_wordPack,Equiv.apply_symm_apply]

lemma nameCost_nestedPack [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (M J s : ℕ) (v w : Fin ((M*J)*s) → A) :
    nameCost v w=∑ I : Fin M,fineWordCost J s (nestedPack M J s v I) (nestedPack M J s w I) := by
  rw [nameCost_wordPack,←Equiv.sum_comp finProdFinEquiv (fun i : Fin (M*J) =>
    nameCost (wordPack (M*J) s v i) (wordPack (M*J) s w i)),Fintype.sum_prod_type]
  simp only [fineWordCost_sum,nestedPack,Equiv.trans_apply,wordPack_apply_coord]

lemma observations_word_cost [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p r : X → A) (hp : Measurable p) (hr : Measurable r)
    (n : ℕ) :
    (MatrixCoupling.observations μ (word f p n) (word f r n)
      (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable r hr n)).cost nameCost=
      (n : ℝ)*μ.real {x | p x≠r x} := by
  rw [show nameCost=(fun v w : Fin n → A => ∑ i,symbolCost (v i) (w i)) from rfl,
    observations_vector_cost]
  have hi (i : Fin n) : (MatrixCoupling.observations μ (fun x => word f p n x i)
      (fun x => word f r n x i) ((measurable_pi_apply i).comp (word_measurable f hf.measurable p hp n))
      ((measurable_pi_apply i).comp (word_measurable f hf.measurable r hr n))).cost symbolCost=
      μ.real {x | p x≠r x} := by
    rw [MatrixCoupling.observations_cost]
    rw [finite_symbolCost_integral μ (fun x => word f p n x i) (fun x => word f r n x i)
      ((measurable_pi_apply i).comp (word_measurable f hf.measurable p hp n))
      ((measurable_pi_apply i).comp (word_measurable f hf.measurable r hr n))]
    change μ.real ((f^[i.val]) ⁻¹' {x | p x≠r x})=μ.real {x | p x≠r x}
    exact congrArg ENNReal.toReal ((hf.iterate i.val).measure_preimage
      (measurableSet_eq_fun hp hr).compl.nullMeasurableSet)
  simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma observations_fineWordCost [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p r : X → A) (hp : Measurable p) (hr : Measurable r)
    (J s : ℕ) :
    (MatrixCoupling.observations μ (word (f^[s]) (word f p s) J) (word (f^[s]) (word f r s) J)
      (word_measurable _ (hf.measurable.iterate _) _ (word_measurable f hf.measurable p hp s) J)
      (word_measurable _ (hf.measurable.iterate _) _ (word_measurable f hf.measurable r hr s) J)).cost
      (fineWordCost J s)=(J*s : ℕ)*μ.real {x | p x≠r x} := by
  rw [MatrixCoupling.observations_cost]
  have he (x : X) : fineWordCost J s (word (f^[s]) (word f p s) J x)
      (word (f^[s]) (word f r s) J x)=nameCost (word f p (J*s) x) (word f r (J*s) x) := by
    simp only [fineWordCost,←wordPack_apply,Equiv.symm_apply_apply]
  simp_rw [he]
  rw [←MatrixCoupling.observations_cost μ _ _
    (word_measurable f hf.measurable p hp _) (word_measurable f hf.measurable r hr _)]
  exact observations_word_cost μ f hf p r hp hr (J*s)

lemma fineWordCost_abs_le [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (J s : ℕ) (v w : Fin J → Fin s → A) :
    |fineWordCost J s v w|≤(J*s : ℕ) := by
  unfold fineWordCost
  rw [abs_of_nonneg (nameCost_nonneg _ _)]
  exact nameCost_le_card _ _

lemma obs_word_rate_lower [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p) (n : ℕ) :
    (n : ℝ)*rate μ f p≤obs μ (word f p n) := by
  by_cases hn : n=0
  · subst n; simpa using obs_nonneg μ (word f p 0) (word_measurable f hf.measurable p hp 0)
  · have hh := (le_div_iff₀ (show (0 : ℝ)<n by exact_mod_cast Nat.pos_of_ne_zero hn)).mp
      (rate_le_div μ f hf p hp hn)
    nlinarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
lemma recoding_entropy_scalar {n j s a δ hp hr P S Q O : ℝ}
    (hn : 0≤n) (hδ : s*δ≤a^2)
    (hQ : n*j*s*(hp-δ)≤Q) (hP : P≤j*s*hp+j*a^2) (hS : j*s*hr≤S)
    (hO : Q+n*(S-P-2)≤O) (hj : 0≤j) :
    n*j*s*hr-2*(n*j)*a^2-2*n≤O := by
  have h₁ := mul_le_mul_of_nonneg_left hP hn
  have h₂ := mul_le_mul_of_nonneg_left hS hn
  have h₃ := mul_le_mul_of_nonneg_left hδ (mul_nonneg hn hj)
  nlinarith only [hQ,h₁,h₂,h₃,hO]

end HyperbolicCoding
end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

lemma nestedOutput_word [StandardBorelSpace X] (f : X → X) (p : X → A) (n J s : ℕ) :
    nestedOutput n J s (word (f^[J*s]) (word (f^[s]) (word f p s) J) n)=
      word f p ((n*J)*s) := by
  funext x
  change (nestedPack n J s).symm (word (f^[J*s]) (word (f^[s]) (word f p s) J) n x)=_
  rw [←nestedPack_word,Equiv.symm_apply_apply]

lemma recoding_nested_entropy [StandardBorelSpace X] [StandardBorelSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (n J s : ℕ)
    (P S : X → Fin J → Fin s → A) (hP : Measurable P) (hS : Measurable S)
    (Q : Y → Fin n → Fin J → Fin s → A) (hQ : Measurable Q)
    {a δ hp hr : ℝ} (hδ : (s : ℝ)*δ≤a^2)
    (hQlo : ((n*J)*s : ℕ)*(hp-δ)≤obs ν Q)
    (hPhi : obs μ P≤(J*s : ℕ)*hp+(J : ℝ)*a^2)
    (hSlo : (J*s : ℕ)*hr≤obs μ S)
    (hin : ∀ i : Fin n,obs ν (fun y => Q y i)≤obs μ P+1)
    (hout : ∀ i : Fin n,obs μ S-1≤obs (recodingLaw μ P S hP hS ν n Q) (fun vw => vw.2 i)) :
    ((n*J)*s : ℕ)*hr-2*(n*J : ℕ)*a^2-2*(n : ℝ)≤
      obs (recodingLaw μ P S hP hS ν n Q) (nestedOutput n J s Prod.snd) := by
  let : StandardBorelSpace (Fin n → Fin J → Fin s → A) := inferInstance
  have := recodingLaw_probability μ P S hP hS ν n Q hQ
  rw [obs_nestedOutput]
  have hh := recodingLaw_entropy_lower μ P S hP hS ν n Q hQ hin hout
  push_cast at hQlo hPhi hSlo ⊢
  exact recoding_entropy_scalar (Nat.cast_nonneg n) hδ hQlo hPhi hSlo (by simpa only [mul_one] using hh)
    (Nat.cast_nonneg J)

lemma nested_reindex_transport [StandardBorelSpace Y]
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    (ν : Measure Y) [IsProbabilityMeasure ν] (ξ : Measure Z) [IsProbabilityMeasure ξ]
    (n J s : ℕ) (Q : Y → Fin n → Fin J → Fin s → A) (V : Z → Fin n → Fin J → Fin s → A)
    (R : MatrixCoupling (mass ν Q) (mass ξ V)) :
    ∃ R' : MatrixCoupling (mass ν (nestedOutput n J s Q)) (mass ξ (nestedOutput n J s V)),
      R'.cost nameCost=R.cost (fun v w => ∑ i,fineWordCost J s (v i) (w i)) := by
  let E := nestedPack (A:=A) n J s
  let U := R.reindex E E
  have hrow (w : Fin ((n*J)*s) → A) : mass ν Q (E w)=mass ν (nestedOutput n J s Q) w :=
    (mass_equiv_inverse_finite ν Q E.symm w).symm
  have hcol (w : Fin ((n*J)*s) → A) : mass ξ V (E w)=mass ξ (nestedOutput n J s V) w :=
    (mass_equiv_inverse_finite ξ V E.symm w).symm
  let R' : MatrixCoupling (mass ν (nestedOutput n J s Q)) (mass ξ (nestedOutput n J s V)) := {
    weight := U.weight
    nonneg := U.nonneg
    row := fun w => (U.row w).trans (hrow w)
    col := fun w => (U.col w).trans (hcol w) }
  refine ⟨R',?_⟩
  change U.cost nameCost=_
  have hc : (nameCost : (Fin ((n*J)*s) → A) → (Fin ((n*J)*s) → A) → ℝ)=
      fun v w => ∑ i,fineWordCost J s (E v i) (E w i) :=
    funext (fun v => funext (fun w => nameCost_nestedPack n J s v w))
  rw [hc]
  exact MatrixCoupling.reindex_cost R E E (fun v w => ∑ i,fineWordCost J s (v i) (w i))

lemma recoding_nested_transport [StandardBorelSpace X] [StandardBorelSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (n J s : ℕ)
    (P S : X → Fin J → Fin s → A) (hP : Measurable P) (hS : Measurable S)
    (Q : Y → Fin n → Fin J → Fin s → A) (hQ : Measurable Q)
    {δ : ℝ} (hb : ∀ i : Fin n,LawClose (μ.map P) (ν.map (fun y => Q y i)) δ) :
    ∃ R : MatrixCoupling (mass ν (nestedOutput n J s Q))
      (mass (recodingLaw μ P S hP hS ν n Q) (nestedOutput n J s Prod.snd)),
      R.cost nameCost≤(n : ℝ)*((MatrixCoupling.observations μ P S hP hS).cost
        (fineWordCost J s)+2*δ*(J*s : ℕ)) := by
  let : StandardBorelSpace (Fin n → Fin J → Fin s → A) := inferInstance
  let ξ := recodingLaw μ P S hP hS ν n Q
  have : IsProbabilityMeasure ξ := recodingLaw_probability μ P S hP hS ν n Q hQ
  obtain ⟨R,hR⟩ := recodingLaw_transport_cost μ P S hP hS ν n Q hQ
    (Nat.cast_nonneg (J*s)) hb (fineWordCost J s) (fineWordCost_abs_le J s)
  obtain ⟨R',hR'⟩ := nested_reindex_transport ν ξ n J s Q Prod.snd R
  exact ⟨R',hR'.trans_le hR⟩

end HyperbolicCoding

end
section
universe u v w
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X : Type u} {Y : Type v} {A : Type w}
    [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma finite_observation_entropy_test_uniform [StandardBorelSpace X] [Nonempty A]
    (μ : Measure X) (p : X → A) (hp : Measurable p)
    {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (Z : Type v) [MeasurableSpace Z] (ν : Measure Z) (q : Z → A),
      Measurable q → LawClose (μ.map p) (ν.map q) δ → |obs μ p-obs ν q|<ε := by
  obtain ⟨δ,hδ,ht⟩ := finite_entropy_continuity (μ.map p) hε
  refine ⟨δ,hδ,?_⟩
  intro Z mZ ν q hq hlaw
  have hh := ht (ν.map q) hlaw
  rwa [←obs_eq_entropy_map μ p hp,←obs_eq_entropy_map ν q hq] at hh

theorem weakBernoulli_limit_finite_determination [StandardBorelSpace X] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (happrox : ∀ ε : ℝ,0<ε → ∃ r : X → A,Measurable r ∧ WeakBernoulliProcess μ e r ∧
      μ.real {x | p x≠r x}<ε) {η : ℝ} (hη : 0<η) :
    ∃ m s₀ : ℕ,0 < s₀ ∧ ∃ δ : ℝ,0<δ ∧
      ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν) (T : Y → Y)
        (_hT : MeasurePreserving T ν ν) (q : Y → A),Measurable q →
        LawClose (μ.map (word e p m)) (ν.map (word T q m)) δ →
        rate μ e p-δ ≤ rate ν T q →
        ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word e p (n*s₀))) (mass ν (word T q (n*s₀))),
          R.cost nameCost≤η*(n*s₀ : ℕ) := by
  let a := η/100
  have ha : 0<a := div_pos hη (by norm_num)
  have ha2 : 0<a^2 := sq_pos_of_pos ha
  obtain ⟨r,hr,hwb,hpaint⟩ := happrox a ha
  obtain ⟨g,hg⟩ := weakBernoulli_forward_blocks μ e he r hr hwb ha
  obtain ⟨k,hk⟩ := exists_nat_gt ((g : ℝ)/a+1)
  have hkpos : 0<k := by
    have hh : 0≤(g : ℝ)/a := div_nonneg (Nat.cast_nonneg _) ha.le
    have : (0 : ℝ)<k := by linarith
    exact_mod_cast this
  have hgap : (g : ℝ)≤a*(k : ℝ) := by
    have hh := (div_lt_iff₀ ha).mp (show (g : ℝ)/a<(k : ℝ) by linarith)
    nlinarith
  let s := k+g
  have hs : 0 < s := by dsimp [s]; omega
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  let pr := word e r s
  let pp := word e p s
  have hpr : Measurable pr := word_measurable e he.measurable r hr s
  have hpp : Measurable pp := word_measurable e he.measurable p hp s
  obtain ⟨L,hL⟩ := (eventually_conditional_single_test μ (e^[s]) (he.iterate _) pr hpr
    (show 0<a^2/2 by positivity)).exists
  rw [rate_power_word μ e he r hr s hs] at hL
  have hfuture : Measurable (fun x => word (e^[s]) pr L (e^[s] x)) :=
    (word_measurable _ (he.measurable.iterate _) pr hpr L).comp (he.measurable.iterate _)
  obtain ⟨δc,hδc,hct⟩ := conditional_entropy_law_test_uniform.{w} μ pr
    (fun x => word (e^[s]) pr L (e^[s] x)) hpr hfuture (show 0<a^2/2 by positivity)
  let C := Real.log (Fintype.card (Fin s → A))
  have hC : 0≤C := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α:=Fin s → A))
  have hconv := (rate_tendsto μ (e^[s]) (he.iterate _) pp hpp).eventually
    (gt_mem_nhds (show rate μ (e^[s]) pp < rate μ (e^[s]) pp+a^2 by linarith))
  rw [rate_power_word μ e he p hp s hs] at hconv
  obtain ⟨J₀,hJ₀⟩ := exists_nat_gt (max ((2+(L : ℝ)*C)/a^2) (2*(L : ℝ)/a)+1)
  obtain ⟨J,hJbound,hJconv⟩ := (hconv.and (eventually_ge_atTop J₀)).exists

  have hJge : J₀≤J := hJconv
  have hJent : obs μ (word (e^[s]) pp J)/(J : ℝ)<(s : ℝ)*rate μ e p+a^2 := hJbound
  have hJpos : 0<J := by
    have hb : 0≤(2+(L : ℝ)*C)/a^2 := div_nonneg (by positivity) ha2.le
    have hJr : (0 : ℝ)<J₀ := by linarith [le_max_left ((2+(L : ℝ)*C)/a^2) (2*(L : ℝ)/a)]
    have : 0<J₀ := by exact_mod_cast hJr
    omega
  have hJR : (0 : ℝ)<J := by exact_mod_cast hJpos
  have hboundary₁ : 2+(L : ℝ)*C≤(J : ℝ)*a^2 := by
    have h₀ : (2+(L : ℝ)*C)/a^2<(J : ℝ) := by
      have hnat : (J₀ : ℝ)≤J := by exact_mod_cast hJge
      linarith [le_max_left ((2+(L : ℝ)*C)/a^2) (2*(L : ℝ)/a)]
    exact ((div_lt_iff₀ ha2).mp h₀).le
  have hboundary₂ : 2*(L : ℝ)≤(J : ℝ)*a := by
    have h₀ : 2*(L : ℝ)/a<(J : ℝ) := by
      have hnat : (J₀ : ℝ)≤J := by exact_mod_cast hJge
      linarith [le_max_right ((2+(L : ℝ)*C)/a^2) (2*(L : ℝ)/a)]
    exact ((div_lt_iff₀ ha).mp h₀).le
  let P := word (e^[s]) pp J
  let S := word (e^[s]) pr J
  have hP : Measurable P := word_measurable _ (he.measurable.iterate _) pp hpp J
  have hS : Measurable S := word_measurable _ (he.measurable.iterate _) pr hpr J
  obtain ⟨δp,hδp,hpt⟩ := finite_observation_entropy_test_uniform.{u,v} μ P hP (show (0 : ℝ)<1 by norm_num)
  obtain ⟨δr,hδr,hrt⟩ := finite_observation_entropy_test_uniform.{u,w} μ S hS (show (0 : ℝ)<1 by norm_num)
  let δ := min (a/2) (min (a^2/s) (min (δc/2) (min δp (δr/2))))
  have hδ : 0<δ := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min hδp (by positivity))))
  have hd₁ : 2*δ≤a := by have := min_le_left (a/2) (min (a^2/s) (min (δc/2) (min δp (δr/2)))); dsimp [δ]; linarith
  have hd₂ : (s : ℝ)*δ≤a^2 := by
    have hh : δ≤a^2/(s : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ hsR).mp hh
    nlinarith
  have hd₃ : 2*δ≤δc := by
    have hh : δ≤δc/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hd₄ : δ≤δp := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd₅ : 2*δ≤δr := by
    have hh : δ≤δr/2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  refine ⟨J*s,J*s,Nat.mul_pos hJpos hs,δ,hδ,?_⟩
  intro ν hν T hT q hq hclose hrate n
  rw [←Nat.mul_assoc]
  let := hν
  let Q₀ := word (T^[s]) (word T q s) J
  let Q := word (T^[J*s]) Q₀ n
  have hQ₀ : Measurable Q₀ := word_measurable _ (hT.measurable.iterate _) _ (word_measurable T hT.measurable q hq s) J
  have hQ : Measurable Q := word_measurable _ (hT.measurable.iterate _) Q₀ hQ₀ n
  have hb₀ : LawClose (μ.map P) (ν.map Q₀) δ := by
    have hh := hclose.map (measurable_of_countable (wordPack J s))
    rw [Measure.map_map (measurable_of_countable (wordPack J s)) (word_measurable e he.measurable p hp _),
      Measure.map_map (measurable_of_countable (wordPack J s)) (word_measurable T hT.measurable q hq _)] at hh
    simpa only [Function.comp_def,wordPack_apply] using hh
  have hb (i : Fin n) : LawClose (μ.map P) (ν.map (fun y => Q y i)) δ := by
    rw [map_word_coordinate ν (T^[J*s]) (hT.iterate _) Q₀ hQ₀ n i]
    exact hb₀
  let : StandardBorelSpace (Fin n → Fin J → Fin s → A) := inferInstance
  let ξ := recodingLaw μ P S hP hS ν n Q
  have : IsProbabilityMeasure ξ := recodingLaw_probability μ P S hP hS ν n Q hQ
  have houtlaw (i : Fin n) : LawClose (μ.map S) (ξ.map (fun vw => vw.2 i)) (2*δ) :=
    recodingLaw_output_lawClose μ P S hP hS ν n Q hQ i (hb i)
  have hin (i : Fin n) : obs ν (fun y => Q y i)≤obs μ P+1 := by
    have hh := hpt Y ν (fun y => Q y i) ((measurable_pi_apply i).comp hQ) ((hb i).mono hd₄)
    linarith [(abs_lt.mp hh).1]
  have hout (i : Fin n) : obs μ S-1≤obs ξ (fun vw => vw.2 i) := by
    have hh := hrt _ ξ (fun vw => vw.2 i) ((measurable_pi_apply i).comp measurable_snd)
      ((houtlaw i).mono hd₅)
    linarith [(abs_lt.mp hh).2]
  have hentropy := recodingLaw_entropy_lower μ P S hP hS ν n Q hQ hin hout
  have hquadlo : ((n*J)*s : ℕ)*rate ν T q≤obs ν Q := by
    rw [obs_nestedPack_word]
    exact obs_word_rate_lower ν T hT q hq _
  have hSlo : (J*s : ℕ)*rate μ e r≤obs μ S := by
    rw [obs_word_pack]
    exact obs_word_rate_lower μ e he r hr _
  have hPhi : obs μ P≤(J*s : ℕ)*rate μ e p+(J : ℝ)*a^2 := by
    have hh := (div_lt_iff₀ hJR).mp hJent
    dsimp only [P]
    push_cast
    nlinarith
  have hQlo : ((n*J)*s : ℕ)*(rate μ e p-δ)≤obs ν Q :=
    (mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg ((n*J)*s))).trans hquadlo
  have hwholeEntropy := recoding_nested_entropy μ ν n J s P S hP hS Q hQ hd₂ hQlo hPhi hSlo hin hout
  obtain ⟨R₁,hR₁budget⟩ := block_recoding_small_cost_q44 μ ξ e he r hr k g L n J Prod.snd measurable_snd
    ha (show 0≤2*δ by positivity) hd₁ hgap hboundary₁ hboundary₂ (hg k) houtlaw (by
      intro u v hu hv hlaw
      have hh := hct _ ξ u v hu hv (hlaw.mono hd₃)
      have hh' := (abs_lt.mp hh).1
      dsimp only [pr,s] at hL hh' ⊢
      linarith only [hh',hL]) hwholeEntropy
  have htransport := recoding_nested_transport μ ν n J s P S hP hS Q hQ hb
  have hQflat : nestedOutput n J s Q=word T q ((n*J)*s) := nestedOutput_word T q n J s
  rw [hQflat] at htransport
  obtain ⟨R₂,hR₂⟩ := htransport
  rw [observations_fineWordCost μ e he p r hp hr J s] at hR₂
  have hR₂budget : R₂.cost nameCost≤2*a*((n*J)*s : ℕ) := by
    have hs' : μ.real {x | p x≠r x}+2*δ≤2*a := by linarith only [hpaint,hd₁]
    have hh := mul_le_mul_of_nonneg_left hs' (Nat.cast_nonneg ((n*J)*s))
    apply hR₂.trans
    push_cast at hh ⊢
    nlinarith only [hh]
  let R₀ := MatrixCoupling.observations μ (word e p ((n*J)*s)) (word e r ((n*J)*s))
    (word_measurable e he.measurable p hp _) (word_measurable e he.measurable r hr _)
  have hR₀ : R₀.cost nameCost≤a*((n*J)*s : ℕ) := by
    change (MatrixCoupling.observations μ _ _ _ _).cost nameCost≤_
    rw [observations_word_cost μ e he p r hp hr]
    have hh := mul_le_mul_of_nonneg_left hpaint.le (Nat.cast_nonneg ((n*J)*s))
    nlinarith only [hh]
  let R := (R₀.comp R₁).comp R₂.symm
  have hR : R.cost nameCost≤η*((n*J)*s : ℕ) := by
    have h₁ := MatrixCoupling.comp_cost_le R₀ R₁ nameCost nameCost nameCost nameCost_triangle
    have h₂ := MatrixCoupling.comp_cost_le (R₀.comp R₁) R₂.symm nameCost nameCost nameCost nameCost_triangle
    rw [MatrixCoupling.symm_cost R₂ nameCost nameCost_comm] at h₂
    have hηa : η=100*a := by dsimp [a]; ring
    dsimp only [R]
    rw [hηa]
    have hpos := mul_nonneg ha.le (Nat.cast_nonneg ((n*J)*s))
    nlinarith only [h₁,h₂,hR₀,hR₁budget,hR₂budget,hpos]
  exact ⟨R,hR⟩
end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_FixedWindowCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators
variable {A B C : Type*} {k t R : ℕ}

lemma symbolCost_factor_le (F : C → B) (a b : C) : symbolCost (F a) (F b)≤ symbolCost a b := by
  classical
  by_cases h : a=b
  · subst b; simp [symbolCost]
  · simpa only [symbolCost,ite_eq_right h] using symbolCost_le_one (F a) (F b)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B C : Type*} {k t R : ℕ}

lemma finite_sum_injective_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (g : κ → ℝ) (hg : ∀ j,0≤g j) :
    (∑ i,g (f i))≤∑ j,g j := by
  classical
  calc
    _=(∑ j∈Finset.univ.image f,g j) := (Finset.sum_image (fun i hi i' hi' h => hf h)).symm
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hg i)

lemma fixedWindowCost_factor_triangle (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → C) (d : Fin (k+t) → A) :
    fixedWindowCost F H D a d≤normalizedPrefixCost id a b+
      fixedWindowCost F H D (fun i => b (Fin.castAdd t i)) d := by
  let b₀ : Fin k → C := fun i => b (Fin.castAdd t i)
  have hp : prefixNameCost F a d≤prefixNameCost id a b+prefixNameCost F b₀ d := by
    unfold prefixNameCost
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact (symbolCost_triangle _ (F (b₀ i)) _).trans
      (add_le_add_left (symbolCost_factor_le F (a i) (b₀ i)) _)
  have hd : decoderNameCost H D a d≤prefixNameCost id a b+decoderNameCost H D b₀ d := by
    have hh : decoderNameCost H D a d≤
        (∑ i : Fin (k-2*R),symbolCost (blockCenter a i) (blockCenter b₀ i))+decoderNameCost H D b₀ d := by
      unfold decoderNameCost
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      exact (symbolCost_triangle _ (H (blockCenter b₀ i)) _).trans
        (add_le_add_left (symbolCost_factor_le H (blockCenter a i) (blockCenter b₀ i)) _)
    apply hh.trans
    apply add_le_add_left
    let f : Fin (k-2*R) → Fin k := fun i => ⟨i.val+R,by have := i.isLt; omega⟩
    have hf : Function.Injective f := by
      intro i j h
      have hh := congrArg Fin.val h
      apply Fin.ext
      dsimp [f] at hh
      omega
    exact finite_sum_injective_le f hf (fun i => symbolCost (a i) (b₀ i)) (fun _ => symbolCost_nonneg _ _)
  unfold fixedWindowCost normalizedPrefixCost
  have hn0 : (0 : ℝ)≤(k+t : ℕ) := Nat.cast_nonneg _
  by_cases hn : k+t=0
  · simp [hn]
  · have hnpos : (0 : ℝ)<(k+t : ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*(k+t : ℕ))).mpr
    have heq : (prefixNameCost id a b/(k+t : ℕ)+
        (prefixNameCost F b₀ d+decoderNameCost H D b₀ d)/(2*(k+t : ℕ)))*(2*(k+t : ℕ))=
        2*prefixNameCost id a b+(prefixNameCost F b₀ d+decoderNameCost H D b₀ d) := by field_simp
    change prefixNameCost F a d+decoderNameCost H D a d≤_
    rw [heq]
    linarith

variable [MeasurableSpace A]

lemma graph_window_word [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    (_decoder : (Fin (2*R+1) → A) → B) (y : ℤ → A) (i : Fin (k-2*R)) :
    centeredWindow R (iidShift^[i.val+R] y)=blockWindow (word iidShift (fun y : ℤ → A => y 0) (k+t) y) i := by
  funext j
  simp only [centeredWindow,iidShift_iterate,blockWindow,iid_word_eq]
  congr 1
  omega

variable [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma graph_fixedWindowCost_zero (D : (Fin (2*R+1) → A) → B) (y : ℤ → A) :
    fixedWindowCost (k:=k) (t:=t) Prod.fst Prod.snd D
      (word iidShift (fun w : ℤ → A => (w 0,D (centeredWindow R w))) k y)
      (word iidShift (fun w : ℤ → A => w 0) (k+t) y)=0 := by
  have hp : prefixNameCost Prod.fst
      (word iidShift (fun w : ℤ → A => (w 0,D (centeredWindow R w))) k y)
      (word iidShift (fun w : ℤ → A => w 0) (k+t) y)=0 := by simp [prefixNameCost,word,symbolCost]
  have hd : decoderNameCost Prod.snd D
      (word iidShift (fun w : ℤ → A => (w 0,D (centeredWindow R w))) k y)
      (word iidShift (fun w : ℤ → A => w 0) (k+t) y)=0 := by
    unfold decoderNameCost
    apply Finset.sum_eq_zero
    intro i _
    dsimp only [blockCenter,word,Prod.snd]
    rw [graph_window_word D y i,symbolCost_self]
  simp only [fixedWindowCost,hp,hd,add_zero,zero_div]

theorem lift_joint_graph_transport {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : X → X) (he : Measurable e)
    (p : X → A×B) (hp : Measurable p)
    (ν : Measure (ℤ → A)) [IsProbabilityMeasure ν]
    (D : (Fin (2*R+1) → A) → B)
    (S : MatrixCoupling (mass μ (word e p (k+t)))
      (mass ν (word iidShift (fun y : ℤ → A => (y 0,D (centeredWindow R y))) (k+t)))) :
    ∃ T : MatrixCoupling (mass μ (word e p k)) (mass ν (word iidShift (fun y : ℤ → A => y 0) (k+t))),
      T.cost (fixedWindowCost Prod.fst Prod.snd D)≤S.cost nameCost/(k+t : ℕ) := by
  classical
  obtain ⟨P,hP⟩ := lift_prefix_transport (k:=k) (t:=t) μ e he p hp id S
  let g : (ℤ → A) → A×B := fun y => (y 0,D (centeredWindow R y))
  have hg : Measurable g := (measurable_pi_apply 0).prodMk ((measurable_of_countable D).comp (measurable_centeredWindow R))
  let Q := MatrixCoupling.observations ν (word iidShift g (k+t))
    (word iidShift (fun y : ℤ → A => y 0) (k+t))
    (word_measurable iidShift iidShift.measurable g hg _)
    (word_measurable iidShift iidShift.measurable _ (measurable_pi_apply 0) _)
  let c := fun (a : Fin (k+t) → A×B) (b : Fin (k+t) → A) =>
    fixedWindowCost Prod.fst Prod.snd D (fun i : Fin k => a (Fin.castAdd t i)) b
  have hQ : Q.cost c=0 := by
    rw [MatrixCoupling.observations_cost]
    have hzero (y : ℤ → A) : c (word iidShift g (k+t) y) (word iidShift (fun y : ℤ → A => y 0) (k+t) y)=0 :=
      graph_fixedWindowCost_zero D y
    simp only [hzero,integral_zero]
  refine ⟨P.comp Q,?_⟩
  have hh := P.comp_cost_le Q (normalizedPrefixCost id) c (fixedWindowCost Prod.fst Prod.snd D)
    (fixedWindowCost_factor_triangle Prod.fst Prod.snd D)
  rw [hQ,add_zero] at hh
  exact hh.trans hP
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

theorem fixed_window_fd_graph (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : Ergodic e μ) (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0<weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α)
    (happrox : ∀ ε : ℝ,0<ε → ∃ r : X → A×B,Measurable r ∧ WeakBernoulliProcess μ e r ∧
      μ.real {x | (p x,α x)≠r x}<ε) {η : ℝ} (hη : 0<η) :
    ∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,∃ s : ℕ,0 < s ∧
      ∀ n : ℕ,∃ W : MatrixCoupling (mass μ (word e (fun x => (p x,α x)) (n*s)))
        (mass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))
          (word iidShift (fun y : ℤ → A => (y 0,D (centeredWindow R y))) (n*s))),
        W.cost nameCost≤η*(n*s : ℕ) := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  obtain ⟨m,s,hs,δ,hδ,hfd⟩ := weakBernoulli_limit_finite_determination (Y:=ℤ → A)
    μ e he.toMeasurePreserving (fun x => (p x,α x)) (hp.prodMk hα) happrox hη
  obtain ⟨R,D,hLaw,hRate⟩ := relative_iid_window_graph μ e he p hp β hβ hβsum hβentropy H hcode α hα m hδ
  refine ⟨R,D,s,hs,?_⟩
  apply hfd _ inferInstance iidShift (iidShift_preserving _) _
    ((measurable_pi_apply 0).prodMk ((measurable_of_countable D).comp (measurable_centeredWindow R))) hLaw
  simp only [Function.comp_apply]
  rw [hRate]
  have hh := H.upper (fun x => (p x,α x)) (hp.prodMk hα)
  linarith
end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_FixedWindowTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

theorem fixed_decoder_arbitrary_tests_q44_oai (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α)
    (happrox : ∀ ε : ℝ,0 < ε → ∃ r : X → A×B,Measurable r ∧ WeakBernoulliProcess μ e r ∧
      μ.real {x | (p x,α x)≠r x} < ε)
    (zero one : A) (h01 : zero≠one) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,
      ∀ l : ℕ,∀ ε ρ : ℝ,0 < ε → 0 < ρ → ∃ q : X → A,Measurable q ∧
        μ.real {x | p x≠q x} < η ∧
        μ.real {x | α (e^[R] x)≠D (word e q (2*R+1) x)} < η ∧
        LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
        weightEntropy β-ρ < rate μ e q := by
  classical
  obtain ⟨R,D,s,hs,hfd⟩ := fixed_window_fd_graph μ e he p hp β hβ hβsum hβentropy H hcode α hα
    happrox (by positivity : 0 < η/8)
  let P : X → A×B := fun x => (p x,α x)
  have hP : Measurable P := hp.prodMk hα
  have hrateP : rate μ e P=weightEntropy β := by
    apply le_antisymm (H.upper P hP)
    rw [←rate_of_iid_factor μ e he.toMeasurePreserving p hp β hβ hβsum hcode]
    exact rate_pair_ge_left μ e he.toMeasurePreserving p α hp hα
  refine ⟨R,D,?_⟩
  intro l ε ρ hε hρ
  obtain ⟨K,r,m,hK,_hr,hm,hcopy⟩ := actual_fixed_window_rate_copy_q44 μ e he htotal P hP Prod.fst Prod.snd R D
    β hβ hβsum hβentropy (H.upper P hP) zero one h01 l (lt_min hε (half_pos hη)) hρ
  have htend : Tendsto (fun n : ℕ => n*s) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_right n hs)
  obtain ⟨n,hn⟩ := (htend.eventually hcopy).exists
  have hN : 0 < n*s*K*m+n*s*m :=
    add_pos (Nat.mul_pos (Nat.mul_pos hn.1 hK) hm) (Nat.mul_pos hn.1 hm)
  have hlen : (n*K*m+n*m)*s=n*s*K*m+n*s*m := by ring
  have hST := hfd (n*K*m+n*m)
  rw [hlen] at hST
  obtain ⟨S,hS⟩ := hST
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  have hRT := lift_joint_graph_transport (k:=n*s*K*m) (t:=n*s*m) μ e e.measurable P hP ν D S
  have hiid : mass ν (word iidShift (fun y : ℤ → A => y 0) (n*s*K*m+n*s*m))=
      productWordWeight β (n*s*K*m+n*s*m) := funext (iid_word_mass β hβ hβsum _)
  rw [hiid] at hRT
  obtain ⟨T,hT⟩ := hRT
  have hcost : T.cost (fixedWindowCost Prod.fst Prod.snd D)≤η/8 :=
    hT.trans ((div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr hS)
  obtain ⟨q,hq,hpaint,hfixed,hlaw,hrate⟩ := hn.2 T
  refine ⟨q,hq,?_,?_,hlaw.mono (min_le_left _ _),?_⟩
  · change μ.real {x | p x≠q x} < _ at hpaint
    linarith only [hpaint,hcost,min_le_right ε (η/2),hη]
  · change μ.real {x | α (e^[R] x)≠D (word e q (2*R+1) x)} < _ at hfixed
    linarith only [hfixed,hcost,min_le_right ε (η/2),hη]
  · rwa [hrateP] at hrate
end HyperbolicCoding

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.HyperbolicCoding.fixed_decoder_arbitrary_tests_q44_oai.{u_1, u_2, u_3} := @OAI.HyperbolicCoding.fixed_decoder_arbitrary_tests_q44_oai.{u_1, u_2, u_3}

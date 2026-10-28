-- Prove2me | solution 1 for OAI.StandardMapEntropy.actual_return_bernoulli_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:19:45.93616+00:00
-- url     : https://prove2.me/submissions/bac2bb97-ecd2-4a46-88e8-236f4349cd90

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_HyperbolicCoding_fixed_decoder_arbitrary_tests_q44
import Theorems.Thm_OAI_HyperbolicCoding_goodIIDStage_next_q44
import Theorems.Thm_OAI_StandardMapEntropy_actual_return_full_entropy_iid_factor_q44

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_HyperbolicSet
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma normalizedArea_probability {E : Set Torus} (hE : 0 < area E) :
    IsProbabilityMeasure (normalizedArea E) := by
  constructor
  simp only [normalizedArea, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hE.ne' (measure_lt_top area E).ne

lemma normalizedArea_absolutelyContinuous (E : Set Torus) : normalizedArea E ≪ area :=
  Measure.absolutelyContinuous_restrict.smul_left _

end StandardMapEntropy

end
end

end OAI
end

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

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ErgodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal ENNReal

namespace HyperbolicCoding

lemma measurable_joinedBinary {X : Type*} [MeasurableSpace X]
    {α : ℕ → ℕ → X → Bool} (hα : ∀ i j,Measurable (α i j)) (N : ℕ) :
    Measurable (joinedBinary α N) :=
  Measurable.of_eval (fun p => hα p.1 p.2)

end HyperbolicCoding

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

lemma rate_le_entropy_increment (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    rate μ f p≤obs μ (word f p (m+1))-obs μ (word f p m) := by
  apply le_of_tendsto (entropy_increment_tendsto μ f hf p hp)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact entropy_increment_antitone μ f hf p hp hn

lemma rate_mul_le_cond_future (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n m : ℕ) :
    (n : ℝ)*rate μ f p ≤ cond μ (word f p n) (fun x => word f p m (f^[n] x)) := by
  rw [cond_word_future_eq μ f hf p hp]
  induction n with
  | zero =>
    simp only [Nat.cast_zero,zero_mul]
    have he (a b : ℕ) (h : a=b) : obs μ (word f p a)=obs μ (word f p b) := by subst b; rfl
    exact sub_nonneg.mpr (le_of_eq (he (0+m) m (Nat.zero_add m)).symm)
  | succ n ih =>
    have hh := rate_le_entropy_increment μ f hf p hp (n+m)
    rw [Nat.cast_add,Nat.cast_one]
    rw [show n+1+m=n+m+1 from by omega]
    nlinarith

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
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HyperbolicCoding

lemma exists_eventual_decoder {Y B : Type*} [MeasurableSpace Y] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
    (G : ℕ → Y → B) (hG : ∀ n,Measurable (G n)) :
    ∃ H : Y → B,Measurable H ∧ ∀ v b,(∀ᶠ n : ℕ in atTop,G n v=b) → H v=b := by
  classical
  let b₀ : B := Classical.choice inferInstance
  let E (b : B) : Set Y := {v | ∀ᶠ n : ℕ in atTop,G n v=b}
  have hEm (b : B) : MeasurableSet (E b) := by
    have he : E b=⋃ N : ℕ,⋂ n : ℕ,⋂ (_h : N≤n),(G n) ⁻¹' {b} := by
      ext v
      simp only [E,mem_ofPred_eq,eventually_atTop,mem_iUnion,mem_iInter,mem_preimage,mem_singleton_iff]
    rw [he]
    exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n =>
      MeasurableSet.iInter (fun _ : N≤n => hG n (measurableSet_singleton b))))
  have huniq (v : Y) (b c : B) (hb : v∈E b) (hc : v∈E c) : b=c := by
    obtain ⟨n,hn⟩ := (hb.and hc).exists
    exact hn.1.symm.trans hn.2
  let H (v : Y) : B := if h : ∃ b,v∈E b then h.choose else b₀
  have hHb (v : Y) (b : B) (hb : v∈E b) : H v=b := by
    have he : ∃ b,v∈E b := ⟨b,hb⟩
    dsimp only [H]
    rw [dite_eq_left he]
    exact huniq v _ b he.choose_spec hb
  refine ⟨H,?_,hHb⟩
  apply measurable_to_countable'
  intro b
  have he : H ⁻¹' {b}=E b ∪ (if b=b₀ then (⋃ c,E c)ᶜ else ∅) := by
    ext v
    simp only [mem_preimage,mem_singleton_iff,mem_union]
    by_cases hv : ∃ c,v∈E c
    · have hn : v∉(⋃ c,E c)ᶜ := by simpa using hv
      have hh : H v=b ↔ v∈E b :=
        ⟨fun h => h ▸ (show v∈E (H v) from by simpa only [H,dite_eq_left hv] using hv.choose_spec),hHb v b⟩
      by_cases hb : b=b₀
      · rw [ite_eq_left hb]
        simpa only [hn,or_false] using hh
      · rw [ite_eq_right hb]
        simpa only [mem_empty_iff_false,or_false] using hh
    · have hh : H v=b₀ := dite_eq_right hv
      have hn : v∈(⋃ c,E c)ᶜ := by simpa using hv
      have hb : v∉E b := fun hb => hv ⟨b,hb⟩
      by_cases he : b=b₀
      · rw [ite_eq_left he]
        simp only [hn,or_true,iff_true]
        exact hh.trans he.symm
      · rw [ite_eq_right he]
        simp only [hb,mem_empty_iff_false,or_self,iff_false]
        exact fun hc => he (hc.symm.trans hh)
  rw [he]
  apply (hEm b).union
  split_ifs
  · exact (MeasurableSet.iUnion hEm).compl
  · exact MeasurableSet.empty

theorem exists_factor_of_approx {X Y B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
    (μ : Measure X) [IsFiniteMeasure μ] (Z : X → Y) (q : X → B)
    (happrox : ∀ ε : ℝ,0<ε → ∃ G : Y → B,Measurable G ∧
      μ {x | G (Z x)≠q x}<ENNReal.ofReal ε) :
    ∃ G : Y → B,Measurable G ∧ q=ᵐ[μ]G ∘ Z := by
  have happ (n : ℕ) := happrox ((1/2 : ℝ)^n) (pow_pos (by norm_num) n)
  choose G hG hsmall using happ
  obtain ⟨H,hH,hHb⟩ := exists_eventual_decoder G hG
  have hs : (∑' n : ℕ,μ {x | G n (Z x)≠q x})≠⊤ := by
    apply ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (fun n => (hsmall n).le))
    simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ)≤1/2),ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr
      (ENNReal.ofReal_lt_one.mpr (by norm_num))))
  have ha := ae_eventually_notMem hs
  refine ⟨H,hH,?_⟩
  filter_upwards [ha] with x hx
  exact (hHb (Z x) (q x) (hx.mono (fun n hn => not_ne_iff.mp hn))).symm

end HyperbolicCoding

end
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

lemma cond_future_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    Tendsto (fun m : ℕ => cond μ (word f p n) (fun x => word f p m (f^[n] x))) atTop
      (𝓝 ((n : ℝ)*rate μ f p)) := by
  simp_rw [cond_word_future_eq μ f hf p hp]
  induction n with
  | zero =>
    have he (m : ℕ) : obs μ (word f p (0+m))=obs μ (word f p m) := by
      have hi (a b : ℕ) (h : a=b) : obs μ (word f p a)=obs μ (word f p b) := by subst b; rfl
      exact hi _ _ (Nat.zero_add m)
    simpa only [he,sub_self,Nat.cast_zero,zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ n ih =>
    have ht : Tendsto (fun m : ℕ => n+m) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_add_left m n) tendsto_id
    have hd := (entropy_increment_tendsto μ f hf p hp).comp ht
    have hh := hd.add ih
    have he (m : ℕ) :
        (obs μ (word f p ((n+m)+1))-obs μ (word f p (n+m)))+
          (obs μ (word f p (n+m))-obs μ (word f p m))=
            obs μ (word f p (n+1+m))-obs μ (word f p m) := by
      rw [show n+1+m=n+m+1 from by omega]
      ring
    simp only [Function.comp_def,he] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.cast_add,Nat.cast_one]
    ring_nf

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
lemma integerIterate_neg_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : integerIterate e (-(n : ℤ)) x=e.symm^[n] x := by
  simp only [integerIterate,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
  rfl
lemma integerIterate_nat_fun (e : X ≃ᵐ X) (n : ℕ) : integerIterate e (n : ℤ)=e^[n] :=
  funext (integerIterate_nat e n)
lemma integerIterate_neg_nat_fun (e : X ≃ᵐ X) (n : ℕ) : integerIterate e (-(n : ℤ))=e.symm^[n] :=
  funext (integerIterate_neg_nat e n)
lemma integerIterate_measurable (e : X ≃ᵐ X) (n : ℤ) : Measurable (integerIterate e n) := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,integerIterate_nat_fun] using e.measurable.iterate m
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    simpa only [hn,integerIterate_neg_nat_fun] using e.symm.measurable.iterate (m+1)
lemma integerIterate_measurePreserving (e : X ≃ᵐ X) {μ : Measure X}
    (he : MeasurePreserving e μ μ) (n : ℤ) : MeasurePreserving (integerIterate e n) μ μ := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,integerIterate_nat_fun] using he.iterate m
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    simpa only [hn,integerIterate_neg_nat_fun] using (he.symm e).iterate (m+1)

lemma measurable_orbitName {A : Type*} [MeasurableSpace A] (e : X ≃ᵐ X) {α : X → A}
    (hα : Measurable α) : Measurable (orbitName e α) :=
  Measurable.of_eval (fun n => hα.comp (integerIterate_measurable e n))
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
-- module Solutions.OAIQ44_CM.StandardMap_Coding_PartitionLimit
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
variable {X A : Type*} [MeasurableSpace X]

theorem exists_partition_limit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) (q : ℕ → X → A) (hq : ∀ n,Measurable (q n))
    (hs : (∑' n : ℕ,μ {x | q (n+1) x≠q n x})≠⊤) :
    ∃ p : X → A,Measurable p ∧ ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x := by
  obtain ⟨p,hp,hlim⟩ := exists_eventual_decoder q hq
  have hh := ae_eventually_notMem hs
  refine ⟨p,hp,?_⟩
  filter_upwards [hh] with x hx
  obtain ⟨N,hN⟩ := eventually_atTop.mp hx
  have hconst : ∀ n,N≤n → q n x=q N x := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (not_ne_iff.mp (hN n hn)).trans ih
  have hc : ∀ᶠ n : ℕ in atTop,q n x=q N x := eventually_atTop.mpr ⟨N,hconst⟩
  rwa [hlim x (q N x) hc]

lemma measureReal_tendsto_zero_of_ae_eventually_notMem (μ : Measure X) [IsFiniteMeasure μ]
    (D : ℕ → Set X) (hD : ∀ n,MeasurableSet (D n))
    (ha : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,x∉D n) :
    Tendsto (fun n => μ.real (D n)) atTop (𝓝 0) := by
  let U (n : ℕ) : Set X := ⋃ j : ℕ,⋃ (_ : n≤j),D j
  have hU (n : ℕ) : MeasurableSet (U n) :=
    MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => hD j))
  have hanti : Antitone U := by
    intro n m hnm x hx
    obtain ⟨j,hx⟩ := mem_iUnion.mp hx
    obtain ⟨hj,hx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hnm.trans hj,hx⟩⟩
  have hi : μ (⋂ n,U n)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ha] with x hx hmem
    obtain ⟨N,hN⟩ := eventually_atTop.mp hx
    obtain ⟨j,hmem⟩ := mem_iUnion.mp (mem_iInter.mp hmem N)
    obtain ⟨hj,hmem⟩ := mem_iUnion.mp hmem
    exact hN j hj hmem
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hU n).nullMeasurableSet)
    hanti ⟨0,measure_ne_top μ _⟩
  rw [hi] at ht
  have htr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞)≠⊤)).comp ht
  simp only [Function.comp_def,ENNReal.toReal_zero] at htr
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) htr
  exact measureReal_mono (μ := μ) (fun x hx => mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨le_rfl,hx⟩⟩) (measure_ne_top μ _)

lemma partition_limit_integer_names [MeasurableSpace A] {μ : Measure X} (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {q : ℕ → X → A} {p : X → A}
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x) :
    ∀ᵐ x ∂μ,∀ s : Finset ℤ,∀ᶠ n : ℕ in atTop,∀ i∈s,
      orbitName e (q n) x i=orbitName e p x i := by
  have hh : ∀ i : ℤ,∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,
      q n (integerIterate e i x)=p (integerIterate e i x) :=
    fun i => (integerIterate_measurePreserving e he i).quasiMeasurePreserving.ae hlim
  filter_upwards [ae_all_iff.mpr hh] with x hx s
  have hall : ∀ᶠ n : ℕ in atTop,∀ i : s,
      q n (integerIterate e i x)=p (integerIterate e i x) :=
    Filter.eventually_all.2 (fun i => hx i)
  exact hall.mono (fun n hn i hi => hn ⟨i,hi⟩)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [Fintype A]

lemma finite_code_error_tendsto_zero {μ : Measure X} [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x) (s : Finset ℤ) :
    Tendsto (fun n => μ.real {x | s.restrict (orbitName e (q n) x)≠s.restrict (orbitName e p x)})
      atTop (𝓝 0) := by
  apply measureReal_tendsto_zero_of_ae_eventually_notMem μ
  · intro n
    exact (measurableSet_eq_fun ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e (hq n)))
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e hp))).compl
  · filter_upwards [partition_limit_integer_names e he hlim] with x hx
    filter_upwards [hx s] with n hn
    simp only [not_ne_iff]
    funext i
    exact hn i i.property

lemma finite_box_law_tendsto {μ : Measure X} [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (s : Finset ℤ) (t : ℤ → Set A) (ht : ∀ i,MeasurableSet (t i)) :
    Tendsto (fun n => (μ.map (orbitName e (q n))).real (Set.pi s t)) atTop
      (𝓝 ((μ.map (orbitName e p)).real (Set.pi s t))) := by
  let D : Set (s → A) := Set.pi Set.univ (fun i => t i)
  have hD : MeasurableSet D := MeasurableSet.univ_pi (fun i => ht i)
  have hpre : (s.restrict : (ℤ → A) → (s → A)) ⁻¹' D=Set.pi s t := by
    ext w
    simp only [D,mem_preimage,Set.mem_pi,mem_univ,true_implies,Finset.mem_coe,Finset.restrict]
    exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.property⟩
  have hdist (n : ℕ) :
      |(μ.map (orbitName e (q n))).real (Set.pi s t)-
       (μ.map (orbitName e p)).real (Set.pi s t)|≤
        μ.real {x | s.restrict (orbitName e (q n) x)≠s.restrict (orbitName e p x)} := by
    have hd := law_distance_le_disagreement μ
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e (hq n)))
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e hp)) hD
    have hr : Measurable (s.restrict : (ℤ → A) → (s → A)) := measurable_restrict (s : Set ℤ)
    have hmap (u : X → A) (hu : Measurable u) :
        (μ.map (s.restrict ∘ orbitName e u)).real D=
          (μ.map (orbitName e u)).real (Set.pi s t) := by
      simp only [Measure.real]
      rw [←Measure.map_map hr (measurable_orbitName e hu),Measure.map_apply hr hD,hpre]
    change |(μ.map (s.restrict ∘ orbitName e (q n))).real D-
      (μ.map (s.restrict ∘ orbitName e p)).real D|≤_ at hd
    rw [hmap (q n) (hq n),hmap p hp] at hd
    exact hd
  have hz := squeeze_zero (fun n => abs_nonneg _ ) hdist
    (finite_code_error_tendsto_zero e he hq hp hlim s)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using hz)

theorem iid_law_of_partition_limit {μ : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (β : Measure A) [IsProbabilityMeasure β]
    (hblock : ∀ (s : Finset ℤ) (t : ℤ → Set A),(∀ i,MeasurableSet (t i)) →
      Tendsto (fun n => (μ.map (orbitName e (q n))).real (Set.pi s t)) atTop
        (𝓝 ((∏ i∈s,β (t i)).toReal))) :
    MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)) := by
  refine ⟨measurable_orbitName e hp,Measure.eq_infinitePi _ ?_⟩
  intro s t ht
  have h := tendsto_nhds_unique (finite_box_law_tendsto e he hq hp hlim s t ht) (hblock s t ht)
  have hf : (∏ i∈s,β (t i))≠⊤ := by
    rw [←Measure.infinitePi_pi (fun _ : ℤ => β) (fun i _ => ht i)]
    exact measure_ne_top _ _
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hf).mp h

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [MeasurableSpace.CountablySeparated Y] [MeasurableEq Y]

theorem measurable_decoder_of_conull_injective (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → Y) (hf : Measurable f) {S : Set X} (hS : MeasurableSet S)
    (hSae : ∀ᵐ x ∂μ,x∈S) (hinj : Set.InjOn f S) :
    ∃ d : Y → X,MeasurePreserving d (μ.map f) μ ∧
      (∀ᵐ x ∂μ,d (f x)=x) ∧ (∀ᵐ y ∂μ.map f,f (d y)=y) := by
  let _ : StandardBorelSpace S := hS.standardBorel
  let _ : Nonempty S := by obtain ⟨x,hx⟩ := hSae.exists; exact ⟨⟨x,hx⟩⟩
  let r : S → Y := fun x => f x
  have hr : MeasurableEmbedding r := (hf.comp measurable_subtype_coe).measurableEmbedding (by
    intro x y h
    exact Subtype.ext (hinj x.property y.property h))
  let d : Y → X := fun y => (hr.invFun y).val
  have hd : Measurable d := measurable_subtype_coe.comp hr.measurable_invFun
  have hl : ∀ᵐ x ∂μ,d (f x)=x := by
    filter_upwards [hSae] with x hx
    exact congrArg Subtype.val (hr.leftInverse_invFun ⟨x,hx⟩)
  have hmp : MeasurePreserving d (μ.map f) μ := by
    refine ⟨hd,?_⟩
    rw [Measure.map_map hd hf]
    have hm : d ∘ f =ᵐ[μ] id := hl
    exact (Measure.map_congr hm).trans (Measure.map_id)
  refine ⟨d,hmp,hl,?_⟩
  apply (ae_map_iff hf.aemeasurable (measurableSet_eq_fun (hf.comp hd) measurable_id)).mpr
  filter_upwards [hl] with x hx
  exact congrArg f hx

theorem measurable_decoder_of_countable_factors {I C : Type*} [Countable I]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)
    (α : I → X → C) (hsep : Function.Injective (fun x => fun i => α i x))
    (hfac : ∀ i,∃ g : Y → C,∀ᵐ x ∂μ,α i x=g (f x)) :
    ∃ d : Y → X,MeasurePreserving d (μ.map f) μ ∧
      (∀ᵐ x ∂μ,d (f x)=x) ∧ (∀ᵐ y ∂μ.map f,f (d y)=y) := by
  choose g hg using hfac
  have hAE : ∀ᵐ x ∂μ,∀ i,α i x=g i (f x) := ae_all_iff.mpr hg
  obtain ⟨S,hSae,hSm,hS⟩ := IsMeasurablyGenerated.exists_measurable_subset hAE
  apply measurable_decoder_of_conull_injective μ f hf hSm hSae
  intro x hx y hy hxy
  apply hsep
  funext i
  exact (hS hx i).trans ((congrArg (g i) hxy).trans (hS hy i).symm)

theorem measurable_decoder_of_generating_approximations {I C : Type*} [Countable I]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [Nonempty C]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)
    (α : I → X → C) (hsep : Function.Injective (fun x => fun i => α i x))
    (happ : ∀ i,∀ ε : ℝ,0<ε → ∃ g : Y → C,Measurable g ∧
      μ {x | g (f x)≠α i x}<ENNReal.ofReal ε) :
    ∃ d : Y → X,MeasurePreserving d (μ.map f) μ ∧
      (∀ᵐ x ∂μ,d (f x)=x) ∧ (∀ᵐ y ∂μ.map f,f (d y)=y) := by
  apply measurable_decoder_of_countable_factors μ f hf α hsep
  intro i
  obtain ⟨g,_hgm,hg⟩ := exists_factor_of_approx μ f (α i) (happ i)
  exact ⟨g,hg⟩

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

lemma LawClose.nonneg {ν η : Measure X} {ε : ℝ} (h : LawClose ν η ε) : 0≤ε := by
  simpa using h ∅ MeasurableSet.empty

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

lemma productWeights_sum (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1) :
    ∑ D,productWeights w D=1 := by
  unfold productWeights
  rw [←Fintype.prod_sum]
  simp only [hw,Finset.prod_const_one]

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

theorem exists_power (r : MatrixCoupling p q) (hp : ∑ a,p a=1) :
    ∀ n : ℕ,∃ R : MatrixCoupling (fun w : Fin n → A => ∏ j,p (w j))
      (fun w : Fin n → A => ∏ j,q (w j)),R.cost nameCost=(n : ℝ)*r.cost symbolCost := by
  classical
  intro n
  induction n with
  | zero =>
    let R : MatrixCoupling (fun w : Fin 0 → A => ∏ j,p (w j)) (fun w : Fin 0 → A => ∏ j,q (w j)) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun _ => by simp
      col := fun _ => by simp }
    refine ⟨R,?_⟩
    simp [cost,nameCost]
  | succ n ih =>
    obtain ⟨R,hR⟩ := ih
    let S := r.product R
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := S.reindex e.symm e.symm
    let T : MatrixCoupling (fun w : Fin (n+1) → A => ∏ j,p (w j))
        (fun w : Fin (n+1) → A => ∏ j,q (w j)) := {
      weight := t.weight
      nonneg := t.nonneg
      row := fun w => (t.row w).trans (by exact (Fin.prod_univ_succ (fun j => p (w j))).symm)
      col := fun w => (t.col w).trans (by exact (Fin.prod_univ_succ (fun j => q (w j))).symm) }
    have he : (nameCost : (Fin (n+1) → A) → (Fin (n+1) → A) → ℝ)=
        (fun v w => symbolCost (e.symm v).1 (e.symm w).1+nameCost (e.symm v).2 (e.symm w).2) := by
      funext v w
      rw [nameCost,Fin.sum_univ_succ]
      rfl
    have hmass : (∑ w : Fin n → A,∏ j,p (w j))=1 :=
      productWeights_sum (fun _ : Fin n => p) (fun _ => hp)
    refine ⟨T,?_⟩
    change t.cost nameCost=_
    rw [he,MatrixCoupling.reindex_cost S e.symm e.symm
      (fun a b : A×(Fin n → A) => symbolCost a.1 b.1+nameCost a.2 b.2)]
    rw [MatrixCoupling.product_cost r R hp hmass symbolCost nameCost,hR]
    push_cast
    ring

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

theorem chunk_process_transport {X Y A : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (T : Y → Y) (hT : MeasurePreserving T ν ν) (q : Y → A) (hq : Measurable q)
    (k g : ℕ) {εP εQ δ : ℝ}
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) εP)
    (hQ : ∀ M : ℕ,LawClose
      (ν.map (fun x => (word T q M (T^[k+g] x),word T q k x)))
      ((ν.map (fun x => word T q M (T^[k+g] x))).prod (ν.map (word T q k))) εQ)
    (hlaw : LawClose (μ.map (word f p k)) (ν.map (word T q k)) δ) :
    ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (mass ν (finiteName (chunkObservation T q k g) 0 n)),
      R.cost nameCost≤(n : ℝ)*(εP+δ+εQ) := by
  intro n
  obtain ⟨RP,hRP⟩ := stationary_chunk_coupling μ f hf p hp k g hP n
  obtain ⟨RQ,hRQ⟩ := stationary_chunk_coupling ν T hT q hq k g hQ n
  obtain ⟨r,hr⟩ := coupling_of_observation_lawClose μ ν (word f p k) (word T q k)
    (word_measurable f hf.measurable p hp k) (word_measurable T hT.measurable q hq k) hlaw
  obtain ⟨S,hS⟩ := r.exists_power (by
    simp only [mass_sum μ (word f p k) (word_measurable f hf.measurable p hp k),
      measure_univ,ENNReal.toReal_one]) n
  refine ⟨(RP.comp S).comp RQ.symm,?_⟩
  have h1 := MatrixCoupling.comp_cost_le RP S nameCost nameCost nameCost nameCost_triangle
  have h2 := MatrixCoupling.comp_cost_le (RP.comp S) RQ.symm nameCost nameCost nameCost nameCost_triangle
  rw [MatrixCoupling.symm_cost RQ nameCost nameCost_comm] at h2
  rw [hS] at h1
  have h3 := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg n)
  nlinarith

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
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators

theorem full_word_transport {X Y A : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (T : Y → Y) (hT : MeasurePreserving T ν ν) (q : Y → A) (hq : Measurable q)
    (k g : ℕ) {εP εQ δ : ℝ}
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) εP)
    (hQ : ∀ M : ℕ,LawClose
      (ν.map (fun x => (word T q M (T^[k+g] x),word T q k x)))
      ((ν.map (fun x => word T q M (T^[k+g] x))).prod (ν.map (word T q k))) εQ)
    (hlaw : LawClose (μ.map (word f p k)) (ν.map (word T q k)) δ) :
    ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word f p (n*(k+g))))
      (mass ν (word T q (n*(k+g)))),
      R.cost nameCost≤(n : ℝ)*((k : ℝ)*(εP+δ+εQ)+(g : ℝ)) := by
  intro n
  obtain ⟨S,hS⟩ := chunk_process_transport μ ν f hf p hp T hT q hq k g hP hQ hlaw n
  have hPsel : selectChunks k g n ∘ word f p (n*(k+g))=
      finiteName (chunkObservation f p k g) 0 n := funext (selectChunks_word f p k g n)
  have hQsel : selectChunks k g n ∘ word T q (n*(k+g))=
      finiteName (chunkObservation T q k g) 0 n := funext (selectChunks_word T q k g n)
  let S' : MatrixCoupling (mass μ (selectChunks k g n ∘ word f p (n*(k+g))))
      (mass ν (selectChunks k g n ∘ word T q (n*(k+g)))) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun w => by rw [hPsel]; exact S.row w
    col := fun w => by rw [hQsel]; exact S.col w }
  obtain ⟨R,hR⟩ := lift_observation_transport μ ν (word f p (n*(k+g))) (word T q (n*(k+g)))
    (word_measurable f hf.measurable p hp _) (word_measurable T hT.measurable q hq _)
    (selectChunks k g n) S' nameCost nameCost_self nameCost_triangle
  refine ⟨R,?_⟩
  have hmass : (∑ v,mass μ (word f p (n*(k+g))) v)=1 := by
    simp only [mass_sum μ _ (word_measurable f hf.measurable p hp _),measure_univ,ENNReal.toReal_one]
  have hbd := R.cost_mono nameCost
    (fun v w => (k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ))
    (nameCost_le_retained_chunks k g n)
  rw [R.cost_affine hmass] at hbd
  have hk0 : 0≤(k : ℝ) := Nat.cast_nonneg k
  have h1 := mul_le_mul_of_nonneg_left hR hk0
  have hS' : S'.cost nameCost≤(n : ℝ)*(εP+δ+εQ) := hS
  have h2 := mul_le_mul_of_nonneg_left hS' hk0
  push_cast at hbd
  nlinarith

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

theorem obs_continuity_in_law (μ : Measure X) (p : X → A) (hp : Measurable p)
    {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧
    ∀ (ν : Measure Y) (q : Y → A),Measurable q → LawClose (μ.map p) (ν.map q) δ →
      |obs μ p-obs ν q|<ε := by
  obtain ⟨δ,hδ,hh⟩ := finite_entropy_continuity (μ.map p) hε
  refine ⟨δ,hδ,?_⟩
  intro ν q hq hclose
  rw [obs_eq_entropy_map μ p hp,obs_eq_entropy_map ν q hq]
  exact hh _ hclose

end StandardMapEntropy.Entropy

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
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped Topology ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem uniform_remote_from_finite_entropy
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L : ℕ) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose
      (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p L (f^[k+g] x))).prod (μ.map (word f p k))) ε)
    (hdef : 4*(cond μ (word f p (k+g))
      (fun x => word f p L (f^[k+g] x))-(k+g : ℕ)*rate μ f p)≤δ^2) :
    ∀ M : ℕ,L≤M → LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) (δ+2*ε) := by
  intro M hLM
  let rM : X → (Fin M → A) := fun x => word f p M (f^[k+g] x)
  let c : (Fin M → A) → (Fin L → A) := fun w i => w (Fin.castLE hLM i)
  let d : (Fin (k+g) → A) → (Fin k → A) := fun w i => w (Fin.castLE (Nat.le_add_right k g) i)
  have hrM : Measurable rM := (word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate (k+g))
  have hc : c ∘ rM=(fun x => word f p L (f^[k+g] x)) := by funext x i; rfl
  have hd : d ∘ word f p (k+g)=word f p k := by funext x i; rfl
  have hdata := conditional_defect_data_processing μ rM (word f p (k+g)) c d
    hrM (word_measurable f hf.measurable p hp (k+g))
  rw [hd,hc] at hdata
  have hlower := rate_mul_le_cond_future μ f hf p hp (k+g) M
  have hdef' : 4*(cond μ (word f p k) (c ∘ rM)-cond μ (word f p k) rM)≤δ^2 := by
    rw [hc]
    change (k+g : ℕ)*rate μ f p ≤ cond μ (word f p (k+g)) rM at hlower
    linarith
  apply lawClose_of_coarse_independence μ rM (word f p k) c hrM
    (word_measurable f hf.measurable p hp k) hδ
  · exact hclose
  · exact hdef'

theorem eventually_finite_entropy_test
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ L : ℕ in atTop,4*(cond μ (word f p n)
      (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p)<δ^2 := by
  have ht := ((cond_future_tendsto μ f hf p hp n).sub_const ((n : ℝ)*rate μ f p)).const_mul 4
  have he : (4 : ℝ)*((n : ℝ)*rate μ f p-(n : ℝ)*rate μ f p)=0 := by ring
  rw [he] at ht
  exact ht.eventually (gt_mem_nhds (sq_pos_of_pos hδ))

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

namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped ENNReal Topology
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem finite_entropy_test_open (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (n L : ℕ) {r : ℝ}
    (hr : cond μ (word f p n) (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p < r) :
    ∃ δ : ℝ,0<δ ∧ ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν)
      (T : Y → Y) (_ : MeasurePreserving T ν ν) (q : Y → A),Measurable q →
      LawClose (μ.map (word f p (n+L))) (ν.map (word T q (n+L))) δ →
      rate μ f p-δ ≤ rate ν T q →
      cond ν (word T q n) (fun y => word T q L (T^[n] y))-(n : ℝ)*rate ν T q < r := by
  let D := cond μ (word f p n) (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p
  let γ := (r-D)/(2*((n : ℝ)+2))
  have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
  have hγ : 0<γ := div_pos (sub_pos.mpr hr) (by positivity)
  obtain ⟨δW,hδW,hW⟩ := obs_continuity_in_law (Y:=Y) μ (word f p (n+L))
    (word_measurable f hf.measurable p hp (n+L)) hγ
  obtain ⟨δL,hδL,hL⟩ := obs_continuity_in_law (Y:=Y) μ (word f p L)
    (word_measurable f hf.measurable p hp L) hγ
  let δ := min γ (min δW δL)
  have hδ : 0<δ := lt_min hγ (lt_min hδW hδL)
  refine ⟨δ,hδ,?_⟩
  intro ν hν T hT q hq hclose hrate
  let : IsProbabilityMeasure ν := hν
  have hW' := hW ν (word T q (n+L)) (word_measurable T hT.measurable q hq (n+L))
    (hclose.mono ((min_le_right γ (min δW δL)).trans (min_le_left δW δL)))
  let c : (Fin (n+L) → A) → (Fin L → A) := fun w i => w (Fin.castLE (Nat.le_add_left L n) i)
  have hshort := hclose.map (measurable_of_countable c)
  rw [Measure.map_map (measurable_of_countable c) (word_measurable f hf.measurable p hp (n+L)),
    Measure.map_map (measurable_of_countable c) (word_measurable T hT.measurable q hq (n+L))] at hshort
  change LawClose (μ.map (word f p L)) (ν.map (word T q L)) δ at hshort
  have hL' := hL ν (word T q L) (word_measurable T hT.measurable q hq L)
    (hshort.mono ((min_le_right γ (min δW δL)).trans (min_le_right δW δL)))
  have hδγ : δ≤γ := min_le_left _ _
  have hmargin : ((n : ℝ)+2)*γ=(r-D)/2 := by dsimp [γ]; field_simp
  have hmul := mul_le_mul_of_nonneg_left (show rate μ f p-γ ≤ rate ν T q by linarith) hn
  obtain ⟨hWlo,hWhi⟩ := abs_lt.mp hW'
  obtain ⟨hLlo,hLhi⟩ := abs_lt.mp hL'
  rw [cond_word_future_eq ν T hT q hq]
  have hD : D=obs μ (word f p (n+L))-obs μ (word f p L)-(n : ℝ)*rate μ f p := by
    dsimp [D]
    rw [cond_word_future_eq μ f hf p hp]
  nlinarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem all_remote_from_finite_entropy
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L : ℕ) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose
      (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p L (f^[k+g] x))).prod (μ.map (word f p k))) ε)
    (hdef : 4*(cond μ (word f p (k+g))
      (fun x => word f p L (f^[k+g] x))-(k+g : ℕ)*rate μ f p)≤δ^2) :
    ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) (δ+2*ε) := by
  intro M
  by_cases hLM : L≤M
  · exact uniform_remote_from_finite_entropy μ f hf p hp k g L hδ hclose hdef M hLM
  · have hML : M≤L := by omega
    let c : (Fin L → A) → (Fin M → A) := fun w i => w (Fin.castLE hML i)
    have h := lawClose_pair_factor_left μ (fun x => word f p L (f^[k+g] x))
      (word f p k) c ((word_measurable f hf.measurable p hp L).comp (hf.measurable.iterate (k+g)))
      (word_measurable f hf.measurable p hp k) (measurable_of_countable c) hclose
    have hε : 0≤ε := hclose.nonneg
    exact h.mono (by linarith)

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped ENNReal Topology BigOperators

lemma lawClose_prefix {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) (f : X → X) (T : Y → Y)
    (hf : Measurable f) (hT : Measurable T) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) {m n : ℕ} (hmn : m≤n) {δ : ℝ}
    (h : LawClose (μ.map (word f p n)) (ν.map (word T q n)) δ) :
    LawClose (μ.map (word f p m)) (ν.map (word T q m)) δ := by
  let c : (Fin n → A) → (Fin m → A) := fun w i => w (Fin.castLE hmn i)
  have hc : Measurable c := measurable_of_countable c
  have hh := h.map hc
  rw [Measure.map_map hc (word_measurable f hf p hp n),
    Measure.map_map hc (word_measurable T hT q hq n)] at hh
  exact hh

lemma lawClose_remote_of_word {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) (f : X → X) (T : Y → Y)
    (hf : Measurable f) (hT : Measurable T) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (k g L : ℕ) {δ : ℝ}
    (h : LawClose (μ.map (word f p ((k+g)+L))) (ν.map (word T q ((k+g)+L))) δ) :
    LawClose (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      (ν.map (fun x => (word T q L (T^[k+g] x),word T q k x))) δ := by
  let c : (Fin ((k+g)+L) → A) → ((Fin L → A)×(Fin k → A)) :=
    fun w => (fun i => w ⟨i.val+(k+g),by omega⟩,fun i => w ⟨i.val,by omega⟩)
  have hc : Measurable c := measurable_of_countable c
  have hh := h.map hc
  rw [Measure.map_map hc (word_measurable f hf p hp _),
    Measure.map_map hc (word_measurable T hT q hq _)] at hh
  have he (x : X) : c (word f p ((k+g)+L) x)=(word f p L (f^[k+g] x),word f p k x) := by
    apply Prod.ext
    · funext i
      exact congrArg p (Function.iterate_add_apply f i.val (k+g) x)
    · rfl
  have he' (y : Y) : c (word T q ((k+g)+L) y)=(word T q L (T^[k+g] y),word T q k y) := by
    apply Prod.ext
    · funext i
      exact congrArg q (Function.iterate_add_apply T i.val (k+g) y)
    · rfl
  simpa only [Function.comp_def,he,he'] using hh

theorem weakBernoulli_finite_determination {X Y A : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (hwb : WeakBernoulliProcess μ e p) {η : ℝ} (hη : 0<η) :
    ∃ m s : ℕ,0 < s ∧ ∃ δ : ℝ,0<δ ∧
      ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν) (_ : NullSingletonClass ν)
        (T : Y → Y) (_ : MeasurePreserving T ν ν) (q : Y → A),Measurable q →
        LawClose (μ.map (word e p m)) (ν.map (word T q m)) δ →
        rate μ e p-δ ≤ rate ν T q →
        ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word e p (n*s))) (mass ν (word T q (n*s))),
          R.cost nameCost≤η*(n*s : ℕ) := by
  let ε : ℝ := η/100
  have hε : 0<ε := div_pos hη (by norm_num)
  obtain ⟨g,hg⟩ := weakBernoulli_forward_blocks μ e he p hp hwb hε
  obtain ⟨k,hk⟩ := exists_nat_gt ((g : ℝ)/ε+1)
  have hkpos : 0<k := by
    have hg0 : 0≤(g : ℝ)/ε := div_nonneg (Nat.cast_nonneg g) hε.le
    have hkR : 0<(k : ℝ) := by linarith
    exact_mod_cast hkR
  have hkg : (g : ℝ)≤ε*(k : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp (show (g : ℝ)/ε<(k : ℝ) by linarith)
    nlinarith
  obtain ⟨L,hL⟩ := (eventually_finite_entropy_test μ e he p hp (k+g) hε).exists
  obtain ⟨δ₀,hδ₀,hopen⟩ := finite_entropy_test_open (Y:=Y) μ e he p hp (k+g) L
    (r:=ε^2/4) (by linarith)
  let δ := min ε δ₀
  have hδ : 0<δ := lt_min hε hδ₀
  refine ⟨(k+g)+L,k+g,by omega,δ,hδ,?_⟩
  intro ν hν hnonatomic T hT q hq hclose hrate n
  let : IsProbabilityMeasure ν := hν
  let : NullSingletonClass ν := hnonatomic
  have hdε : δ≤ε := min_le_left _ _
  have hd₀ : δ≤δ₀ := min_le_right _ _
  have hd := hopen ν hν T hT q hq (hclose.mono hd₀) (by linarith)
  have hj := lawClose_remote_of_word μ ν e T he.measurable hT.measurable p q hp hq k g L hclose
  have hfinite := independence_law_stable μ ν
    (fun x => word e p L (e^[k+g] x)) (word e p k)
    (fun y => word T q L (T^[k+g] y)) (word T q k)
    ((word_measurable e he.measurable p hp L).comp (he.measurable.iterate _))
    (word_measurable e he.measurable p hp k)
    ((word_measurable T hT.measurable q hq L).comp (hT.measurable.iterate _))
    (word_measurable T hT.measurable q hq k) hj (hg k L)
  have hremoteQ := all_remote_from_finite_entropy ν T hT q hq k g L hε.le hfinite
    (show 4*(cond ν (word T q (k+g)) (fun y => word T q L (T^[k+g] y))-
      (k+g : ℕ)*rate ν T q)≤ε^2 by linarith)
  have hshort := lawClose_prefix μ ν e T he.measurable hT.measurable p q hp hq
    (show k≤(k+g)+L by omega) hclose
  obtain ⟨R,hR⟩ := full_word_transport μ ν e he p hp T hT q hq k g (hg k) hremoteQ hshort n
  refine ⟨R,hR.trans ?_⟩
  have hb : (k : ℝ)*(ε+δ+(ε+2*(ε+3*δ)))+(g : ℝ)≤η*(k+g : ℕ) := by
    have hk0 : 0≤(k : ℝ) := Nat.cast_nonneg k
    have hg0 : 0≤(g : ℝ) := Nat.cast_nonneg g
    have hsmall : ε+δ+(ε+2*(ε+3*δ))≤11*ε := by linarith
    have hh := mul_le_mul_of_nonneg_left hsmall hk0
    have hηε : η=100*ε := by dsimp [ε]; ring
    push_cast
    rw [hηε]
    nlinarith [mul_nonneg hε.le hk0,mul_nonneg hε.le hg0]
  have hn := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
  push_cast at hn ⊢
  nlinarith

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

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_disjoint_coordinate_independent {I J : Type*} (β : Measure A) [IsProbabilityMeasure β]
    (f : I → ℤ) (g : J → ℤ) (hfg : ∀ i j,f i≠g j) :
    IndepFun (fun w : ℤ → A => fun i => w (f i)) (fun w : ℤ → A => fun j => w (g j))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
  classical
  apply IndepFun.process_indepFun_process (fun i => measurable_pi_apply (f i))
    (fun j => measurable_pi_apply (g j))
  intro S T
  have hST : Disjoint (S.image f) (T.image g) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hz'
    exact hfg i j he.symm
  have h := (iIndepFun_infinitePi (P:=fun _ : ℤ => β) (X:=fun _ a => a)
    (fun _ => measurable_id)).indepFun_finset (S.image f) (T.image g) hST
    (fun _ => measurable_pi_apply _)
  let F : ((S.image f) → A) → (S → A) := fun w i => w ⟨f i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩
  let G : ((T.image g) → A) → (T → A) := fun w j => w ⟨g j,Finset.mem_image.mpr ⟨j,j.2,rfl⟩⟩
  exact h.comp (Measurable.of_eval (fun _ => measurable_pi_apply _))
    (Measurable.of_eval (fun _ => measurable_pi_apply _)) (φ:=F) (ψ:=G)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_symm_iterate (w : ℤ → A) (n : ℕ) (i : ℤ) :
    (iidShift.symm^[n]) w i=w (i-n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (iidShift.symm^[n]) w (i-1)=_
    rw [ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_tail_eq (w : ℤ → A) (n : ℕ) :
    tailName iidShift (fun w : ℤ → A => w 0) n w=fun i : ℕ => w ((i+n : ℕ) : ℤ) := by
  funext i
  simp only [tailName,iidShift_iterate,zero_add]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_past_eq (w : ℤ → A) (n : ℕ) :
    tailName iidShift.symm (fun w : ℤ → A => w 0) n w=fun i : ℕ => w (-((i+n : ℕ) : ℤ)) := by
  funext i
  simp only [tailName,iidShift_symm_iterate,zero_sub]

omit [Fintype A] [MeasurableSingletonClass A] in
theorem iid_weakBernoulli (β : Measure A) [IsProbabilityMeasure β] :
    WeakBernoulliProcess (Measure.infinitePi (fun _ : ℤ => β)) iidShift (fun w : ℤ → A => w 0) := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 1] with n hn
  let μ := Measure.infinitePi (fun _ : ℤ => β)
  have hi := iid_disjoint_coordinate_independent β (fun i : ℕ => -((i+n : ℕ) : ℤ))
    (fun i : ℕ => ((i+n : ℕ) : ℤ)) (by intro i j h; omega)
  have hp : IndepFun (tailName iidShift.symm (fun w : ℤ → A => w 0) n)
      (tailName iidShift (fun w : ℤ → A => w 0) n) μ := by
    have hP : tailName iidShift.symm (fun w : ℤ → A => w 0) n=
        fun w : ℤ → A => fun i : ℕ => w (-((i+n : ℕ) : ℤ)) := funext (fun w => iid_past_eq w n)
    have hF : tailName iidShift (fun w : ℤ → A => w 0) n=
        fun w : ℤ → A => fun i : ℕ => w ((i+n : ℕ) : ℤ) := funext (fun w => iid_tail_eq w n)
    rw [hP,hF]
    exact hi
  have hmap := hp.map_prod_eq_prod_map_map
    (measurable_tailName iidShift.symm.measurable (measurable_pi_apply 0) n).aemeasurable
    (measurable_tailName iidShift.measurable (measurable_pi_apply 0) n).aemeasurable
  have hpres := iidShift_preserving β
  rw [stationary_tail_law μ (hpres.symm iidShift) (measurable_pi_apply 0) n,
    stationary_tail_law μ hpres (measurable_pi_apply 0) n] at hmap
  have heq : μ.map (remotePair iidShift iidShift.symm (fun w : ℤ → A => w 0) n)=
      remoteProductLaw μ iidShift iidShift.symm (fun w : ℤ → A => w 0) := hmap
  change LawClose (μ.map (remotePair iidShift iidShift.symm (fun w : ℤ → A => w 0) n))
    (remoteProductLaw μ iidShift iidShift.symm (fun w : ℤ → A => w 0)) ε
  rw [heq]
  intro D _
  simpa only [sub_self,abs_zero] using hε.le

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

theorem iid_finite_determination {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Nonempty A] [DecidableEq A]
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) {η : ℝ} (hη : 0 < η) :
    ∃ m s : ℕ,0 < s ∧ ∃ δ : ℝ,0 < δ ∧
      ∀ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : NullSingletonClass μ)
        (f : X → X) (_ : MeasurePreserving f μ μ) (q : X → A),Measurable q →
        LawClose (μ.map (word f q m)) (Measure.pi (fun _ : Fin m => finiteWeightLaw β)) δ →
        weightEntropy β-δ ≤ rate μ f q →
        ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word f q (n*s))) (productWordWeight β (n*s)),
          R.cost nameCost≤η*(n*s : ℕ) := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  let : NullSingletonClass ν := iid_nullSingleton β hβ hβsum hβentropy
  obtain ⟨m,s,hs,δ,hδ,hfd⟩ := weakBernoulli_finite_determination (Y:=X) ν iidShift
    (iidShift_preserving _) (fun w : ℤ → A => w 0) (measurable_pi_apply 0)
    (iid_weakBernoulli _) hη
  refine ⟨m,s,hs,δ,hδ,?_⟩
  intro μ hμ hnull f hf q hq hlaw hrate n
  let : IsProbabilityMeasure μ := hμ
  let : NullSingletonClass μ := hnull
  have hclose : LawClose (ν.map (word iidShift (fun w : ℤ → A => w 0) m))
      (μ.map (word f q m)) δ := by
    rw [iid_word_law]
    exact hlaw.symm
  have hrate' : rate ν iidShift (fun w : ℤ → A => w 0)-δ ≤ rate μ f q := by
    simpa only [ν,iid_rate β hβ hβsum] using hrate
  obtain ⟨R,hR⟩ := hfd μ hμ hnull f hf q hq hclose hrate' n
  have hR' : R.symm.cost nameCost≤η*(n*s : ℕ) := by
    rw [MatrixCoupling.symm_cost R nameCost nameCost_comm]
    exact hR
  have heq : mass ν (word iidShift (fun w : ℤ → A => w 0) (n*s)) =
      productWordWeight β (n*s) := funext (iid_word_mass β hβ hβsum (n*s))
  rw [←heq]
  exact ⟨R.symm,hR'⟩

end HyperbolicCoding

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
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

lemma exists_iidCopyTest (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) {η : ℝ} (hη : 0 < η) :
    Nonempty (IIDCopyTest μ e β η) := by
  obtain ⟨m,t,ht,δ,hδ,hfd⟩ := iid_finite_determination (X:=X) β hβ hβsum hβentropy hη
  exact ⟨⟨m,t,ht,δ,hδ,fun q hq hl hr => hfd μ inferInstance inferInstance e he q hq hl hr⟩⟩

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
  [OpensMeasurableSpace X] [DecidableEq A] [Nonempty A] in
lemma iid_lawClose_prefix (μ : Measure X) (e : X ≃ᵐ X) (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    {m n : ℕ} (hmn : m≤n) {δ : ℝ}
    (h : LawClose (μ.map (word e p n))
      (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) δ) :
    LawClose (μ.map (word e p m))
      (Measure.pi (fun _ : Fin m => finiteWeightLaw β)) δ := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  have h' : LawClose (μ.map (word e p n))
      (ν.map (word iidShift (fun w : ℤ → A => w 0) n)) δ := by
    simpa only [ν,iid_word_law] using h
  have hh := lawClose_prefix μ ν e iidShift e.measurable iidShift.measurable p
    (fun w : ℤ → A => w 0) hp (measurable_pi_apply 0) hmn h'
  simpa only [ν,iid_word_law] using hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_integerIterate (n : ℤ) (w : ℤ → A) (i : ℤ) :
    integerIterate iidShift n w i=w (i+n) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast,integerIterate_nat,iidShift_iterate]
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    rw [hn,integerIterate_neg_nat,iidShift_symm_iterate,sub_eq_add_neg]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_orbitName (w : ℤ → A) : orbitName iidShift (fun z : ℤ → A => z 0) w=w := by
  funext i
  exact (iidShift_integerIterate i w 0).trans (by rw [zero_add])

lemma finite_integer_window (s : Finset ℤ) :
    ∃ a : ℤ,∃ N : ℕ,∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ) := by
  let b := s.sup Int.natAbs
  refine ⟨-(b : ℤ),2*b+1,?_⟩
  intro i hi
  have hb : i.natAbs≤b := Finset.le_sup (f:=Int.natAbs) hi
  have hb' : (i.natAbs : ℤ)≤b := by exact_mod_cast hb
  have h1 : -i≤(i.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a:=-i))
  have h2 := (Int.le_natAbs (a:=i))
  constructor <;> omega

lemma orbit_restrict_map_eq_window (μ : Measure X) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (s : Finset ℤ) (a : ℤ) (N : ℕ) (hb : ∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ)) :
    μ.map (s.restrict ∘ orbitName e p)=
      (μ.map (word e p N)).map (fun w : Fin N → A => fun i : s =>
        w ⟨(i.val-a).toNat,by have h := hb i.val i.property; omega⟩) := by
  let W : (Fin N → A) → (s → A) := fun w i =>
    w ⟨(i.val-a).toNat,by have h := hb i.val i.property; omega⟩
  have hW : Measurable W := measurable_of_finite W
  have hpN := word_measurable e e.measurable p hp N
  have hfun : s.restrict ∘ orbitName e p=(W ∘ word e p N) ∘ integerIterate e a := by
    funext x i
    change p (integerIterate e i.val x) = p (e^[((i.val-a).toNat)] (integerIterate e a x))
    rw [←integerIterate_nat,←integerIterate_add]
    have h := hb i.val i.property
    congr 2
    omega
  change μ.map (s.restrict ∘ orbitName e p)=(μ.map (word e p N)).map W
  rw [hfun,←Measure.map_map (hW.comp hpN) (integerIterate_measurable e a),
    (integerIterate_measurePreserving e he a).map_eq,Measure.map_map hW hpN]

lemma lawClose_orbit_restrict_of_word
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ X) (d : Y ≃ᵐ Y)
    (he : MeasurePreserving e μ μ) (hd : MeasurePreserving d ν ν)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    (s : Finset ℤ) (a : ℤ) (N : ℕ) (hb : ∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ))
    {δ : ℝ} (hl : LawClose (μ.map (word e p N)) (ν.map (word d q N)) δ) :
    LawClose (μ.map (s.restrict ∘ orbitName e p))
      (ν.map (s.restrict ∘ orbitName d q)) δ := by
  rw [orbit_restrict_map_eq_window μ e he p hp s a N hb,
    orbit_restrict_map_eq_window ν d hd q hq s a N hb]
  exact hl.map (measurable_of_finite _)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma restricted_box_lawClose (μ : Measure X) (ν : Measure Y)
    (e : X ≃ᵐ X) (d : Y ≃ᵐ Y) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (s : Finset ℤ)
    (t : ℤ → Set A) (ht : ∀ i,MeasurableSet (t i)) {δ : ℝ}
    (h : LawClose (μ.map (s.restrict ∘ orbitName e p))
      (ν.map (s.restrict ∘ orbitName d q)) δ) :
    |(μ.map (orbitName e p)).real (Set.pi s t)-
      (ν.map (orbitName d q)).real (Set.pi s t)|≤δ := by
  let D : Set (s → A) := Set.pi Set.univ (fun i => t i.val)
  have hD : MeasurableSet D := MeasurableSet.pi Set.countable_univ (fun i _ => ht i.val)
  have hpre : (s.restrict : (ℤ → A) → (s → A)) ⁻¹' D=Set.pi s t := by
    ext w
    simp only [D,mem_preimage,Set.mem_pi,mem_univ,true_implies,Finset.mem_coe,Finset.restrict]
    exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.property⟩
  have hr : Measurable (s.restrict : (ℤ → A) → (s → A)) := measurable_restrict (s : Set ℤ)
  have h1 : (μ.map (s.restrict ∘ orbitName e p)).real D=
      (μ.map (orbitName e p)).real (Set.pi s t) := by
    simp only [Measure.real]
    rw [←Measure.map_map hr (measurable_orbitName e hp),Measure.map_apply hr hD,hpre]
  have h2 : (ν.map (s.restrict ∘ orbitName d q)).real D=
      (ν.map (orbitName d q)).real (Set.pi s t) := by
    simp only [Measure.real]
    rw [←Measure.map_map hr (measurable_orbitName d hq),Measure.map_apply hr hD,hpre]
  simpa only [h1,h2] using h D hD

theorem iid_law_of_growing_forward_words [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (q : ℕ → X → A) (hq : ∀ n,Measurable (q n))
    (p : X → A) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (β : Measure A) [IsProbabilityMeasure β] (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hlaw : ∀ n,LawClose (μ.map (word e (q n) n))
      (Measure.pi (fun _ : Fin n => β)) (ε n)) :
    MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)) := by
  apply iid_law_of_partition_limit e he hq hp hlim β
  intro s t ht
  let ν := Measure.infinitePi (fun _ : ℤ => β)
  obtain ⟨a,N,hN⟩ := finite_integer_window s
  have htarget : (ν.map (orbitName iidShift (fun w : ℤ → A => w 0))).real (Set.pi s t)=
      (∏ i∈s,β (t i)).toReal := by
    rw [show orbitName iidShift (fun w : ℤ → A => w 0)=id from funext iid_orbitName,
      Measure.map_id]
    exact congrArg ENNReal.toReal (Measure.infinitePi_pi (fun _ : ℤ => β) (fun i _ => ht i))
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(μ.map (orbitName e (q n))).real (Set.pi s t)-(∏ i∈s,β (t i)).toReal|≤ε n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hb : ∀ i∈s,0≤ i-a ∧ i-a < (n : ℤ) := by
      intro i hi
      have h := hN i hi
      exact ⟨h.1,lt_of_lt_of_le h.2 (by exact_mod_cast hn)⟩
    have hl : LawClose (μ.map (word e (q n) n))
        (ν.map (word iidShift (fun w : ℤ → A => w 0) n)) (ε n) := by
      simpa only [ν,iid_word_law] using hlaw n
    have hr := lawClose_orbit_restrict_of_word μ ν e iidShift he (iidShift_preserving β)
      (q n) (fun w : ℤ → A => w 0) (hq n) (measurable_pi_apply 0) s a n hb hl
    have hh := restricted_box_lawClose μ ν e iidShift (q n) (fun w : ℤ → A => w 0)
      (hq n) (measurable_pi_apply 0) s t ht hr
    rwa [htarget] at hh
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hε

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

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma geometric_repainting_summable (μ : Measure X) [IsFiniteMeasure μ]
    (q : ℕ → X → A)
    (h : ∀ n,μ.real {x | q (n+1) x≠q n x}<((1/2 : ℝ≥0)^n : ℝ)) :
    (∑' n : ℕ,μ {x | q (n+1) x≠q n x})≠⊤ := by
  have hs : (∑' n : ℕ,(((1/2 : ℝ≥0)^n) : ℝ≥0∞))≠⊤ := by
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr
    simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
      (summable_geometric_of_lt_one (show (0 : ℝ)≤1/2 by norm_num) (by norm_num : (1/2 : ℝ) < 1))
  apply ne_top_of_le_ne_top hs
  apply ENNReal.tsum_le_tsum
  intro n
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) (by simp)).mp
  simpa only [Measure.real,ENNReal.toReal_pow,ENNReal.coe_toReal,NNReal.coe_pow] using (h n).le

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

omit mX in
lemma joinedBinary_comap_monotone (α : ℕ → ℕ → X → Bool) :
    Monotone (fun N => MeasurableSpace.comap (joinedBinary α N) inferInstance) := by
  intro i j hij
  let r : ((Fin j×Fin j) → Bool) → ((Fin i×Fin i) → Bool) :=
    fun w p => w (p.1.castLE hij,p.2.castLE hij)
  have hF : Measurable[MeasurableSpace.comap (joinedBinary α j) inferInstance]
      (joinedBinary α j) := measurable_iff_comap_le.mpr le_rfl
  have hr := (measurable_of_countable r).comp hF
  exact measurable_iff_comap_le.mp hr

lemma joinedBinary_generates [StandardBorelSpace X]
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x)) :
    ‹MeasurableSpace X›=⨆ N,MeasurableSpace.comap (joinedBinary α N) inferInstance := by
  let F : X → ℕ → ℕ → Bool := fun x i j => α i j x
  have hF : Measurable F := Measurable.of_eval (fun index => Measurable.of_eval (hα index))
  have hFE : MeasurableEmbedding F := hF.measurableEmbedding hsep
  have heq : MeasurableSpace.comap F inferInstance = mX := hFE.comap_eq
  have hupper : (⨆ N,MeasurableSpace.comap (joinedBinary α N) inferInstance) ≤ mX := by
    apply iSup_le
    intro N
    exact measurable_iff_comap_le.mp (measurable_joinedBinary hα N)
  let m : MeasurableSpace X := ⨆ N,MeasurableSpace.comap (joinedBinary α N) inferInstance
  have hlarge (i j : ℕ) : @Measurable X Bool m inferInstance (α i j) := by
    let N := max i j+1
    let a : Fin N×Fin N := (⟨i,by dsimp [N]; omega⟩,⟨j,by dsimp [N]; omega⟩)
    have hN : @Measurable X ((Fin N×Fin N) → Bool) m inferInstance (joinedBinary α N) :=
      measurable_iff_comap_le.mpr
        (le_iSup (fun n => MeasurableSpace.comap (joinedBinary α n) inferInstance) N)
    exact (measurable_pi_apply a).comp hN
  have hsup : @Measurable X (ℕ → ℕ → Bool) m inferInstance F :=
    Measurable.of_eval (fun index => Measurable.of_eval (hlarge index))
  apply le_antisymm
  · have hle : MeasurableSpace.comap F inferInstance ≤ m := measurable_iff_comap_le.mp hsup
    exact (le_of_eq heq.symm).trans hle
  · exact hupper

theorem joinedBinary_approximates [StandardBorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ,∃ D : ((Fin N×Fin N) → Bool) → A,
      μ.real {x | D (joinedBinary α N x)≠p x}<ε :=
  finite_factor_approx μ (fun N => (Fin N×Fin N) → Bool) (joinedBinary α)
    (joinedBinary_comap_monotone α) (joinedBinary_generates α hα hsep) p hp hε
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
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B]

lemma WeakBernoulliProcess.factor [Fintype B] [MeasurableSingletonClass B]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (p : X → A) (hp : Measurable p) (hwb : WeakBernoulliProcess μ e p)
    (d : A → B) : WeakBernoulliProcess μ e (d ∘ p) := by
  let D : (ℕ → A) → (ℕ → B) := fun w i => d (w i)
  have hD : Measurable D := Measurable.of_eval
    (fun i => (measurable_of_countable d).comp (measurable_pi_apply i))
  intro ε hε
  filter_upwards [hwb ε hε] with n hn
  have h := hn.map (hD.prodMap hD)
  have hrem := measurable_remotePair e.measurable e.symm.measurable hp n
  have hlu := measurable_tailName e.symm.measurable hp 0
  have hru := measurable_tailName e.measurable hp 0
  rw [Measure.map_map (hD.prodMap hD) hrem] at h
  unfold remoteProductLaw at h
  rw [←Measure.map_prod_map _ _ hD hD,Measure.map_map hD hlu,Measure.map_map hD hru] at h
  exact h

theorem separating_wb_approximation [StandardBorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : X ≃ᵐ X)
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary α M))
    [Nonempty A] (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0<ε) :
    ∃ q : X → A,Measurable q ∧ WeakBernoulliProcess μ e q ∧ μ.real {x | q x≠p x}<ε := by
  obtain ⟨M,D,hD⟩ := joinedBinary_approximates μ α hα hsep p hp hε
  exact ⟨D ∘ joinedBinary α M,(measurable_of_countable D).comp (measurable_joinedBinary hα M),
    WeakBernoulliProcess.factor μ e (joinedBinary α M) (measurable_joinedBinary hα M) (hwb M) D,hD⟩
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
variable {X A B : Type*} [MeasurableSpace X] [MeasurableSpace B]

lemma disagreement_triangle [MeasurableSpace A]
    (μ : Measure X) [IsFiniteMeasure μ] (p q r : X → A) :
    μ.real {x | p x≠r x}≤μ.real {x | p x≠q x}+μ.real {x | q x≠r x} := by
  apply (measureReal_mono (μ:=μ) (show {x | p x≠r x}⊆{x | p x≠q x} ∪ {x | q x≠r x} from ?_)).trans
  · exact measureReal_union_le _ _
  · intro x hx
    by_cases h : p x=q x
    · exact Or.inr (by simpa only [mem_ofPred_eq,h] using hx)
    · exact Or.inl h

lemma disagreement_symm [MeasurableSpace A] (μ : Measure X) (p q : X → A) :
    μ.real {x | p x≠q x}=μ.real {x | q x≠p x} := by
  congr 1
  ext x
  exact ne_comm

variable [MeasurableSpace A]

lemma sequence_distance_le_sum (μ : Measure X) [IsFiniteMeasure μ]
    (q : ℕ → X → A) (η : ℕ → ℝ) (hη : ∀ n,μ.real {x | q n x≠q (n+1) x}≤η n) (n : ℕ) :
    μ.real {x | q 0 x≠q n x}≤∑ j∈Finset.range n,η j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (disagreement_triangle μ (q 0) (q n) (q (n+1))).trans (add_le_add ih (hη n))

lemma partition_limit_distance_bound [MeasurableEq A]
    (μ : Measure X) [IsFiniteMeasure μ] (q : ℕ → X → A) (p r : X → A)
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    {δ : ℝ} (hδ : ∀ n,μ.real {x | r x≠q n x}≤δ) :
    μ.real {x | r x≠p x}≤δ := by
  have hz := measureReal_tendsto_zero_of_ae_eventually_notMem μ
    (fun n => {x | q n x≠p x}) (fun n => (measurableSet_eq_fun (hq n) hp).compl)
    (hlim.mono (fun x hx => hx.mono (fun n hn => by simpa using hn)))
  have ht : Tendsto (fun n => μ.real {x | r x≠p x}-μ.real {x | q n x≠p x}) atTop
      (𝓝 (μ.real {x | r x≠p x})) := by simpa using tendsto_const_nhds.sub hz
  apply le_of_tendsto ht
  filter_upwards [] with n
  have h := disagreement_triangle μ r (q n) p
  linarith [hδ n]

lemma finite_decoder_perturbation [StandardBorelSpace X] [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X → X) (he : MeasurePreserving e μ μ)
    (p q : X → A) (hp : Measurable p) (hq : Measurable q)
    (α : X → B) (n : ℕ) (D : (Fin n → A) → B) :
    μ.real {x | α x≠D (word e q n x)}≤μ.real {x | α x≠D (word e p n x)}+
      (n : ℝ)*μ.real {x | p x≠q x} := by
  classical
  apply (disagreement_triangle μ α (D ∘ word e p n) (D ∘ word e q n)).trans
  apply add_le_add_right
  have hsub : {x | (D ∘ word e p n) x≠(D ∘ word e q n) x}⊆{x | word e p n x≠word e q n x} := by
    intro x h heq
    exact h (congrArg D heq)
  exact (measureReal_mono (μ:=μ) hsub).trans
    (word_disagreement_le μ e he p q hp hq n)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal NNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

theorem seeded_exact_iid_limit (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (H : FiniteRateSupremum μ e (weightEntropy β))
    (zero one : A) (h01 : zero≠one) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ,∃ δ : ℝ,0 < δ ∧ ∀ q₀ : X → A,Measurable q₀ →
      LawClose (μ.map (word e q₀ L)) (Measure.pi (fun _ : Fin L => finiteWeightLaw β)) δ →
      weightEntropy β-δ ≤ rate μ e q₀ →
      ∃ p : X → A,Measurable p ∧
        MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
        μ.real {x | q₀ x≠p x} < ε := by
  let θ : ℝ := min (ε/4) (1/4)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθε : 2*θ < ε := by have hh := min_le_left (ε/4) (1/4 : ℝ); dsimp [θ]; linarith
  have hθ1 : θ≤1 := (min_le_right _ _).trans (by norm_num)
  let η : ℕ → ℝ := fun n => θ*(1/2 : ℝ)^n
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hT (n : ℕ) : Nonempty (IIDCopyTest μ e β (η n/2)) :=
    exists_iidCopyTest μ e he.toMeasurePreserving β hβ hβsum hβentropy (half_pos (hη n))
  let T (n : ℕ) : IIDCopyTest μ e β (η n/2) := Classical.choice (hT n)
  refine ⟨max (T 0).length 0,min (T 0).tolerance 1,lt_min (T 0).tolerance_pos zero_lt_one,?_⟩
  intro q₀ hq₀ hl₀ hr₀
  have hg₀ : GoodIIDStage μ e β (T 0) 0 q₀ := by
    refine ⟨hq₀,?_,hr₀.trans' ?_⟩
    · simpa only [Nat.cast_zero,zero_add,div_one] using hl₀
    · linarith only [min_le_left (T 0).tolerance (1 : ℝ)]
  have hnext (n : ℕ) (q : {q : X → A // GoodIIDStage μ e β (T n) n q}) :
      ∃ q' : X → A,GoodIIDStage μ e β (T (n+1)) (n+1) q' ∧
        μ.real {x | q.val x≠q' x} < η n :=
    goodIIDStage_next_q44 μ e he htotal β hβ hβsum hβentropy H zero one h01 (hη n)
      (T n) (T (n+1)) q.property
  let next (n : ℕ) (q : {q : X → A // GoodIIDStage μ e β (T n) n q}) :
      {q' : X → A // GoodIIDStage μ e β (T (n+1)) (n+1) q'} :=
    ⟨Classical.choose (hnext n q),(Classical.choose_spec (hnext n q)).1⟩
  let z : (n : ℕ) → {q : X → A // GoodIIDStage μ e β (T n) n q} :=
    fun n => Nat.rec (motive:=fun j => {q : X → A // GoodIIDStage μ e β (T j) j q})
      ⟨q₀,hg₀⟩ next n
  let q : ℕ → X → A := fun n => (z n).val
  have hq (n : ℕ) : Measurable (q n) := (z n).property.1
  have hpaint (n : ℕ) : μ.real {x | q n x≠q (n+1) x} < η n :=
    (Classical.choose_spec (hnext n (z n))).2
  have hgeom (n : ℕ) : μ.real {x | q (n+1) x≠q n x} < ((1/2 : ℝ≥0)^n : ℝ) := by
    rw [disagreement_symm]
    apply (hpaint n).trans_le
    change θ*(1/2 : ℝ)^n≤_
    simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,one_mul] using
      mul_le_mul_of_nonneg_right hθ1 (by positivity : 0≤(1/2 : ℝ)^n)
  obtain ⟨p,hp,hlim⟩ := exists_partition_limit μ q hq (geometric_repainting_summable μ q hgeom)
  have hlaw (n : ℕ) : LawClose (μ.map (word e (q n) n))
      (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) (1/(n+1 : ℝ)) :=
    (iid_lawClose_prefix μ e (q n) (hq n) β hβ hβsum
      (le_max_right _ _) (z n).property.2.1).mono (min_le_right _ _)
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hcode := iid_law_of_growing_forward_words μ e he.toMeasurePreserving q hq p hp hlim
    (finiteWeightLaw β) (fun n => 1/(n+1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat hlaw
  refine ⟨p,hp,hcode,lt_of_le_of_lt ?_ hθε⟩
  apply partition_limit_distance_bound μ q p q₀ hq hp hlim
  intro n
  have hh := sequence_distance_le_sum μ q η (fun j => (hpaint j).le) n
  have hsum : (∑ j∈Finset.range n,η j)≤2*θ := by
    simp only [η,←Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hθ.le
    nlinarith only [h]
  exact hh.trans hsum
end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_CenteredDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma centeredWindow_orbit_shift [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (e : X ≃ᵐ X) (p : X → A) (R : ℕ) (x : X) :
    centeredWindow R (orbitName e p (e^[R] x))=word e p (2*R+1) x := by
  funext i
  change p (integerIterate e ((i.val : ℤ)-R) (e^[R] x))=p (e^[i.val] x)
  rw [←integerIterate_nat e R x,←integerIterate_add,sub_add_cancel,integerIterate_nat]

variable [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma centered_decoder_error_eq (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → B) (p : X → A) (hα : Measurable α) (hp : Measurable p)
    (R : ℕ) (D : (Fin (2*R+1) → A) → B) :
    μ.real {x | α x≠D (centeredWindow R (orbitName e p x))}=
      μ.real {x | α (e^[R] x)≠D (word e p (2*R+1) x)} := by
  have hD : Measurable (fun x => D (centeredWindow R (orbitName e p x))) :=
    (measurable_of_countable D).comp ((measurable_centeredWindow R).comp (measurable_orbitName e hp))
  have hset : {x | α (e^[R] x)≠D (word e p (2*R+1) x)}=
      (e^[R]) ⁻¹' {x | α x≠D (centeredWindow R (orbitName e p x))} := by
    ext x
    simp only [mem_ofPred_eq,mem_preimage,centeredWindow_orbit_shift]
  have hm : MeasurableSet {x | α x≠D (centeredWindow R (orbitName e p x))} := (measurableSet_eq_fun hα hD).compl
  rw [hset,Measure.real,Measure.real,(he.iterate R).measure_preimage hm.nullMeasurableSet]

lemma centered_decoder_perturbation [StandardBorelSpace X] [Nonempty A]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → B) (p q : X → A) (hα : Measurable α) (hp : Measurable p) (hq : Measurable q)
    (R : ℕ) (D : (Fin (2*R+1) → A) → B) :
    μ.real {x | α x≠D (centeredWindow R (orbitName e q x))}≤
      μ.real {x | α x≠D (centeredWindow R (orbitName e p x))}+
        (2*R+1 : ℕ)*μ.real {x | p x≠q x} := by
  rw [centered_decoder_error_eq μ e he α q hα hq R D,
    centered_decoder_error_eq μ e he α p hα hp R D]
  exact finite_decoder_perturbation μ e he p q hp hq (fun x => α (e^[R] x)) _ D
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

theorem exact_iid_decoder_density (μ : Measure X) [IsProbabilityMeasure μ]
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
    ∃ q : X → A,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,Measurable q ∧
      MeasurePreserving (orbitName e q) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      μ.real {x | p x≠q x} < η ∧
      μ.real {x | α x≠D (centeredWindow R (orbitName e q x))} < η := by
  obtain ⟨R,D,hproduce⟩ := fixed_decoder_arbitrary_tests_q44 μ e he htotal p hp β hβ hβsum hβentropy
    H hcode α hα happrox zero one h01 (half_pos hη)
  let c : ℝ := η/(4*((2*R+1 : ℕ)+1))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨L,δ,hδ,hcomplete⟩ := seeded_exact_iid_limit μ e he htotal β hβ hβsum hβentropy H zero one h01 hc
  obtain ⟨q₀,hq₀,hpaint,hfixed,hlaw,hrate⟩ := hproduce L δ δ hδ hδ
  obtain ⟨q,hq,hcodeq,hclose⟩ := hcomplete q₀ hq₀ hlaw hrate.le
  have hwidth : (0 : ℝ)≤(2*R+1 : ℕ) := Nat.cast_nonneg _
  have hceq : c*(4*((2*R+1 : ℕ)+1))=η := by dsimp [c]; field_simp
  have hcη : c≤η/4 := by nlinarith only [hceq,hc,hwidth]
  have hWc : (2*R+1 : ℕ)*c≤η/4 := by nlinarith only [hceq,hc,hwidth]
  refine ⟨q,R,D,hq,hcodeq,?_,?_⟩
  · have hh := disagreement_triangle μ p q₀ q
    linarith only [hh,hpaint,hclose,hcη,hη]
  · rw [centered_decoder_error_eq μ e he.toMeasurePreserving α q hα hq R D]
    have hh := finite_decoder_perturbation μ e he.toMeasurePreserving q₀ q hq₀ hq (fun x => α (e^[R] x)) (2*R+1) D
    have hd := mul_le_mul_of_nonneg_left hclose.le hwidth
    linarith only [hh,hfixed,hd,hWc,hη]

theorem exact_iid_decoder_density_of_separating_wb (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (ξ : ℕ → ℕ → X → Bool) (hξ : ∀ i j,Measurable (ξ i j))
    (hsep : Function.Injective (fun x => fun i j => ξ i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary ξ M))
    (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α) (zero one : A) (h01 : zero≠one) {η : ℝ} (hη : 0 < η) :
    ∃ q : X → A,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,Measurable q ∧
      MeasurePreserving (orbitName e q) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      μ.real {x | p x≠q x} < η ∧
      μ.real {x | α x≠D (centeredWindow R (orbitName e q x))} < η := by
  apply exact_iid_decoder_density μ e he htotal p hp β hβ hβsum hβentropy H hcode α hα _ zero one h01 hη
  intro ε hε
  obtain ⟨r,hr,hwr,herr⟩ := separating_wb_approximation μ e ξ hξ hsep hwb
    (fun x => (p x,α x)) (hp.prodMk hα) hε
  refine ⟨r,hr,hwr,?_⟩
  rwa [disagreement_symm]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma budget_geometric_decay (b : ℕ → ℝ) (hb : ∀ n,b (n+1)≤b n/2) (n k : ℕ) :
    b (n+k)≤b n*(1/2 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,pow_succ]
    have hh := hb (n+k)
    nlinarith only [ih,hh]

lemma geometric_tail_distance (μ : Measure X) [IsFiniteMeasure μ]
    (q : ℕ → X → A) (b : ℕ → ℝ) (hpos : ∀ n,0≤b n)
    (hb : ∀ n,b (n+1)≤b n/2)
    (hpaint : ∀ n,μ.real {x | q n x≠q (n+1) x}≤b n/2) (n k : ℕ) :
    μ.real {x | q n x≠q (n+k) x}≤b n := by
  let η : ℕ → ℝ := fun j => b n/2*(1/2 : ℝ)^j
  have hstep (j : ℕ) : μ.real {x | q (n+j) x≠q (n+(j+1)) x}≤η j := by
    have h := hpaint (n+j)
    have hh := budget_geometric_decay b hb n j
    dsimp [η]
    rw [Nat.add_succ]
    nlinarith only [h,hh]
  have hh := sequence_distance_le_sum μ (fun j => q (n+j)) η hstep k
  simp only [Nat.add_zero] at hh
  apply hh.trans
  simp only [η,←Finset.mul_sum]
  have hs := mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (show 0≤b n/2 from div_nonneg (hpos n) (by norm_num))
  nlinarith only [hs]

lemma geometric_tail_limit [MeasurableEq A]
    (μ : Measure X) [IsFiniteMeasure μ] (q : ℕ → X → A) (p : X → A)
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (b : ℕ → ℝ) (hpos : ∀ n,0≤b n) (hb : ∀ n,b (n+1)≤b n/2)
    (hpaint : ∀ n,μ.real {x | q n x≠q (n+1) x}≤b n/2) (n : ℕ) :
    μ.real {x | q n x≠p x}≤b n := by
  have ht : Tendsto (fun j : ℕ => n+j) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  have hl : ∀ᵐ x ∂μ,∀ᶠ j : ℕ in atTop,q (n+j) x=p x :=
    hlim.mono (fun x hx => ht.eventually hx)
  exact partition_limit_distance_bound μ (fun j => q (n+j)) p (q n) (fun j => hq _) hp hl
    (fun k => geometric_tail_distance μ q b hpos hb hpaint n k)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology

lemma exists_post_decoder_budget (W : ℕ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ b : ℝ,0 < b ∧ b ≤ c ∧ (W : ℝ)*b≤ε := by
  let b := min c (ε/((W : ℝ)+1))
  have hW : (0 : ℝ)≤W := Nat.cast_nonneg W
  have hb : 0 < b := lt_min hc (by positivity)
  have hsmall : b≤ε/((W : ℝ)+1) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : (0 : ℝ)<(W : ℝ)+1)).mp hsmall
  exact ⟨b,hb,min_le_left _ _,by nlinarith only [hh,hb]⟩
end HyperbolicCoding
end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal NNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

lemma generating_iid_stage (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary α M))
    (zero one : A) (h01 : zero≠one)
    (p : X → A) (hp : Measurable p)
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (n : ℕ) {η c : ℝ} (hη : 0 < η) (hc : 0 < c) :
    ∃ S : GeneratingIIDStage μ e β α n,
      μ.real {x | p x≠S.partition x} < η ∧ S.budget ≤ c := by
  have hε : 0 < (1/2 : ℝ)^(n+2) := by positivity
  obtain ⟨q,R,D,hq,hcodeq,hpaint,hdecode⟩ := exact_iid_decoder_density_of_separating_wb μ e he htotal
    α hα hsep hwb p hp β hβ hβsum hβentropy H hcode (joinedBinary α (n+1))
    (measurable_joinedBinary hα _) zero one h01 (lt_min hη hε)
  obtain ⟨b,hb,hbc,hbudget⟩ := exists_post_decoder_budget (2*R+1) hε hc
  refine ⟨⟨q,hq,hcodeq,R,D,hdecode.trans_le (min_le_right _ _),b,hb,hbudget⟩,?_,hbc⟩
  exact hpaint.trans_le (min_le_left _ _)

theorem generating_iid_partition (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary α M))
    (zero one : A) (h01 : zero≠one)
    (p₀ : X → A) (hp₀ : Measurable p₀)
    (hcode₀ : MeasurePreserving (orbitName e p₀) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))) :
    ∃ p : X → A,Measurable p ∧
      MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      ∀ n : ℕ,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → ((Fin (n+1) × Fin (n+1)) → Bool),
        μ.real {x | joinedBinary α (n+1) x≠D (centeredWindow R (orbitName e p x))}≤2*(1/2 : ℝ)^(n+2) := by
  have hstart := generating_iid_stage μ e he htotal β hβ hβsum hβentropy H α hα hsep hwb
    zero one h01 p₀ hp₀ hcode₀ 0 zero_lt_one zero_lt_one
  let S₀ : GeneratingIIDStage μ e β α 0 := Classical.choose hstart
  have hnext (n : ℕ) (S : GeneratingIIDStage μ e β α n) :
      ∃ T : GeneratingIIDStage μ e β α (n+1),
        μ.real {x | S.partition x≠T.partition x} < S.budget/2 ∧ T.budget≤S.budget/2 :=
    generating_iid_stage μ e he htotal β hβ hβsum hβentropy H α hα hsep hwb
      zero one h01 S.partition S.measurable_partition S.iid (n+1) (half_pos S.budget_pos) (half_pos S.budget_pos)
  let next (n : ℕ) (S : GeneratingIIDStage μ e β α n) : GeneratingIIDStage μ e β α (n+1) :=
    Classical.choose (hnext n S)
  let z : (n : ℕ) → GeneratingIIDStage μ e β α n := fun n =>
    Nat.rec (motive:=fun n => GeneratingIIDStage μ e β α n) S₀ next n
  let q : ℕ → X → A := fun n => (z n).partition
  let b : ℕ → ℝ := fun n => (z n).budget
  have hq (n : ℕ) : Measurable (q n) := (z n).measurable_partition
  have hbpos (n : ℕ) : 0 < b n := (z n).budget_pos
  have hb0 : b 0≤1 := (Classical.choose_spec hstart).2
  have hb (n : ℕ) : b (n+1)≤b n/2 := (Classical.choose_spec (hnext n (z n))).2
  have hpaint (n : ℕ) : μ.real {x | q n x≠q (n+1) x} < b n/2 :=
    (Classical.choose_spec (hnext n (z n))).1
  have hgeom (n : ℕ) : μ.real {x | q (n+1) x≠q n x} < ((1/2 : ℝ≥0)^n : ℝ) := by
    rw [disagreement_symm]
    have hdecay := budget_geometric_decay b hb 0 n
    simp only [Nat.zero_add] at hdecay
    have hbn : b n≤(1/2 : ℝ)^n := hdecay.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb0 (by positivity : 0≤(1/2 : ℝ)^n))
    have hh : b n/2≤b n := by linarith only [hbpos n]
    have hc := (hpaint n).trans_le (hh.trans hbn)
    simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hc
  obtain ⟨p,hp,hlim⟩ := exists_partition_limit μ q hq (geometric_repainting_summable μ q hgeom)
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hlaw (n : ℕ) : LawClose (μ.map (word e (q n) n))
      (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) (1/(n+1 : ℝ)) := by
    rw [word_law_of_iid_factor μ e (q n) (hq n) (finiteWeightLaw β) (z n).iid]
    intro S hS
    simp only [sub_self,abs_zero]
    positivity
  have hcode := iid_law_of_growing_forward_words μ e he.toMeasurePreserving q hq p hp hlim
    (finiteWeightLaw β) (fun n => 1/(n+1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat hlaw
  refine ⟨p,hp,hcode,?_⟩
  intro n
  refine ⟨(z n).radius,(z n).decoder,?_⟩
  have htail := geometric_tail_limit μ q p hq hp hlim b (fun n => (hbpos n).le) hb (fun n => (hpaint n).le) n
  have hh := centered_decoder_perturbation μ e he.toMeasurePreserving (joinedBinary α (n+1))
    (q n) p (measurable_joinedBinary hα _) (hq n) hp (z n).radius (z n).decoder
  have hd := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg (2*(z n).radius+1) : (0 : ℝ)≤_)
  have he := (z n).error
  have hb := (z n).budget_small
  change _≤_+_ at hh
  change _ < (1/2 : ℝ)^(n+2) at he
  change (2*(z n).radius+1 : ℕ)*b n≤(1/2 : ℝ)^(n+2) at hb
  linarith only [hh,hd,he,hb]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

theorem binary_factors_of_joined_decoders (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (p : X → A) (α : ℕ → ℕ → X → Bool)
    (hdecode : ∀ n : ℕ,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → ((Fin (n+1) × Fin (n+1)) → Bool),
      μ.real {x | joinedBinary α (n+1) x≠D (centeredWindow R (orbitName e p x))}≤2*(1/2 : ℝ)^(n+2)) :
    ∀ i j : ℕ,∀ ε : ℝ,0 < ε → ∃ g : (ℤ → A) → Bool,Measurable g ∧
      μ {x | g (orbitName e p x)≠α i j x} < ENNReal.ofReal ε := by
  intro i j ε hε
  have hz : Tendsto (fun n : ℕ => 2*(1/2 : ℝ)^(n+2)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ) < 1)
    simpa using tendsto_const_nhds.mul (hp.comp (tendsto_add_atTop_nat 2))
  obtain ⟨n,hnε,hnlarge⟩ := ((hz.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop (max i j))).exists
  obtain ⟨R,D,hD⟩ := hdecode n
  have hi : i < n+1 := by omega
  have hj : j < n+1 := by omega
  let ij : Fin (n+1) × Fin (n+1) := (⟨i,hi⟩,⟨j,hj⟩)
  let g : (ℤ → A) → Bool := fun w => D (centeredWindow R w) ij
  have hg : Measurable g := (measurable_pi_apply ij).comp
    ((measurable_of_countable D).comp (measurable_centeredWindow R))
  have hsub : {x | g (orbitName e p x)≠α i j x}⊆
      {x | joinedBinary α (n+1) x≠D (centeredWindow R (orbitName e p x))} := by
    intro x hx heq
    have hh := congrFun heq ij
    exact hx hh.symm
  have hh : μ.real {x | g (orbitName e p x)≠α i j x} < ε :=
    ((measureReal_mono (μ:=μ) hsub).trans hD).trans_lt hnε
  refine ⟨g,hg,?_⟩
  rw [←ENNReal.ofReal_toReal (measure_ne_top μ {x | g (orbitName e p x)≠α i j x})]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hh
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

theorem bernoulli_model_of_generating_iid (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (p : X → A) (hp : Measurable p) (β : Measure A) [IsProbabilityMeasure β]
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)))
    (α : ℕ → ℕ → X → Bool) (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hdecode : ∀ n : ℕ,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → ((Fin (n+1) × Fin (n+1)) → Bool),
      μ.real {x | joinedBinary α (n+1) x≠D (centeredWindow R (orbitName e p x))}≤2*(1/2 : ℝ)^(n+2)) :
    ∃ βR : Measure ℝ,IsProbabilityMeasure βR ∧
      ∃ (encode : X → (ℤ → ℝ)) (decode : (ℤ → ℝ) → X),
        MeasurePreserving encode μ (Measure.infinitePi (fun _ : ℤ => βR)) ∧
        MeasurePreserving decode (Measure.infinitePi (fun _ : ℤ => βR)) μ ∧
        (∀ᵐ x ∂μ,decode (encode x)=x) ∧
        (∀ᵐ w ∂Measure.infinitePi (fun _ : ℤ => βR),encode (decode w)=w) ∧
        (∀ᵐ x ∂μ,encode (e x)=fun i : ℤ => encode x (i+1)) := by
  have hsep' : Function.Injective (fun x => fun i : ℕ × ℕ => α i.1 i.2 x) := by
    intro x y h
    apply hsep
    funext i j
    exact congrFun h (i,j)
  obtain ⟨d,hd,hl,_hr⟩ := measurable_decoder_of_generating_approximations μ (orbitName e p)
    (measurable_orbitName e hp) (fun i : ℕ × ℕ => α i.1 i.2) hsep'
    (fun i => binary_factors_of_joined_decoders μ e p α hdecode i.1 i.2)
  rw [hcode.map_eq] at hd
  let b : A → ℝ := embeddingReal A
  have hb : MeasurableEmbedding b := measurableEmbedding_embeddingReal A
  let βR := β.map b
  have : IsProbabilityMeasure βR := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  let F : (ℤ → A) → (ℤ → ℝ) := fun w i => b (w i)
  let G : (ℤ → ℝ) → (ℤ → A) := fun w i => hb.invFun (w i)
  have hF : Measurable F := Measurable.of_eval (fun index => hb.measurable.comp (measurable_pi_apply index))
  have hG : Measurable G := Measurable.of_eval (fun index => hb.measurable_invFun.comp (measurable_pi_apply index))
  have hGF (w : ℤ → A) : G (F w)=w := funext (fun i => hb.leftInverse_invFun (w i))
  have hmpF : MeasurePreserving F (Measure.infinitePi (fun _ : ℤ => β))
      (Measure.infinitePi (fun _ : ℤ => βR)) :=
    ⟨hF,Measure.infinitePi_map_pi _ (fun _ => hb.measurable)⟩
  have hmpG : MeasurePreserving G (Measure.infinitePi (fun _ : ℤ => βR))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
    refine ⟨hG,?_⟩
    rw [←hmpF.map_eq,Measure.map_map hG hF,show G ∘ F=id from funext hGF,Measure.map_id]
  let encode : X → (ℤ → ℝ) := F ∘ orbitName e p
  let decode : (ℤ → ℝ) → X := d ∘ G
  have hE : MeasurePreserving encode μ (Measure.infinitePi (fun _ : ℤ => βR)) := hmpF.comp hcode
  have hD : MeasurePreserving decode (Measure.infinitePi (fun _ : ℤ => βR)) μ := hd.comp hmpG
  have hleft : ∀ᵐ x ∂μ,decode (encode x)=x := by
    filter_upwards [hl] with x hx
    exact (congrArg d (hGF (orbitName e p x))).trans hx
  refine ⟨βR,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),encode,decode,hE,hD,hleft,?_,?_⟩
  · rw [←hE.map_eq]
    apply (ae_map_iff hE.measurable.aemeasurable
      (measurableSet_eq_fun (hE.measurable.comp hD.measurable) measurable_id)).mpr
    filter_upwards [hleft] with x hx
    exact congrArg encode hx
  · exact ae_of_all _ (fun x => funext (fun i => congrArg b (congrFun (orbitName_shift e p x) i)))

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_PositiveWeakBernoulliRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StandardMapEntropy
open MeasureTheory Set Filter HyperbolicCoding Entropy
open scoped BigOperators ENNReal Topology

lemma normalizedArea_nullSingleton (E : Set Torus) : NullSingletonClass (normalizedArea E) := by
  have : NullSingletonClass area := by unfold area; infer_instance
  constructor
  intro z
  exact normalizedArea_absolutelyContinuous E (measure_singleton z)

end StandardMapEntropy

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ComponentsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StandardMapEntropy
open MeasureTheory Set Filter HyperbolicCoding Entropy
open scoped BigOperators ENNReal Topology

theorem actual_return_bernoulli_q44_oai (k : ℝ) (hk : 0≤k) (N : ℕ)
    (E : Set Torus) (hE : 0 < area E)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (((standardMap k)^[N])^[m]) (normalizedArea E))
    (α : ℕ → ℕ → Torus → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun z => fun i j => α i j z))
    (hwb : ∀ M : ℕ,WeakBernoulliProcess (normalizedArea E)
      (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M)) :
    IsBernoulli ((standardMap k)^[N]) (normalizedArea E) := by
  let := normalizedArea_probability hE
  let := normalizedArea_nullSingleton E
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have he : Ergodic e (normalizedArea E) := by
    rw [heq]
    simpa only [Function.iterate_one] using htotal 1 (by omega)
  have het : ∀ m : ℕ,0 < m → Ergodic (e^[m]) (normalizedArea E) := by simpa only [heq] using htotal
  obtain ⟨n,β,p₀,hβ,hβsum,hβentropy,hp₀,H,hcode₀,_hr,_hshift,_hjoint⟩ :=
    actual_return_full_entropy_iid_factor_q44 k hk N E hE htotal α hα hsep hwb
  have Hβ : FiniteRateSupremum (normalizedArea E) e (weightEntropy β) := by simpa only [heq] using H
  let zero : Fin (n+2) := ⟨0,by omega⟩
  let one : Fin (n+2) := ⟨1,by omega⟩
  have h01 : zero≠one := by
    intro h
    have hv : (0 : ℕ)=1 := congrArg Fin.val h
    omega
  obtain ⟨p,hp,hcode,hdecode⟩ := generating_iid_partition (normalizedArea E) e he het
    β hβ hβsum hβentropy Hβ α hα hsep hwb zero one h01 p₀ hp₀ hcode₀
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hm := bernoulli_model_of_generating_iid (normalizedArea E) e p hp (finiteWeightLaw β) hcode α hsep hdecode
  simpa only [IsBernoulli,heq] using hm
end StandardMapEntropy

end

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.actual_return_bernoulli_q44_oai := @OAI.StandardMapEntropy.actual_return_bernoulli_q44_oai

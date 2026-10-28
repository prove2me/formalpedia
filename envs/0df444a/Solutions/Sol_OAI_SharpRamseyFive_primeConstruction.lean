-- Prove2me | solution 1 for OAI.SharpRamseyFive.primeConstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:51:14.403994+00:00
-- url     : https://prove2.me/submissions/2adcaf24-47da-4f0c-bbd4-2bea8e9cb70d

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_iter_produce

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

lemma atom_bound_entropy (p : Law α) (A : ℝ)
    (hpa : ∀ a,p a ≤ A) : -Real.log A ≤ entropy p := by
  have hsum : (∑ a,p a*Real.log (p a)) ≤ Real.log A := by
    calc
      _ ≤ ∑ a,p a*Real.log A := Finset.sum_le_sum fun a _ => by
        by_cases h : p a=0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left
            (Real.log_le_log (lt_of_le_of_ne (p.nonneg a) (Ne.symm h)) (hpa a)) (p.nonneg a)
      _ = Real.log A := by rw [←Finset.sum_mul,p.sum_one,one_mul]
  exact neg_le_neg hsum

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EventMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma eventMass_nonneg (p : Law α) (E : Finset α) : 0≤eventMass p E :=
  Finset.sum_nonneg fun a _ => p.nonneg a

lemma iid_cons (p : Law α) {n : ℕ} (a : α) (x : Fin n → α) :
    iid p (Fin (n+1)) (Fin.cons a x)=p a*iid p (Fin n) x := by
  simp [iid,Fin.prod_univ_succ]

lemma sum_iid_succ (p : Law α) (n : ℕ) (f : (Fin (n+1) → α) → ℝ) :
    (∑ x,iid p (Fin (n+1)) x*f x)=
      ∑ a,∑ x,p a*iid p (Fin n) x*f (Fin.cons a x) := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α))
    (fun z => p z.1*iid p (Fin n) z.2*f (Fin.cons z.1 z.2))
    (fun x => iid p (Fin (n+1)) x*f x) (by
      intro z
      change _ = iid p (Fin (n+1)) (Fin.cons z.1 z.2)*f (Fin.cons z.1 z.2)
      rw [iid_cons])
  simpa only [Fintype.sum_prod_type] using h.symm

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Hits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma hits_cons (H : Finset α) {n : ℕ} (a : α) (x : Fin n → α) :
    hits H (Fin.cons a x)=(if a∈H then 1 else 0)+hits H x := by
  simp only [hits,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma event_markov (p : Law α) (w : α → ℝ) (hw : ∀ a,0≤w a) (t : ℝ)
    (E : Finset α) (hE : ∀ a∈E,t≤w a) :
    t*eventMass p E≤∑ a,p a*w a := by
  rw [eventMass,Finset.mul_sum]
  calc
    _ ≤ ∑ a∈E,p a*w a := Finset.sum_le_sum fun a ha => by
      simpa only [mul_comm t] using mul_le_mul_of_nonneg_left (hE a ha) (p.nonneg a)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
      mul_nonneg (p.nonneg a) (hw a))

end
open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped BigOperators Classical
open FiniteEntropy
variable {α ι : Type*} [Fintype α] [Fintype ι]

lemma completion_count (I : Finset ι) (v : I → α) :
    (Finset.univ.filter fun s : ι → α => ∀ i : I,s i.val = v i).card =
      Fintype.card α ^ (Fintype.card ι-I.card) := by
  classical
  have he := Fintype.card_congr (completionEquiv I v)
  rw [Fintype.card_fun,Fintype.card_subtype_compl,Fintype.card_coe] at he
  simpa only [Fintype.card_subtype] using he

variable {N l : ℕ}

lemma matching_count (I : {I : Finset (Fin N) // I.card=l}) (f : Fin l → α) :
    (matching I f).card = Fintype.card α ^ (N-l) := by
  let e := I.val.orderIsoOfFin I.property
  have he : matching I f = Finset.univ.filter fun s : Fin N → α =>
      ∀ i : I.val,s i.val = f (e.symm i) := by
    ext s
    simp only [matching,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hs i
      have h := hs (e.symm i)
      have hi : I.val.orderEmbOfFin I.property (e.symm i) = i.val :=
        congrArg Subtype.val (e.apply_symm_apply i)
      rwa [hi] at h
    · intro hs j
      have h := hs (e j)
      change s (I.val.orderEmbOfFin I.property j) = f (e.symm (e j)) at h
      simpa only [e.symm_apply_apply] using h
  rw [he]
  convert (completion_count I.val (fun i => f (e.symm i))) using 1
  · congr
    exact Subsingleton.elim _ _
  · simp only [Fintype.card_fin,I.property]

lemma position_set_count : Fintype.card {I : Finset (Fin N) // I.card=l} = N.choose l := by
  classical
  have he : (Finset.univ.filter fun I : Finset (Fin N) => I.card=l) =
      Finset.univ.powersetCard l := by ext I; simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

theorem occurrence_count (f : Fin l → α) :
    (occurrences (N := N) f).card ≤ N.choose l * Fintype.card α^(N-l) := by
  calc
    _ ≤ ∑ I : {I : Finset (Fin N) // I.card=l},(matching I f).card :=
      Finset.card_biUnion_le
    _ = _ := by simp only [matching_count,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,position_set_count,Nat.cast_id]

theorem selected_atom [Nonempty α] (hl : l ≤ N)
    (p : Law ((Fin N → α) × (Fin l → α))) (C : ℝ) (hC : 0 ≤ C)
    (hstream : ∀ s,first p s ≤ C/(Fintype.card α:ℝ)^N)
    (rev : (Fin l → α) → (Fin l → α))
    (hselect : ∀ s f,0 < p (s,f) →
      s ∈ occurrences f ∨ s ∈ occurrences (rev f)) (f : Fin l → α) :
    second p f ≤ 2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l := by
  classical
  let E := occurrences (N := N) f ∪ occurrences (N := N) (rev f)
  have hm : 0 < (Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hmass : second p f ≤ ∑ s∈E,first p s := by
    change (∑ s,p (s,f)) ≤ _
    calc
      _ ≤ ∑ s,if s∈E then first p s else 0 := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : s ∈ E
        · simp only [hs,ite_true]
          exact le_first p s f
        · simp only [hs,ite_false]
          apply le_of_not_gt
          intro hp
          exact hs (Finset.mem_union.mpr (hselect s f hp))
      _ = _ := by rw [←Finset.sum_filter,Finset.filter_univ_mem]
  have hc : E.card ≤ 2*(N.choose l*Fintype.card α^(N-l)) := by
    exact (Finset.card_union_le _ _).trans ((add_le_add (occurrence_count f)
      (occurrence_count (rev f))).trans_eq (by ring))
  have hc' : (E.card:ℝ) ≤ 2*((N.choose l:ℝ)*(Fintype.card α:ℝ)^(N-l)) := by
    exact_mod_cast hc
  calc
    second p f ≤ ∑ s∈E,first p s := hmass
    _ ≤ ∑ _s∈E,C/(Fintype.card α:ℝ)^N := Finset.sum_le_sum fun s _ => hstream s
    _ = (E.card:ℝ)*(C/(Fintype.card α:ℝ)^N) := by simp
    _ ≤ 2*((N.choose l:ℝ)*(Fintype.card α:ℝ)^(N-l))*(C/(Fintype.card α:ℝ)^N) :=
      mul_le_mul_of_nonneg_right hc' (div_nonneg hC (pow_nonneg hm.le _))
    _ = _ := by
      have he : (Fintype.card α:ℝ)^N = (Fintype.card α:ℝ)^(N-l)*(Fintype.card α:ℝ)^l := by
        rw [←pow_add,Nat.sub_add_cancel hl]
      rw [he]
      field_simp

theorem selected_entropy [Nonempty α] (hl : l ≤ N)
    (p : Law ((Fin N → α) × (Fin l → α))) (C : ℝ) (hC : 0 ≤ C)
    (hstream : ∀ s,first p s ≤ C/(Fintype.card α:ℝ)^N)
    (rev : (Fin l → α) → (Fin l → α))
    (hselect : ∀ s f,0 < p (s,f) →
      s ∈ occurrences f ∨ s ∈ occurrences (rev f)) :
    -Real.log (2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l) ≤ entropy (second p) :=
  atom_bound_entropy (second p) _ (selected_atom hl p C hC hstream rev hselect)

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_StageState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α β γ Ω κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω] [Fintype κ]

namespace SelectedStream
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

theorem entropy_lower [Nonempty α] (hn : n≤N)
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) :
    -Real.log (2*S.density*(N.choose n:ℝ)/(Fintype.card α:ℝ)^n)≤
      entropy (map S.law S.tuple) := by
  have hh:=selected_entropy hn (pair S.law S.stream
    (fun a=>sourceSequence S.reverse S.view (S.tuple a))) S.density S.density_nonneg
    (by simpa only [first_pair] using S.density_bound) id (by
      intro s f hp
      obtain ⟨a,ha,he⟩:=map_positive S.law
        (fun a=>(S.stream a,sourceSequence S.reverse S.view (S.tuple a))) (s,f) hp
      cases he
      exact Or.inl (S.selected a ha))
  simp only [second_pair] at hh
  have he:=entropy_map_le (map S.law S.tuple) (sourceSequence S.reverse S.view)
  rw [map_comp] at he
  exact hh.trans he

end SelectedStream
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CoreGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry

section
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma geometric_card_bound (q : ℝ) (hq : 2≤q) (r : ℕ) :
    (∑ i∈Finset.range r,q^i)≤2*q^(r-1) := by
  cases r with
  | zero => simp
  | succ r =>
    simp only [Nat.add_sub_cancel]
    have h := geom_sum_mul q (r+1)
    rw [pow_succ] at h
    have hp : 0≤q^r := pow_nonneg (by linarith) _
    have hh : q*q^r≤2*q^r*(q-1) := by nlinarith
    have hq' : 0<q-1 := by linarith
    nlinarith

end

open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReciprocalLossBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype β] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {Λ J Λ' J' : ℝ}
lemma card_le_of_log_le {a b : ℝ} (ha : 0≤a) (hb : 0<b)
    (h : Real.log a≤Real.log b) : a≤b := by
  rcases eq_or_lt_of_le ha with he|he
  · linarith
  · exact (Real.log_le_log_iff he hb).mp h
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DescriptionClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {L J : ℝ}
lemma ContextDescription.clean_contains (C : ContextDescription (κ:=κ) p x L J) :
    ∀z,0<p z→∀i,x z i∈C.cleanDomain (C.context z) i := by
  intro z hz i
  have hp : 0 < map p C.context (C.context z) := by
    change 0 < ∑a,if C.context a=C.context z then p a else 0
    have hh:=Finset.single_le_sum (s:=Finset.univ) (a:=z)
      (f:=fun a=>if C.context a=C.context z then p a else 0)
      (fun a _=>by split_ifs; exact p.nonneg a; exact le_rfl) (Finset.mem_univ z)
    simp only at hh
    exact hz.trans_le hh
  simpa only [cleanDomain,ite_eq_left hp] using C.contains z hz i
lemma ContextDescription.clean_cap (C : ContextDescription (κ:=κ) p x L J) :
    ∀c i,((C.cleanDomain c i).card:ℝ)≤Real.exp J := by
  intro c i
  by_cases hp : 0 < map p C.context c
  · obtain ⟨z,hz,rfl⟩:=map_positive p C.context c hp
    have hh:=C.cap z hz i
    rw [cleanDomain,ite_eq_left hp]
    apply card_le_of_log_le (by positivity) (Real.exp_pos _)
    simpa only [Real.log_exp] using hh
  · simp only [cleanDomain,ite_eq_right hp,Finset.card_empty,Nat.cast_zero]
    exact (Real.exp_pos _).le
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Rectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module
open scoped LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem count_subspaces : Nat.card (Submodule K V)≤
    (finrank K V+1)*Nat.card V^(finrank K V) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let f : (Σ r : Fin (finrank K V+1),Fin r.val → V) → Submodule K V :=
    fun v => Submodule.span K (Set.range v.2)
  have hf : Function.Surjective f := by
    intro U
    let r : Fin (finrank K V+1) := ⟨finrank K U,Nat.lt_succ_of_le (Submodule.finrank_le U)⟩
    use ⟨r,fun i => (Module.finBasis K U i).val⟩
    change Submodule.span K (Set.range (U.subtype ∘ Module.finBasis K U))=U
    rw [Set.range_comp,←Submodule.map_span,(Module.finBasis K U).span_eq,
      Submodule.map_subtype_top]
  have hc := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sigma] at hc
  calc
    _ ≤ ∑ r : Fin (finrank K V+1),Nat.card (Fin r.val → V) := hc
    _ ≤ ∑ _r : Fin (finrank K V+1),Nat.card V^finrank K V := by
      apply Finset.sum_le_sum
      intro r _
      rw [Nat.card_fun,Nat.card_fin]
      exact Nat.pow_le_pow_right (Nat.card_pos (α := V)) (Nat.le_of_lt_succ r.isLt)
    _ = _ := by simp

omit [FiniteDimensional K V] in

theorem card_rectangle (U : Submodule K (Module.Dual K V)) :
    Nat.card {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U} =
      (∑ i∈Finset.range (finrank K U.dualCoannihilator),Nat.card K^i)*
      (∑ i∈Finset.range (finrank K U),Nat.card K^i) := by
  let e : {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U} ≃
      {a : ℙ K V // a.submodule≤U.dualCoannihilator} ×
        {b : ℙ K (Module.Dual K V) // b.submodule≤U} :=
    { toFun := fun ab => (⟨ab.val.1,ab.property.1⟩,⟨ab.val.2,ab.property.2⟩)
      invFun := fun ab => ⟨(ab.1.val,ab.2.val),⟨ab.1.property,ab.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_prod,
    SharpRamseyFive.ProjectiveIncidence.card_subspacePoints,
    SharpRamseyFive.ProjectiveIncidence.card_subspacePoints]

theorem card_rectangle_le (hdim : finrank K V=5)
    (U : Submodule K (Module.Dual K V)) :
    (Nat.card {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U}:ℝ)≤4*(Nat.card K:ℝ)^3 := by
  rw [card_rectangle]
  push_cast
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq U
  rw [hdim] at hd
  by_cases hU : finrank K U=0
  · simp only [hU,Finset.range_zero,Finset.sum_empty,mul_zero]
    positivity
  by_cases hD : finrank K U.dualCoannihilator=0
  · simp only [hD,Finset.range_zero,Finset.sum_empty,zero_mul]
    positivity
  have hpow : (finrank K U.dualCoannihilator-1)+(finrank K U-1)=3 := by omega
  calc
    _ ≤ (2*(Nat.card K:ℝ)^(finrank K U.dualCoannihilator-1))*
        (2*(Nat.card K:ℝ)^(finrank K U-1)) :=
      mul_le_mul (geometric_card_bound _ hq _) (geometric_card_bound _ hq _)
        (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4*(Nat.card K:ℝ)^((finrank K U.dualCoannihilator-1)+(finrank K U-1)) := by
      rw [pow_add]; ring
    _ = _ := by rw [hpow]
end SharpRamseyFive.CoreGeometry

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma exp_single_hit (p : Law α) (H : Finset α) :
    (∑ a,p a*Real.exp (if a∈H then 1 else 0))=
      1+(Real.exp 1-1)*eventMass p H := by
  have ht (a : α) : p a*Real.exp (if a∈H then 1 else 0)=
      p a+(Real.exp 1-1)*(if a∈H then p a else 0) := by
    split_ifs
    · ring
    · simp
  simp only [ht,Finset.sum_add_distrib,←Finset.mul_sum,p.sum_one]
  rw [←Finset.sum_filter,Finset.filter_univ_mem]
  rfl

theorem exp_hits (p : Law α) (H : Finset α) (n : ℕ) :
    (∑ x,iid p (Fin n) x*Real.exp (hits H x))=
      (1+(Real.exp 1-1)*eventMass p H)^n := by
  induction n with
  | zero => simp [iid,hits]
  | succ n hn =>
    rw [sum_iid_succ]
    have ht (a : α) (x : Fin n → α) :
        p a*iid p (Fin n) x*Real.exp (hits H (Fin.cons a x))=
        (p a*Real.exp (if a∈H then 1 else 0))*(iid p (Fin n) x*Real.exp (hits H x)) := by
      rw [hits_cons,Real.exp_add]
      ring
    simp_rw [ht,←Finset.mul_sum,hn,←Finset.sum_mul,exp_single_hit]
    rw [pow_succ]
    ring

theorem exp_hits_le (p : Law α) (H : Finset α) (n : ℕ) :
    (∑ x,iid p (Fin n) x*Real.exp (hits H x))≤
      Real.exp (2*n*eventMass p H) := by
  rw [exp_hits]
  have hm := eventMass_nonneg p H
  have hone : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have htwo : Real.exp 1-1≤2 := by linarith [Real.exp_one_lt_d9]
  calc
    _ ≤ (Real.exp (2*eventMass p H))^n := by
      apply pow_le_pow_left₀ (by positivity)
      have h := Real.add_one_le_exp (2*eventMass p H)
      nlinarith
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring

theorem iid_occupancy_tail (p : Law α) (H : Finset α) (n : ℕ) (M : ℝ) :
    eventMass (iid p (Fin n)) (Finset.univ.filter fun x => M≤hits H x)≤
      Real.exp (2*n*eventMass p H-M) := by
  have hh := event_markov (iid p (Fin n)) (fun x => Real.exp (hits H x))
    (fun x => (Real.exp_pos _).le) (Real.exp M)
    (Finset.univ.filter fun x => M≤hits H x) (by
      intro x hx
      exact Real.exp_le_exp.mpr (Finset.mem_filter.mp hx).2)
  have hl := hh.trans (exp_hits_le p H n)
  apply (mul_le_mul_iff_right₀ (Real.exp_pos M)).mp
  calc
    _ ≤ Real.exp (2*n*eventMass p H) := hl
    _ = Real.exp M*Real.exp (2*n*eventMass p H-M) := by
      rw [←Real.exp_add]; congr 1; ring

lemma event_biUnion_le {ι : Type*} [Fintype ι] (p : Law α) (E : ι → Finset α) :
    eventMass p (Finset.univ.biUnion E)≤∑ i,eventMass p (E i) := by
  have ht (a : α) : (if a∈Finset.univ.biUnion E then p a else 0)≤
      ∑ i,if a∈E i then p a else 0 := by
    by_cases ha : a∈Finset.univ.biUnion E
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
      simp only [ha,ite_true]
      have h := Finset.single_le_sum (s := Finset.univ) (f := fun i => if a∈E i then p a else 0)
        (fun i _ => by split_ifs; exact p.nonneg a; exact le_rfl) (Finset.mem_univ i)
      simpa only [hi,ite_true] using h
    · simp only [ha,ite_false]
      exact Finset.sum_nonneg fun i _ => by split_ifs; exact p.nonneg a; exact le_rfl
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => ht a)
  rw [Finset.sum_comm] at h
  simpa only [←Finset.sum_filter,Finset.filter_univ_mem,eventMass] using h

theorem all_occupancy_tail {ι : Type*} [Fintype ι] (p : Law α)
    (H : ι → Finset α) (n : ℕ) (μ M : ℝ)
    (hμ : ∀ i,(n:ℝ)*eventMass p (H i)≤μ) :
    eventMass (iid p (Fin n)) (Finset.univ.biUnion fun i =>
      Finset.univ.filter fun x => M≤hits (H i) x)≤
      (Fintype.card ι:ℝ)*Real.exp (2*μ-M) := by
  calc
    _ ≤ ∑ i,eventMass (iid p (Fin n)) (Finset.univ.filter fun x => M≤hits (H i) x) :=
      by
        convert event_biUnion_le (iid p (Fin n)) (fun i =>
          Finset.univ.filter fun x => M≤hits (H i) x) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        ext x
        simp
    _ ≤ ∑ _i : ι,Real.exp (2*μ-M) := Finset.sum_le_sum fun i _ =>
      (iid_occupancy_tail p (H i) n M).trans (Real.exp_le_exp.mpr (by linarith [hμ i]))
    _ = _ := by simp
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators
variable {α : Type*} [Fintype α]

lemma uniform_event (h : 0<Fintype.card α) (E : Finset α) :
    eventMass (uniform h) E=(E.card:ℝ)/(Fintype.card α:ℝ) := by
  simp [eventMass,uniform,div_eq_mul_inv]
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.RectangleGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
  SharpRamseyFive.CoreGeometry
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

omit [FiniteDimensional K V] [Finite K] in
lemma card_rectangle_flags (U : Submodule K (Module.Dual K V)) :
    (rectangle U).card=Nat.card {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U} := by
  let e : {ab : Flag (K := K) (V := V) //
      ab.val.1.submodule≤U.dualCoannihilator ∧ ab.val.2.submodule≤U} ≃
      {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U} :=
    { toFun := fun ab => ⟨ab.val.val,ab.property⟩
      invFun := fun ab => ⟨⟨ab.val,by
        apply (incident_iff ab.val.1 ab.val.2).mpr
        have ha := (rep_mem_iff ab.val.1 U.dualCoannihilator).mpr ab.property.1
        have hb := (rep_mem_iff ab.val.2 U).mpr ab.property.2
        exact (Submodule.mem_dualCoannihilator ab.val.1.rep).mp ha ab.val.2.rep hb⟩,ab.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [rectangle,←Fintype.card_subtype,←Nat.card_eq_fintype_card,Nat.card_congr e]

theorem rectangle_mass (hdim : finrank K V=5) (U : Submodule K (Module.Dual K V)) :
    eventMass (uniform (flags_nonempty hdim)) (rectangle U)≤4/(Nat.card K:ℝ)^4 := by
  rw [uniform_event,card_rectangle_flags]
  have hn : (Nat.card K:ℝ)^7≤Fintype.card (Flag (K := K) (V := V)) := by
    rw [←Nat.card_eq_fintype_card]
    exact_mod_cast (card_flags_lower hdim)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  have hc := card_rectangle_le hdim U
  have hd : (0:ℝ)<Fintype.card (Flag (K := K) (V := V)) := by exact_mod_cast flags_nonempty hdim
  calc
    _ ≤ (4*(Nat.card K:ℝ)^3)/(Nat.card K:ℝ)^7 :=
      div_le_div₀ (by positivity) hc (by positivity) hn
    _ = _ := by field_simp
end SharpRamseyFive.RectangleGeometry

namespace SharpRamseyFive.RectangleGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]
  [Fintype (Submodule K (Module.Dual K V))]

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))] in
lemma count_rectangles (hdim : finrank K V=5) :
    (Fintype.card (Submodule K (Module.Dual K V)):ℝ)≤6*(Nat.card K:ℝ)^25 := by
  let : Fintype K := Fintype.ofFinite K
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (Module.Dual K V) := Fintype.ofFinite _
  have hv : Nat.card (Module.Dual K V)=Nat.card K^5 := by
    rw [Nat.card_eq_fintype_card (α := Module.Dual K V),Module.card_eq_pow_finrank (K := K),
      Subspace.dual_finrank_eq,hdim,←Nat.card_eq_fintype_card]
  have h := count_subspaces (K := K) (V := Module.Dual K V)
  rw [Subspace.dual_finrank_eq,hdim,hv,←pow_mul] at h
  norm_num at h
  simpa only [Nat.card_eq_fintype_card,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
    (show (Fintype.card (Submodule K (Module.Dual K V)):ℝ)≤6*(Fintype.card K:ℝ)^25 by exact_mod_cast h)

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]
  [Fintype (Submodule K (Module.Dual K V))] in
lemma rectangle_tail_scalar (q : ℝ) (hq : 0<q) :
    6*q^25*Real.exp (-(32*Real.log q))=6/q^7 := by
  have he : Real.exp (32*Real.log q)=q^32 := by
    simpa only [Real.exp_log hq,Nat.cast_ofNat] using Real.exp_nat_mul (Real.log q) 32
  rw [Real.exp_neg,he,show (32:ℕ)=25+7 by norm_num,pow_add,mul_inv_rev]
  have hp : q^25≠0 := pow_ne_zero _ (ne_of_gt hq)
  rw [mul_assoc,mul_comm ((q^7)⁻¹),←mul_assoc,←mul_assoc,mul_inv_cancel_right₀ hp]
  rfl

omit [Fintype (Submodule K (Module.Dual K V))] in
lemma rectangle_mean (hdim : finrank K V=5) (n : ℕ)
    (hn : (n:ℝ)≤(Nat.card K:ℝ)^4*Real.log (Nat.card K))
    (U : Submodule K (Module.Dual K V)) :
    (n:ℝ)*eventMass (uniform (flags_nonempty hdim)) (rectangle U)≤4*Real.log (Nat.card K) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  have hq2 : (2:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  have hlog : 0≤Real.log (Nat.card K) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ((Nat.card K:ℝ)^4*Real.log (Nat.card K))*(4/(Nat.card K:ℝ)^4) :=
      mul_le_mul hn (rectangle_mass hdim U) (eventMass_nonneg _ _) (by positivity)
    _ = _ := by field_simp

attribute [local instance] OAI.SharpRamseyFive.RectangleGeometry.instDecidableEqFlag
theorem rectangle_occupancy_tail (hdim : finrank K V=5) (n : ℕ)
    (hn : (n:ℝ)≤(Nat.card K:ℝ)^4*Real.log (Nat.card K)) :
    eventMass (iid (uniform (flags_nonempty hdim)) (Fin n))
      (Finset.univ.biUnion fun U : Submodule K (Module.Dual K V) =>
        Finset.univ.filter fun x => 40*Real.log (Nat.card K)≤hits (rectangle U) x)
      ≤6/(Nat.card K:ℝ)^7 := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  have h := all_occupancy_tail (α := Flag (K := K) (V := V))
    (ι := Submodule K (Module.Dual K V))
    (uniform (flags_nonempty hdim)) (rectangle (K := K) (V := V)) n
    (4*Real.log (Nat.card K)) (40*Real.log (Nat.card K)) (rectangle_mean hdim n hn)
  calc
    _ ≤ (Fintype.card (Submodule K (Module.Dual K V)):ℝ)*
        Real.exp (2*(4*Real.log (Nat.card K))-40*Real.log (Nat.card K)) := h
    _ ≤ (6*(Nat.card K:ℝ)^25)*Real.exp (-(32*Real.log (Nat.card K))) := by
      rw [show 2*(4*Real.log (Nat.card K))-40*Real.log (Nat.card K)=
        -(32*Real.log (Nat.card K)) by ring]
      exact mul_le_mul_of_nonneg_right (count_rectangles hdim) (Real.exp_pos _).le
    _ = _ := rectangle_tail_scalar _ hq
end SharpRamseyFive.RectangleGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_AllWindowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance boundsBDE_r56f9bb_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.boundsIDE
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V))) ]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
  {s : ℝ} (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)

lemma log_card_of_card_bound {A : Type*} (E : Finset A) (C M : ℝ)
    (hC : (E.card:ℝ)≤C) (hM : 0≤M) (hlog : Real.log C≤M) : Real.log E.card≤M := by
  by_cases he : E.card=0
  · simpa only [he,Nat.cast_zero,Real.log_zero] using hM
  · have hp : (0:ℝ)<E.card := by exact_mod_cast Nat.pos_of_ne_zero he
    exact (Real.log_le_log hp hC).trans hlog
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FlagAlphabetLogs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_card_le_two (hd : finrank K V=5) :
    (Fintype.card (ℙ K V):ℝ)≤2*(Nat.card K:ℝ)^4 := by
  have he : (Fintype.card (ℙ K V):ℝ)=∑i∈Finset.range 5,(Nat.card K:ℝ)^i := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hd]
    push_cast
    rfl
  rw [he]
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α:=K)
  have ht:=q_mul_geometric_bound (Nat.card K:ℝ) hq 5
  have hq0 : (0:ℝ)<Nat.card K := by linarith
  have hh : (Nat.card K:ℝ)*(∑i∈Finset.range 5,(Nat.card K:ℝ)^i)≤
      (Nat.card K:ℝ)*(2*(Nat.card K:ℝ)^4) := by nlinarith [ht]
  exact (mul_le_mul_iff_right₀ hq0).mp hh

omit [FiniteDimensional K V] in
lemma flagPair_log_card (hd : finrank K V=5) (σ : ℝ)
    (hσ : 0≤σ) (hq : Real.exp σ=Nat.card K) :
    Real.log (Fintype.card (FlagPair K V))≤8*σ+Real.log 4 := by
  have hp:=point_card_le_two hd
  have hb:=point_card_le_two (K:=K) (V:=Dual K V) (by simpa using hd)
  have hq0 : (0:ℝ)<Nat.card K := by rw [←hq];exact Real.exp_pos _
  have hcap : (Fintype.card (FlagPair K V):ℝ)≤4*(Nat.card K:ℝ)^8 := by
    have hh:=mul_le_mul hp hb (Nat.cast_nonneg _) (by positivity)
    simpa only [FlagPair,Fintype.card_prod,Nat.cast_mul] using hh.trans_eq (by ring)
  have hlog : Real.log (4*(Nat.card K:ℝ)^8)=8*σ+Real.log 4 := by
    rw [Real.log_mul (by norm_num) (pow_pos hq0 _).ne',Real.log_pow,←hq,Real.log_exp]
    ring
  have ht:=log_card_of_card_bound (Finset.univ : Finset (FlagPair K V))
    (4*(Nat.card K:ℝ)^8) (8*σ+Real.log 4) (by simpa using hcap)
    (by have := Real.log_nonneg (show (1:ℝ)≤4 by norm_num);positivity) hlog.le
  simpa only [Finset.card_univ] using ht

lemma incidentFlag_log_card (hd : finrank K V=5) (σ : ℝ) (hq : Real.exp σ=Nat.card K) :
    7*σ≤Real.log (Fintype.card (RectangleGeometry.Flag (K:=K) (V:=V))) := by
  have hq0 : (0:ℝ)<Nat.card K := by rw [←hq];exact Real.exp_pos _
  have hh : (Nat.card K:ℝ)^7≤Fintype.card (RectangleGeometry.Flag (K:=K) (V:=V)) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using RectangleGeometry.card_flags_lower hd)
  have ht:=Real.log_le_log (pow_pos hq0 7) hh
  simpa only [Real.log_pow,←hq,Real.log_exp,Nat.cast_ofNat] using ht
end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open FiniteEntropy
open scoped Classical BigOperators
noncomputable section

lemma log_choose_le (N n : ℕ) (hn : 0<n) (hnN : n≤N) :
    Real.log (N.choose n)≤(n:ℝ)*(Real.log N-Real.log n+1) := by
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  have hN : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hf : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hc : (0:ℝ)<N.choose n := by exact_mod_cast Nat.choose_pos hnN
  have h1:=Real.log_le_log hc (Nat.choose_le_pow_div (α:=ℝ) n N)
  rw [Real.log_div (pow_pos hN _).ne' hf.ne',Real.log_pow] at h1
  have h2:=Real.log_le_log (div_pos (pow_pos hp _) hf)
    (Real.pow_div_factorial_le_exp (n:ℝ) hp.le n)
  rw [Real.log_div (pow_pos hp _).ne' hf.ne',Real.log_pow,Real.log_exp] at h2
  nlinarith

variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω] [Nonempty α]
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

omit [Fintype β] [Nonempty α] in
lemma SelectedStream.density_pos (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) :
    0<S.density := by
  have hx : 0<∑ s,map S.law S.stream s := by rw [(map S.law S.stream).sum_one]; norm_num
  obtain ⟨s,_,hs⟩:=Finset.sum_pos_iff_of_nonneg (fun s _=>(map S.law S.stream).nonneg s) |>.mp hx
  have hp:=lt_of_lt_of_le hs (S.density_bound s)
  exact (div_pos_iff.mp hp).resolve_right
    (fun h=>(pow_nonneg (Nat.cast_nonneg _) _).not_gt h.2) |>.1

theorem SelectedStream.entropy_lower_explicit (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (hn : 0<n) (hnN : n≤N) :
    (n:ℝ)*(Real.log (Fintype.card α)-Real.log N+Real.log n-1)-Real.log (2*S.density)≤
      entropy (map S.law S.tuple) := by
  have hα : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc : (0:ℝ)<N.choose n := by exact_mod_cast Nat.choose_pos hnN
  have hd : 0<2*S.density := mul_pos (by norm_num) S.density_pos
  have h:=S.entropy_lower hnN
  rw [Real.log_div (mul_pos hd hc).ne' (pow_pos hα _).ne',
    Real.log_mul hd.ne' hc.ne',Real.log_pow] at h
  have hb:=log_choose_le N n hn hnN
  apply le_trans _ h
  have hh:=add_le_add_right (neg_le_neg hb)
    ((n:ℝ)*Real.log (Fintype.card α)-Real.log (2*S.density))
  convert hh using 1 <;> ring

theorem SelectedStream.flag_entropy_lower (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (σ : ℝ) (hσ : 0<σ) (hn : 0<n) (hnN : n≤N)
    (hα : 7*σ≤Real.log (Fintype.card α))
    (hN : (N:ℝ)≤Real.exp (4*σ)*σ) :
    4*σ*n+(n:ℝ)*(Real.log n-σ-Real.log σ-1)-Real.log (2*S.density)≤
      entropy (map S.law S.tuple) := by
  have hNpos : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hlogN:=Real.log_le_log hNpos hN
  rw [Real.log_mul (Real.exp_pos _).ne' hσ.ne',Real.log_exp] at hlogN
  have nn : (0:ℝ)≤n := Nat.cast_nonneg _
  have h:=S.entropy_lower_explicit hn hnN
  nlinarith

theorem SelectedStream.flag_entropy_lower_fraction
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (σ η c C : ℝ) (hσ : 0<σ) (hc : 0 < c) (hC : S.density≤C)
    (hn : 0<n) (hnN : n≤N) (hα : 7*σ≤Real.log (Fintype.card α))
    (hN : (N:ℝ)≤Real.exp (4*σ)*σ)
    (hlen : c*Real.exp σ*σ^(1+η)≤n) :
    4*σ*n+η*n*Real.log σ+(n:ℝ)*(Real.log c-1)-Real.log (2*C)≤
      entropy (map S.law S.tuple) := by
  have hp : 0 < c*Real.exp σ*σ^(1+η) := mul_pos (mul_pos hc (Real.exp_pos _))
    (Real.rpow_pos_of_pos hσ _)
  have hlogn:=Real.log_le_log hp hlen
  rw [Real.log_mul (mul_pos hc (Real.exp_pos _)).ne'
      (Real.rpow_pos_of_pos hσ _).ne',
    Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_exp,
    Real.log_rpow hσ] at hlogn
  have hlogC:=Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<2) S.density_pos)
    (mul_le_mul_of_nonneg_left hC (by norm_num))
  have h:=S.flag_entropy_lower σ hσ hn hnN hα hN
  have nn : (0:ℝ)≤n := Nat.cast_nonneg _
  nlinarith
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open FiniteEntropy
noncomputable section
variable {Ω α β : Type} [Fintype Ω] [Fintype α] [Fintype β]
  {N n : ℕ} {admissible : (Fin N→α)→Prop}
omit [Fintype β] in
lemma SelectedStream.length_le_source (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) : n≤N := by
  obtain ⟨z,hz⟩:=S.law.exists_positive
  obtain ⟨e,he⟩:=(mem_occurrences_iff _ _).mp (S.selected z hz)
  have h:=Fintype.card_le_of_injective e e.injective
  simpa only [Fintype.card_fin] using h
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FinalMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
attribute [local instance] OAI.SharpRamseyFive.Marking.finalMarkingDecEq
variable {K V κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N : ℕ}

theorem final_marking_entropy (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (S : κ→Fin N→Finset (FlagPair K V)) (cap L : ℝ) (hcap : 1 ≤ cap)
    (hS : ∀ c i,((S c i).card:ℝ) ≤ cap)
    (hsupp : ∀ c x,0<p (c,x)→∀ i,x i∈S c i)
    (hΔ : Real.log (153*(Nat.card K:ℝ)^4)≤Real.log cap)
    (hctx : entropy (first p)≤L) :
    entropy (second p)≤(N:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)+L+(N:ℝ)*Real.log 800+
      (800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))))*
      (Real.log cap-Real.log (153*(Nat.card K:ℝ)^4)) := by
  let J:=Real.log (153*(Nat.card K:ℝ)^4)
  have hd:=marking_expected_deficit hdim p hc S cap J ((N:ℝ)*J-entropy (second p)) L
    hcap hS hsupp (sub_nonneg.mpr hΔ) le_rfl hctx
  have hn : 0 ≤ mean (first (withMessage p markingMessage))
      (fun z=>activeDeficit (fiber (withMessage p markingMessage) z) (unspecified z.2) J) := by
    have hh:=mean_mono_pos (first (withMessage p markingMessage)) (f:=fun _=>0)
      (g:=fun z=>activeDeficit (fiber (withMessage p markingMessage) z) (unspecified z.2) J)
      (fun z hz=>marking_deficit_nonneg hdim p hf hc z.1 z.2 hz)
    simpa only [mean_const] using hh
  dsimp [J] at hd hn
  linarith

end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.cfmFinDE
variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
  [Fintype α] {N n : ℕ} {adm : (Fin N→α)→Prop} {d Λ Δ M : ℝ}
lemma CodedStream.final_entropy_bound (hd : finrank K V=5) (hΔ : 0≤Δ)
    (S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M) :
    entropy (map S.stream.law S.stream.tuple)≤n*Real.log (153*(Nat.card K:ℝ)^4)+Λ+
      n*Real.log 800+expensiveBound K V*Δ := by
  have hcheap : 0≤Real.log (153*(Nat.card K:ℝ)^4) := by
    apply Real.log_nonneg
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
    have hh:=one_le_pow₀ (n:=4) hq
    linarith
  let p:=pair S.stream.law S.description.context S.stream.tuple
  have hp : ∀c x,0<p (c,x)→∃z,0<S.stream.law z ∧
      (S.description.context z,S.stream.tuple z)=(c,x) := by
    intro c x hx
    exact map_positive S.stream.law (fun z=>(S.description.context z,S.stream.tuple z)) (c,x) hx
  have h:=final_marking_entropy hd p
    (fun c x hx=>by obtain ⟨z,hz,he⟩:=hp c x hx;cases he;exact S.geometric.incident z hz)
    (fun c x hx=>by obtain ⟨z,hz,he⟩:=hp c x hx;cases he;exact S.geometric.consistent z hz)
    S.description.cleanDomain (Real.exp (Real.log (153*(Nat.card K:ℝ)^4)+Δ)) Λ
    (Real.one_le_exp_iff.mpr (add_nonneg hcheap hΔ)) S.description.clean_cap
    (fun c x hx=>by obtain ⟨z,hz,he⟩:=hp c x hx;cases he;exact S.description.clean_contains z hz)
    (by rw [Real.log_exp];linarith)
    (by simpa only [p,first_pair] using S.description.entropy_bound)
  simpa only [p,second_pair,Real.log_exp,add_sub_cancel_left,expensiveBound] using h
end
end SharpRamseyFive.SelectedTuple

namespace SharpRamseyFive.SelectedTuple
open FiniteEntropy Filter
open scoped Classical
noncomputable section

theorem eventually_stream_entropy_gain {η : ℝ} (hη : 0<η) (c C A : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ (Ω α β : Type) [Fintype Ω] [Fintype α] [Fintype β] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (S : SelectedStream (Ω:=Ω) (β:=β) N n adm),
      1≤σ→7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      (n:ℝ)*(4*σ+Real.log 153+A)≤entropy (map S.law S.tuple) := by
  have ht : Tendsto (fun σ : ℝ=>η*Real.log σ) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hη
  have he : Tendsto (fun σ : ℝ=>c*Real.exp σ) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  filter_upwards [ht.eventually_ge_atTop (Real.log 153+A+2-Real.log c),
    he.eventually_ge_atTop (Real.log (2*C))] with σ ht he
  intro Ω α β _ _ _ _ N n adm S hσ hα hN hlen hC
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hn : 0<n := by
    have hh : 0<(n:ℝ) := (by positivity : 0 < c*Real.exp σ*σ^(1+η)).trans_le hlen
    exact_mod_cast hh
  have hlog : Real.log (2*C)≤n := by
    have hp : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ c*Real.exp σ)
    nlinarith
  have hb:=S.flag_entropy_lower_fraction σ η c C hs hc hC hn S.length_le_source hα hN hlen
  have hh:=mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg n)
  nlinarith
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MarkingNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_log_one_add_card (hd : finrank K V=5) (σ : ℝ)
    (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) :
    Real.log (1+Fintype.card (ℙ K V))≤6*σ := by
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hp:=point_card_le_two hd
  have hh : (1:ℝ)+Fintype.card (ℙ K V)≤3*(Nat.card K:ℝ)^4 := by
    have hh : (1:ℝ)≤(Nat.card K:ℝ)^4 := one_le_pow₀ hq1
    linarith
  have ht:=Real.log_le_log (by positivity : (0:ℝ)<1+Fintype.card (ℙ K V)) hh
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,←hq,Real.log_exp] at ht
  have hl : Real.log 3≤2 := by have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3);linarith
  norm_num only [Nat.cast_ofNat] at ht
  linarith
omit [FiniteDimensional K V] in
lemma expensiveBound_coarse [Fintype (ℙ K (Dual K (Dual K V)))] (hd : finrank K V=5) (σ : ℝ)
    (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) :
    expensiveBound K V≤9600*Real.exp σ*σ := by
  have ha:=point_log_one_add_card hd σ hσ hq
  have hb:=point_log_one_add_card (K:=K) (V:=Dual K V) (by simpa using hd) σ hσ hq
  unfold expensiveBound
  rw [←hq]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hb ha) (by positivity : (0:ℝ)≤800*Real.exp σ)]

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_StageNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics Real
open scoped Topology
noncomputable section

theorem eventually_stage_recurrence {η : ℝ} (hη : 0<η) (CΔ : ℝ) (_hCΔ : 0≤CΔ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D A Δ : ℝ),0≤D→A≤D*σ^(-η/3)→Δ≤CΔ*D*σ^(6*beta η)→
      σ^beta η*(1+A+Δ*σ^(-η))≤σ^(2*beta η)+D*σ^(-η/4) := by
  have h1 : 0<η/12-beta η := by unfold beta;linarith
  have h2 : 0<3*η/4-7*beta η := by unfold beta;linarith
  have ht1:=tendsto_rpow_neg_atTop h1
  have ht2 : Tendsto (fun σ : ℝ=>CΔ*σ^(-(3*η/4-7*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop h2).const_mul CΔ
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht1.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    ht2.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with σ hσ hs1 hs2
  intro D A Δ hD hA hΔ
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hbase : σ^beta η≤σ^(2*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη;linarith)
  have hp1 : σ^beta η*(D*σ^(-η/3))=D*σ^(-η/4)*σ^(-(η/12-beta η)) := by
    calc
      _ =D*(σ^beta η*σ^(-η/3)) := by ring
      _ =_ := by rw [←Real.rpow_add hs,mul_assoc,←Real.rpow_add hs];congr 2;ring
  have hp2 : σ^beta η*(CΔ*D*σ^(6*beta η)*σ^(-η))=
      D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η))) := by
    calc
      _ =CΔ*D*(σ^beta η*σ^(6*beta η)*σ^(-η)) := by ring
      _ =_ := by rw [←Real.rpow_add hs,←Real.rpow_add hs];
                 rw [show D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η)))=
                   CΔ*D*(σ^(-η/4)*σ^(-(3*η/4-7*beta η))) by ring,
                   ←Real.rpow_add hs];congr 2;ring
  calc
    _ ≤ σ^beta η*(1+D*σ^(-η/3)+(CΔ*D*σ^(6*beta η))*σ^(-η)) := by gcongr
    _ = σ^beta η+D*σ^(-η/4)*σ^(-(η/12-beta η))+
        D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η))) := by
      rw [mul_add,mul_add,mul_one,hp1,hp2]
    _ ≤ σ^(2*beta η)+D*σ^(-η/4)*(1/2)+D*σ^(-η/4)*(1/2) := by gcongr
    _ = _ := by ring
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalStageArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking ProjectiveIncidence SelectedTuple
open scoped Topology NNReal
noncomputable section

lemma domainSlackConstant_pos : 0<domainSlackConstant := by
  have h1 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : 0≤Real.log (2*(320/(9/100000)+320)^2) := Real.log_nonneg (by norm_num)
  unfold domainSlackConstant
  linarith

end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_TerminalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.tsFinDE
theorem eventually_no_terminal_stream {η : ℝ} (hη : 0<η) (c d : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (Λ Δ M k₀ : ℝ)
      (_S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      Λ≤k₀→0≤Δ→Δ ≤ c/9600*σ^η→False := by
  filter_upwards [eventually_stream_entropy_gain hη c d (2+1/c+Real.log 800) hc] with σ hent
  intro K V α _ _ _ _ _ _ _ _ _ _ _ _ _ N n adm Λ Δ M k₀ S
    hd hσ hq hα hN hlen hk hΛ hΔ hΔhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hp : (0:ℝ)<Nat.card K := by rw [←hq];positivity
  have hn : 0<(n:ℝ) := (by positivity : 0 < c*(Nat.card K:ℝ)*σ^(1+η)).trans_le hlen
  have hlow:=hent S.sample α (FlagPair K V) N n adm S.stream hσ hα hN
    (by simpa only [hq] using hlen) S.density_bound
  have hfin:=S.final_entropy_bound hd hΔ
  have hE:=expensiveBound_coarse (K:=K) (V:=V) hd σ hσ hq
  rw [hq] at hE
  have hEC : expensiveBound K V*Δ≤(n:ℝ) := by
    calc
      _ ≤ (9600*(Nat.card K:ℝ)*σ)*(c/9600*σ^η) :=
        mul_le_mul hE hΔhi hΔ (by positivity)
      _ = c*(Nat.card K:ℝ)*σ^(1+η) := by rw [Real.rpow_add hs,Real.rpow_one];ring
      _ ≤ n := hlen
  have hΛhi : Λ≤(n:ℝ)/c := by
    apply hΛ.trans
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hJ : Real.log (153*(Nat.card K:ℝ)^4)=4*σ+Real.log 153 := by
    rw [Real.log_mul (by norm_num) (pow_pos hp _).ne',Real.log_pow,←hq,Real.log_exp]
    norm_num;ring
  conv_rhs at hfin => rw [hJ]
  have hdiv : (n:ℝ)/c=(n:ℝ)*(1/c) := by ring
  rw [hdiv] at hΛhi
  have hlow' : (n:ℝ)*(4*σ+Real.log 153+(2+1/c+Real.log 800))≤entropy (map S.stream.law S.stream.tuple) := by
    convert hlow using 1; congr 1; exact Subsingleton.elim _ _
  nlinarith only [hlow',hfin,hEC,hΛhi,hn]
end

noncomputable section
variable (K α : Type) [Field K] [Finite K] [Fintype α]

attribute [instance] PolarState.group PolarState.module PolarState.dimension PolarState.points
  PolarState.hyperplanes PolarState.bipoints PolarState.pointNonempty PolarState.planeNonempty
  PolarState.bipointNonempty
variable {K α}

theorem eventually_polar_terminal {η : ℝ} (hη : 0<η) (c d : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ (K α : Type) [Field K] [Finite K] [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (Λ Δ M k₀ : ℝ)
      (_S : PolarState K α N n adm d Λ Δ M),
      1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      Λ≤k₀→0≤Δ→Δ ≤ c/9600*σ^η→False := by
  filter_upwards [eventually_no_terminal_stream hη c d hc] with σ h
  intro K α _ _ _ _ N n adm Λ Δ M k₀ S hσ hq hα hN hlen hk hΛ hΔ hΔhi
  exact h K S.ambient α N n adm Λ Δ M k₀ S.coded S.dim hσ hq hα hN hlen hk hΛ hΔ hΔhi
end
end

open FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]

omit [Fintype α] [Nonempty α] in
lemma firstWitness_spec {N n : ℕ} (hn : n≤N)
    (P : (Fin N→α)→(Fin n↪o Fin N)→Prop) (s : Fin N→α)
    (h : ∃ e,P s e) : P s (firstWitness hn P s) := by
  simp only [firstWitness,dite_eq_left h]
  exact h.choose_spec

end

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlagGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FlagConstruction

open scoped LinearAlgebra.Projectivization
open Module

variable {K : Type*} [Field K]

lemma incident_iff (a : Point K) (b : DualPoint K) :
    Incident a b ↔ b.rep a.rep = 0 := by
  rw [Incident, Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    LinearMap.mem_ker]

lemma adj_iff_of_lt {N : ℕ} (X : Fin N → Flag K) {i j : Fin N} (h : i < j) :
    (graph X).Adj i j ↔ Incident (X i).1.1 (X j).1.2 ∧
      ¬ Incident (X j).1.1 (X i).1.2 := by
  simp only [graph, h, true_and, not_lt_of_ge h.le, false_and, or_false]

private lemma five_independent {v : Fin 5 → Space K}
    {b : Fin 5 → Module.Dual K (Space K)} (hv : v 0 ≠ 0)
    (hz : ∀ i j, i ≤ j → b j (v i) = 0)
    (hn : ∀ i j, i < j → b i (v j) ≠ 0) : LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : c 0 • v 0 + c 1 • v 1 + c 2 • v 2 + c 3 • v 3 + c 4 • v 4 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hc
  have h4 : c 4 = 0 := by
    have h := congrArg (b 3) hsum
    simp only [map_add, map_smul, map_zero] at h
    simp only [hz 0 3 (by decide), hz 1 3 (by decide), hz 2 3 (by decide),
      hz 3 3 le_rfl, smul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (hn 3 4 (by decide))
  have h3 : c 3 = 0 := by
    have h := congrArg (b 2) hsum
    simp only [map_add, map_smul, map_zero, h4, zero_smul, add_zero] at h
    simp only [hz 0 2 (by decide), hz 1 2 (by decide), hz 2 2 le_rfl,
      smul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (hn 2 3 (by decide))
  have h2 : c 2 = 0 := by
    have h := congrArg (b 1) hsum
    simp only [map_add, map_smul, map_zero, h4, h3, zero_smul, add_zero] at h
    simp only [hz 0 1 (by decide), hz 1 1 le_rfl, smul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (hn 1 2 (by decide))
  have h1 : c 1 = 0 := by
    have h := congrArg (b 0) hsum
    simp only [map_add, map_smul, map_zero, h4, h3, h2, zero_smul, add_zero] at h
    simp only [hz 0 0 le_rfl, smul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (hn 0 1 (by decide))
  have h0 : c 0 = 0 := by
    simp only [h4, h3, h2, h1, zero_smul, add_zero] at hsum
    exact (smul_eq_zero.mp hsum).resolve_right hv
  intro i
  fin_cases i <;> assumption

theorem cliqueFree_five {N : ℕ} (X : Fin N → Flag K) : (graph X).CliqueFree 5 := by
  intro s hs
  let e : Fin 5 ↪o Fin N := s.orderEmbOfFin hs.card_eq
  have he (i : Fin 5) : e i ∈ s := s.orderEmbOfFin_mem hs.card_eq i
  have hadj (i j : Fin 5) (hij : i < j) :
      Incident (X (e i)).1.1 (X (e j)).1.2 ∧
      ¬ Incident (X (e j)).1.1 (X (e i)).1.2 := by
    apply (adj_iff_of_lt X (e.strictMono hij)).mp
    exact hs.isClique (he i) (he j) (ne_of_lt (e.strictMono hij))
  let v : Fin 5 → Space K := fun i => (X (e i)).1.1.rep
  let b : Fin 5 → Module.Dual K (Space K) := fun i => (X (e i)).1.2.rep
  have hz (i j : Fin 5) (hij : i ≤ j) : b j (v i) = 0 := by
    apply (incident_iff _ _).mp
    rcases lt_or_eq_of_le hij with h | rfl
    · exact (hadj i j h).1
    · exact (X (e i)).2
  have hn (i j : Fin 5) (hij : i < j) : b i (v j) ≠ 0 := by
    exact fun h => (hadj i j hij).2 ((incident_iff _ _).mpr h)
  have hli : LinearIndependent K v := five_independent (Projectivization.rep_nonzero _) hz hn
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Space])
  have hker : Submodule.span K (Set.range v) ≤ LinearMap.ker (b 4) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hz i 4 (by omega)
  rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hker
  exact (X (e 4)).1.2.rep_nonzero hker

end SharpRamseyFive.FlagConstruction

namespace SharpRamseyFive.FlagConstruction
open Module SharpRamseyFive.Marking SharpRamseyFive.FiniteEntropy SharpRamseyFive.SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K : Type*} [Field K] {N n : ℕ}

lemma independent_selector_of_not_cliqueFree (X : Fin N → Flag K)
    (h : ¬(graph X)ᶜ.CliqueFree n) :
    ∃ e : Fin n ↪o Fin N, TupleIncident (fun i=>(X (e i)).val) ∧
      TupleConsistent (fun i=>(X (e i)).val) := by
  rw [SimpleGraph.CliqueFree] at h
  push Not at h
  obtain ⟨s,hs⟩:=h
  let e : Fin n ↪o Fin N:=s.orderEmbOfFin hs.card_eq
  have he : ∀ i,e i∈s := fun i=>s.orderEmbOfFin_mem hs.card_eq i
  refine ⟨e,fun i=>(X (e i)).property,?_⟩
  intro i j hij hab
  by_contra hba
  have hadj:=hs.isClique (he i) (he j) (ne_of_lt (e.strictMono hij))
  have hg : (graph X).Adj (e i) (e j) :=
    (adj_iff_of_lt X (e.strictMono hij)).mpr ⟨hab,hba⟩
  exact hadj.2 hg

variable [Nonempty (Flag K)]

lemma encodeRaw_leftInverse : Function.LeftInverse (encodeRaw (K:=K)) Subtype.val := by
  intro x
  apply Subtype.ext
  simp only [encodeRaw,dite_eq_left x.property]

end
end SharpRamseyFive.FlagConstruction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_InitialPolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive

namespace FlagConstruction
open Module ProjectiveIncidence FiniteEntropy SelectedTuple CoreGeometry Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K : Type} [Field K] [Finite K]
  [Fintype (Point K)] [Fintype (DualPoint K)]
  [Fintype (ℙ K (Dual K (Dual K (Space K))))]
  [Fintype (Submodule K (Dual K (Space K)))]
  [Nonempty (RectangleGeometry.Flag (K:=K) (V:=Space K))] [Nonempty (Point K)] [Nonempty (DualPoint K)]
  [Nonempty (ℙ K (Dual K (Dual K (Space K))))]

omit [Finite K] [Fintype (ℙ K (Dual K (Dual K (Space K))))]
  [Fintype (Submodule K (Dual K (Space K)))]
  [Nonempty (RectangleGeometry.Flag (K:=K) (V:=Space K))]
  [Nonempty (Point K)] [Nonempty (DualPoint K)]
  [Nonempty (ℙ K (Dual K (Dual K (Space K))))] in
lemma rectangle_mem_iff (U : Submodule K (Dual K (Space K))) (x : RectangleGeometry.Flag (K:=K) (V:=Space K)) :
    x∈RectangleGeometry.rectangle U ↔ InRectangle U x.val.1.rep x.val.2.rep := by
  simp [RectangleGeometry.rectangle,InRectangle,rep_mem_iff]

theorem initial_polar_of_no_graph {N n : ℕ} (hn : n≤N) (σ : ℝ)
    (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hq3 : 3≤Nat.card K)
    (hN : (N:ℝ)≤(Nat.card K:ℝ)^4*σ)
    (hno : ∀s : Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K),¬(graph s)ᶜ.CliqueFree n) :
    ∃ adm : (Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K))→Prop,
      Nonempty (PolarState K (RectangleGeometry.Flag (K:=K) (V:=Space K)) N n adm 2 0 (10*σ) (40*σ)) := by
  let : Nonempty (Flag K) := ‹Nonempty (RectangleGeometry.Flag (K:=K) (V:=Space K))›
  have hd : finrank K (Space K)=5 := by simp [Space]
  have hs : 0≤σ := by linarith
  have hqp : (0:ℝ)<Nat.card K := by rw [←hq];positivity
  have hlog : Real.log (Nat.card K)=σ := by rw [←hq,Real.log_exp]
  let bad : Finset (Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K)) := Finset.univ.biUnion fun U : Submodule K (Dual K (Space K)) =>
    Finset.univ.filter fun x=>40*Real.log (Nat.card K)≤hits (RectangleGeometry.rectangle U) x
  let E:=badᶜ
  let p:Law (Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K)):=iid (uniform Fintype.card_pos) (Fin N)
  have hbad : eventMass p bad≤6/(Nat.card K:ℝ)^7 := by
    have hh:=RectangleGeometry.rectangle_occupancy_tail hd N
      (by simpa only [hlog] using hN)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp [bad]
  have htail : 6/(Nat.card K:ℝ)^7≤1/2 := by
    have hq' : (3:ℝ)≤Nat.card K := by exact_mod_cast hq3
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hq' 7
    rw [div_le_iff₀ (pow_pos hqp 7)]
    norm_num at hp ⊢
    linarith
  have hmass : 1/2≤eventMass p E := by
    have hc : eventMass p E+eventMass p bad=1 := by
      convert eventMass_complement p bad using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      ext x
      simp [E]
    have hh:=hbad.trans htail
    linarith only [hc,hh]
  have hE : 0<eventMass p E := lt_of_lt_of_le (by norm_num) hmass
  let adm:=fun s : Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K) => ∀U : Submodule K (Dual K (Space K)),
    (∑i,if InRectangle U (s i).val.1.rep (s i).val.2.rep then (1:ℝ) else 0)≤40*σ
  have hgood : ∀s,s∈E→adm s := by
    intro s hs U
    have hh : ¬40*σ≤hits (RectangleGeometry.rectangle U) s := by
      intro hh
      exact Finset.mem_compl.mp hs (Finset.mem_biUnion.mpr ⟨U,Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hlog] using hh⟩⟩)
    have he : hits (RectangleGeometry.rectangle U) s=
        ∑i,if InRectangle U (s i).val.1.rep (s i).val.2.rep then (1:ℝ) else 0 := by
      simp only [hits,rectangle_mem_iff]
    rw [he] at hh
    exact (not_le.mp hh).le
  let P:=fun (s : Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K)) (e : Fin n↪o Fin N) =>
    TupleIncident (fun i=>(s (e i)).val) ∧ TupleConsistent (fun i=>(s (e i)).val)
  let choose:=firstWitness hn P
  have hchoose : ∀s,P s (choose s) := fun s=>firstWitness_spec hn P s
    (independent_selector_of_not_cliqueFree s (hno s))
  let S:=initialSelectedStream adm E hE hgood choose Subtype.val encodeRaw encodeRaw_leftInverse
  have hgeom : Geometric S (40*σ) := by
    refine ⟨fun z _=>(hchoose z).1,fun z _=>(hchoose z).2,?_⟩
    intro z hz
    exact occupancy_reindex (fun i=>(z i).val) (choose z) (choose z).injective (40*σ)
      (hgood z (conditionOn_positive p E hE z hz).1)
  have hcap : Real.log (Fintype.card (FlagPair K (Space K)))≤
      Real.log (153*(Nat.card K:ℝ)^4)+10*σ := by
    have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
    have hj : Real.log 4≤Real.log (153*(Nat.card K:ℝ)^4) := by
      apply Real.log_le_log (by norm_num)
      have hh : (1:ℝ)≤(Nat.card K:ℝ)^4 := one_le_pow₀ hq1
      nlinarith
    have hh:=flagPair_log_card hd σ hs hq
    linarith
  let C : ContextDescription (κ:=Unit) S.law S.tuple 0
      (Real.log (153*(Nat.card K:ℝ)^4)+10*σ) :=
    { context:=fun _=>()
      domain:=fun _ _=>Finset.univ
      entropy_bound:=by simpa using entropy_le_log_card (map S.law (fun _=>()))
      contains:=by intros;exact Finset.mem_univ _
      cap:=by intros;simpa only [Finset.card_univ] using hcap }
  have hden : S.density≤2 := by
    change 1/eventMass p E≤2
    rw [div_le_iff₀ hE]
    linarith
  exact ⟨adm,⟨PolarState.of hd {
    sample:=Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K)
    stream:=S
    code:=Unit
    description:=C
    density_bound:=hden
    geometric:=hgeom }⟩⟩
end
end FlagConstruction

open Filter
open scoped Topology
noncomputable section
lemma initial_floor_scales {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,
      1≤σ ∧ 3≤Real.exp σ ∧
      ⌊Real.exp σ*σ^(1+η)⌋₊≤⌊(Real.exp σ)^4*σ⌋₊ ∧
      (1/2:ℝ)*Real.exp σ*σ^(1+η)≤(⌊Real.exp σ*σ^(1+η)⌋₊:ℝ) := by
  have hg : Tendsto (fun σ : ℝ=>Real.exp σ) atTop atTop := Real.tendsto_exp_atTop
  filter_upwards [eventually_ge_atTop (1:ℝ),hg.eventually_ge_atTop 3] with σ hs hq
  have hsp : 0<σ := zero_lt_one.trans_le hs
  have hqp : 0<Real.exp σ := Real.exp_pos _
  have ht : 1≤σ^(1+η) := Real.one_le_rpow hs (by linarith)
  have hp : σ^η≤σ := by
    nth_rw 2 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have hσq : σ≤Real.exp σ := le_trans (by linarith : σ≤σ+1) (Real.add_one_le_exp σ)
  have hq1 : 1≤Real.exp σ := by linarith
  have hq3 : Real.exp σ≤(Real.exp σ)^3 := by
    have hh : 1≤(Real.exp σ)^2 := one_le_pow₀ hq1
    nlinarith
  have hp' : Real.exp σ*σ^(1+η)≤(Real.exp σ)^4*σ := by
    rw [Real.rpow_add hsp,Real.rpow_one]
    have hh:=mul_le_mul_of_nonneg_left (hp.trans (hσq.trans hq3))
      (show 0≤Real.exp σ*σ by positivity)
    nlinarith only [hh]
  have hlo : 2≤Real.exp σ*σ^(1+η) := by nlinarith
  have hf:=Nat.lt_floor_add_one (Real.exp σ*σ^(1+η))
  exact ⟨hs,hq,Nat.floor_mono hp',by linarith⟩
end

end SharpRamseyFive

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CompressionRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter
open scoped Topology
noncomputable section

theorem finite_affine_recurrence (a b d : ℝ) (D : ℕ→ℝ)
    (hb : 0≤b) (hb' : b<1) (hD : D 0≤d)
    (hstep : ∀n,D (n+1)≤a+b*D n) :
    ∀n,D n≤a/(1-b)*(1-b^n)+b^n*d := by
  intro n
  induction n with
  | zero => simpa using hD
  | succ n ih =>
    apply (hstep n).trans
    have hineq:=mul_le_mul_of_nonneg_left ih hb
    have hnz : 1-b≠0 := ne_of_gt (sub_pos.mpr hb')
    calc
      a+b*D n≤a+b*(a/(1-b)*(1-b^n)+b^n*d) := add_le_add le_rfl hineq
      _ = a/(1-b)*(1-b^(n+1))+b^(n+1)*d := by rw [pow_succ]; field_simp; ring

theorem compression_recurrence_terminal (σ η β : ℝ) (m : ℕ) (D : ℕ→ℝ)
    (hσ : 1≤σ) (_hη : 0<η) (_hβ : 0≤β)
    (ha : 2≤σ^(2*β)) (hr : σ^(-η/4)≤(1:ℝ)/3)
    (hm : 1≤η*(m:ℝ)/4) (hD : D 0≤σ)
    (hstep : ∀n,D (n+1)≤σ^(2*β)+D n*σ^(-η/4)) :
    D m≤2*σ^(2*β) := by
  have hs : 0<σ := lt_of_lt_of_le zero_lt_one hσ
  have hp : 0≤σ^(-η/4) := Real.rpow_nonneg hs.le _
  have hb : σ^(-η/4)<1 := lt_of_le_of_lt hr (by norm_num)
  have hh:=finite_affine_recurrence (σ^(2*β)) (σ^(-η/4)) σ D hp hb hD
    (fun n=>by simpa only [mul_comm] using hstep n) m
  have hnon : 0≤σ^(2*β) := Real.rpow_nonneg hs.le _
  have hden : (2:ℝ)/3≤1-σ^(-η/4) := by linarith
  have hfac : σ^(2*β)/(1-σ^(-η/4))≤(3/2)*σ^(2*β) := by
    have h:=div_le_div_of_nonneg_left hnon (by norm_num : (0:ℝ)<2/3) hden
    calc
      _ ≤ σ^(2*β)/(2/3) := h
      _ = _ := by ring
  have htail : (σ^(-η/4))^m*σ≤1 := by
    calc
      _ = σ^((-η/4)*(m:ℝ)+1) := by
        rw [Real.rpow_add hs,Real.rpow_one,Real.rpow_mul hs.le,Real.rpow_natCast]
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hσ (by nlinarith)
  have hpow0 : 0≤(σ^(-η/4))^m := pow_nonneg hp _
  have hquot0 : 0≤σ^(2*β)/(1-σ^(-η/4)) := div_nonneg hnon (sub_nonneg.mpr hb.le)
  have hprod : σ^(2*β)/(1-σ^(-η/4))*(1-(σ^(-η/4))^m)≤(3/2)*σ^(2*β) := by
    apply le_trans _ hfac
    nlinarith
  linarith
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IteratedBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma iterD_eq (σ η : ℝ) (n : ℕ) :
    iterD σ η n=σ^beta η*(1+iterA σ η n+iterDelta σ η n*σ^(-η)) := by
  cases n  <;> simp [iterD,iterA,iterDelta]
lemma iter_budgets_nonneg {σ η : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    σ^beta η ≤ iterD σ η n ∧ 0 ≤ iterA σ η n ∧ 0 ≤ iterDelta σ η n := by
  have hC:=domainSlackConstant_pos.le
  have hb:=Real.rpow_nonneg hσ (beta η)
  induction n with
  | zero => dsimp [iterD,iterA,iterDelta];constructor
            · have hh : 0 ≤ 10*σ*σ^(-η) := by positivity
              nlinarith
            · constructor  <;> positivity
  | succ n ih =>
    have hd : 0 ≤ iterD σ η n := hb.trans ih.1
    have hA : 0 ≤ iterD σ η n*σ^(-η/3) := by positivity
    have hΔ : 0 ≤ domainSlackConstant*iterD σ η n*σ^(6*beta η) := by positivity
    dsimp only [iterD,iterA,iterDelta]
    refine ⟨?_,hA,hΔ⟩
    have hh : 0 ≤ domainSlackConstant*iterD σ η n*σ^(6*beta η)*σ^(-η) := by positivity
    nlinarith

theorem eventually_iterD_range {η : ℝ} (hη : 0 < η) (hη' : η < 1/10) :
    ∀ᶠ σ : ℝ in atTop,∀n,iterD σ η n ≤ σ^(1-η/2) := by
  have he0 : 0 < η/2-beta η := by unfold beta;linarith
  have he1 : 0 < 1-η/2-2*beta η := by unfold beta;linarith
  have ht0 : Tendsto (fun σ : ℝ=>11*σ^(-(η/2-beta η))) atTop (𝓝 0) :=
    by simpa using (tendsto_rpow_neg_atTop he0).const_mul 11
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht0.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    (tendsto_rpow_neg_atTop he1).eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
    (tendsto_rpow_neg_atTop (by linarith : 0 < η/4)).eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
    eventually_stage_recurrence hη domainSlackConstant domainSlackConstant_pos.le]
    with σ hσ h0 h1 hratio hrec
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hbase : σ^(2*beta η) ≤ (1/2)*σ^(1-η/2) := by
    have hh:=mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg hs.le (1-η/2))
    have hid : σ^(-(1-η/2-2*beta η))*σ^(1-η/2)=σ^(2*beta η) := by
      rw [←Real.rpow_add hs];congr 1;ring
    rwa [hid] at hh
  have hr : σ^(-η/4) ≤ (1:ℝ)/2 := by simpa only [neg_div] using hratio.le
  intro n
  induction n with
  | zero =>
    have hpow : 1 ≤ σ^(1-η) := Real.one_le_rpow hσ (by linarith)
    have hid : 10*σ*σ^(-η)=10*σ^(1-η) := by rw [Real.rpow_sub hs,Real.rpow_one,Real.rpow_neg hs.le];ring
    have hinit : iterD σ η 0 ≤ 11*σ^(1-η+beta η) := by
      dsimp [iterD]
      rw [hid]
      calc
        _  ≤  σ^beta η*(11*σ^(1-η)) := by gcongr;nlinarith
        _ = _ := by rw [mul_left_comm,←Real.rpow_add hs];congr 2;ring
    apply hinit.trans
    have hh:=mul_le_mul_of_nonneg_right h0.le (Real.rpow_nonneg hs.le (1-η/2))
    have hid' : (11*σ^(-(η/2-beta η)))*σ^(1-η/2)=11*σ^(1-η+beta η) := by
      rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
    simpa only [hid',one_mul] using hh
  | succ n ih =>
    have hd:=(iter_budgets_nonneg (η:=η) hs.le n).1
    have h:=hrec (iterD σ η n) (iterA σ η (n+1)) (iterDelta σ η (n+1))
      ((Real.rpow_nonneg hs.le _).trans hd) le_rfl le_rfl
    rw [←iterD_eq] at h
    calc
      _  ≤  σ^(2*beta η)+iterD σ η n*σ^(-η/4) := h
      _  ≤  (1/2)*σ^(1-η/2)+σ^(1-η/2)*(1/2) := by gcongr
      _ = _ := by ring

theorem eventually_iter_terminal {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (m : ℕ) (hm : 1 ≤ η*(m:ℝ)/4) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,iterA σ η (m+1) ≤ 1 ∧ iterDelta σ η (m+1) ≤ c/9600*σ^η := by
  have ha : 0 < η/3-2*beta η := by unfold beta;linarith
  have hb : 0 < η-8*beta η := by unfold beta;linarith
  have htA : Tendsto (fun σ : ℝ=>2*σ^(-(η/3-2*beta η))) atTop (𝓝 0) :=
    by simpa using (tendsto_rpow_neg_atTop ha).const_mul 2
  have htB : Tendsto (fun σ : ℝ=>2*domainSlackConstant*σ^(-(η-8*beta η))) atTop (𝓝 0) :=
    by simpa using (tendsto_rpow_neg_atTop hb).const_mul (2*domainSlackConstant)
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_iterD_range hη hη',
    (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<2) (beta_pos hη))).eventually_ge_atTop 2,
    (tendsto_rpow_neg_atTop (by linarith : 0 < η/4)).eventually_lt_const (by norm_num : (0:ℝ) < 1/3),
    eventually_stage_recurrence hη domainSlackConstant domainSlackConstant_pos.le,
    htA.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    htB.eventually_lt_const (by positivity : (0:ℝ) < c/9600)]
    with σ hσ hrange hpow hratio hrec hA hB
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hinit : iterD σ η 0 ≤ σ := (hrange 0).trans (by
    conv_rhs => rw [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith))
  have hh:=compression_recurrence_terminal σ η (beta η) m (iterD σ η) hσ hη (beta_pos hη).le
    hpow (by simpa only [neg_div] using hratio.le) hm hinit (fun n=>by
      rw [iterD_eq σ η (n+1)]
      exact hrec _ _ _ ((Real.rpow_nonneg hs.le _).trans (iter_budgets_nonneg (η:=η) hs.le n).1) le_rfl le_rfl)
  constructor
  · calc
      iterA σ η (m+1) ≤ (2*σ^(2*beta η))*σ^(-η/3) := by dsimp [iterA];gcongr
      _ = 2*σ^(-(η/3-2*beta η)) := by rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
      _  ≤  1 := hA.le
  · calc
      iterDelta σ η (m+1) ≤ domainSlackConstant*(2*σ^(2*beta η))*σ^(6*beta η) := by
        dsimp [iterDelta];gcongr;exact domainSlackConstant_pos.le
      _ = (2*domainSlackConstant*σ^(-(η-8*beta η)))*σ^η := by
        rw [show domainSlackConstant*(2*σ^(2*beta η))*σ^(6*beta η)=
          2*domainSlackConstant*(σ^(2*beta η)*σ^(6*beta η)) by ring,
          ←Real.rpow_add hs]
        rw [show (2*domainSlackConstant*σ^(-(η-8*beta η)))*σ^η=
          2*domainSlackConstant*(σ^(-(η-8*beta η))*σ^η) by ring,←Real.rpow_add hs]
        congr 2;ring
      _  ≤  c/9600*σ^η := by gcongr
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_PolarIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

theorem eventually_no_initial_polar {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c d Cm : ℝ) (hc : 0 < c) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K α : Type) [Field K] [Finite K] [CharP K q₀]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (M k₀ : ℝ)
      (_ : PolarState K α N n adm d 0 (10*σ) M),
      3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→(n:ℝ)≤k₀→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤M→M≤Cm*σ→False := by
  obtain ⟨m,hm⟩:=exists_nat_ge (4/η)
  have hm' : 1≤η*(m:ℝ)/4 := by have hh:=(div_le_iff₀ hη).mp hm;nlinarith
  let c':=c/(40000:ℝ)^(m+1)
  have hc' : 0 < c' := by dsimp [c'];positivity
  filter_upwards [eventually_iter_produce hη hη' (m+1) c d Cm hc hCm,
    eventually_iter_terminal hη hη' m hm' c' hc',
    eventually_polar_terminal hη c' ((44:ℝ)^(m+1)*d) hc'] with σ hI hbudget hterminal
  intro q₀ K α _ _ _ _ _ N n adm M k₀ S hq3 hcard hσ hq hα hN hlen hn hk hklo hM hMhi
  obtain ⟨⟨T⟩,hTlen,hTn⟩:=hI q₀ K α N n adm M k₀ S hq3 hcard hσ hq hα hN hlen hn hk hklo hM hMhi
  have hkp : 0≤k₀ := (Nat.cast_nonneg n).trans hn
  exact hterminal K α N (iterLength n (m+1)) adm (k₀*iterA σ η (m+1)) (iterDelta σ η (m+1)) M k₀ T
    hσ hq hα hN hTlen hk (by nlinarith only [mul_le_mul_of_nonneg_left hbudget.1 hkp])
    (iter_budgets_nonneg (by linarith : 0≤σ) (m+1)).2.2 hbudget.2
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Bounds_PrimeStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive

section
open Module Filter FlagConstruction SelectedTuple Marking
open scoped Classical LinearAlgebra.Projectivization Topology
noncomputable section

theorem primeConstruction_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10) : PrimeConstruction η := by
  have hlog : Tendsto (fun q : ℕ=>Real.log (q:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent := hlog.eventually ((eventually_no_initial_polar hη hη' (1/2) 2 40
    (by norm_num) (by norm_num)).and (initial_floor_scales hη hη'))
  obtain ⟨q₀,hq₀⟩:=eventually_atTop.mp hevent
  refine ⟨max q₀ 3,?_⟩
  intro q hlarge hprime
  let : Fact q.Prime:=⟨hprime⟩
  let K:=ZMod q
  let V:=Space K
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  let : Fintype (ℙ K V):=Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K V)):=Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Dual K V))):=Fintype.ofFinite _
  let : Finite (Submodule K (Dual K V)):=Finite.of_injective
    (fun W : Submodule K (Dual K V)=>(W:Set (Dual K V))) SetLike.coe_injective
  let : Fintype (Submodule K (Dual K V)):=Fintype.ofFinite _
  have hd : finrank K V=5 := by simp [V,Space]
  let : Nonempty (RectangleGeometry.Flag (K:=K) (V:=V)):=
    Fintype.card_pos_iff.mp (RectangleGeometry.flags_nonempty hd)
  have hcard : Nat.card K=q := by simp [K,Nat.card_eq_fintype_card]
  let σ:=Real.log (q:ℝ)
  have hqp : (0:ℝ)<q := by exact_mod_cast hprime.pos
  have hqexp : Real.exp σ=Nat.card K := by rw [hcard];exact Real.exp_log hqp
  have hq3 : 3≤Nat.card K := by rw [hcard];exact (le_max_right _ _).trans hlarge
  obtain ⟨hforbid,hσ,hqexp3,hfloor,hlen⟩:=hq₀ q ((le_max_left _ _).trans hlarge)
  let N:=⌊(q:ℝ)^4*σ⌋₊
  let n:=⌊(q:ℝ)*σ^(1+η)⌋₊
  have heq : Real.exp σ=(q:ℝ) := Real.exp_log hqp
  change 1≤σ at hσ
  change ⌊Real.exp σ*σ^(1+η)⌋₊≤⌊(Real.exp σ)^4*σ⌋₊ at hfloor
  rw [heq] at hfloor
  have hN : (N:ℝ)≤(Nat.card K:ℝ)^4*σ := by
    rw [hcard]
    exact Nat.floor_le (by dsimp [σ];positivity)
  have hNexp : (N:ℝ)≤Real.exp (4*σ)*σ := by
    have he : Real.exp (4*σ)=(Nat.card K:ℝ)^4 := by
      simpa only [Nat.cast_ofNat,hqexp] using Real.exp_nat_mul σ 4
    rw [he]
    exact hN
  have hlen' : (1/2:ℝ)*(Nat.card K:ℝ)*σ^(1+η)≤(n:ℝ) := by
    simpa only [n,σ,Real.exp_log hqp,hcard] using hlen
  have hk : (n:ℝ)≤(Nat.card K:ℝ)*σ^(1+η) := by
    rw [hcard]
    exact Nat.floor_le (by positivity)
  by_contra hnone
  have hno : ∀s : Fin N→RectangleGeometry.Flag (K:=K) (V:=V),¬(graph s)ᶜ.CliqueFree n := by
    intro s hs
    exact hnone ⟨graph s,cliqueFree_five s,hs⟩
  obtain ⟨adm,⟨S⟩⟩:=initial_polar_of_no_graph (K:=K) hfloor σ hσ hqexp hq3 hN hno
  exact hforbid q K (RectangleGeometry.Flag (K:=K) (V:=V)) N n adm (40*σ) (n:ℝ) S
    hq3 hcard hσ hqexp (incidentFlag_log_card hd σ hqexp) hNexp hlen' le_rfl hk
    (by linarith only [hlen']) (by positivity) le_rfl
end
end

open Filter
open scoped Topology

end SharpRamseyFive

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.primeConstruction_oai := @OAI.SharpRamseyFive.primeConstruction_oai

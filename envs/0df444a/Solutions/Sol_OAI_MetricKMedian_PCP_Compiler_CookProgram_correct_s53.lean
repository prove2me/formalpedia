-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.Compiler.CookProgram.correct_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:44:20.690144+00:00
-- url     : https://prove2.me/submissions/f66b33af-049d-4d73-b61c-2285cd9646d1

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K082
import Theorems.Thm_OAI_MetricKMedian_PCP_CookLevin_sound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_FiniteConstraints
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteConstraints

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace FiniteCSP
variable {V T Q A : Type} [Fintype Q] [Fintype A] [DecidableEq A]
variable [Nonempty Q] [Inhabited A]
variable (C : FiniteCSP V T Q A)
omit [Nonempty Q] [Inhabited A] in
lemma binary_complete (a : V → A) (h : C.Satisfies a) : C.binary.Satisfies (C.honest a) := by
  rintro ⟨t,i⟩
  simp only [binary,mem_filter,mem_univ,true_and,honest,Sum.elim_inl,Sum.elim_inr]
  exact ⟨a (C.query t i),a ∘ C.query t,rfl,h t,rfl⟩
lemma binary_sound (a : V ⊕ T → Label (Q := Q) (A := A)) (h : C.binary.Satisfies a) :
    C.Satisfies (decoded a) := by
  intro t
  have hh (i : Q) : ∃ x b, (a (.inl (C.query t i)),a (.inr t))=(.inl x,.inr b) ∧
      b∈C.accept t ∧ x=b i := by
    simpa only [binary,mem_filter,mem_univ,true_and] using h (t,i)
  obtain ⟨x,b,hb,hmem,hx⟩ := hh (Classical.arbitrary Q)
  have he : decoded a ∘ C.query t=b := by
    funext i
    obtain ⟨y,c,hc,hcm,hy⟩ := hh i
    have hc' : c=b := Sum.inr.inj ((congrArg Prod.snd hc).symm.trans (congrArg Prod.snd hb))
    subst c
    change (a (.inl (C.query t i))).elim id (fun _ => default)=b i
    have hc0 : a (.inl (C.query t i))=Sum.inl y := congrArg Prod.fst hc
    rw [hc0]
    exact hy
  rw [he]
  exact hmem
lemma binary_iff : (∃ a, C.binary.Satisfies a) ↔ ∃ a, C.Satisfies a := by
  constructor
  · rintro ⟨a,ha⟩; exact ⟨decoded a,C.binary_sound a ha⟩
  · rintro ⟨a,ha⟩; exact ⟨C.honest a,C.binary_complete a ha⟩
end FiniteCSP
end MetricKMedian.PCP

end Inline_PCPFiniteConstraints

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TM2Locality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTM2Locality

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

lemma append_update (P T : ∀ k, List (Γ k)) (k : K) (L : List (Γ k)) :
    update (fun j => P j++T j) k (L++T k) = fun j => update P k L j++T j := by
  funext j
  by_cases h : j=k
  · subst j; simp
  · simp [h]
omit [DecidableEq K] in
lemma safe_mono {r s : ℕ} {P T : ∀ k, List (Γ k)} (h : Safe r P T) (hs : s ≤ r) :
    Safe s P T := fun k => (h k).imp_left (hs.trans ·)
lemma safe_update {r : ℕ} {P T : ∀ k, List (Γ k)} (h : Safe r P T)
    (k : K) (L : List (Γ k)) (hL : r≤L.length ∨ T k=[]) : Safe r (update P k L) T := by
  intro j
  by_cases he : j=k
  · subst j; simpa using hL
  · simpa [he] using h j
omit [DecidableEq K] in
lemma head_append {Element : Type*} {P T : List Element} (h : 1≤P.length ∨ T=[]) :
    (P++T).head?=P.head? := by
  rcases h with h|rfl
  · cases P <;> simp_all
  · simp
omit [DecidableEq K] in
lemma tail_append {Element : Type*} {P T : List Element} (h : 1≤P.length ∨ T=[]) :
    (P++T).tail=P.tail++T := by
  rcases h with h|rfl
  · cases P <;> simp_all
  · simp

lemma stepAux_suffix (q : Stmt Γ Λ σ) (v : σ) (P T : ∀ k, List (Γ k))
    (h : Safe (depth q) P T) :
    stepAux q v (fun k => P k++T k)=appendCfg (stepAux q v P) T := by
  induction q generalizing v P with
  | push k f q ih =>
    simp only [stepAux]
    rw [show f v::(P k++T k)=(f v::P k)++T k from rfl,append_update]
    apply ih
    apply safe_update (safe_mono h (by simp [depth]))
    exact (h k).imp_left (by simp only [depth,List.length_cons]; omega)
  | peek k f q ih =>
    simp only [stepAux]
    rw [head_append ((h k).imp_left (by simp only [depth]; omega))]
    exact ih _ _ (safe_mono h (by simp [depth]))
  | pop k f q ih =>
    simp only [stepAux]
    have hk : 1≤(P k).length ∨ T k=[] := (h k).imp_left (by simp only [depth]; omega)
    rw [head_append hk,tail_append hk,append_update]
    apply ih
    apply safe_update (safe_mono h (by simp [depth]))
    exact (h k).imp_left (by simp only [depth,List.length_tail]; omega)
  | load f q ih =>
    simp only [stepAux]
    exact ih _ _ (safe_mono h (by simp [depth]))
  | branch f q r ihq ihr =>
    simp only [stepAux]
    cases hf : f v
    · simp only [Bool.cond_false]
      exact ihr _ _ (safe_mono h (by simp [depth]; omega))
    · simp only [Bool.cond_true]
      exact ihq _ _ (safe_mono h (by simp [depth]; omega))
  | goto f => rfl
  | halt => rfl

omit [DecidableEq K] in
lemma take_drop_safe (r : ℕ) (S : ∀ k, List (Γ k)) :
    Safe r (fun k => (S k).take r) (fun k => (S k).drop r) := by
  intro k
  by_cases h : r≤(S k).length
  · exact Or.inl (by simp [List.length_take, min_eq_left h])
  · exact Or.inr (List.drop_eq_nil_of_le (by omega))
lemma stepAux_prefix (q : Stmt Γ Λ σ) (r : ℕ) (hq : depth q ≤ r)
    (v : σ) (S : ∀ k, List (Γ k)) :
    stepAux q v S=appendCfg (stepAux q v (fun k => (S k).take r))
      (fun k => (S k).drop r) := by
  have h := stepAux_suffix q v (fun k => (S k).take r) (fun k => (S k).drop r)
    (safe_mono (take_drop_safe r S) hq)
  simpa only [List.take_append_drop] using h

end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Locality

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TM2Response
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTM2Response

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ]
variable (M : Λ → Stmt Γ Λ σ)
lemma advance_stackPrefix (c : Cfg Γ Λ σ) :
    advance M c = appendCfg (advance M ⟨c.l,c.var,fun k => (stackPrefix M c.stk k).val⟩)
      (fun k => (c.stk k).drop (radius M)) := by
  cases h : c.l with
  | none =>
    cases c with
    | mk l v S =>
      simp only at h
      subst l
      simp only [advance,appendCfg,stackPrefix,List.take_append_drop]
  | some l =>
    simp only [advance,h,stackPrefix]
    exact stepAux_prefix (M l) (radius M) (depth_le M l) c.var c.stk

lemma response_control (c : Cfg Γ Λ σ) :
    ((advance M c).l,(advance M c).var)=(respond M (c.l,c.var) (stackPrefix M c.stk)).1 := by
  rw [advance_stackPrefix]
  rfl
lemma response_stack (c : Cfg Γ Λ σ) (k : K) :
    (advance M c).stk k=((respond M (c.l,c.var) (stackPrefix M c.stk)).2 k).val ++
      (c.stk k).drop (radius M) := by
  rw [advance_stackPrefix]
  rfl

lemma response_cell (c : Cfg Γ Λ σ) (k : K) (i : ℕ) :
    ((advance M c).stk k)[i]? =
      let p := (respond M (c.l,c.var) (stackPrefix M c.stk)).2 k
      if i<p.val.length then p.val[i]? else (c.stk k)[radius M+(i-p.val.length)]? := by
  rw [response_stack]
  dsimp only
  split_ifs with h
  · exact List.getElem?_append_left h
  · rw [List.getElem?_append_right (by omega),List.getElem?_drop]

lemma advance_length (c : Cfg Γ Λ σ) (k : K) :
    ((advance M c).stk k).length ≤ (c.stk k).length+radius M := by
  cases h : c.l with
  | none => simp [advance,h]
  | some l =>
    simp only [advance,h]
    exact (stepAux_length (M l) c.var c.stk k).trans (Nat.add_le_add_left (depth_le M l) _)
end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Response

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauLocal

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ]
variable (M : Λ → Stmt Γ Λ σ)

lemma prefixRelation_complete (c : Cfg Γ Λ σ) :
    PrefixRelation M (c.l,c.var) (fun k i => (c.stk k)[i.val]?)
      (respond M (c.l,c.var) (stackPrefix M c.stk)) := by
  refine ⟨stackPrefix M c.stk,?_,rfl⟩
  intro k
  funext i
  simp only [BoundedList.cells,stackPrefix,List.getElem?_take,ite_eq_left i.isLt]

lemma cellTable_exact (c : Cfg Γ Λ σ) (k : K) (i : ℕ) :
    cellTable M k (category M i) ((respond M (c.l,c.var) (stackPrefix M c.stk)).2 k)
      (fun h => (c.stk k)[(i+radius M)-h.val]?) = ((advance M c).stk k)[i]? := by
  rw [response_cell]
  dsimp only [cellTable,category]
  let p := (respond M (c.l,c.var) (stackPrefix M c.stk)).2 k
  change (if min i (2*radius M)<p.val.length then p.val[min i (2*radius M)]?
    else (c.stk k)[i+radius M-p.val.length]?) =
    if i<p.val.length then p.val[i]? else (c.stk k)[radius M+(i-p.val.length)]?
  have hp := p.property
  by_cases hi : i<p.val.length
  · have hb : i≤2*radius M := by omega
    simp only [min_eq_left hb,ite_eq_left hi]
  · have hb : ¬ min i (2*radius M)<p.val.length := by omega
    simp only [ite_eq_right hi,ite_eq_right hb]
    congr 1
    omega

end MetricKMedian.PCP.Tableau

end Inline_PCPTableauLocal

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauBoundary
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauBoundary

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

lemma prefixCell_complete {A : Type} (p w : List A) (b : ℕ) (hw : w.length≤b) (i : ℕ) :
    prefixCell p b i (p++w)[i]? := by
  constructor
  · intro hi; exact List.getElem?_append_left hi
  · intro hi; exact List.getElem?_eq_none (by simp only [List.length_append]; omega)

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
lemma bounded_satisfies_iff (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ)
    (a : Var (K := K) T L → Value M) : (boundedSystem M B T L).Satisfies a ↔
      (system M T L).Satisfies a ∧ ∀ b, boundaryRelation M B L b (a ∘ boundaryQuery M T L b) := by
  simp only [FiniteCSP.Satisfies,boundedSystem,Sum.forall,Sum.elim_inl,Sum.elim_inr,
    mem_filter,mem_univ,true_and,system]

end MetricKMedian.PCP.Tableau

end Inline_PCPTableauBoundary

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauCorrect
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauCorrect

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)

variable [Inhabited σ]
omit [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma honest_clamp (T L : ℕ) (cs : Fin (T+1) → Cfg Γ Λ σ) (hL : ∀ t k, ((cs t).stk k).length≤L)
    (t : Fin (T+1)) (k : K) (i : ℕ) :
    (honest M T L cs (cell T L t k (clamp L i))).2.2 k=((cs t).stk k)[i]? := by
  change ((cs t).stk k)[min i L]?=((cs t).stk k)[i]?
  by_cases hi : i≤L
  · rw [min_eq_left hi]
  · rw [min_eq_right (by omega : L ≤ i),List.getElem?_eq_none (hL t k),
      List.getElem?_eq_none ((hL t k).trans (by omega : L ≤ i))]

lemma honest_satisfies (T L : ℕ) (cs : Fin (T+1) → Cfg Γ Λ σ)
    (hL : ∀ t k, ((cs t).stk k).length≤L)
    (hs : ∀ t : Fin T, cs (later T t)=advance M (cs (now T t))) :
    (system M T L).Satisfies (honest M T L cs) := by
  apply (satisfies_iff M T L _).mpr
  intro cl
  cases cl with
  | shape t k i =>
    change ((cs t).stk k)[i.val]?=none → ((cs t).stk k)[i.val+1]?=none
    intro hi
    exact List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hi; omega)
  | «end» t k => exact List.getElem?_eq_none (hL t k)
  | «prefix» t =>
    dsimp only [relation,Function.comp_def,query,q0,q1,qtop]
    simp_rw [honest_clamp M T L cs hL]
    exact prefixRelation_complete M (cs (now T t))
  | control t =>
    change ((cs (later T t)).l,(cs (later T t)).var)=_
    rw [hs t]
    exact response_control M (cs (now T t))
  | update t k i =>
    dsimp only [relation,Function.comp_def,query,q0,q1,qwin]
    simp_rw [honest_clamp M T L cs hL]
    change ((cs (later T t)).stk k)[i.val]?=cellTable M k (category M i.val)
      ((respond M ((cs (now T t)).l,(cs (now T t)).var) (stackPrefix M (cs (now T t)).stk)).2 k)
      (fun h => ((cs (now T t)).stk k)[i.val+radius M-h.val]?)
    rw [hs t,cellTable_exact]
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauCorrect

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauRun

namespace MetricKMedian.PCP.Tableau
open Function Relation

namespace Padded
variable {A : Type} (f : A → Option A)
lemma none_iterate (n : ℕ) : (flip Bind.bind f)^[n] (none : Option A)=none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih]; rfl
lemma option_to_next (a b : A) (n : ℕ)
    (h : (flip Bind.bind f)^[n] (some a)=some b) : (next f)^[n] a=b := by
  induction n generalizing a with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip Bind.bind f)^[n] (f a)=some b at h
    cases hf : f a with
    | none => rw [hf,none_iterate] at h; contradiction
    | some c =>
      simp only [next,hf,Option.getD_some]
      exact ih c (by simpa only [hf] using h)
lemma fixed (b : A) (h : f b=none) (n : ℕ) : (next f)^[n] b=b :=
  Function.iterate_fixed (by simp [next,h]) n
lemma bounded (a b : A) {T : ℕ} (h : StateTransition.EvalsToInTime f a (some b) T)
    (hb : f b=none) : (next f)^[T] a=b := by
  have he := option_to_next f a b h.steps h.evals_in_steps
  have ht : T=(T-h.steps)+h.steps := by have := h.steps_le_m; omega
  rw [ht,Function.iterate_add_apply,he,fixed f b hb]
end Padded

open Turing.TM2

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
omit [Fintype K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma advance_eq_padded : advance M=Padded.next (step M) := by
  funext c
  cases c with
  | mk l v S => cases l <;> rfl
omit [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma run_length (c : Cfg Γ Λ σ) (n : ℕ) (k : K) :
    (((advance M)^[n] c).stk k).length≤(c.stk k).length+radius M*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := advance_length M ((advance M)^[n] c) k
    rw [Nat.mul_succ]
    omega
omit [Fintype K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma run_of_outputs {c d : Cfg Γ Λ σ} {T : ℕ}
    (h : StateTransition.EvalsToInTime (step M) c (some d) T) (hd : d.l=none) :
    (advance M)^[T] c=d := by
  rw [advance_eq_padded]
  apply Padded.bounded _ _ _ h
  cases d with
  | mk l v S => simp only at hd; subst l; rfl
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauRun

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauEndpoints
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauEndpoints

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
variable (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ)

variable [Inhabited σ]
lemma bounded_complete (cs : Fin (T+1) → Cfg Γ Λ σ)
    (hL : ∀ t k, ((cs t).stk k).length≤L)
    (hs : ∀ t : Fin T, cs (later T t)=advance M (cs (now T t)))
    (hc : ((cs (time0 T)).l,(cs (time0 T)).var)=B.firstControl)
    (hw : ∀ k, ∃ w, w.length≤B.certificateBound k ∧ (cs (time0 T)).stk k=B.firstPrefix k++w)
    (he : cs (timeLast T)=B.last) :
    (boundedSystem M B T L).Satisfies (honest M T L cs) := by
  apply (bounded_satisfies_iff M B T L _).mpr
  refine ⟨honest_satisfies M T L cs hL hs,?_⟩
  rintro ⟨side,cl⟩
  cases cl with
  | inl u =>
    cases side
    · exact hc
    · change ((cs (timeLast T)).l,(cs (timeLast T)).var)=(B.last.l,B.last.var)
      rw [he]
  | inr ki =>
    obtain ⟨k,i⟩ := ki
    cases side
    · change prefixCell (B.firstPrefix k) (B.certificateBound k) i.val ((cs (time0 T)).stk k)[i.val]?
      obtain ⟨w,hw,hs⟩ := hw k
      rw [hs]
      exact prefixCell_complete _ _ _ hw _
    · change ((cs (timeLast T)).stk k)[i.val]?=(B.last.stk k)[i.val]?
      rw [he]

lemma path_complete (c : Cfg Γ Λ σ)
    (hL : ∀ k, (c.stk k).length+radius M*T≤L)
    (hc : (c.l,c.var)=B.firstControl)
    (hw : ∀ k, ∃ w, w.length≤B.certificateBound k ∧ c.stk k=B.firstPrefix k++w)
    (he : (advance M)^[T] c=B.last) :
    ∃ a, (boundedSystem M B T L).Satisfies a := by
  let cs : Fin (T+1) → Cfg Γ Λ σ := fun t => (advance M)^[t.val] c
  refine ⟨honest M T L cs,bounded_complete M B T L cs ?_ ?_ hc hw he⟩
  · intro t k
    exact (run_length M c _ k).trans ((Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : t.val≤T)) _).trans (hL k))
  · intro t
    exact Function.iterate_succ_apply' (advance M) t.val c
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauEndpoints

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookLevin
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.testNonempty _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookLevin

namespace MetricKMedian.PCP.CookLevin
open Turing Turing.TM2 Function Finset
open Complexity Tableau
open scoped Classical

lemma polynomial_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeσTmBool_solutions
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma init_length (w : Word) (x : Word) (hw : w.length ≤ p.eval x.length) (k : P.tm.K) :
    ((initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun)).stk k).length ≤ inputSize p x := by
  dsimp only [initList]
  split_ifs with hk
  · subst k
    simpa [initList,encodePair,inputSize,firstWord,Nat.add_assoc] using Nat.add_le_add_left hw ((encodeNat x.length).length+x.length)
  · exact Nat.zero_le _
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma initial_prefix (w : Word) (x : Word) (hw : w.length ≤ p.eval x.length) (k : P.tm.K) :
    ∃ z, z.length ≤ (boundary P p x).certificateBound k ∧
      ((initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun)).stk k)=(boundary P p x).firstPrefix k++z := by
  by_cases hk : k=P.tm.k₀
  · subst k
    refine ⟨w.map P.inputAlphabet.invFun,?_,?_⟩
    · simpa [boundary] using hw
    · simp [boundary,initList,inputPrefix,firstWord,encodePair,List.map_append]
  · refine ⟨[],by simp [boundary,hk],?_⟩
    simp [initList,boundary,hk]

lemma complete (x w : Word) (hw : w.length ≤ p.eval x.length) (hv : verify (x,w)=true) :
    ∃ a, (system P p x).Satisfies a := by
  let c := initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun)
  apply path_complete P.tm.m (boundary P p x) (time P p x) (space P p x) c
  · intro k
    have hh := init_length P p w x hw k
    change (c.stk k).length ≤ inputSize p x at hh
    dsimp only [space]
    omega
  · rfl
  · exact initial_prefix P p w x hw
  · have ht := P.outputsFun (x,w)
    have hn : (encodePair (x,w)).length ≤ inputSize p x := by
      simp only [encodePair,inputSize,firstWord,List.length_append]
      omega
    have htime := polynomial_mono P.time hn
    have out : StateTransition.EvalsToInTime (step P.tm.m) c (some (boundary P p x).last) (time P p x) := by
      have out := (show StateTransition.EvalsToInTime (step P.tm.m)
        (initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun))
        (some (haltList P.tm ((encodeBit (verify (x,w))).map P.outputAlphabet.invFun)))
        (time P p x) from ⟨ht.toEvalsTo,ht.steps_le_m.trans htime⟩)
      simpa [c,boundary,encodeBit,hv] using out
    apply run_of_outputs P.tm.m out rfl

lemma correct (x : Word) : (∃ a, (system P p x).Satisfies a) ↔
    ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x,w)=true :=
  ⟨sound_s53 P p x,fun ⟨w,hw,hv⟩ => complete P p x w hw hv⟩
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookLevin

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_BinaryReindex
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBinaryReindex

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E V' E' A : Type} [DecidableEq A]
variable (C : BinaryCSP V E A) (ev : V ≃ V') (ee : E ≃ E')
omit [DecidableEq A]
lemma reindex_satisfies (a : V' → A) :
    (C.reindex ev ee).Satisfies a ↔ C.Satisfies (a ∘ ev) := by
  constructor
  · intro h e
    simpa only [reindex,Equiv.symm_apply_apply,Function.comp_def] using h (ee e)
  · intro h e
    exact h (ee.symm e)
lemma reindex_complete (a : V → A) (h : C.Satisfies a) :
    (C.reindex ev ee).Satisfies (a ∘ ev.symm) := by
  apply (C.reindex_satisfies ev ee _).mpr
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using h
end BinaryCSP
end MetricKMedian.PCP

end Inline_PCPBinaryReindex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawCSP
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_bad _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.CloudCopies.honest_dart _root_.OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed_index _root_.OAI.MetricKMedian.PCP.FlexibleCloud.honest_dart _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawCSP
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

lemma csp_ext {V E A : Type} {C D : BinaryCSP V E A}
    (hl : C.left=D.left) (hr : C.right=D.right) (ha : C.allowed=D.allowed) : C=D := by
  cases C; cases D; simp_all
namespace CSPTable
variable {A : Type} [Fintype A] [DecidableEq A]
variable {V E : Type} [Fintype V] [Fintype E]
omit [Fintype A] [DecidableEq A] [Fintype V] [Fintype E] in
lemma Represents.csp_eq {t : CSPTable A} {C : BinaryCSP V E A}
    (r : t.Represents C) (h : t.WellFormed) : t.csp h=C.reindex r.vertex r.edge := by
  cases C with
  | mk l rr aa =>
    apply csp_ext
    · funext i
      apply Fin.ext
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg Prod.fst hr
    · funext i
      apply Fin.ext
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg (fun x : CSPRow A => x.2.1) hr
    · funext i
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg (fun x : CSPRow A => x.2.2) hr
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawCSP

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_TablePromises
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTablePromises
namespace MetricKMedian.PCP.Compiler.CSPTable
open scoped Classical

variable {A V E : Type} [Fintype A] [DecidableEq A] [Fintype V] [Fintype E]
variable {s : CSPTable A} {C : BinaryCSP V E A}
omit [Fintype A] [DecidableEq A] [Fintype V] [Fintype E] in
lemma Represents.satisfies (r : s.Represents C) (h : s.WellFormed) :
    (∃ a, (s.csp h).Satisfies a) ↔ ∃ a, C.Satisfies a := by
  rw [r.csp_eq h]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a ∘ r.vertex,(C.reindex_satisfies _ _ _).mp ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a ∘ r.vertex.symm,C.reindex_complete _ _ _ ha⟩
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPTablePromises

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookTable
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedValueKTmBoolΓΛσM
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedQueryKTmBoolΓΛσM
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM
lemma correct_s53_oai (x : Word) : (∃ a, ((table P p x).csp (wellFormed P p x)).Satisfies a) ↔
    ∃ w : Word, w.length≤p.eval x.length ∧ verify (x,w)=true := by
  rw [(represents P p x).satisfies,FiniteCSP.binary_iff,CookLevin.correct]
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookTable

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.Compiler.CookProgram.correct_s53_oai := @OAI.MetricKMedian.PCP.Compiler.CookProgram.correct_s53_oai

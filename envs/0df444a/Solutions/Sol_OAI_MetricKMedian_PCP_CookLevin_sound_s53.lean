-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.CookLevin.sound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:45:47.978976+00:00
-- url     : https://prove2.me/submissions/b6a034c3-92ed-4719-87ec-873bd4a18a23

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K082

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

end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Response

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauRows

namespace MetricKMedian.PCP.Tableau
open scoped Classical

variable {A : Type}

lemma list_eq_of_row (L : ℕ) (l m : List A) (hl : l.length≤L) (hm : m.length≤L)
    (h : ∀ i≤L, l[i]?=m[i]?) : l=m := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i≤L
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

lemma stack_eq_of_cells (L : ℕ) (l m : List A) (hm : m.length≤L)
    (h : ∀ i≤L, l[i]?=m[i]?) : l=m := by
  have hl : l.length≤L := List.getElem?_eq_none_iff.mp ((h L le_rfl).trans (List.getElem?_eq_none hm))
  exact list_eq_of_row L l m hl hm h
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauRows

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

lemma prefixRelation_exact (c : Cfg Γ Λ σ) (r : Response M)
    (h : PrefixRelation M (c.l,c.var) (fun k i => (c.stk k)[i.val]?) r) :
    r=respond M (c.l,c.var) (stackPrefix M c.stk) := by
  obtain ⟨p,hp,hr⟩ := h
  have he : p=stackPrefix M c.stk := by
    funext k
    apply BoundedList.cells_injective
    funext i
    have hh := congrFun (hp k) i
    simpa only [BoundedList.cells,stackPrefix,List.getElem?_take,ite_eq_left i.isLt] using hh
  rwa [he] at hr
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

omit [DecidableEq K] [Fintype Λ] in
lemma clampedCell_eq {Alphabet : Type} (L : ℕ) (row : Row Alphabet L) (h : ValidRow L row) (j : ℕ) :
    clampedCell L row j=rowCell L row j := by
  unfold clampedCell rowCell
  by_cases hj : j≤L
  · simp only [min_eq_left hj,dite_eq_left hj]
  · simp only [min_eq_right (by omega : L≤j),dite_eq_right hj]
    exact h.1

lemma local_transition_exact (L : ℕ) (c d : Cfg Γ Λ σ)
    (hd : ∀ k, (d.stk k).length≤L) (r : Response M)
    (hresp : PrefixRelation M (c.l,c.var) (fun k i => (c.stk k)[i.val]?) r)
    (hctrl : (d.l,d.var)=r.1)
    (hcell : ∀ k i, i≤L → (d.stk k)[i]?=
      cellTable M k (category M i) (r.2 k) (fun h => (c.stk k)[i+radius M-h.val]?)) :
    d=advance M c := by
  have hr := prefixRelation_exact M c r hresp
  have hct : (d.l,d.var)=((advance M c).l,(advance M c).var) :=
    hctrl.trans ((congrArg Prod.fst hr).trans (response_control M c).symm)
  have hs : d.stk=(advance M c).stk := by
    funext k
    apply (stack_eq_of_cells L ((advance M c).stk k) (d.stk k) (hd k) _).symm
    intro i hi
    rw [hcell k i hi,hr,cellTable_exact]
  have hl := congrArg Prod.fst hct
  have hv := congrArg Prod.snd hct
  cases d
  generalize advance M c = e at hl hv hs ⊢
  cases e
  simp only [Cfg.mk.injEq]
  exact ⟨hl,hv,hs⟩
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauLocal

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauSystem
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauSystem

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
lemma decodeRow_length (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) (k : K) :
    (decodeRow M T L a ha t k).length≤L :=
  (valid_row_list L (getRow M T L a t k) (row_valid M T L a ha t k)).choose_spec.1
lemma decodeRow_cell (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) (k : K) (i : ℕ) :
    (decodeRow M T L a ha t k)[i]?=rowCell L (getRow M T L a t k) i :=
  (valid_row_list L (getRow M T L a t k) (row_valid M T L a ha t k)).choose_spec.2 i

lemma clamp_decode (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) (k : K) (i : ℕ) :
    (a (cell T L t k (clamp L i))).2.2 k=((decodeCfg M T L a ha t).stk k)[i]? := by
  change clampedCell L (getRow M T L a t k) i=(decodeRow M T L a ha t k)[i]?
  rw [clampedCell_eq L _ (row_valid M T L a ha t k),decodeRow_cell]

lemma decoded_transition (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin T) :
    decodeCfg M T L a ha (later T t)=advance M (decodeCfg M T L a ha (now T t)) := by
  have h := (satisfies_iff M T L a).mp ha
  apply local_transition_exact M L _ _ (decodeRow_length M T L a ha (later T t)) (getResponse M T L a t)
  · have hp := h (.prefix t)
    dsimp only [relation,Function.comp_def,query,q0,q1,qtop] at hp
    simp_rw [clamp_decode M T L a ha] at hp
    simpa only [decodeCfg,getControl,getResponse,Prod.mk.eta] using hp
  · exact h (.control t)
  · intro k i hi
    have hp := h (.update t k ⟨i,by omega⟩)
    dsimp only [relation,Function.comp_def,query,q0,q1,qwin] at hp
    change (decodeRow M T L a ha (later T t) k)[i]?=_
    rw [decodeRow_cell,rowCell,dite_eq_left hi]
    simp_rw [clamp_decode M T L a ha] at hp
    simpa only [getResponse,getRow] using hp
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauSystem

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

lemma prefixCell_sound {A : Type} (p s : List A) (b : ℕ)
    (h : ∀ i, prefixCell p b i s[i]?) : ∃ w, w.length≤b ∧ s=p++w := by
  have hp : p <+: s := List.prefix_iff_getElem?.mpr (fun i hi => by simpa only [List.getElem?_eq_getElem hi] using (h i).1 hi)
  obtain ⟨w,rfl⟩ := hp
  refine ⟨w,?_,rfl⟩
  have hl := List.getElem?_eq_none_iff.mp ((h (p.length+b)).2 le_rfl)
  simp only [List.length_append] at hl
  omega

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
lemma bounded_satisfies_iff (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ)
    (a : Var (K := K) T L → Value M) : (boundedSystem M B T L).Satisfies a ↔
      (system M T L).Satisfies a ∧ ∀ b, boundaryRelation M B L b (a ∘ boundaryQuery M T L b) := by
  simp only [FiniteCSP.Satisfies,boundedSystem,Sum.forall,Sum.elim_inl,Sum.elim_inr,
    mem_filter,mem_univ,true_and,system]

lemma decoded_boundary (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ)
    (a : Var (K := K) T L → Value M) (ha : (system M T L).Satisfies a)
    (hb : ∀ b, boundaryRelation M B L b (a ∘ boundaryQuery M T L b))
    (hL : ∀ k, (B.last.stk k).length≤L) :
    let c := decodeCfg M T L a ha (time0 T)
    (c.l,c.var)=B.firstControl ∧
    (∀ k, ∃ w, w.length≤B.certificateBound k ∧ c.stk k=B.firstPrefix k++w) ∧
    decodeCfg M T L a ha (timeLast T)=B.last := by
  refine ⟨hb (false,.inl ()),?_,?_⟩
  · intro k
    apply prefixCell_sound
    intro i
    by_cases hi : i≤L
    · have hh := hb (false,.inr (k,⟨i,by omega⟩))
      change prefixCell (B.firstPrefix k) (B.certificateBound k) i ((a (cell T L (time0 T) k ⟨i,by omega⟩)).2.2 k) at hh
      have hd := clamp_decode M T L a ha (time0 T) k i
      simp only [clamp,min_eq_left hi] at hd
      rw [← hd]
      exact hh
    · have hs := hb (false,.inr (k,⟨L,by omega⟩))
      change prefixCell (B.firstPrefix k) (B.certificateBound k) L ((a (cell T L (time0 T) k ⟨L,by omega⟩)).2.2 k) at hs
      have hend := (row_valid M T L a ha (time0 T) k).1
      change (a (cell T L (time0 T) k ⟨L,by omega⟩)).2.2 k=none at hend
      rw [hend] at hs
      have hp : (B.firstPrefix k).length≤L := by
        by_contra hn
        have hx := hs.1 (by omega)
        have hx' := List.getElem?_eq_none_iff.mp hx.symm
        omega
      change prefixCell (B.firstPrefix k) (B.certificateBound k) i (decodeRow M T L a ha (time0 T) k)[i]?
      rw [List.getElem?_eq_none ((decodeRow_length M T L a ha (time0 T) k).trans (by omega))]
      exact ⟨fun h => False.elim (by omega),fun _ => rfl⟩
  · have hc := hb (true,.inl ())
    change ((decodeCfg M T L a ha (timeLast T)).l,(decodeCfg M T L a ha (timeLast T)).var)=
      (B.last.l,B.last.var) at hc
    have hstk : (decodeCfg M T L a ha (timeLast T)).stk=B.last.stk := by
      funext k
      apply List.ext_getElem?
      intro i
      by_cases hi : i≤L
      · have hh := hb (true,.inr (k,⟨i,by omega⟩))
        change (a (cell T L (timeLast T) k ⟨i,by omega⟩)).2.2 k=(B.last.stk k)[i]? at hh
        have hd := clamp_decode M T L a ha (timeLast T) k i
        simp only [clamp,min_eq_left hi] at hd
        exact hd.symm.trans hh
      · change (decodeRow M T L a ha (timeLast T) k)[i]?=(B.last.stk k)[i]?
        rw [List.getElem?_eq_none ((decodeRow_length M T L a ha (timeLast T) k).trans (by omega)),
          List.getElem?_eq_none ((hL k).trans (by omega))]
    cases hd : decodeCfg M T L a ha (timeLast T) with
    | mk l v stk =>
      cases he : B.last with
      | mk l' v' stk' =>
        rw [hd,he] at hc hstk
        cases congrArg Prod.fst hc
        cases congrArg Prod.snd hc
        cases hstk
        rfl
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

lemma decoded_run (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) :
    decodeCfg M T L a ha ⟨T,by omega⟩ = (advance M)^[T] (decodeCfg M T L a ha (time0 T)) := by
  have hrun : ∀ n, ∀ hn : n≤T, decodeCfg M T L a ha ⟨n,by omega⟩ =
      (advance M)^[n] (decodeCfg M T L a ha (time0 T)) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hh := decoded_transition M T L a ha ⟨n,by omega⟩
      change decodeCfg M T L a ha ⟨n+1,by omega⟩ =
        advance M (decodeCfg M T L a ha ⟨n,by omega⟩) at hh
      rw [hh,ih (by omega),Function.iterate_succ_apply']
  exact hrun T le_rfl

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
lemma reaches (a : A) (n : ℕ) : StateTransition.Reaches f a ((next f)^[n] a) := by
  induction n with
  | zero => exact ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    cases h : f ((next f)^[n] a) with
    | none => simpa only [next,h,Option.getD_none] using ih
    | some b =>
      simp only [next,h,Option.getD_some]
      exact ih.tail h
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
lemma terminal_unique (a b c : A) (h : StateTransition.Reaches f a b)
    (h' : StateTransition.Reaches f a c) (hb : f b=none) (hc : f c=none) : b=c :=
  Part.mem_unique (StateTransition.mem_eval.mpr ⟨h,hb⟩) (StateTransition.mem_eval.mpr ⟨h',hc⟩)
lemma agrees (a b c : A) (n : ℕ) (hn : (next f)^[n] a=b) (hb : f b=none)
    (hc : f c=none) (h : StateTransition.EvalsTo f a (some c)) : b=c := by
  have hr0 := reaches f a n
  rw [hn] at hr0
  have hr1 := reaches f a h.steps
  rw [option_to_next f a c h.steps h.evals_in_steps] at hr1
  exact terminal_unique f a b c hr0 hr1 hb hc
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
lemma bounded_sound (a : Var (K := K) T L → Value M)
    (ha : (boundedSystem M B T L).Satisfies a) (hL : ∀ k, (B.last.stk k).length≤L) :
    ∃ c : Cfg Γ Λ σ, (c.l,c.var)=B.firstControl ∧
      (∀ k, ∃ w, w.length≤B.certificateBound k ∧ c.stk k=B.firstPrefix k++w) ∧
      (advance M)^[T] c=B.last := by
  obtain ⟨ha,hb⟩ := (bounded_satisfies_iff M B T L a).mp ha
  obtain ⟨hc,hw,he⟩ := decoded_boundary M B T L a ha hb hL
  refine ⟨decodeCfg M T L a ha (time0 T),hc,hw,?_⟩
  exact (decoded_run M T L a ha).symm.trans he

end MetricKMedian.PCP.Tableau

end Inline_PCPTableauEndpoints

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookLevin
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.testNonempty _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
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

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]

attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeσTmBool_solutions
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma last_length (x : Word) (k : P.tm.K) : ((boundary P p x).last.stk k).length ≤ space P p x := by
  dsimp only [boundary,haltList]
  split_ifs with hk
  · subst k
    change 1 ≤ space P p x
    unfold space
    omega
  · exact Nat.zero_le _

omit [∀ k, Fintype (P.tm.Γ k)] in
lemma initial_decode (x : Word) (c : Cfg P.tm.Γ P.tm.Λ P.tm.σ)
    (hc : (c.l,c.var)=(boundary P p x).firstControl)
    (hw : ∀ k, ∃ z, z.length ≤ (boundary P p x).certificateBound k ∧ c.stk k=(boundary P p x).firstPrefix k++z) :
    ∃ w : Word, w.length ≤ p.eval x.length ∧ c=initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun) := by
  obtain ⟨z,hz,hs⟩ := hw P.tm.k₀
  let w := z.map P.inputAlphabet
  have hwlen : w.length ≤ p.eval x.length := by simpa [boundary,w] using hz
  refine ⟨w,hwlen,?_⟩
  have hstk : c.stk=(initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun)).stk := by
    funext k
    by_cases hk : k=P.tm.k₀
    · subst k
      simpa [boundary,initList,inputPrefix,firstWord,encodePair,w,List.map_append,List.map_map,Function.comp_def] using hs
    · obtain ⟨z,hz,hs⟩ := hw k
      have he : z=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (by simpa [boundary,hk] using hz))
      simpa [boundary,initList,hk,he] using hs
  cases c with
  | mk l v stk =>
    change (l,v)=(some P.tm.main,P.tm.initialState) at hc
    cases congrArg Prod.fst hc
    cases congrArg Prod.snd hc
    cases hstk
    rfl

lemma sound_s53_oai (x : Word) (ha : ∃ a, (system P p x).Satisfies a) :
    ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x,w)=true := by
  obtain ⟨a,ha⟩ := ha
  obtain ⟨c,hc,hcert,he⟩ := bounded_sound P.tm.m (boundary P p x) (time P p x) (space P p x) a ha (last_length P p x)
  obtain ⟨w,hlen,rfl⟩ := initial_decode P p x c hc hcert
  refine ⟨w,hlen,?_⟩
  have ht := (P.outputsFun (x,w)).toEvalsTo
  have hi := Padded.agrees (step P.tm.m) _ (boundary P p x).last
    (haltList P.tm ((encodeBit (verify (x,w))).map P.outputAlphabet.invFun)) (time P p x)
    (by simpa only [advance_eq_padded] using he) rfl rfl ht
  have hh := congrArg (fun c : Cfg P.tm.Γ P.tm.Λ P.tm.σ => c.stk P.tm.k₁) hi
  simpa [boundary,haltList,encodeBit] using (congrArg (List.map P.outputAlphabet) hh).symm
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookLevin

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.CookLevin.sound_s53_oai := @OAI.MetricKMedian.PCP.CookLevin.sound_s53_oai

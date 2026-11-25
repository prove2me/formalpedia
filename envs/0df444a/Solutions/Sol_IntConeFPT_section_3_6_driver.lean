-- Prove2me | solution 1 for IntConeFPT.section_3_6_driver
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:52:37.512859+00:00
-- url     : https://prove2.me/submissions/8df6f603-45dc-413b-9c35-d6abf6697aac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_IntConeFPT_runsWithin_chain
import Theorems.Thm_IntConeFPT_runsWithin_thread
import Definitions.Def_IntConeFPT_Homogenized
import Theorems.Thm_IntConeFPT_section_3_6_nstar_bound

import Theorems.Thm_IntConeFPT_count_query_writer
import Theorems.Thm_IntConeFPT_resolve_word_evaluation

open Turing IntConeFPT OnlineCRS.Combine Function

noncomputable section
namespace IntConeFPT.Routing

-- A streaming transducer collecting a fixed finite number of output segments.
-- Its output is the concatenation of the segments, not their interleaving.
private structure Spec where
  Q : Type
  [finQ : Fintype Q]
  q₀ : Q
  next : Q → Sym → Q
  emit : Q → Sym → Fin 3 → List Sym
  last : Q → Fin 3 → List Sym

attribute [local instance] Spec.finQ

private def parts (S : Spec) (q : S.Q) : List Sym → Fin 3 → List Sym
  | [] => S.last q
  | a::w => fun j => S.emit q a j ++ parts S (S.next q a) w j

private def cat (s : Fin 3 → List Sym) := s 0 ++ s 1 ++ s 2
private abbrev K := Fin 5
private abbrev A : K → Type := fun _ => OnlineCRS.Combine.Sym
private abbrev L := Option (Fin 3)
private abbrev V (S : Spec) := S.Q × Option Sym
private abbrev Stmt (S : Spec) := TM2.Stmt A L (V S)
private def key (j : Fin 3) : K := ⟨j+2, by omega⟩

private def emit {S : Spec} (k : K) (xs : List Sym) (p : Stmt S) : Stmt S :=
  xs.foldr (fun s p => .push k (fun _ => s) p) p

-- Branches are compiled into a fixed finite syntax tree.
private noncomputable def dispatch {S : Spec} (qs : List S.Q) (s : Sym) (acc : S.Q → Sym → Stmt S) : Stmt S :=
  match qs with
  | [] => .halt
  | q::tl => by
    classical
    exact .branch (fun v => decide (v.1=q)) (acc q s) (dispatch tl s acc)

private noncomputable def route {S : Spec} (acc : S.Q → Sym → Stmt S) : Stmt S :=
  .branch (fun v => decide (v.2.getD 0 = 0)) (dispatch Finset.univ.toList 0 acc)
    (.branch (fun v => decide (v.2.getD 0 = 1)) (dispatch Finset.univ.toList 1 acc)
      (.branch (fun v => decide (v.2.getD 0 = 2)) (dispatch Finset.univ.toList 2 acc)
        (dispatch Finset.univ.toList 3 acc)))

private def push3 {S : Spec} (w : Fin 3 → List Sym) (p : Stmt S) :=
  emit (key 0) (w 0) (emit (key 1) (w 1) (emit (key 2) (w 2) p))

private noncomputable def prog (S : Spec) : L → Stmt S
  | none => .pop 0 (fun v o => (v.1,o)) (.branch (fun v => v.2.isSome)
      (route (fun q s => push3 (S.emit q s) (.load (fun _ => (S.next q s,none)) (.goto (fun _ => none)))))
      (route (fun q _ => push3 (S.last q) (.load (fun _ => (S.q₀,none)) (.goto (fun _ => some 2))))))
  | some i => .pop (key i) (fun _ o => (S.q₀,o)) (.branch (fun v => v.2.isSome)
      (.push 1 (fun v => v.2.getD 0) (.goto (fun _ => some i)))
      (if i=0 then .halt else .goto (fun _ => some (i-1))))

private noncomputable abbrev W (S : Spec) : Machine where
  tm := { K := K, k₀ := 0, k₁ := 1, Γ := A, Λ := L, main := none, σ := V S, initialState := (S.q₀,none), m := prog S }
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _

private def buf (x o : List Sym) (b : Fin 3 → List Sym) : K → List Sym :=
  ![x,o,b 0,b 1,b 2]

private lemma input_upd x o b w : update (buf x o b) (0:K) w = buf w o b := by
  funext k; fin_cases k <;> rfl
private lemma output_upd x o b w : update (buf x o b) (1:K) w = buf x w b := by
  funext k; fin_cases k <;> rfl
private lemma buf_upd x o b (j : Fin 3) w : update (buf x o b) (key j) w = buf x o (update b j w) := by
  funext k; fin_cases k <;> fin_cases j <;> rfl
private lemma buf_key x o b (j : Fin 3) : buf x o b (key j) = b j := by fin_cases j <;> rfl

private lemma emit_spec {S : Spec} (k : K) (xs : List Sym) (p : Stmt S)
    (v : V S) (s : K → List Sym) :
    TM2.stepAux (emit k xs p) v s = TM2.stepAux p v (update s k (xs.reverse ++ s k)) := by
  induction xs generalizing s with
  | nil => simp [emit]
  | cons a tl ih =>
    change TM2.stepAux (emit k tl p) v (update s k (a::s k)) = _
    rw [ih]; simp

private lemma push3_spec {S : Spec} (xs : Fin 3 → List Sym) (p : Stmt S) v x o b :
    TM2.stepAux (push3 xs p) v (buf x o b) =
      TM2.stepAux p v (buf x o fun j => (xs j).reverse ++ b j) := by
  simp only [push3,emit_spec,buf_key,buf_upd]
  congr 2
  funext j; fin_cases j <;> rfl

private lemma dispatch_spec {S : Spec} (qs : List S.Q) (s : Sym) (acc : S.Q → Sym → Stmt S)
    (v : V S) (w : K → List Sym) (hv : v.1 ∈ qs) :
    TM2.stepAux (dispatch qs s acc) v w = TM2.stepAux (acc v.1 s) v w := by
  classical
  induction qs with
  | nil => simp at hv
  | cons q qs ih =>
    by_cases he : v.1=q
    · simp [dispatch,TM2.stepAux,he]
    · simpa [dispatch,TM2.stepAux,he] using ih (List.mem_cons.mp hv |>.resolve_left he)
private lemma route_spec {S : Spec} (acc : S.Q → Sym → Stmt S) (v : V S) w :
    TM2.stepAux (route acc) v w = TM2.stepAux (acc v.1 (v.2.getD 0)) v w := by
  have hh := dispatch_spec (Finset.univ.toList) (acc:=acc) (v:=v) (w:=w)
  generalize he : v.2.getD 0 = s
  fin_cases s <;> simp [route,TM2.stepAux,he,dispatch_spec]

private abbrev it (S : Spec) (n : ℕ) (c : (W S).tm.Cfg) :=
  (flip Option.bind (W S).tm.step)^[n] (some c)
private def cfg (S : Spec) (l : L) (q : S.Q) (v : Option Sym) (x o : List Sym) (b : Fin 3 → List Sym) : (W S).tm.Cfg :=
  ⟨some l,(q,v),buf x o b⟩

private lemma scan (S : Spec) (q : S.Q) (w : List Sym) (b : Fin 3 → List Sym) :
    it S (w.length+1) (cfg S none q none w [] b) =
      some (cfg S (some 2) S.q₀ none [] [] (fun j => (parts S q w j).reverse ++ b j)) := by
  induction w generalizing q b with
  | nil =>
    change some (TM2.stepAux (prog S none) (q,none) (buf [] [] b)) = _
    simp only [prog,TM2.stepAux,show buf [] [] b 0 = [] from rfl,List.head?_nil,List.tail_nil,
      input_upd,Option.isSome_none,Bool.cond_false, route_spec,push3_spec,Option.getD_none,parts,cfg]
    rfl
  | cons a w ih =>
    rw [it,List.length_cons,Function.iterate_succ_apply]
    change (flip Option.bind (W S).tm.step)^[w.length+1]
      (some (TM2.stepAux (prog S none) (q,none) (buf (a::w) [] b))) = _
    simp only [prog,TM2.stepAux,show buf (a::w) [] b 0 = a::w from rfl,List.head?_cons,List.tail_cons,
      input_upd,Option.isSome_some,Bool.cond_true, route_spec,push3_spec,Option.getD_some]
    simpa only [it,parts,List.reverse_append,List.append_assoc,cfg] using ih (S.next q a)
      (fun j => (S.emit q a j).reverse ++ b j)

private lemma drain (S : Spec) (j : Fin 3) (xs out : List Sym) (b : Fin 3 → List Sym) (v : Option Sym) :
    ∃ v', it S xs.length (cfg S (some j) S.q₀ v [] out (update b j xs)) =
      some (cfg S (some j) S.q₀ v' [] (xs.reverse ++ out) (update b j [])) := by
  induction xs generalizing out v with
  | nil => exact ⟨v,rfl⟩
  | cons a tl ih =>
    obtain ⟨v',hh⟩ := ih (a::out) (some a)
    refine ⟨v',?_⟩
    rw [it,List.length_cons,Function.iterate_succ_apply]
    change (flip Option.bind (W S).tm.step)^[tl.length]
      (some (TM2.stepAux (prog S (some j)) (S.q₀,v) (buf [] out (update b j (a::tl))))) = _
    simp only [prog,TM2.stepAux,buf_key,update_self,List.head?_cons,List.tail_cons,buf_upd,update_idem,
      Option.isSome_some,Bool.cond_true,Option.getD_some,output_upd]
    simp only [show buf [] out (update b j tl) 1 = out from rfl]
    simpa only [it,cfg,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

private lemma run (S : Spec) (x : List Sym) : RunsWithin (W S) x (cat (parts S S.q₀ x))
    ((x.length + (cat (parts S S.q₀ x)).length + 4 : ℕ) : ℝ) := by
  let w := parts S S.q₀ x
  let b := fun j => (w j).reverse
  let b₂ := update b 2 []
  let b₁ := update b₂ 1 []
  have hs := scan S S.q₀ x (fun _ => [])
  have ini : initList (W S).tm (x.map (W S).inputAlphabet.invFun) = cfg S none S.q₀ none x [] (fun _ => []) := by
    simp only [List.map_id_fun' ]; apply TM2.Cfg.mk.injEq .. |>.mpr
    exact ⟨rfl,rfl,funext fun k => by fin_cases k <;> simp [initList,W,buf,Equiv.refl]⟩
  obtain ⟨v₂,h₂⟩ := drain S 2 (b 2) [] b none
  obtain ⟨v₁,h₁⟩ := drain S 1 (b 1) (w 2) b₂ none
  obtain ⟨v₀,h₀⟩ := drain S 0 (b 0) (w 1 ++ w 2) b₁ none
  have next (j : Fin 3) (hj : j ≠ 0) (v : Option Sym) out (bs : Fin 3 → List Sym) (hem : bs j = []) :
      (W S).tm.step (cfg S (some j) S.q₀ v [] out bs) = some (cfg S (some (j-1)) S.q₀ none [] out bs) := by
    simp [cfg,FinTM2.step,TM2.step,prog,TM2.stepAux,buf_key,hem,buf_upd,hj,
      show update bs j [] = bs from hem ▸ update_eq_self j bs]
    rfl
  have hlast : (W S).tm.step (cfg S (some 0) S.q₀ v₀ [] (cat w) (update b₁ 0 [])) =
      some (haltList (W S).tm ((cat w).map (W S).outputAlphabet.invFun)) := by
    change some (TM2.stepAux (prog S (some 0)) _ _) = _
    simp only [prog,TM2.stepAux,buf_key,update_self,List.tail_nil,List.head?_nil,Option.isSome_none,
      Bool.cond_false,buf_upd,update_idem,if_pos rfl]
    apply congrArg some; apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl,rfl,funext fun k => ?_⟩
    fin_cases k <;> simp [buf,b₁,b₂,haltList,update,W,Equiv.refl,cat]
  let step := flip Option.bind (W S).tm.step
  have join {t u : ℕ} {A B C : (W S).tm.Cfg} (ha : it S t A = some B) (hb : it S u B = some C) :
      it S (u+t) A = some C := by change step^[u+t] (some A) = _; rw [Function.iterate_add_apply]; exact (congrArg (step^[u]) ha).trans hb
  have a : it S (x.length+1) (initList _ (x.map (W S).inputAlphabet.invFun)) = some (cfg S (some 2) S.q₀ none [] [] b) := by
    rw [ini]; simpa [b,w] using hs
  have c2 : it S (b 2).length (cfg S (some 2) S.q₀ none [] [] b) =
      some (cfg S (some 2) S.q₀ v₂ [] (w 2) b₂) := by simpa [b₂,b] using h₂
  have c1 : it S (b 1).length (cfg S (some 1) S.q₀ none [] (w 2) b₂) =
      some (cfg S (some 1) S.q₀ v₁ [] (w 1 ++ w 2) b₁) := by
    change it S _ (cfg S _ _ _ _ _ _) = _
    have he : update b₂ 1 (b 1) = b₂ := by rw [show b 1 = b₂ 1 from rfl,update_eq_self]
    rw [he] at h₁; simpa [b,b₁] using h₁
  have c0 : it S (b 0).length (cfg S (some 0) S.q₀ none [] (w 1 ++ w 2) b₁) =
      some (cfg S (some 0) S.q₀ v₀ [] (cat w) (update b₁ 0 [])) := by
    have he : update b₁ 0 (b 0) = b₁ := by rw [show b 0 = b₁ 0 from rfl,update_eq_self]
    rw [he] at h₀; simpa [b,cat,List.append_assoc] using h₀
  have d2 : it S 1 (cfg S (some 2) S.q₀ v₂ [] (w 2) b₂) = _ := next 2 (by decide) v₂ _ b₂ rfl
  have d1 : it S 1 (cfg S (some 1) S.q₀ v₁ [] (w 1 ++ w 2) b₁) = _ := next 1 (by decide) v₁ _ b₁ rfl
  have d0 : it S 1 (cfg S (some 0) S.q₀ v₀ [] (cat w) (update b₁ 0 [])) = _ := hlast
  have h := join (join (join (join (join (join a c2) d2) c1) d1) c0) d0
  let steps := x.length + (cat w).length + 4
  refine ⟨steps,le_rfl,⟨⟨⟨steps,?_⟩,le_rfl⟩⟩⟩
  change it S steps _ = some (haltList _ ((cat w).map (W S).outputAlphabet.invFun))
  have he : steps = 1 + ((b 0).length + (1 + ((b 1).length + (1 + ((b 2).length + (x.length+1)))))) := by
    simp only [steps,cat,b,List.length_append,List.length_reverse]; omega
  rw [he]; exact h

private def pair (x y : List Sym) := x.flatMap (fun s => [0,s]) ++ 1::y
private def quote (x : List Sym) := x.flatMap (fun s => [0,s])

private lemma plen (x y : List Sym) : (pair x y).length = 2*x.length+y.length+1 := by
  induction x with
  | nil => simp [pair]
  | cons a x ih =>
    change ((0:Sym)::a::pair x y).length = _
    simp only [List.length_cons,ih]; omega

private def dupl : Spec where
  Q := Unit
  q₀ := ()
  next _ _ := ()
  emit _ s := ![[0,s],[s],[]]
  last _ := ![[1],[],[]]

private lemma dup_spec (x : List Sym) : parts dupl () x = ![pair x [],x,[]] := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    have h j : parts dupl () (a::x) j = ![[0,a],[a],[]] j ++ parts dupl () x j := rfl
    funext j; rw [h,ih]; fin_cases j <;> rfl

private abbrev sw : Spec where
  Q := Fin 7
  q₀ := 0
  next
    | 0,_ => 1
    | 1,s => if s=0 then 2 else 4
    | 2,_ => 3
    | 3,_ => 0
    | 4,s => if s=0 then 5 else 6
    | 5,_ => 4
    | 6,_ => 6
  emit
    | 1,s => if s=0 then fun _ => [] else ![[0,1],[],[]]
    | 3,s => ![[0,0,0,s],[],[]]
    | 5,s => ![[],[],[s]]
    | 6,s => ![[],[0,s],[]]
    | _,_ => fun _ => []
  last _ := ![[],[1],[]]

private lemma third (z : List Sym) : parts sw 6 z = ![[],pair z [],[]] := by
  induction z with
  | nil => rfl
  | cons s z ih =>
    have h (j) : parts sw 6 (s::z) j = (![[],[0,s],[]] j) ++ parts sw 6 z j := rfl
    funext j; rw [h,ih]; fin_cases j <;> rfl
private lemma second (y z : List Sym) : parts sw 4 (pair y z) = ![[],pair z [],y] := by
  induction y with
  | nil =>
    have h (j) : parts sw 4 (pair [] z) j = parts sw 6 z j := rfl
    funext j; rw [h,third]
  | cons s y ih =>
    have h (j) : parts sw 4 (pair (s::y) z) j = (![[],[],[s]] j) ++ parts sw 4 (pair y z) j := rfl
    funext j; rw [h,ih]; fin_cases j <;> rfl
private lemma first (x y z : List Sym) :
    parts sw 0 (pair (pair x y) z) = ![quote (pair x []),pair z [],y] := by
  induction x with
  | nil =>
    have h (j) : parts sw 0 (pair (pair [] y) z) j = (![[0,1],[],[]] j) ++ parts sw 4 (pair y z) j := rfl
    funext j; rw [h,second]; fin_cases j <;> rfl
  | cons s x ih =>
    have h (j) : parts sw 0 (pair (pair (s::x) y) z) j =
        (![[0,0,0,s],[],[]] j) ++ parts sw 0 (pair (pair x y) z) j := rfl
    funext j; rw [h,ih]; fin_cases j <;> rfl

private lemma rearrange (x y z : List Sym) :
    cat (parts sw sw.q₀ (pair (pair x y) z)) = pair (pair x z) y := by
  rw [show sw.q₀ = 0 from rfl, first]
  change (quote (pair x []) ++ pair z []) ++ y = _
  simp [quote,pair,List.flatMap_append,List.append_assoc]

theorem dup_machine : ∃ M : Machine, ∀ x, RunsWithin M x (pair x x) ((x.length+2:ℝ)^3) := by
  refine ⟨W dupl,fun x => ?_⟩
  obtain ⟨n,hn,hh⟩ := run dupl x
  have he : cat (parts dupl dupl.q₀ x) = pair x x := by
    rw [show dupl.q₀ = () from rfl,dup_spec]; simp [pair,cat,List.append_assoc]
  rw [he] at hh hn
  refine ⟨n,hn.trans ?_,hh⟩
  rw [plen]; push_cast; nlinarith [sq_nonneg (x.length : ℝ),pow_nonneg (Nat.cast_nonneg x.length : (0:ℝ) ≤ x.length) 3]

theorem swap_machine : ∃ M : Machine, ∀ x y z, let u := pair (pair x y) z
    RunsWithin M u (pair (pair x z) y) ((u.length+2:ℝ)^3) := by
  refine ⟨W sw,fun x y z => ?_⟩
  obtain ⟨n,hn,hh⟩ := run sw (pair (pair x y) z)
  rw [rearrange] at hh hn
  refine ⟨n,hn.trans ?_,hh⟩
  let u := pair (pair x y) z
  have hlen : (pair (pair x z) y).length ≤ 2*u.length := by simp [u,plen]; omega
  change ((u.length+(pair (pair x z) y).length+4 : ℕ) : ℝ) ≤ (u.length+2:ℝ)^3
  have h := (Nat.cast_le (α:=ℝ)).mpr hlen
  push_cast at h ⊢
  nlinarith [sq_nonneg (u.length : ℝ),pow_nonneg (Nat.cast_nonneg u.length : (0:ℝ) ≤ u.length) 3]

end IntConeFPT.Routing

end

/- Stack volume accounting adapted from Prove2Me submission 70c7eb16-aa64-45fc-9619-d6fd621972a7 (Apache-2.0). -/
open Turing
/-! ### Growth and size bounds (from the swarm's `Growth.lean`) -/

attribute [instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin Turing.FinTM2.ΛFin
  Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

namespace Turing

namespace TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- The number of `push` statements executed inside a single statement chain.

A single `TM2.step` runs a whole chain (`push`/`peek`/`pop`/`load`/`branch` continue within the
same step), ending at `goto` or `halt`; `pushes` therefore bounds the number of symbols that a step
can add to the stacks. -/
def pushes : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

variable [Fintype K] [DecidableEq K]

/-- Total number of symbols stored on all stacks. -/
def volume (s : (k : K) → List (Γ k)) : ℕ := ∑ k, (s k).length

theorem length_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
  funext j
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem volume_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (Function.update s k v) + (s k).length = volume s + v.length := by
  classical
  unfold volume
  rw [length_update, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s + pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have hv := volume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      have hq := ih v (Function.update s k (g v :: s k))
      simp only [TM2.stepAux, pushes]
      omega
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      have hq := ih (g v (s k).head?) (Function.update s k (s k).tail)
      simp only [TM2.stepAux, pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [TM2.stepAux, hg, Bool.cond_false, pushes]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simp only [TM2.stepAux, hg, Bool.cond_true, pushes]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _
  | halt => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _

end TM2

open TM2 in
/-- Number of symbols a machine can add to all of its stacks in one step, summed over its program. -/
noncomputable def FinTM2.growth (tm : FinTM2) : ℕ := ∑ l, TM2.pushes (tm.m l)

namespace FinTM2

variable (tm : FinTM2)

theorem flip_bind_none : (flip bind tm.step) (none : Option tm.Cfg) = none := rfl

theorem flip_bind_some (c : tm.Cfg) : (flip bind tm.step) (some c) = tm.step c := rfl

theorem step_volume {a b : tm.Cfg} (h : tm.step a = some b) :
    TM2.volume b.stk ≤ TM2.volume a.stk + tm.growth := by
  classical
  obtain ⟨l, v, s⟩ := a
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
      have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
      rw [hb, FinTM2.growth]
      refine (TM2.stepAux_volume _ _ _).trans (Nat.add_le_add_left ?_ _)
      exact Finset.single_le_sum (f := fun x => TM2.pushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem iterate_volume (tm : FinTM2) : ∀ (m : ℕ) (a b : tm.Cfg),
    (flip bind tm.step)^[m] (some a) = some b →
      TM2.volume b.stk ≤ TM2.volume a.stk + m * tm.growth
  | 0, a, b, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h; simp
  | m + 1, a, b, h => by
      rw [Function.iterate_succ_apply'] at h
      cases hprev : (flip bind tm.step)^[m] (some a) with
      | none => rw [hprev, tm.flip_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hprev, tm.flip_bind_some] at h
          have ih := iterate_volume tm m a c hprev
          have hs := tm.step_volume h
          have hmul : (m + 1) * tm.growth = m * tm.growth + tm.growth := Nat.succ_mul _ _
          rw [hmul]
          omega

theorem volume_initList (s : List (tm.Γ tm.k₀)) : TM2.volume (initList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk
    simp only [initList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem volume_haltList (s : List (tm.Γ tm.k₁)) : TM2.volume (haltList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk
    simp only [haltList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

end FinTM2

end Turing

namespace Turing

/-- **Output length bound for an arbitrary `FinTM2`.** If `tm` outputs `t` on input `s` within `n`
steps, then `t` has at most `s.length + n * growth` symbols. -/
theorem TM2OutputsInTime.output_length_le {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) : t.length ≤ s.length + n * tm.growth := by
  have hvol := tm.iterate_volume h.steps (initList tm s) (haltList tm t) h.evals_in_steps
  rw [tm.volume_initList, tm.volume_haltList] at hvol
  exact hvol.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Turing

open OnlineCRS.Combine IntConeFPT
namespace IntConeFPT.DriverAssembly

private def pair (x y : List Sym) := x.flatMap (fun s => [0,s]) ++ 1::y
private lemma pair_len (x y : List Sym) : (pair x y).length = 2*x.length+y.length+1 := by
  induction x with
  | nil => simp [pair]
  | cons a x ih =>
    simp only [pair,List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append,
      List.length_cons] at ih ⊢
    omega

private abbrev Cut (I : Instance) (M : ℕ) := Nstar I.τ I.d I.k (coeffBoundU I M)
private abbrev inp (I : Instance) (n : ℕ) := encInstance I ++ encNat n ++ [3]

-- Domination is uniform in the case index. Exponents must be chosen before the input.
private def Dom {ι : Type} (B x : ι → ℝ) := ∃ e : ℕ, ∀ i, x i ≤ B i ^ e

private lemma dom_le {ι : Type} {B x y : ι → ℝ} (h : Dom B x) (hle : ∀ i, y i ≤ x i) :
    Dom B y := by obtain ⟨e,he⟩ := h; exact ⟨e,fun i => (hle i).trans (he i)⟩

private lemma dom_const {ι : Type} {B : ι → ℝ} (hB : ∀ i, 2 ≤ B i) (c : ℕ) :
    Dom B (fun _ => (c : ℝ)) :=
  ⟨c, fun i => (by exact_mod_cast (Nat.lt_two_pow_self (n:=c)).le : (c:ℝ) ≤ (2:ℝ)^c).trans
    (pow_le_pow_left₀ (by norm_num) (hB i) c)⟩

private lemma dom_add {ι : Type} {B x y : ι → ℝ} (hB : ∀ i, 2 ≤ B i) (hx : Dom B x) (hy : Dom B y) :
    Dom B (fun i => x i + y i) := by
  obtain ⟨e,he⟩ := hx; obtain ⟨f,hf⟩ := hy
  refine ⟨max e f + 1,fun i => ?_⟩
  have h1 : 1 ≤ B i := (by norm_num : (1:ℝ) ≤ 2).trans (hB i)
  have h := (he i).trans (pow_le_pow_right₀ h1 (le_max_left e f))
  have h' := (hf i).trans (pow_le_pow_right₀ h1 (le_max_right e f))
  rw [pow_succ]
  exact (add_le_add h h').trans (by rw [← mul_two]; gcongr; exact hB i)

private lemma dom_pow {ι : Type} {B x : ι → ℝ} (hx : Dom B x) (hn : ∀ i, 0 ≤ x i) (d : ℕ) :
    Dom B (fun i => x i ^ d) := by
  obtain ⟨e,he⟩ := hx
  exact ⟨e*d,fun i => by rw [pow_mul]; exact pow_le_pow_left₀ (hn i) (he i) d⟩

private lemma dom_mul_const {ι : Type} {B x : ι → ℝ} (hB : ∀ i, 2 ≤ B i) (hx : Dom B x) (c : ℕ) :
    Dom B (fun i => x i*c) := by
  obtain ⟨e,he⟩ := hx
  obtain ⟨d,hd⟩ := dom_const hB c
  refine ⟨e+d,?_⟩
  intro i; rw [pow_add]
  exact mul_le_mul (he i) (hd i) (Nat.cast_nonneg _) (pow_nonneg ((by norm_num : (0:ℝ) ≤ 2).trans (hB i)) _)

private abbrev sz {ι : Type} (x : ι → List Sym) := fun i => ((x i).length : ℝ)
private def stage {ι : Type} (B : ι → ℝ) (x y : ι → List Sym) :=
  ∃ M : Machine, ∃ T : ι → ℝ, Dom B T ∧ ∀ i, RunsWithin M (x i) (y i) (T i)

private lemma output_size {A : Machine} {x y : List Sym} {T : ℝ}
    (h : RunsWithin A x y T) : (y.length : ℝ) ≤ x.length + T*A.tm.growth := by
  obtain ⟨n,hn,⟨hh⟩⟩ := h
  have hl := hh.output_length_le
  simp only [List.length_map] at hl
  exact (by exact_mod_cast hl : (y.length:ℝ) ≤ x.length + (n:ℝ)*A.tm.growth).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg _)))

private lemma stage_size {ι : Type} {B : ι → ℝ} (hB : ∀ i, 2 ≤ B i) {x y : ι → List Sym}
    (h : stage B x y) (hx : Dom B (sz x)) : Dom B (sz y) := by
  obtain ⟨A,T,ht,hr⟩ := h
  exact dom_le (dom_add hB hx (dom_mul_const hB ht A.tm.growth)) fun i => output_size (hr i)

private lemma glue {ι : Type} {B : ι → ℝ} (hB : ∀ i, 2 ≤ B i) {x y z : ι → List Sym}
    (hxy : stage B x y) (hyz : stage B y z) (hy : Dom B (sz y)) : stage B x z := by
  obtain ⟨M,T,hT,hM⟩ := hxy
  obtain ⟨N,U,hU,hN⟩ := hyz
  obtain ⟨W,hW⟩ := runsWithin_chain M N
  refine ⟨W,_,?_,fun i => hW _ _ _ _ _ (hM i) (hN i)⟩
  exact dom_le (dom_add hB (dom_add hB hT hU) (dom_mul_const hB (dom_add hB hy (dom_const hB 1)) 2))
    fun i => by dsimp [sz]; push_cast; linarith

private lemma save {ι : Type} {B : ι → ℝ} (hB : ∀ i, 2 ≤ B i) {x y c : ι → List Sym}
    (h : stage B x y) (hc : Dom B (sz c)) :
    stage B (fun i => pair (c i) (x i)) (fun i => pair (c i) (y i)) := by
  obtain ⟨M,T,ht,hr⟩ := h
  obtain ⟨W,hw⟩ := runsWithin_thread M
  refine ⟨W,_,?_,fun i => hw (c i) _ _ _ (hr i)⟩
  exact dom_le (dom_add hB (dom_add hB ht (dom_mul_const hB hc 2)) (dom_const hB 3))
    fun i => by dsimp [sz]; push_cast; linarith

private structure Run (X O : Machine) where
  I : Instance
  valid : I.Valid
  M : ℕ
  pos : 1 ≤ M
  o : Output I
  h : Output (homInstance I)
  tx : ℝ
  to₁ : ℝ
  to₂ : ℝ
  hx : RunsWithin X (encInstance I) (encNat M) tx
  ho : RunsWithin O (inp I (Cut I M)) (encOutput o) to₁
  hh : RunsWithin O (inp (homInstance I) (Cut I M)) (encOutput h) to₂

-- All that remains of the driver in this formulation are bounded data transformations.
theorem assemble
    (dup : Machine) (d₀ : ℕ) (hdup : ∀ x, RunsWithin dup x (pair x x) ((x.length + 2 : ℝ)^d₀))
    (prep : Machine) (d₁ : ℕ) (hprep : ∀ I : Instance, I.Valid → ∀ M : ℕ, 1 ≤ M →
      let q := inp I (Cut I M)
      let qh := inp (homInstance I) (Cut I M)
      RunsWithin prep (pair (encInstance I) (encNat M)) (pair (pair (encInstance I) qh) q)
        (((encInstance I).length + (encNat M).length + (encNat (Cut I M)).length + 2 : ℝ)^d₁))
    (perm : Machine) (d₂ : ℕ) (hperm : ∀ x y z, let u := pair (pair x y) z
      RunsWithin perm u (pair (pair x z) y) ((u.length + 2 : ℝ)^d₂))
    (finish : Machine) (d₃ : ℕ) (hfinish : ∀ (I : Instance), I.Valid →
      ∀ (a : Output I) (b : Output (homInstance I)), let u := pair (pair (encInstance I) (encOutput a)) (encOutput b)
      RunsWithin finish u (encOutput (resolveOutput I a b)) ((u.length + 2 : ℝ)^d₃))
    (X O : Machine) :
    ∃ C : ℕ, ∃ W : Machine, ∀ (I : Instance), I.Valid → ∀ M : ℕ, 1 ≤ M →
      ∀ (a : Output I) (b : Output (homInstance I)) (tx t₁ t₂ : ℝ),
      0 ≤ tx → 0 ≤ t₁ → 0 ≤ t₂ →
      RunsWithin X (encInstance I) (encNat M) tx →
      RunsWithin O (inp I (Cut I M)) (encOutput a) t₁ →
      RunsWithin O (inp (homInstance I) (Cut I M)) (encOutput b) t₂ →
      RunsWithin W (encInstance I) (encOutput (resolveOutput I a b))
        (((encInstance I).length + (encNat M).length + (encNat (Cut I M)).length + tx+t₁+t₂+2 : ℝ)^C) := by
  let x := fun r : Run X O => encInstance r.I
  let m := fun r : Run X O => encNat r.M
  let n := fun r : Run X O => encNat (Cut r.I r.M)
  let q := fun r : Run X O => inp r.I (Cut r.I r.M)
  let qh := fun r : Run X O => inp (homInstance r.I) (Cut r.I r.M)
  let a := fun r : Run X O => encOutput r.o
  let b := fun r : Run X O => encOutput r.h
  let B := fun r : Run X O => sz x r + sz m r + sz n r + r.tx+r.to₁+r.to₂+2
  have times (r : Run X O) : 0 ≤ r.tx ∧ 0 ≤ r.to₁ ∧ 0 ≤ r.to₂ := by
    have hh {V : Machine} {i o t} (h : RunsWithin V i o t) : 0 ≤ t := by
      obtain ⟨k,hk,_⟩ := h; exact (Nat.cast_nonneg _).trans hk
    exact ⟨hh r.hx,hh r.ho,hh r.hh⟩
  have hB r : 2 ≤ B r := by
    obtain ⟨ht,h₁,h₂⟩ := times r
    dsimp only [B,sz]
    linarith [Nat.cast_nonneg (α:=ℝ) (x r).length,Nat.cast_nonneg (α:=ℝ) (m r).length,
      Nat.cast_nonneg (α:=ℝ) (n r).length]
  have dom_base {f : Run X O → ℝ} (h : ∀ r, f r ≤ B r) : Dom B f :=
    ⟨1,fun r => (h r).trans_eq (pow_one _).symm⟩
  have small r : sz x r ≤ B r ∧ sz m r ≤ B r ∧ sz n r ≤ B r ∧ r.tx ≤ B r ∧ r.to₁ ≤ B r ∧ r.to₂ ≤ B r ∧
      sz x r + sz m r + sz n r + 2 ≤ B r := by
    obtain ⟨ht,h₁,h₂⟩ := times r
    have hx : 0 ≤ sz x r := Nat.cast_nonneg _
    have hm : 0 ≤ sz m r := Nat.cast_nonneg _
    have hn : 0 ≤ sz n r := Nat.cast_nonneg _
    dsimp only [B]; exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  have dx := dom_base (fun r => (small r).1)
  have mkstage {i o : Run X O → List Sym} (D : Machine) (e : ℕ)
      (run : ∀ r, RunsWithin D (i r) (o r) ((sz i r+2)^e)) (di : Dom B (sz i)) : stage B i o :=
    ⟨D,_,dom_pow (dom_add hB di (dom_const hB 2)) (fun r => by dsimp [sz]; positivity) e,run⟩
  have s1 := mkstage dup d₀ (fun r => hdup (x r)) dx
  have s2 := save hB (show stage B x m from ⟨X,_,dom_base (fun r => (small r).2.2.2.1),fun r => r.hx⟩) dx
  have s12 := glue hB s1 s2 (stage_size hB s1 dx)
  have s3 : stage B _ _ := ⟨prep,_,dom_pow (dom_base (fun r => (small r).2.2.2.2.2.2))
    (fun r => by dsimp [sz]; positivity) d₁,fun r => hprep r.I r.valid r.M r.pos⟩
  have s123 := glue hB s12 s3 (stage_size hB s12 dx)
  have fstSize {c v : Run X O → List Sym} (hp : Dom B (sz (fun r => pair (c r) (v r)))) :
      Dom B (sz c) := dom_le hp fun r => by dsimp [sz]; exact_mod_cast (by rw [pair_len]; omega : (c r).length ≤ _)
  have s4 := save hB (show stage B q a from ⟨O,_,dom_base (fun r => (small r).2.2.2.2.1),fun r => r.ho⟩)
    (fstSize (c:=fun r => pair (x r) (qh r)) (v:=q) (stage_size hB s123 dx))
  have t4 := glue hB s123 s4 (stage_size hB s123 dx)
  have s5 := mkstage perm d₂ (fun r => hperm (x r) (qh r) (a r)) (stage_size hB t4 dx)
  have t5 := glue hB t4 s5 (stage_size hB t4 dx)
  have s6 := save hB (show stage B qh b from ⟨O,_,dom_base (fun r => (small r).2.2.2.2.2.1),fun r => r.hh⟩)
    (fstSize (c:=fun r => pair (x r) (a r)) (v:=qh) (stage_size hB t5 dx))
  have t6 := glue hB t5 s6 (stage_size hB t5 dx)
  have s7 := mkstage finish d₃ (fun r => hfinish r.I r.valid r.o r.h) (stage_size hB t6 dx)
  obtain ⟨W,T,⟨e,he⟩,hr⟩ := glue hB t6 s7 (stage_size hB t6 dx)
  refine ⟨e,W,?_⟩
  intro I hI M hM a b tx t₁ t₂ _ _ _ hx ho hh
  let r : Run X O := ⟨I,hI,M,hM,a,b,tx,t₁,t₂,hx,ho,hh⟩
  obtain ⟨k,hk,hhk⟩ := hr r
  exact ⟨k,hk.trans (he r),hhk⟩

end IntConeFPT.DriverAssembly

theorem solution (M_box M_cnt : Machine) :
    ∃ C_drv : ℕ, ∃ M_main : Machine,
      ∀ (I : Instance), I.Valid →
      ∀ (M : ℕ), 1 ≤ M →
      ∀ (o₀ : Output I) (oHom : Output (homInstance I)) (T_box T₀ T_hom : ℝ),
        0 ≤ T_box → 0 ≤ T₀ → 0 ≤ T_hom →
        let N_star := Nstar I.τ I.d I.k (coeffBoundU I M)
        RunsWithin M_box (encInstance I) (encNat M) T_box →
        RunsWithin M_cnt (encInstance I ++ encNat N_star ++ [3]) (encOutput o₀) T₀ →
        RunsWithin M_cnt (encInstance (homInstance I) ++ encNat N_star ++ [3]) (encOutput oHom) T_hom →
        RunsWithin M_main (encInstance I) (encOutput (resolveOutput I o₀ oHom))
          (((encInstance I).length + (encNat M).length + (encNat N_star).length +
            T_box + T₀ + T_hom + 2 : ℝ) ^ C_drv)  := by
  obtain ⟨D,hD⟩ := IntConeFPT.Routing.dup_machine
  obtain ⟨S,hS⟩ := IntConeFPT.Routing.swap_machine
  obtain ⟨e,P,hP⟩ := count_query_writer
  obtain ⟨f,F,hF⟩ := resolve_word_evaluation
  exact IntConeFPT.DriverAssembly.assemble D 3 hD P e hP S 3 hS F f hF M_box M_cnt

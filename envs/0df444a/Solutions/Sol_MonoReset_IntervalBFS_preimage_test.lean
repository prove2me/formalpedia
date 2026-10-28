-- Prove2me | solution 1 for MonoReset.IntervalBFS.preimage_test
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:33.127251+00:00
-- url     : https://prove2.me/submissions/d8d5f2eb-4552-4211-8d8d-25fc6300496e

import Definitions.Def_MonoReset_IntervalBFS_Model
import Definitions.Def_MonoReset_IntervalBFS_Algorithm
import Init
import Mathlib


section
noncomputable section
namespace Queelius.MonotonicReset
variable {S A : Type*} [DecidableEq S] [Fintype A]

def successors (step : A→Option S→Option S) (L : Finset S) : Finset S :=
  L.biUnion fun x=>Finset.univ.biUnion fun a=> (step a (some x)).toFinset

def searchLayers (step : A→Option S→Option S) (initial : Finset S) : ℕ→Finset S×Finset S
  | 0 => (initial,initial)
  | d+1 => let p:=searchLayers step initial d
           let L:=successors step p.1 \ p.2
           (L,p.2∪L)

def Path (step : A→Option S→Option S) (initial : Finset S) : ℕ→S→Prop
  | 0,x => x∈initial
  | d+1,x => ∃y,Path step initial d y ∧ ∃a,step a (some y)=some x

theorem mem_successors (step : A→Option S→Option S) (L : Finset S) (x : S) :
    x∈successors step L ↔ ∃y∈L,∃a,step a (some y)=some x := by
  simp [successors,Option.mem_def]

theorem search_invariants (step : A→Option S→Option S) (initial : Finset S) (d : ℕ) :
    (∀x,x∈(searchLayers step initial d).1 ↔
      Path step initial d x ∧ ∀e<d,¬Path step initial e x) ∧
    (∀x,x∈(searchLayers step initial d).2 ↔ ∃e≤d,Path step initial e x) := by
  induction d with
  | zero => simp [searchLayers,Path]
  | succ d ih =>
    obtain ⟨hL,hV⟩:=ih
    have hnext (x:S) : x∈(searchLayers step initial (d+1)).1 ↔
        Path step initial (d+1) x ∧ ∀e<d+1,¬Path step initial e x := by
      change x∈successors step (searchLayers step initial d).1 \ (searchLayers step initial d).2 ↔ _
      rw [Finset.mem_sdiff,mem_successors,hV]
      constructor
      · rintro ⟨⟨y,hy,a,ha⟩,hn⟩
        refine ⟨⟨y,(hL y).mp hy |>.1,a,ha⟩,?_⟩
        intro e he hp
        exact hn ⟨e,by omega,hp⟩
      · rintro ⟨⟨y,hy,a,ha⟩,hs⟩
        refine ⟨⟨y,(hL y).mpr ⟨hy,?_⟩,a,ha⟩,?_⟩
        · intro e he hp
          exact hs (e+1) (by omega) ⟨y,hp,a,ha⟩
        · rintro ⟨e,he,hp⟩
          exact hs e (by omega) hp
    refine ⟨hnext,?_⟩
    intro x
    change x∈(searchLayers step initial d).2 ∪ (searchLayers step initial (d+1)).1 ↔ _
    rw [Finset.mem_union]
    constructor
    · rintro (hv|hl)
      · obtain ⟨e,he,hp⟩:=(hV x).mp hv
        exact ⟨e,by omega,hp⟩
      · exact ⟨d+1,le_rfl,((hnext x).mp hl).1⟩
    · rintro ⟨e,he,hp⟩
      by_cases hv : x∈(searchLayers step initial d).2
      · exact Or.inl hv
      · right
        have hed : e=d+1 := by
          by_contra hn
          exact hv ((hV x).mpr ⟨e,by omega,hp⟩)
        apply (hnext x).mpr
        refine ⟨by simpa only [hed] using hp,?_⟩
        intro j hj hpath
        exact hv ((hV x).mpr ⟨j,by omega,hpath⟩)

theorem fold_none (step : A→Option S→Option S) (hn : ∀a,step a none=none) (word : List A) :
    word.foldl (fun x a=>step a x) none=none := by
  induction word with
  | nil => rfl
  | cons a w ih => simpa only [List.foldl_cons,hn] using ih

theorem path_has_word (step : A→Option S→Option S) (initial : Finset S)
    (d : ℕ) (x : S) (h : Path step initial d x) :
    ∃word : List A,word.length=d ∧ ∃s∈initial,word.foldl (fun x a=>step a x) (some s)=some x := by
  induction d generalizing x with
  | zero => exact ⟨[],rfl,x,h,rfl⟩
  | succ d ih =>
    obtain ⟨y,hy,a,ha⟩:=h
    obtain ⟨word,hlen,s,hs,hreach⟩:=ih y hy
    refine ⟨word++[a],by simp [hlen],s,hs,?_⟩
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,hreach] using ha

theorem word_has_path (step : A→Option S→Option S) (hn : ∀a,step a none=none)
    (initial : Finset S) (word : List A) (s x : S) (hs : s∈initial)
    (h : word.foldl (fun x a=>step a x) (some s)=some x) : Path step initial word.length x := by
  induction word using List.reverseRecOn generalizing x with
  | nil =>
    simp only [List.foldl_nil,Option.some.injEq] at h
    subst x
    exact hs
  | append_singleton word a ih =>
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil] at h
    cases he : word.foldl (fun x a=>step a x) (some s) with
    | none => simp only [he,hn] at h; cases h
    | some y =>
      simp only [List.length_append,List.length_singleton]
      exact ⟨y,ih y he,a,by simpa only [he] using h⟩

theorem layer_iff_shortest_word (step : A→Option S→Option S) (hn : ∀a,step a none=none)
    (initial : Finset S) (d : ℕ) (x : S) :
    x∈(searchLayers step initial d).1 ↔
      (∃word : List A,word.length=d ∧ ∃s∈initial,word.foldl (fun x a=>step a x) (some s)=some x) ∧
      ∀word : List A,(∃s∈initial,word.foldl (fun x a=>step a x) (some s)=some x)→d≤word.length := by
  rw [(search_invariants step initial d).1 x]
  constructor
  · rintro ⟨hp,hmin⟩
    refine ⟨path_has_word step initial d x hp,?_⟩
    rintro word ⟨s,hs,hw⟩
    by_contra hle
    exact hmin word.length (by omega) (word_has_path step hn initial word s x hs hw)
  · rintro ⟨⟨word,hlen,s,hs,hw⟩,hmin⟩
    refine ⟨by simpa only [←hlen] using word_has_path step hn initial word s x hs hw,?_⟩
    intro e he hp
    obtain ⟨w,hw,s,hs,hreach⟩:=path_has_word step initial e x hp
    have hm:=hmin w ⟨s,hs,hreach⟩
    omega
end Queelius.MonotonicReset

end


section
noncomputable section
open Finset
namespace Queelius.MonotonicReset
open MonoReset.IntervalBFS

variable {n : ℕ}

theorem left_mem (I : Fin n × Fin n) : I.1 ∈ ivSet I := by
  simp only [ivSet,mem_filter,mem_univ,true_and]
  fin_omega

theorem right_mem (I : Fin n × Fin n) : I.2 ∈ ivSet I := by
  simp [ivSet]

theorem interval_nonempty (I : Fin n × Fin n) : (ivSet I).Nonempty := ⟨I.1,left_mem I⟩

theorem interval_singleton (a : Fin n) : ivSet (a,a)={a} := by
  ext s
  simp only [ivSet,mem_filter,mem_univ,true_and,mem_singleton]
  fin_omega

theorem interval_linear (a b s : Fin n) (hab : a ≤ b) : s ∈ ivSet (a,b) ↔ a ≤ s ∧ s ≤ b := by
  simp only [ivSet,mem_filter,mem_univ,true_and]
  fin_omega

theorem interval_translate (a b s m : Fin n) :
    s ∈ ivSet (a,b) ↔ s-m ∈ ivSet (a-m,b-m) := by
  letI : NeZero n := ⟨by have h:=a.isLt; omega⟩
  simp only [ivSet,mem_filter,mem_univ,true_and,sub_sub_sub_cancel_right]

theorem full_circle_iff (I : Fin n × Fin n) : ivSet I=univ ↔ (I.2-I.1).val=n-1 := by
  letI : NeZero n := ⟨by have h:=I.1.isLt; omega⟩
  have hn : 0 < n := by have h:=I.1.isLt; omega
  constructor
  · intro h
    let z : Fin n := ⟨n-1,by omega⟩
    have hz : I.1+z ∈ ivSet I := by rw [h]; exact mem_univ _
    simp only [ivSet,mem_filter,mem_univ,true_and,add_sub_cancel_left] at hz
    have hlen:=(I.2-I.1).isLt
    dsimp [z] at hz
    omega
  · intro h
    ext s
    simp only [ivSet,mem_filter,mem_univ,true_and,iff_true]
    rw [h]
    have hs:=(s-I.1).isLt
    omega

theorem prec_subset (J I : Fin n × Fin n) (h : Prec J I) : ivSet J ⊆ ivSet I := by
  intro s hs
  have htr:=interval_translate J.1 J.2 s I.1
  have hj : s-I.1 ∈ ivSet (J.1-I.1,J.2-I.1) := htr.mp hs
  have hxy : J.1-I.1 ≤ J.2-I.1 := h.1
  have hy:=(interval_linear _ _ _ hxy).mp hj
  simp only [ivSet,mem_filter,mem_univ,true_and]
  exact hy.2.trans h.2

theorem subset_prec_or_full (J I : Fin n × Fin n) (h : ivSet J ⊆ ivSet I) :
    (I.2-I.1).val=n-1 ∨ Prec J I := by
  letI : NeZero n := ⟨by have hh:=I.1.isLt; omega⟩
  by_cases hfull : (I.2-I.1).val=n-1
  · exact Or.inl hfull
  · right
    have ha:=h (left_mem J)
    have hb:=h (right_mem J)
    simp only [ivSet,mem_filter,mem_univ,true_and] at ha hb
    refine ⟨?_,hb⟩
    by_contra hrev
    have hxy : (J.2-I.1).val < (J.1-I.1).val := by omega
    have hn : 0 < n := by have hh:=I.1.isLt; omega
    let z : Fin n := ⟨n-1,by omega⟩
    have hz : I.1+z ∈ ivSet J := by
      rw [interval_translate J.1 J.2 (I.1+z) I.1]
      simp only [add_sub_cancel_left]
      simp only [ivSet,mem_filter,mem_univ,true_and]
      dsimp [z]
      fin_omega
    have hh:=h hz
    simp only [ivSet,mem_filter,mem_univ,true_and,add_sub_cancel_left] at hh
    dsimp [z] at hh
    have hlen:=(I.2-I.1).isLt
    omega

theorem interval_subset_iff (J I : Fin n × Fin n) :
    ivSet J ⊆ ivSet I ↔ (I.2-I.1).val=n-1 ∨ Prec J I := by
  constructor
  · exact subset_prec_or_full J I
  · rintro (hf | hp)
    · rw [(full_circle_iff I).mpr hf]
      exact subset_univ _
    · exact prec_subset J I hp
end Queelius.MonotonicReset

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.MonotonicReset
variable {S A : Type*} [DecidableEq S] [Fintype A]

theorem search_layers_disjoint (step : A→Option S→Option S) (initial : Finset S)
    (i j : ℕ) (hij : i≠j) :
    Disjoint (searchLayers step initial i).1 (searchLayers step initial j).1 := by
  have hlt (a b : ℕ) (hab : a<b) :
      Disjoint (searchLayers step initial a).1 (searchLayers step initial b).1 := by
    apply Finset.disjoint_left.mpr
    intro x ha hb
    have hp:=((search_invariants step initial a).1 x).mp ha
    have hq:=((search_invariants step initial b).1 x).mp hb
    exact hq.2 a hab hp.1
  rcases lt_or_gt_of_ne hij with h|h
  · exact hlt i j h
  · exact (hlt j i h).symm

theorem search_total_visits [Fintype S] (step : A→Option S→Option S) (initial : Finset S)
    (D : Finset ℕ) : ∑d∈D,(searchLayers step initial d).1.card≤Fintype.card S := by
  have hd : (↑D : Set ℕ).PairwiseDisjoint (fun d=>(searchLayers step initial d).1) := by
    intro i hi j hj hij
    exact search_layers_disjoint step initial i j hij
  rw [←Finset.card_biUnion hd]
  exact Finset.card_le_univ _

theorem empty_layer_succ (step : A→Option S→Option S) (initial : Finset S) (d : ℕ)
    (h : (searchLayers step initial d).1=∅) : (searchLayers step initial (d+1)).1=∅ := by
  simp [searchLayers,successors,h]

theorem empty_layer_later (step : A→Option S→Option S) (initial : Finset S) (d e : ℕ)
    (hde : d≤e) (h : (searchLayers step initial d).1=∅) :
    (searchLayers step initial e).1=∅ := by
  induction e,hde using Nat.le_induction with
  | base => exact h
  | succ e he ih => exact empty_layer_succ step initial e ih

theorem nonempty_layer_bound [Fintype S] (step : A→Option S→Option S) (initial : Finset S)
    (d : ℕ) (hd : (searchLayers step initial d).1.Nonempty) : d<Fintype.card S := by
  have hp (e : ℕ) (he : e∈Finset.range (d+1)) : 1≤(searchLayers step initial e).1.card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    by_contra hn
    have hempty : (searchLayers step initial e).1=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hlast:=empty_layer_later step initial e d (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using he) hempty
    simpa only [hlast,Finset.not_nonempty_empty] using hd
  have hs:=Finset.sum_le_sum hp
  have hb:=search_total_visits step initial (Finset.range (d+1))
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one] at hs
  omega

theorem layer_empty_after_card [Fintype S] (step : A→Option S→Option S) (initial : Finset S)
    (d : ℕ) (hd : Fintype.card S≤d) : (searchLayers step initial d).1=∅ := by
  by_contra h
  have hb:=nonempty_layer_bound step initial d (Finset.nonempty_iff_ne_empty.mpr h)
  omega
end Queelius.MonotonicReset

end

section
noncomputable section
namespace Queelius.MonotonicReset
open MonoReset.IntervalBFS

theorem platform_layers_eq {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n)) (d : ℕ) :
    layers δ X d=searchLayers (dPrimeFast δ) (minIntervals X) d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [layers,searchLayers,ih,successors]

theorem interval_shortest_layers {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n))
    (d : ℕ) (I : Fin n×Fin n) :
    I∈(layers δ X d).1 ↔
      (∃τ : List (Fin k),τ.length=d ∧ ∃I₀∈minIntervals X,
        τ.foldl (fun J a=>dPrimeFast δ a J) (some I₀)=some I) ∧
      ∀τ : List (Fin k),(∃I₀∈minIntervals X,
        τ.foldl (fun J a=>dPrimeFast δ a J) (some I₀)=some I)→d≤τ.length := by
  rw [platform_layers_eq]
  exact layer_iff_shortest_word (dPrimeFast δ) (fun _=>rfl) (minIntervals X) d I

theorem layer_parent {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n))
    (d : ℕ) (I : Fin n×Fin n) (h : I∈(layers δ X (d+1)).1) :
    ∃p : (Fin n×Fin n)×Fin k,p.1∈(layers δ X d).1 ∧ dPrimeFast δ p.2 (some p.1)=some I := by
  change I∈successors (dPrimeFast δ) (layers δ X d).1 \ (layers δ X d).2 at h
  obtain ⟨y,hy,a,ha⟩:=(mem_successors (dPrimeFast δ) (layers δ X d).1 I).mp (Finset.mem_sdiff.mp h).1
  exact ⟨(y,a),hy,ha⟩

theorem backtrack_correct {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n))
    (d : ℕ) (I : Fin n×Fin n) (h : I∈(layers δ X d).1) :
    (backtrack δ X d I).length=d ∧ ∃I₀∈minIntervals X,
      (backtrack δ X d I).foldl (fun J a=>dPrimeFast δ a J) (some I₀)=some I := by
  induction d generalizing I with
  | zero => exact ⟨rfl,I,h,rfl⟩
  | succ d ih =>
    have hp:=layer_parent δ X d I h
    have hs:=Classical.choose_spec hp
    obtain ⟨hlen,I₀,hI₀,hreach⟩:=ih (Classical.choose hp).1 hs.1
    rw [backtrack,dif_pos hp]
    refine ⟨by simp [hlen],I₀,hI₀,?_⟩
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,hreach] using hs.2
theorem backtrack_shortest {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n))
    (d : ℕ) (I : Fin n×Fin n) (h : I∈(layers δ X d).1) (word : List (Fin k))
    (hw : ∃I₀∈minIntervals X,word.foldl (fun J a=>dPrimeFast δ a J) (some I₀)=some I) :
    (backtrack δ X d I).length≤word.length := by
  rw [(backtrack_correct δ X d I h).1]
  exact ((interval_shortest_layers δ X d I).mp h).2 word hw
end Queelius.MonotonicReset

end

section
noncomputable section
open Finset
namespace Queelius.MonotonicReset
open MonoReset.IntervalBFS
variable {n : ℕ}

theorem monotone_fiber_interval (f : Fin n → Fin n) (hf : IsMonotonic f) (y : Fin n)
    (hy : ∃ x,f x=y) : ∃ I : Fin n × Fin n,ivSet I=univ.filter (fun x => f x=y) := by
  classical
  letI : NeZero n := ⟨by have h:=y.isLt; omega⟩
  rcases hf with hn | ⟨m,hm⟩
  · have h:=y.isLt
    omega
  · let F : Finset (Fin n) := univ.filter (fun x => f (m+x)=y)
    have hF : F.Nonempty := by
      obtain ⟨x,hx⟩:=hy
      refine ⟨x-m,?_⟩
      simpa [F,add_comm m] using hx
    let a:=F.min' hF
    let b:=F.max' hF
    have ha : a ∈ F := min'_mem F hF
    have hb : b ∈ F := max'_mem F hF
    have hab : a ≤ b := min'_le F b hb
    have hfa : f (m+a)=y := (mem_filter.mp ha).2
    have hfb : f (m+b)=y := (mem_filter.mp hb).2
    have he (x : Fin n) : x ∈ ivSet (a,b) ↔ f (m+x)=y := by
      rw [interval_linear a b x hab]
      constructor
      · rintro ⟨hax,hxb⟩
        have hlo:=hm hax
        have hhi:=hm hxb
        dsimp only at hlo hhi
        rw [hfa] at hlo
        rw [hfb] at hhi
        have hEq : f (m+x)-f m=y-f m := Fin.ext (le_antisymm hhi hlo)
        simpa only [sub_add_cancel] using congrArg (fun t : Fin n => t+f m) hEq
      · intro hx
        have hxf : x ∈ F := mem_filter.mpr ⟨mem_univ _,hx⟩
        exact ⟨min'_le F x hxf,le_max' F x hxf⟩
    refine ⟨(m+a,m+b),?_⟩
    ext x
    rw [interval_translate (m+a) (m+b) x m]
    simp only [add_sub_cancel_left]
    rw [he]
    simp only [mem_filter,mem_univ,true_and,add_comm m,sub_add_cancel]
end Queelius.MonotonicReset

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.MonotonicReset
open MonoReset.IntervalBFS

theorem bounded_find_default (p : ℕ→Bool) (N : ℕ) :
    ((List.range (N+1)).find? p).getD N≤N := by
  cases h : (List.range (N+1)).find? p with
  | none => simp only [Option.getD_none,le_refl]
  | some d =>
    simp only [Option.getD_some]
    have hd:=List.mem_of_find?_eq_some h
    have hh:=List.mem_range.mp hd
    omega

theorem bfs_stop_bound {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n)) :
    bfsStop δ X≤n^2 := bounded_find_default _ _

theorem interval_total_visits {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n))
    (D : Finset ℕ) : ∑d∈D,(layers δ X d).1.card≤n^2 := by
  simpa only [←platform_layers_eq,Fintype.card_prod,Fintype.card_fin,pow_two] using
    search_total_visits (dPrimeFast δ) (minIntervals X) D

theorem interval_layer_empty {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n))
    (d : ℕ) (hd : n^2≤d) : (layers δ X d).1=∅ := by
  rw [platform_layers_eq]
  apply layer_empty_after_card
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using hd

theorem letter_cost_bound {n k : ℕ} (δ : Fin k→Fin n→Fin n) (I : Fin n×Fin n) :
    (∑a : Fin k,evalCost δ a I)≤8*k := by
  calc
    _ ≤ ∑_a : Fin k,8 := by
      apply Finset.sum_le_sum
      intro a ha
      unfold evalCost
      split_ifs <;> omega
    _ = _ := by simp; omega

theorem bfs_counted_cost {n k : ℕ} (δ : Fin k→Fin n→Fin n) (X : Finset (Fin n))
    (hk : 0<k) : bfsCost δ X≤11*k*n^2 := by
  let D := Finset.range (bfsStop δ X+1)
  have hlocal (d : ℕ) :
      (∑I∈(layers δ X d).1,(1+∑a : Fin k,evalCost δ a I))≤(layers δ X d).1.card*(1+8*k) := by
    calc
      _ ≤ ∑_I∈(layers δ X d).1,(1+8*k) := by
        apply Finset.sum_le_sum
        intro I hI
        exact Nat.add_le_add_left (letter_cost_bound δ I) 1
      _ = _ := by simp
  have hsum : (∑d∈D,∑I∈(layers δ X d).1,(1+∑a : Fin k,evalCost δ a I))≤n^2*(1+8*k) := by
    calc
      _ ≤ ∑d∈D,(layers δ X d).1.card*(1+8*k) := Finset.sum_le_sum (fun d _=>hlocal d)
      _ = (∑d∈D,(layers δ X d).1.card)*(1+8*k) := by rw [Finset.sum_mul]
      _ ≤ n^2*(1+8*k) := Nat.mul_le_mul_right _ (interval_total_visits δ X D)
  have hstop:=bfs_stop_bound δ X
  have hkn : n^2≤k*n^2 := Nat.le_mul_of_pos_left _ hk
  change k*n*n+(∑d∈D,∑I∈(layers δ X d).1,(1+∑a : Fin k,evalCost δ a I))+bfsStop δ X≤_
  nlinarith
end Queelius.MonotonicReset

end

section
noncomputable section
namespace Queelius.MonotonicReset.Controls
open Queelius.MonotonicReset MonoReset.IntervalBFS

def selfLoop (_ : Unit) (s : Option Bool) : Option Bool := s

theorem reachable_again_is_not_rediscovered :
    [(),()].foldl (fun s a=>selfLoop a s) (some true)=some true ∧
    true∉(searchLayers selfLoop {true} 2).1 := by
  decide

def resurrect (a : Bool) (s : Option Bool) : Option Bool :=
  match s with
  | none => if a then some true else none
  | some _ => none

theorem absorbing_failure_is_necessary :
    [false,true].foldl (fun s a=>resurrect a s) (some false)=some true ∧
    true∉(searchLayers resurrect {false} 2).1 := by
  decide

def noLetters : Fin 0→Fin 1→Fin 1 := Fin.elim0

theorem positive_alphabet_needed_for_cost : bfsCost noLetters {0}=1 := by
  have hs : bfsStop noLetters {0}=0 := by
    norm_num [bfsStop,List.range_succ,List.find?,layers,minIntervals,ivSet,Finset.univ_unique]
  rw [bfsCost,hs]
  norm_num [layers,minIntervals,ivSet,Finset.univ_unique]
end Queelius.MonotonicReset.Controls

end

section
noncomputable section
open Finset
namespace Queelius.MonotonicReset
open MonoReset.IntervalBFS
variable {n k : ℕ}

theorem preimage_table_exists (δ : Fin k → Fin n → Fin n) (hδ : ∀ a,IsMonotonic (δ a))
    (a : Fin k) (s : Fin n) (hs : ∃ x,δ a x=s) : preimTable δ a s ≠ none := by
  classical
  have h:=monotone_fiber_interval (δ a) (hδ a) s hs
  simp [preimTable,h]

theorem equal_endpoints_test (δ : Fin k → Fin n → Fin n) (a : Fin k)
    (I : Fin n × Fin n) (he : δ a I.1=δ a I.2) :
    dPrime1 δ a (some I) ≠ none ↔ ivSet I ⊆ univ.filter (fun x=>δ a x=δ a I.1) := by
  classical
  simp only [dPrime1,ne_eq,he,not_true_eq_false,ite_false]
  simp only [subset_iff,mem_filter,mem_univ,true_and]
  split_ifs <;> simp_all

theorem fast_transition_eq (δ : Fin k → Fin n → Fin n) (hδ : ∀ a,IsMonotonic (δ a))
    (a : Fin k) : dPrimeFast δ a=dPrime1 δ a := by
  classical
  funext O
  cases O with
  | none => rfl
  | some I =>
    by_cases hne : δ a I.1 ≠ δ a I.2
    · simp [dPrimeFast,dPrime1,hne]
    · have h : ∃ P : Fin n × Fin n,ivSet P=univ.filter (fun x=>δ a x=δ a I.1) :=
        monotone_fiber_interval (δ a) (hδ a) (δ a I.1) ⟨I.1,rfl⟩
      have hp:=Classical.choose_spec h
      have hc : ((Classical.choose h).2-(Classical.choose h).1).val=n-1 ∨
          Prec I (Classical.choose h) ↔ ∀ s ∈ ivSet I,δ a s=δ a I.1 := by
        rw [← interval_subset_iff, hp]
        simp only [subset_iff,mem_filter,mem_univ,true_and]
      simp only [dPrimeFast,dPrime1,hne,ite_false,preimTable,dif_pos h]
      simp only [hc]

theorem preimage_test (δ : Fin k → Fin n → Fin n) (hδ : ∀ a,IsMonotonic (δ a)) (a : Fin k) :
    (∀ s : Fin n,(∃ x,δ a x=s) → preimTable δ a s ≠ none) ∧
    (∀ I : Fin n × Fin n,δ a I.1=δ a I.2 →
      (dPrime1 δ a (some I) ≠ none ↔ ivSet I ⊆ univ.filter (fun x=>δ a x=δ a I.1))) ∧
    dPrimeFast δ a=dPrime1 δ a :=
  ⟨preimage_table_exists δ hδ a,equal_endpoints_test δ a,fast_transition_eq δ hδ a⟩
end Queelius.MonotonicReset

end

section
noncomputable section
open Finset
namespace Queelius.MonotonicReset
open MonoReset.IntervalBFS
variable {n k : ℕ}

theorem monotone_image_between (f : Fin n → Fin n) (hf : IsMonotonic f)
    (a b s : Fin n) (hne : f a ≠ f b) (hs : s ∈ ivSet (a,b)) :
    f s ∈ ivSet (f a,f b) := by
  letI : NeZero n := ⟨by have h:=a.isLt; omega⟩
  rcases hf with hn | ⟨m,hm⟩
  · have h:=a.isLt
    omega
  · have hmono (x y : Fin n) (h : x-m ≤ y-m) :
        (f x-f m).val ≤ (f y-f m).val := by
      simpa only [add_comm m,sub_add_cancel] using hm h
    have hne' : f a-f m ≠ f b-f m := by
      intro h
      apply hne
      simpa only [sub_add_cancel] using congrArg (fun t : Fin n=>t+f m) h
    rw [interval_translate a b s m] at hs
    rw [interval_translate (f a) (f b) (f s) (f m)]
    simp only [ivSet,mem_filter,mem_univ,true_and] at hs ⊢
    by_cases has : a-m ≤ s-m
    · by_cases hsb : s-m ≤ b-m
      · have h1:=hmono a s has
        have h2:=hmono s b hsb
        fin_omega
      · have hba : b-m ≤ a-m := by fin_omega
        have h1:=hmono b a hba
        have h2:=hmono a s has
        fin_omega
    · by_cases hsb : s-m ≤ b-m
      · have hba : b-m ≤ a-m := by fin_omega
        have h1:=hmono s b hsb
        have h2:=hmono b a hba
        fin_omega
      · fin_omega

theorem letter_image_subset (δ : Fin k → Fin n → Fin n) (hδ : ∀ a,IsMonotonic (δ a))
    (a : Fin k) (I J : Fin n × Fin n) (h : dPrime1 δ a (some I)=some J) :
    (ivSet I).image (δ a) ⊆ ivSet J := by
  classical
  intro y hy
  obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
  simp only [dPrime1] at h
  split_ifs at h with hne hc
  · cases Option.some.inj h
    exact monotone_image_between (δ a) (hδ a) I.1 I.2 x hne hx
  · cases Option.some.inj h
    rw [hc x hx]
    exact left_mem _

theorem run_cons (δ : Fin k → Fin n → Fin n) (a : Fin k) (τ : List (Fin k)) (s : Fin n) :
    run δ (a::τ) s=run δ τ (δ a s) := rfl

theorem dPrime_none (δ : Fin k → Fin n → Fin n) (τ : List (Fin k)) :
    dPrime δ τ none=none := by
  induction τ with
  | nil => rfl
  | cons a τ ih => exact ih

theorem word_image_subset (δ : Fin k → Fin n → Fin n) (hδ : ∀ a,IsMonotonic (δ a))
    (τ : List (Fin k)) (I J : Fin n × Fin n) (h : dPrime δ τ (some I)=some J) :
    (ivSet I).image (run δ τ) ⊆ ivSet J := by
  classical
  induction τ generalizing I with
  | nil =>
    have he : I=J:=Option.some.inj h
    subst J
    change (ivSet I).image id ⊆ ivSet I
    simp
  | cons a τ ih =>
    change dPrime δ τ (dPrime1 δ a (some I))=some J at h
    cases hd : dPrime1 δ a (some I) with
    | none => rw [hd,dPrime_none] at h; contradiction
    | some K =>
      rw [hd] at h
      have hk:=ih K h
      intro y hy
      obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
      apply hk
      apply mem_image.mpr
      exact ⟨δ a x,letter_image_subset δ hδ a I K hd (mem_image.mpr ⟨x,hx,rfl⟩),rfl⟩
end Queelius.MonotonicReset

end

section
namespace MonoReset.IntervalBFS

theorem bfs_layers {n k : ℕ} (δ : Fin k → Fin n → Fin n) (X : Finset (Fin n)) (d : ℕ)
    (I : Fin n × Fin n) :
    I ∈ (layers δ X d).1 ↔
      (∃ τ : List (Fin k), τ.length = d ∧
          ∃ I₀ ∈ minIntervals X, τ.foldl (fun J a => dPrimeFast δ a J) (some I₀) = some I) ∧
      ∀ τ : List (Fin k),
        (∃ I₀ ∈ minIntervals X, τ.foldl (fun J a => dPrimeFast δ a J) (some I₀) = some I) →
          d ≤ τ.length := by
  exact Queelius.MonotonicReset.interval_shortest_layers δ X d I

end MonoReset.IntervalBFS

end

section
theorem solution : (
  ∀ {n k : Nat} (δ : Fin k → Fin n → Fin n),
    (∀ (a : Fin k), @MonoReset.IntervalBFS.IsMonotonic n (δ a)) →
      ∀ (a : Fin k),
        And
          (∀ (s : Fin n),
            (@Exists (Fin n) fun (x : Fin n) => @Eq (Fin n) (δ a x) s) →
              @Ne (Option (Prod (Fin n) (Fin n))) (@MonoReset.IntervalBFS.preimTable n k δ a s)
                (@Option.none (Prod (Fin n) (Fin n))))
          (And
            (∀ (I : Prod (Fin n) (Fin n)),
              @Eq (Fin n) (δ a (@Prod.fst (Fin n) (Fin n) I)) (δ a (@Prod.snd (Fin n) (Fin n) I)) →
                Iff
                  (@Ne (Option (Prod (Fin n) (Fin n)))
                    (@MonoReset.IntervalBFS.dPrime1 n k δ a (@Option.some (Prod (Fin n) (Fin n)) I))
                    (@Option.none (Prod (Fin n) (Fin n))))
                  (@LE.le (Finset (Fin n))
                    (@Preorder.toLE (Finset (Fin n))
                      (@PartialOrder.toPreorder (Finset (Fin n)) (@Finset.instPartialOrder (Fin n))))
                    (@MonoReset.IntervalBFS.ivSet n I)
                    (@Finset.filter (Fin n) (fun (x : Fin n) => @Eq (Fin n) (δ a x) (δ a (@Prod.fst (Fin n) (Fin n) I)))
                      (fun (a_2 : Fin n) => instDecidableEqFin n (δ a a_2) (δ a (@Prod.fst (Fin n) (Fin n) I)))
                      (@Finset.univ (Fin n) (Fin.fintype n)))))
            (@Eq (Option (Prod (Fin n) (Fin n)) → Option (Prod (Fin n) (Fin n)))
              (@MonoReset.IntervalBFS.dPrimeFast n k δ a) (@MonoReset.IntervalBFS.dPrime1 n k δ a)))
) := @Queelius.MonotonicReset.preimage_test

end

section
noncomputable section
namespace Queelius.MonotonicReset.Controls
open MonoReset.IntervalBFS

def wrapMap (s : Fin 3) : Fin 3 := if s=1 then 1 else 0

theorem wrapMap_monotonic : IsMonotonic wrapMap := by
  right
  refine ⟨1,?_⟩
  decide

theorem wrapping_fiber : ivSet ((2 : Fin 3),0)=Finset.univ.filter (fun x=>wrapMap x=0) := by
  decide

theorem equal_endpoints_reject_whole_circle :
    dPrime1 (fun _ : Fin 1=>wrapMap) 0 (some (0,2))=none := by
  decide

theorem equal_endpoints_accept_wrapping_fiber :
    dPrime1 (fun _ : Fin 1=>wrapMap) 0 (some (2,0))=some (0,0) := by
  decide

theorem full_circle_exception_needed :
    ivSet ((0 : Fin 3),2) ⊆ ivSet (1,0) ∧ ¬ Prec ((0 : Fin 3),2) (1,0) := by
  decide

def alternating (s : Fin 4) : Fin 4 := if s.val % 2=0 then 0 else 1

theorem noncyclic_fiber_not_interval :
    ¬∃ I : Fin 4 × Fin 4,ivSet I=Finset.univ.filter (fun x=>alternating x=0) := by
  decide

theorem alternating_not_monotonic : ¬ IsMonotonic alternating := by
  intro h
  have hExists:=Queelius.MonotonicReset.monotone_fiber_interval alternating h 0 ⟨0,rfl⟩
  exact noncyclic_fiber_not_interval hExists
end Queelius.MonotonicReset.Controls

end

section
open MonoReset.IntervalBFS
theorem cost_clause {n k : ℕ} (δ : Fin k→Fin n→Fin n) (_hδ : ∀a,IsMonotonic (δ a)) (X : Finset (Fin n)) :
  0<k → bfsCost δ X≤11*k*n^2 := Queelius.MonotonicReset.bfs_counted_cost δ X

end

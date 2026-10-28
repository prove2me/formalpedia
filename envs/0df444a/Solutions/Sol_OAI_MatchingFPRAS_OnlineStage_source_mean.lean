-- Prove2me | solution 1 for OAI.MatchingFPRAS.OnlineStage.source_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:35:09.488577+00:00
-- url     : https://prove2.me/submissions/d603725f-70a3-46b3-9850-bccbc91e95d7

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004
import Theorems.Thm_OAI_MatchingFPRAS_NumericMarking_sample_source

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_AdaptiveStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

lemma average_const (n : ℕ) (a : ℚ) : average (fun _ : Bits n=>a)=a := by
  simp [average]

lemma average_split {n m : ℕ} (f : Bits (n+m) → ℚ) :
    average f=average (fun a : Bits n=>average (fun b : Bits m=>f (concat a b))) := by
  unfold average
  have h : (∑ b : Bits (n+m),f b)=∑ a : Bits n,∑ b : Bits m,f (concat a b) := by
    calc
      _ = ∑ ab : Bits n × Bits m,f (concat ab.1 ab.2) :=
        Fintype.sum_equiv (split n m) f (fun ab=>f (concat ab.1 ab.2)) (fun b=>by
          change f b=f ((split n m).symm ((split n m) b))
          rw [Equiv.symm_apply_apply])
      _ = _ := Fintype.sum_prod_type _
  rw [h,←sum_div,pow_add,div_div]
  congr 1
  ring

lemma average_one (f : Bits 1 → ℚ) :
    average f=(f (fun _=>false)+f (fun _=>true))/2 := by
  have h : (∑ b : Bits 1,f b)=f (fun _=>false)+f (fun _=>true) := by
    let e : Bits 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
    have hh:=Fintype.sum_equiv e f (fun b=>f (fun _=>b)) (fun b=>by
      congr 1; funext i; exact congrArg b (Subsingleton.elim i default))
    simpa only [Fintype.sum_bool,add_comm] using hh
  simp only [average,h,pow_one]

lemma shift_extend_concat {n m : ℕ} (a : Bits n) (b : Bits m) (i : ℕ) (hi : i < m) :
    shift n (extend (concat a b)) i=extend b i := by
  have hni : n+i<n+m := Nat.add_lt_add_left hi n
  simp only [shift,extend,dite_eq_left hi,dite_eq_left hni]
  exact concat_right a b ⟨i,hi⟩

lemma extend_concat_zero {m : ℕ} (a : Bits 1) (b : Bits m) :
    extend (concat a b) 0=a 0 := by
  simp only [extend,dite_eq_left (by omega : 0<1+m)]
  exact concat_left a b 0

namespace Experiment
variable {α β : Type}

lemma run_congr (p : Experiment α) (a b : Stream)
    (h : ∀ i,i<p.cost → a i=b i) : p.run a=p.run b := by
  induction p generalizing a b with
  | done x => rfl
  | read p ih =>
    have h0 : a 0=b 0 := h 0 (by simp [cost])
    simp only [run,h0]
    have hh : run (p (b 0)) (shift 1 a)=run (p (b 0)) (shift 1 b) := by
      apply ih
      intro i hi
      apply h
      cases he : b 0 <;> simp only [he] at hi <;> simp only [cost] <;> omega
    rw [hh]
  | delay n p ih =>
    simp only [run]
    have hh : run p (shift n a)=run p (shift n b) := by
      apply ih
      intro i hi
      exact h (n+i) (by simp only [cost]; omega)
    rw [hh]

lemma run_suffix {n m : ℕ} (p : Experiment α) (h : p.cost ≤ m)
    (a : Bits n) (b : Bits m) :
    p.run (shift n (extend (concat a b)))=p.run (extend b) := by
  apply run_congr
  intro i hi
  exact shift_extend_concat a b i (lt_of_lt_of_le hi h)

theorem average_run (p : Experiment α) (f : α → ℚ) (n : ℕ) (hn : p.cost≤n) :
    average (fun b : Bits n=>f (p.run (extend b)).1)=p.mean f := by
  induction p generalizing n with
  | done a => exact average_const n (f a)
  | delay k p ih =>
    have hk : k≤n := by simp only [cost] at hn; omega
    obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hk
    have hm : p.cost ≤ m := by simpa only [cost,Nat.add_le_add_iff_left] using hn
    rw [average_split]
    have hrun (a : Bits k) (b : Bits m) :
        f ((delay k p).run (extend (concat a b))).1=f (p.run (extend b)).1 := by
      simp only [run,run_suffix p hm a b]
    simp_rw [hrun,ih m hm]
    exact average_const k (p.mean f)
  | read p ih =>
    have hk : 1≤n := by simp only [cost] at hn; omega
    obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hk
    have hm (b : Bool) : (p b).cost ≤ m := by
      simp only [cost,Nat.add_le_add_iff_left] at hn
      cases b <;> omega
    rw [average_split]
    have hrun (a : Bits 1) (b : Bits m) :
        f ((read p).run (extend (concat a b))).1=f ((p (a 0)).run (extend b)).1 := by
      simp only [run,extend_concat_zero,run_suffix _ (hm (a 0)) a b]
    simp_rw [hrun,ih _ m (hm _)]
    rw [average_one]
    rfl

lemma run_bind (p : Experiment α) (q : α → Experiment β) (b : Stream) :
    (p.bind q).run b=
      let r:=p.run b
      let s:=(q r.1).run (shift r.2 b)
      (s.1,r.2+s.2) := by
  induction p generalizing b with
  | done a => simp [bind,run]
  | read p ih =>
    simp only [bind,run,ih]
    have hs (n : ℕ) : shift n (shift 1 b)=shift (1+n) b := by
      funext i; simp [shift,Nat.add_assoc]
    simp only [hs,Nat.add_assoc]
  | delay n p ih =>
    simp only [bind,run,ih]
    have hs (m : ℕ) : shift m (shift n b)=shift (n+m) b := by
      funext i; simp [shift,Nat.add_assoc]
    simp only [hs,Nat.add_assoc]

lemma run_map (f : α → β) (p : Experiment α) (b : Stream) :
    (p.map f).run b=(f (p.run b).1,(p.run b).2) := by simp [map,run_bind,run]

lemma run_word (n : ℕ) (b : Stream) :
    (word n).run b=((fun i : Fin n=>b i),n) := by
  induction n generalizing b with
  | zero => exact Prod.ext (funext (fun i=>Fin.elim0 i)) rfl
  | succ n ih =>
    simp only [word,run,run_map,ih,shift]
    congr 1
    · funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · rfl
      · simp only [Fin.cons_succ,Fin.val_succ]; congr 1; omega
    · omega

lemma mean_word (n : ℕ) (f : Bits n → ℚ) : (word n).mean f=average f := by
  rw [←average_run (word n) f n (by rw [cost_word])]
  congr 1
  funext b
  rw [run_word]
  congr 1
  funext i
  simp [extend,i.isLt]

end Experiment
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma normalize_repr (x : Fraction) : normalize x=repr (val x) := by
  by_cases hd : x.2=0
  · simp [normalize,repr,val,hd]
  · have he : val x=mkRat (x.1:Int) x.2 := by simp [val,Rat.mkRat_eq_div]
    simp only [normalize,hd,↓reduceIte,he,repr,Rat.num_mkRat,Rat.den_mkRat]
    simp [Nat.gcd_comm,←Int.natCast_ediv]

lemma val_nonneg (x : Fraction) : 0≤val x := by unfold val; positivity
lemma val_repr {q : ℚ} (h : 0≤q) : val (repr q)=q := by
  have hn : 0≤q.num := by exact Rat.num_nonneg.mpr h
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  change (q.num.natAbs:ℚ)/(q.den:ℚ)=q
  rw [←Int.cast_natCast q.num.natAbs,he]
  exact Rat.num_div_den q

lemma normalize_val (x : Fraction) : val (normalize x)=val x := by
  rw [normalize_repr]
  exact val_repr (val_nonneg x)

lemma mul_val (x y : Fraction) : val (mul (x,y))=val x*val y := by
  rw [mul,normalize_val]
  simp only [val,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

lemma add_val (x y : Fraction) (hx : x.2≠0) (hy : y.2≠0) :
    val (add (x,y))=val x+val y := by
  rw [add,normalize_val]
  simp only [val,Nat.cast_add,Nat.cast_mul]
  rw [div_add_div (x.1:ℚ) (y.1:ℚ) (b:=(x.2:ℚ)) (d:=(y.2:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast hy)]
  ring

lemma div_val (x y : Fraction) : val (div (x,y))=val x/val y := by
  rw [div,normalize_val]
  simp only [val,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

lemma less_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) :
    less (x,y)=decide (val x<val y) := by
  unfold less
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [val,val,div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  norm_cast

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_OnlineWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineWord
open PhysicalStream TreeData TreeFunction TreeTyped OnlineTree

lemma mean_prepend (n : ℕ) (acc : List Bool) (f : List Bool → ℚ) :
    (prepend n acc).mean f=(Experiment.word n).mean (fun w=>f ((List.ofFn w).reverse++acc)) := by
  induction n generalizing acc with
  | zero => simp [prepend,Experiment.word,Experiment.mean]
  | succ n ih =>
    simp only [prepend,Experiment.word,Experiment.mean,Experiment.mean_map,ih]
    congr 2 <;> congr 1 <;> funext w <;>
      simp [List.ofFn_succ,List.reverse_cons,List.append_assoc]

lemma ofFn_reverse (n : ℕ) (w : Bits n) :
    List.ofFn (reverseBits n w)=(List.ofFn w).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_ofFn] at hi hj
    simp only [reverseBits,Equiv.coe_fn_mk,List.getElem_ofFn,List.getElem_reverse,Fin.rev,List.length_ofFn]
    congr 1
    apply Fin.ext
    change n-(i+1)=n-1-i
    omega
lemma average_reverse (n : ℕ) (f : List Bool → ℚ) :
    average (fun w : Bits n=>f (List.ofFn w).reverse)=average (fun w : Bits n=>f (List.ofFn w)) := by
  unfold average
  congr 1
  exact Fintype.sum_equiv (reverseBits n) _ _ (fun w=>by rw [ofFn_reverse])
lemma mean_prepend_nil (n : ℕ) (f : List Bool → ℚ) :
    (prepend n []).mean f=average (fun w : Bits n=>f (List.ofFn w)) := by
  rw [mean_prepend,Experiment.mean_word]
  simp only [List.append_nil]
  exact average_reverse n f

end MatchingFPRAS.OnlineWord

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

variable {A B C : Type} [Fintype A] [Fintype B]
omit [Fintype A] [Fintype B] in
lemma qaverage_bits {n : ℕ} (f : Bits n → ℚ) : qaverage f=average f := by
  simp [qaverage,average,Bits]
lemma qaverage_equiv (e : A ≃ B) (f : B → ℚ) : qaverage (f ∘ e)=qaverage f := by
  unfold qaverage
  simp only [Function.comp_apply]
  rw [Fintype.card_congr e,e.sum_comp]
lemma qaverage_prod (f : A×B → ℚ) :
    qaverage f=qaverage (fun a=>qaverage (fun b=>f (a,b))) := by
  simp only [qaverage,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,←sum_div,div_div]
  congr 1
  ring
omit [Fintype B] in
lemma qaverage_congr (f g : A → ℚ) (h : ∀ a,f a=g a) : qaverage f=qaverage g := by
  rw [show f=g from funext h]
omit [Fintype B] in
lemma qaverage_unit (f : (Fin 0 → A) → ℚ) : qaverage f=f Fin.elim0 := by
  simp only [qaverage,Fintype.sum_unique,Fintype.card_fun,Fintype.card_fin,pow_zero,Nat.cast_one,div_one]
  congr 1
omit [Fintype B] in
lemma qaverage_succ (n : ℕ) (f : (Fin (n+1) → A) → ℚ) :
    qaverage f=qaverage (fun a : A=>qaverage (fun as : Fin n → A=>f (Fin.cons a as))) := by
  rw [←qaverage_equiv (splitFunction n A).symm f,qaverage_prod]
  rfl

omit [Fintype A] [Fintype B] in
lemma mean_word_qaverage (n : ℕ) (f : List Bool → ℚ) :
    (OnlineWord.prepend n []).mean f=qaverage (fun w : Bits n=>f (List.ofFn w)) := by
  rw [OnlineWord.mean_prepend_nil,qaverage_bits]

omit [Fintype A] [Fintype B] in
lemma mean_traverse_ofFn {X Y Ω : Type} [Fintype Ω]
    (f : X → Experiment Y) (n : ℕ) (xs : Fin n → X) (draw : Fin n → Ω → Y)
    (hf : ∀ i h,(f (xs i)).mean h=qaverage (fun u=>h (draw i u)))
    (h : List Y → ℚ) :
    (OnlineTree.traverseM f (List.ofFn xs)).mean h=
      qaverage (fun us : Fin n → Ω=>h (List.ofFn (fun i=>draw i (us i)))) := by
  induction n generalizing h with
  | zero => simp only [List.ofFn_zero,OnlineTree.traverseM,Experiment.mean,qaverage_unit]
  | succ n ih =>
    rw [List.ofFn_succ,OnlineTree.traverseM,Experiment.mean_bind,hf 0,qaverage_succ]
    apply qaverage_congr
    intro u
    simp only [Experiment.mean_map]
    rw [ih (fun i=>xs i.succ) (fun i=>draw i.succ) (fun i=>hf i.succ)]
    apply qaverage_congr
    intro us
    congr 1
    rw [List.ofFn_succ]
    rfl
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type} [Codec A] [Codec B] [Codec X]

lemma listMin_le_default (as : List ℕ) (d : ℕ) : listMin (as,d)≤d := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih => exact (ih (min d a)).trans (min_le_left _ _)

lemma listMin_le {as : List ℕ} {d a : ℕ} (ha : a∈as) : listMin (as,d)≤a := by
  induction as generalizing d with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl|ha
    · exact (listMin_le_default bs (min d a)).trans (min_le_right _ _)
    · exact ih ha

lemma le_listMin {as : List ℕ} {d a : ℕ} (hd : a≤d) (ha : ∀ b∈as,a≤b) :
    a≤listMin (as,d) := by
  induction as generalizing d with
  | nil => exact hd
  | cons b bs ih =>
    apply ih (le_min hd (ha b (by simp)))
    intro c hc; exact ha c (by simp [hc])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeCategorical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

lemma bitDenominator_eq (bs : List Bool) : bitDenominator bs=2^bs.length := by
  have h : ∀ a,bs.foldl (fun a _=>2*a) a=a*2^bs.length := by
    induction bs with
    | nil => intro a; simp
    | cons _ _ ih => intro a; simp only [List.foldl_cons,ih,List.length_cons,pow_succ]; ring
  simpa [bitDenominator] using h 1

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFractionExtra
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

lemma sub_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) (h : val y≤val x) :
    val (sub (x,y))=val x-val y := by
  have hxy : y.1*x.2≤x.1*y.2 := by
    rw [val,val,div_le_div_iff₀ (by exact_mod_cast hy) (by exact_mod_cast hx)] at h
    exact_mod_cast h
  rw [sub,normalize_val]
  simp only [val,Nat.cast_sub hxy,Nat.cast_mul]
  rw [div_sub_div (x.1:ℚ) (y.1:ℚ) (by exact_mod_cast hx.ne') (by exact_mod_cast hy.ne')]
  ring
lemma mul_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    mul (repr x,repr y)=repr (x*y) := by
  have h:=mul_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold mul at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma div_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    div (repr x,repr y)=repr (x/y) := by
  have h:=div_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold div at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma sub_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) (hxy : y≤x) :
    sub (repr x,repr y)=repr (x-y) := by
  have h:=sub_val (repr x) (repr y) x.pos y.pos (by simpa only [val_repr hx,val_repr hy] using hxy)
  rw [val_repr hx,val_repr hy] at h
  unfold sub at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped Polynomial Enlargement RealGeometry

variable {n m : ℕ}
lemma logicalRepr_injective : Function.Injective (logicalRepr (n:=n)) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
lemma vertexRepr_injective : Function.Injective (vertexRepr (n:=n) (m:=m)) := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext (Sum.inl.inj h))
    | inr b => cases h
  | inr a => cases b with
    | inl b => cases h
    | inr b =>
      have h':(logicalRepr a.1,a.2.val)=(logicalRepr b.1,b.2.val):=Sum.inr.inj h
      exact congrArg Sum.inr (Prod.ext (logicalRepr_injective (congrArg Prod.fst h'))
        (Fin.ext (congrArg Prod.snd h')))
lemma at_repr (e : LogicalEdge (Fin n)) (i : Fin (m+2)) :
    position (m,(logicalRepr e,i.val))=vertexRepr (atVertex source target m e i) := by
  unfold position atVertex
  split_ifs <;> rfl

lemma mem_logicalEdges (vs : List ℕ) (e : RawLogical) :
    e∈logicalEdges vs ↔ e.1∈vs ∧ e.2∈vs ∧ e.1<e.2 := by
  rcases e with ⟨a,b⟩
  simp [logicalEdges,and_assoc]
lemma logicalRepr_mem (e : LogicalEdge (Fin n)) : logicalRepr e∈logicalEdges (List.range n) := by
  rw [mem_logicalEdges]
  exact ⟨List.mem_range.mpr e.val.1.isLt,List.mem_range.mpr e.val.2.isLt,e.property⟩
lemma logicalEdges_complete (e : RawLogical) (h : e∈logicalEdges (List.range n)) :
    ∃ a : LogicalEdge (Fin n),logicalRepr a=e := by
  rw [mem_logicalEdges] at h
  exact ⟨⟨(⟨e.1,List.mem_range.mp h.1⟩,⟨e.2,List.mem_range.mp h.2.1⟩),h.2.2⟩,rfl⟩
lemma vertexRepr_mem (fuel : List Bool) (v : Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)) :
    vertexRepr v∈vertices (List.range n,fuel) := by
  cases v with
  | inl v => simp only [vertices,List.mem_append,List.mem_map]; exact Or.inl ⟨v.val,List.mem_range.mpr v.isLt,rfl⟩
  | inr q =>
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨(logicalRepr q.1,q.2.val),List.mem_product.mpr ⟨logicalRepr_mem q.1,List.mem_range.mpr q.2.isLt⟩,rfl⟩
lemma vertices_complete (fuel : List Bool) (v : RawVertex) (h : v∈vertices (List.range n,fuel)) :
    ∃ a : Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length),vertexRepr a=v := by
  simp only [vertices,List.mem_append,List.mem_map] at h
  rcases h with ⟨i,hi,rfl⟩|⟨⟨e,i⟩,hi,rfl⟩
  · exact ⟨.inl ⟨i,List.mem_range.mp hi⟩,rfl⟩
  · obtain ⟨he,hj⟩:=List.mem_product.mp hi
    obtain ⟨a,rfl⟩:=logicalEdges_complete e he
    exact ⟨.inr (a,⟨i,List.mem_range.mp hj⟩),rfl⟩
lemma realRepr_mem (fuel : List Bool) (e : LogicalEdge (Fin n)×Fin (4*fuel.length+1)) :
    realRepr e∈realEdges (List.range n,fuel) := by
  exact List.mem_product.mpr ⟨logicalRepr_mem e.1,List.mem_range.mpr e.2.isLt⟩
lemma realEdges_complete (fuel : List Bool) (e : RawReal) (h : e∈realEdges (List.range n,fuel)) :
    ∃ a : LogicalEdge (Fin n)×Fin (4*fuel.length+1),realRepr a=e := by
  obtain ⟨he,hi⟩:=List.mem_product.mp h
  obtain ⟨a,ha⟩:=logicalEdges_complete e.1 he
  exact ⟨(a,⟨e.2,List.mem_range.mp hi⟩),Prod.ext ha rfl⟩
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeDyadic
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction Polynomial

lemma findGreatest_lt_size (H s : ℕ) : Nat.findGreatest (fun k=>k < s) H=min H (s-1) := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨min_le_left _ _,?_,?_⟩
  · intro h
    have hle:=min_le_right H (s-1)
    omega
  · intro k hk hkH hks
    have hmin:=le_min hkH (show k ≤ s-1 by omega)
    omega
lemma level_val (H : ℕ) (x : Fraction) : level (H,x)=(NumberedHierarchy.level H (val x)).val := by
  have hp : (fun k=>(2:ℚ)^k≤val x)=(fun k=>k<(x.1/x.2).size) := by
    funext k
    apply propext
    rw [Nat.lt_size]
    rw [←Rat.natFloor_natCast_div_natCast]
    have h:=Nat.le_floor_iff' (R:=ℚ) (n:=2^k) (a:=val x) (by positivity)
    simpa only [val,Nat.cast_pow,Nat.cast_ofNat] using h.symm
  simp only [NumberedHierarchy.level,level,hp,findGreatest_lt_size]
lemma level_repr (H : ℕ) (q : ℚ) (hq : 0≤q) :
    level (H,TreeFraction.repr q)=(NumberedHierarchy.level H q).val := by
  rw [level_val,TreeFraction.val_repr hq]

lemma threshold_repr (xs : List Bool) (k : ℕ) (hk : k≤xs.length) :
    threshold (xs,k)=TreeFraction.repr ((2:ℚ)^k) := by
  simp only [threshold,bitDenominator_eq,List.length_take,min_eq_left hk]
  have h : val ((2^k,1):Fraction)=(2:ℚ)^k := by simp [val]
  rw [←h,←normalize_repr]
  simp [TreeFraction.normalize]
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneck
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma maximum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    maximum (repr x,repr y)=repr (max x y) := by
  unfold maximum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [max_eq_right (le_of_lt h)]
  · rw [max_eq_left (le_of_not_gt h)]
lemma minimum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    minimum (repr x,repr y)=repr (min x y) := by
  unfold minimum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [min_eq_left (le_of_lt h)]
  · rw [min_eq_right (le_of_not_gt h)]
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneckCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma maximum_fold_repr (xs : List ℚ) (z : ℚ) (hz : 0≤z) (hx : ∀ x∈xs,0≤x) :
    (xs.map TreeFraction.repr).foldl (fun z x=>maximum (x,z)) (TreeFraction.repr z)=
      TreeFraction.repr (xs.foldl (fun z x=>max x z) z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [maximum_repr (hx x (by simp)) hz]
    exact ih _ (hz.trans (le_max_right _ _)) (fun x h=>hx x (by simp [h]))
lemma le_fold_max (xs : List ℚ) (z : ℚ) : z≤xs.foldl (fun z x=>max x z) z := by
  induction xs generalizing z with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_right x z).trans (ih _)
lemma mem_le_fold_max (xs : List ℚ) (z v : ℚ) (hv : v∈xs) : v≤xs.foldl (fun z x=>max x z) z := by
  induction xs generalizing z with
  | nil => simp at hv
  | cons x xs ih =>
    rcases List.mem_cons.mp hv with rfl|hv
    · exact (le_max_left _ _).trans (le_fold_max xs _)
    · exact ih _ hv
lemma fold_max_le (xs : List ℚ) (z B : ℚ) (hz : z≤B) (hx : ∀ x∈xs,x≤B) :
    xs.foldl (fun z x=>max x z) z≤B := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
    exact ih _ (max_le (hx x (by simp)) hz) (fun x h=>hx x (by simp [h]))
lemma fold_max_ofFn {n : ℕ} (w : Fin n→ℚ) (z : ℚ) (a : Fin n) :
    (List.ofFn w).foldl (fun z x=>max x z) z=max z (Finset.univ.sup' ⟨a,Finset.mem_univ a⟩ w) := by
  apply le_antisymm
  · apply fold_max_le _ _ _ (le_max_left _ _)
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact (Finset.le_sup' w (Finset.mem_univ i)).trans (le_max_right _ _)
  · apply max_le (le_fold_max _ _)
    apply Finset.sup'_le
    intro i _
    exact mem_le_fold_max _ _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableBottleneck
open TreeTyped TreeFraction

lemma matrixRep_length {n : ℕ} (w : Fin n→Fin n→ℚ) : (matrixRep w).length=n := by
  simp [matrixRep]
lemma cell_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (a b : Fin n) :
    cell (matrixRep w,(a.val,b.val))=TreeFraction.repr (w a b) := by
  simp [cell,matrixRep,List.getD_eq_getElem?_getD,a.isLt,b.isLt]

lemma square_eq_ofFn {A B : Type} (n : ℕ) (x : A) (f : A×(ℕ×ℕ)→B) :
    square n x f=List.ofFn fun i : Fin n=>List.ofFn fun j : Fin n=>f (x,(i.val,j.val)) := by
  apply List.ext_getElem
  · simp [square]
  · intro i hi hi'
    simp only [square,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp
lemma one_repr : one=TreeFraction.repr (1:ℚ) := rfl
lemma seedEntry_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b : Fin n) :
    seedEntry (matrixRep w,(a.val,b.val))=TreeFraction.repr (BottleneckAlgorithm.seed w a b) := by
  unfold seedEntry BottleneckAlgorithm.seed BottleneckAlgorithm.edge
  dsimp only
  by_cases hab : a=b
  · subst b; simp only [↓reduceIte,one_repr]
  · have hv : a.val≠b.val := fun he=>hab (Fin.ext he)
    rw [ite_eq_right hv,ite_eq_right hab]
    by_cases hlt : a<b
    · rw [ite_eq_left hlt,min_eq_left (show a.val≤b.val from le_of_lt hlt),max_eq_right (show a.val≤b.val from le_of_lt hlt),cell_matrixRep,one_repr]
      exact maximum_repr (by norm_num) (hw a b)
    · rw [ite_eq_right hlt,min_eq_right (show b.val≤a.val from le_of_not_gt hlt),max_eq_left (show b.val≤a.val from le_of_not_gt hlt),cell_matrixRep,one_repr]
      exact maximum_repr (by norm_num) (hw b a)
lemma seed_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    seed (matrixRep w)=matrixRep (BottleneckAlgorithm.seed w) := by
  rw [seed,matrixRep_length,square_eq_ofFn]
  unfold matrixRep
  congr 1
  funext a
  congr 1
  funext b
  exact seedEntry_matrixRep w hw a b

lemma via_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b c : Fin n) :
    via ((matrixRep w,(a.val,b.val)),c.val)=TreeFraction.repr (min (w a c) (w c b)) := by
  unfold via
  dsimp only
  rw [cell_matrixRep,cell_matrixRep]
  exact minimum_repr (hw a c) (hw c b)
lemma entry_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b : Fin n) :
    entry (matrixRep w,(a.val,b.val))=TreeFraction.repr (BottleneckAlgorithm.advance w a b) := by
  unfold entry BottleneckAlgorithm.advance
  dsimp only
  by_cases hab : a=b
  · subst b; simp only [↓reduceIte,one_repr]
  · have hv : a.val≠b.val := fun he=>hab (Fin.ext he)
    rw [ite_eq_right hv,ite_eq_right hab,cell_matrixRep,matrixRep_length]
    have he : (List.range n).map (fun c=>via ((matrixRep w,(a.val,b.val)),c))=
        (List.ofFn fun c : Fin n=>min (w a c) (w c b)).map TreeFraction.repr := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        have hi0 : i<n := by simpa using hi
        simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
        exact via_matrixRep w hw a b ⟨i,hi0⟩
    rw [he,maximum_fold_repr _ _ (hw a b) (by
      intro x hx
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
      exact le_min (hw a i) (hw i b)),fold_max_ofFn _ _ a]
lemma advance_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    advance (matrixRep w)=matrixRep (BottleneckAlgorithm.advance w) := by
  rw [advance,matrixRep_length,square_eq_ofFn]
  unfold matrixRep
  congr 1
  funext a
  congr 1
  funext b
  exact entry_matrixRep w hw a b
lemma fold_advance_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (_hw : ∀ a b,0≤w a b)
    (ls : List (List Fraction)) (k : ℕ) :
    ls.foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w k))=
      matrixRep (BottleneckAlgorithm.close w (k+ls.length)) := by
  induction ls generalizing k with
  | nil => simp
  | cons r ls ih =>
    rw [List.foldl_cons,advance_matrixRep _ (fun a b=>
      (show (0:ℚ)≤1 by norm_num).trans (BottleneckAlgorithm.close_one w k a b))]
    change ls.foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w (k+1)))=_
    rw [ih]
    congr 2
    simp only [List.length_cons]; omega

theorem close_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    close (matrixRep w)=matrixRep (BottleneckAlgorithm.close w n) := by
  unfold close
  rw [seed_matrixRep w hw]
  change (matrixRep w).foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w 0))=_
  rw [fold_advance_matrixRep _ hw,matrixRep_length,Nat.zero_add]
end MatchingFPRAS.ExecutableBottleneck

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHierarchyRoot
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma related_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a b : Fin n) :
    related (((matrixRep B,TreeFraction.repr t),a.val),b.val)=decide (NumberedHierarchy.related B t a b) := by
  unfold related NumberedHierarchy.related
  rw [cell_matrixRep,TreeFraction.less_val _ _ (B a b).pos t.pos,
    TreeFraction.val_repr (hB a b),TreeFraction.val_repr ht]
  apply Bool.eq_iff_iff.mpr
  simp [Fin.ext_iff,not_lt]
lemma component_mem_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a b : Fin n) :
    b.val∈component ((matrixRep B,TreeFraction.repr t),a.val) ↔ b∈NumberedHierarchy.component B t a := by
  simp only [component,List.mem_filter,List.mem_range,matrixRep_length,
    related_matrixRep B hB t ht,decide_eq_true_eq,NumberedHierarchy.component,
    Finset.mem_filter,Finset.mem_univ,true_and]
  exact and_iff_right b.isLt
lemma root_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a : Fin n) :
    root ((matrixRep B,TreeFraction.repr t),a.val)=(NumberedHierarchy.root B t a).val := by
  apply le_antisymm
  · apply listMin_le
    exact (component_mem_matrixRep B hB t ht a _).mpr (NumberedHierarchy.root_mem B t a)
  · unfold root
    apply le_listMin (by rw [matrixRep_length]; exact Nat.le_of_lt (NumberedHierarchy.root B t a).isLt)
    intro v hv
    have hvlt : v<n := by
      have h:=List.mem_range.mp (List.mem_filter.mp hv).1
      simpa only [matrixRep_length] using h
    have hv' := (component_mem_matrixRep B hB t ht a ⟨v,hvlt⟩).mp hv
    exact Finset.min'_le _ _ hv'
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma mem_labels (x : HierarchyInput) (l : LabelKey) :
    l∈labels x ↔ l.1≤x.2.length ∧ l.2<x.1.length ∧ labelRoot (x,l)=l.2 := by
  simp only [labels,List.mem_filter,List.mem_flatMap,List.mem_map,List.mem_range,fixedRoot,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k,hk,v,hv,he⟩,hr⟩
    cases he
    exact ⟨by omega,hv,hr⟩
  · rintro ⟨hk,hv,hr⟩
    exact ⟨⟨l.1,by omega,l.2,hv,rfl⟩,hr⟩

lemma labelRoot_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (xs : List Bool) (k : Fin (xs.length+1)) (a : Fin n) :
    labelRoot ((matrixRep B,xs),(k.val,a.val))=(NumberedHierarchy.root B ((2:ℚ)^k.val) a).val := by
  unfold labelRoot
  dsimp only
  rw [threshold_repr xs k.val (by omega)]
  exact root_matrixRep B hB _ (by positivity) a

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeReweight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder Enlargement RealGeometry

lemma rawReweight_rep {n : ℕ} (w w₁ : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (hw₁ : ∀ i j,0≤w₁ i j) (K : ℕ)
    (fuel : List Bool) (hf : fuel.length=2*K+2) (e : SourceRealEdge (Fin n) K) :
    rawReweight (((matrixRep w,matrixRep w₁),fuel),(logicalRepr e.1,e.2.val))=
      TreeFraction.repr (RationalSource.rawReweight w w₁ K e) := by
  unfold rawReweight RationalSource.rawReweight
  dsimp only
  rw [hf]
  split_ifs
  · dsimp only [logicalRepr]
    rw [cell_matrixRep,cell_matrixRep,div_repr (hw₁ _ _) (hw _ _)]
    congr 1
    have hp : source e.1<target e.1 := e.1.property
    simp only [BottleneckAlgorithm.edge,ite_eq_left hp]
    rfl
  · rfl

end MatchingFPRAS.ExecutableSource

namespace MatchingFPRAS.ExecutableLadder
lemma lookup_image {I E A : Type} [DecidableEq E] (d : A) (keys : List I)
    (f : I→E) (g : I→A) (hf : Function.Injective f) (i : I) (hi : i∈keys) :
    lookup d (keys.map (fun j=>(f j,g j)),f i)=g i := by
  induction keys with
  | nil=>simp at hi
  | cons j keys ih=>
    by_cases hji : j=i
    · subst j; simp [lookup]
    · have hne : f j≠f i:=fun h=>hji (hf h)
      have hi' : i∈keys:=(List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simpa [lookup,hne] using ih hi'
lemma lookup_off {I E A : Type} [DecidableEq E] (d : A) (keys : List I)
    (f : I→E) (g : I→A) (e : E) (he : ∀ i∈keys,f i≠e) :
    lookup d (keys.map (fun j=>(f j,g j)),e)=d := by
  induction keys with
  | nil=>simp [lookup]
  | cons i keys ih=>
    have hne:=he i (by simp)
    have ht:=ih (fun j hj=>he j (by simp [hj]))
    simpa [lookup,hne] using ht
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeClosureReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BottleneckAlgorithm
open Finset

variable {V W α : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    [LinearOrder α] [OfNat α 1]
omit [Fintype V] [Fintype W] in
lemma seed_reindex (e : V≃W) (he : ∀ a b,e a<e b ↔ a<b) (w : W→W→α) (a b : V) :
    seed (fun i j=>w (e i) (e j)) a b=seed w (e a) (e b) := by
  simp only [seed,edge,e.injective.eq_iff,he]
lemma advance_reindex (e : V≃W) (w : W→W→α) (a b : V) :
    advance (fun i j=>w (e i) (e j)) a b=advance w (e a) (e b) := by
  unfold advance
  simp only [e.injective.eq_iff]
  split_ifs
  · rfl
  · congr 1
    apply le_antisymm
    · apply Finset.sup'_le
      intro c _
      exact Finset.le_sup' (fun k=>min (w (e a) k) (w k (e b))) (Finset.mem_univ (e c))
    · apply Finset.sup'_le
      intro c _
      obtain ⟨d,rfl⟩:=e.surjective c
      exact Finset.le_sup' (fun k=>min (w (e a) (e k)) (w (e k) (e b))) (Finset.mem_univ d)
lemma close_reindex (e : V≃W) (he : ∀ a b,e a<e b ↔ a<b) (w : W→W→α) (k : ℕ) :
    close (fun i j=>w (e i) (e j)) k=fun i j=>close w k (e i) (e j) := by
  induction k with
  | zero=>funext a b; exact seed_reindex e he w a b
  | succ k ih=>
    simp only [close,ih]
    funext a b
    exact advance_reindex e _ a b
end MatchingFPRAS.BottleneckAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeNumberedCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]

lemma index_orderedEnum (i : Fin (Fintype.card A)) :
    index (UnitRefresh.orderedEnum A i)=i.val := by simp [index]
end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeNumberedSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]
lemma sort_set (s : Finset A) : (set s).sort (·≤·)=(s.sort (·≤·)).map index := by
  symm
  exact Finset.map_sort embedding s (·≤·) (·≤·) (fun a _ b _=>(index_le a b).symm)
end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma ofFn_orderedEnum (A : Type) [Fintype A] [LinearOrder A] :
    List.ofFn (orderedEnum A)=(Finset.univ : Finset A).sort (· ≤ ·) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp only [List.getElem_ofFn]
    rfl
end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Finset

lemma key_injective {n H : ℕ} (B : Fin n→Fin n→ℚ) : Function.Injective (key (B:=B) (H:=H)) := by
  rintro ⟨k,a⟩ ⟨j,b⟩ he
  have he' : k=j := Fin.ext (congrArg Prod.fst he)
  cases he'
  exact congrArg (Sigma.mk k) (Subtype.ext (Fin.ext (congrArg Prod.snd he)))

lemma labels_pairwise (x : HierarchyInput) :
    (labels x).Pairwise (fun a b=>toLex a < toLex b) := by
  apply List.Pairwise.filter
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k _
    apply List.pairwise_map.mpr
    exact (List.pairwise_lt_range (n:=x.1.length)).imp (fun h=>by exact Prod.Lex.right _ h)
  · apply (List.pairwise_lt_range (n:=x.2.length+1)).imp
    intro k j hkj a ha b hb
    obtain ⟨u,_,rfl⟩:=List.mem_map.mp ha
    obtain ⟨v,_,rfl⟩:=List.mem_map.mp hb
    exact Prod.Lex.left _ _ hkj

lemma mem_labels_iff_key {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) (l : LabelKey) :
    l∈labels (matrixRep B,xs) ↔ ∃ a : NumberedHierarchy.Label B xs.length,key a=l := by
  rw [mem_labels,matrixRep_length]
  dsimp only
  constructor
  · rintro ⟨hk,hv,hr⟩
    let k : Fin (xs.length+1):=⟨l.1,by omega⟩
    let v : Fin n:=⟨l.2,hv⟩
    have hr' : NumberedHierarchy.root B ((2:ℚ)^k.val) v=v := by
      apply Fin.ext
      exact (labelRoot_matrixRep B hB xs k v).symm.trans hr
    exact ⟨⟨k,⟨v,hr'⟩⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨Nat.le_of_lt_succ a.1.isLt,a.2.val.isLt,(labelRoot_matrixRep B hB xs a.1 a.2.val).trans (congrArg Fin.val a.2.property)⟩

attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLELabelFin
lemma key_le_iff {n H : ℕ} (B : Fin n→Fin n→ℚ) (a b : NumberedHierarchy.Label B H) :
    toLex (key a) ≤ toLex (key b) ↔ a ≤ b := by
  change _ ↔ toLex (a.1,a.2.val) ≤ toLex (b.1,b.2.val)
  simp only [Prod.Lex.le_iff,key,Fin.lt_def,Fin.le_def]
  exact or_congr Iff.rfl (and_congr Fin.val_inj Iff.rfl)
attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLinearOrderLabelFin
lemma labels_eq_sorted_keys {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) :
    labels (matrixRep B,xs)=((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key := by
  let R : LabelKey→LabelKey→Prop:=fun a b=>toLex a ≤ toLex b
  have ha : (labels (matrixRep B,xs)).Pairwise R := (labels_pairwise _).imp (fun h=>h.le)
  have hb : (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key).Pairwise R := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le_iff B _ _).mpr h)
  have hn : (labels (matrixRep B,xs)).Nodup :=
    (labels_pairwise _).imp (fun h he=>h.ne (congrArg toLex he))
  have hm : (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key).Nodup :=
    (Finset.sort_nodup _ _).map (key_injective B)
  have hp : (labels (matrixRep B,xs)).Perm (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext l
    simp only [List.mem_toFinset,mem_labels_iff_key B hB,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
  exact hp.eq_of_pairwise (fun a b _ _ hab hba=>toLex.injective (le_antisymm hab hba)) ha hb
lemma labels_eq_ofFn {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) :
    labels (matrixRep B,xs)=List.ofFn (fun i=>key (UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length) i)) := by
  change _=List.ofFn (key ∘ UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length))
  rw [←List.map_ofFn,UnitRefresh.ofFn_orderedEnum,labels_eq_sorted_keys B hB]
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLTProdOfLinearOrder_solutions
lemma pairwise_product {A B : Type} [LinearOrder A] [LinearOrder B]
    {as : List A} {bs : List B} (ha : as.Pairwise (· < ·)) (hb : bs.Pairwise (· < ·)) :
    (as.product bs).Pairwise (· < ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    apply List.pairwise_map.mpr
    exact hb.imp (fun h=>Prod.Lex.right _ h)
  · apply ha.imp
    intro a b hab x hx y hy
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hy
    exact Prod.Lex.left _ _ hab

lemma logicalEdges_pairwise (n : ℕ) :
    (logicalEdges (List.range n)).Pairwise (· < ·) :=
  List.Pairwise.filter _ (pairwise_product (List.pairwise_lt_range) (List.pairwise_lt_range))
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLTSumOfLinearOrder_solutions
lemma vertices_pairwise (n : ℕ) (fuel : List Bool) :
    (vertices (List.range n,fuel)).Pairwise (· < ·) := by
  unfold vertices
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_map.mpr
    exact (List.pairwise_lt_range (n:=n)).imp (fun h=>Sum.Lex.inl h)
  · apply List.pairwise_map.mpr
    exact (pairwise_product (logicalEdges_pairwise n) List.pairwise_lt_range).imp
      (fun h=>Sum.Lex.inr h)
  · intro a ha b hb
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hb
    exact Sum.Lex.sep _ _

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLEProdOfLinearOrder_solutions
lemma logicalRepr_le {n : ℕ} (a b : LogicalEdge (Fin n)) :
    logicalRepr a ≤ logicalRepr b ↔ a ≤ b := by
  change toLex (logicalRepr a) ≤ toLex (logicalRepr b) ↔ toLex a.val ≤ toLex b.val
  simp only [Prod.Lex.le_iff,logicalRepr,ofLex_toLex,Fin.lt_def,Fin.le_def,Fin.val_inj]
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLESumOfLinearOrder_solutions
lemma vertexRepr_le {n m : ℕ} (a b : Vertex (Fin n) (LogicalEdge (Fin n)) m) :
    vertexRepr a ≤ vertexRepr b ↔ a ≤ b := by
  cases a with
  | inl a => cases b with
    | inl b =>
      change toLex (Sum.inl a.val : ℕ⊕RawReal) ≤ toLex (Sum.inl b.val : ℕ⊕RawReal) ↔
        toLex (Sum.inl a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inl b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp only [Sum.Lex.inl_le_inl_iff,Fin.le_def]
    | inr b =>
      change toLex (Sum.inl a.val : ℕ⊕RawReal) ≤ toLex (Sum.inr (logicalRepr b.1,b.2.val) : ℕ⊕RawReal) ↔
        toLex (Sum.inl a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inr b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp
  | inr a => cases b with
    | inl b =>
      change toLex (Sum.inr (logicalRepr a.1,a.2.val) : ℕ⊕RawReal) ≤ toLex (Sum.inl b.val : ℕ⊕RawReal) ↔
        toLex (Sum.inr a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inl b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp
    | inr b =>
      change toLex (Sum.inr (logicalRepr a.1,a.2.val) : ℕ⊕RawReal) ≤ toLex (Sum.inr (logicalRepr b.1,b.2.val) : ℕ⊕RawReal) ↔
        toLex (Sum.inr a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inr b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp only [Sum.Lex.inr_le_inr_iff]
      change toLex (logicalRepr a.1,a.2.val) ≤ toLex (logicalRepr b.1,b.2.val) ↔ toLex a ≤ toLex b
      simp only [Prod.Lex.le_iff,ofLex_toLex,Fin.le_def,logicalRepr_injective.eq_iff]
      have hlt : logicalRepr a.1 < logicalRepr b.1 ↔ a.1 < b.1 := by
        rw [lt_iff_not_ge,lt_iff_not_ge,logicalRepr_le]
      rw [hlt]

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instPreorderSumOfLinearOrder_solutions
lemma vertices_eq_ofFn (n : ℕ) (fuel : List Bool) :
    vertices (List.range n,fuel)=List.ofFn (fun i=>vertexRepr
      (UnitRefresh.orderedEnum (Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)) i)) := by
  classical
  let V:=Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)
  rw [show (fun i=>vertexRepr (UnitRefresh.orderedEnum V i))=vertexRepr ∘ UnitRefresh.orderedEnum V from rfl,
    ←List.map_ofFn,UnitRefresh.ofFn_orderedEnum]
  have ha : (vertices (List.range n,fuel)).Pairwise (· ≤ ·) :=
    (vertices_pairwise n fuel).imp (fun h=>le_of_lt h)
  have hb : (((Finset.univ : Finset V).sort (· ≤ ·)).map vertexRepr).Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(vertexRepr_le _ _).mpr h)
  have hn : (vertices (List.range n,fuel)).Nodup := (vertices_pairwise n fuel).imp (fun h=>h.ne)
  have hm := (Finset.sort_nodup (Finset.univ : Finset V) (· ≤ ·)).map vertexRepr_injective
  have hp : (vertices (List.range n,fuel)).Perm (((Finset.univ : Finset V).sort (· ≤ ·)).map vertexRepr) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext v
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
    constructor
    · exact vertices_complete fuel v
    · rintro ⟨a,rfl⟩; exact vertexRepr_mem fuel a
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.sumOrder.toPartialOrder _ _ h₁ h₂) ha hb
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

lemma map_range_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeSamplerRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
lemma rows_getD {a b : Bags} (h : List.Forall₂ List.Perm a b) (i : ℕ) :
    (a.getD i []).Perm (b.getD i []) := by
  induction h generalizing i with
  | nil=>exact List.Perm.refl []
  | @cons a b as bs hab _hs ih=>
    cases i with
    | zero=>exact hab
    | succ i=>exact ih i
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Polynomial

section Source
open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)}
lemma key_injective : Function.Injective (key (bags:=bags)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Sym2.sortEquiv.injective
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z=>z.1.1) h)
    · exact Fin.ext (congrArg (fun z=>z.1.2) h)
  · exact Fin.ext (congrArg Prod.snd h)
end Source

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped ExecutableDP ExecutableSource Polynomial

open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)} {a : Bags}
local instance (priority := 2000) instLEProdOfLinearOrder_solutions_ra58985_1 {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTProdOfLinearOrder_solutions
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instPreorderProdOfLinearOrder_solutions
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTSym2OfLinearOrder_solutions
lemma key_le (e f : BagEdge bags) : @LE.le Key Transport.prodOrder.toLE (key e) (key f) ↔ @LE.le _ Transport.bagEdgeOrder.toLE e f := by
  change toLex (key e) ≤ toLex (key f) ↔ toLex e.val.val ≤ toLex f.val.val
  simp only [Prod.Lex.le_iff,key,ofLex_toLex,Fin.le_def]
  have hlt : (e.val.val.1.inf.val,e.val.val.1.sup.val)<(f.val.val.1.inf.val,f.val.val.1.sup.val) ↔ e.val.val.1<f.val.val.1 := by
    change toLex (e.val.val.1.inf.val,e.val.val.1.sup.val)<toLex (f.val.val.1.inf.val,f.val.val.1.sup.val) ↔
      toLex (Sym2.sortEquiv e.val.val.1).val<toLex (Sym2.sortEquiv f.val.val.1).val
    simp only [Prod.Lex.lt_iff,ofLex_toLex,Fin.lt_def,Fin.val_inj,Sym2.sortEquiv]
    rfl
  have heq : (e.val.val.1.inf.val,e.val.val.1.sup.val)=(f.val.val.1.inf.val,f.val.val.1.sup.val) ↔ e.val.val.1=f.val.val.1 := by
    constructor
    · intro h
      apply Sym2.sortEquiv.injective
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · intro h; rw [h]
  rw [hlt,heq]
lemma row_mem (ha : List.Forall₂ List.Perm a (orderedRep bags)) (i : Fin n) (j : ℕ) :
    j∈a.getD i.val [] ↔ ∃ c∈bags i,c.val=j := by
  rw [(rows_getD ha i.val).mem_iff]
  simp only [orderedRep,List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some,bagRep,List.mem_map,Finset.mem_toList]
lemma storedCatalog_mem (ha : List.Forall₂ List.Perm a (orderedRep bags)) (e : Key) :
    e∈storedCatalog (a,List.range m) ↔ ∃ b : BagEdge bags,key b=e := by
  have hn : a.length=n := by simpa only [orderedRep,List.length_ofFn] using ha.length_eq
  constructor
  · intro he
    obtain ⟨he,hs⟩:=List.mem_filter.mp he
    obtain ⟨he,hc⟩:=List.mem_product.mp he
    obtain ⟨he,huv⟩:=List.mem_filter.mp he
    obtain ⟨hu,hv⟩:=List.mem_product.mp he
    have hu : e.1.1<n := by simpa only [List.mem_range,hn] using hu
    have hv : e.1.2<n := by simpa only [List.mem_range,hn] using hv
    have hc : e.2 < m := List.mem_range.mp hc
    have huv : e.1.1<e.1.2 := of_decide_eq_true huv
    have hs : e.2∈a.getD e.1.1 [] ∧ e.2∈a.getD e.1.2 [] := of_decide_eq_true hs
    have hcu': (⟨e.2,hc⟩ : Fin m)∈bags ⟨e.1.1,hu⟩ := by
      obtain ⟨l,hl,he⟩:=(row_mem ha ⟨e.1.1,hu⟩ e.2).mp hs.1
      have he' : l=(⟨e.2,hc⟩ : Fin m) := Fin.ext he
      simpa only [he'] using hl
    have hcv': (⟨e.2,hc⟩ : Fin m)∈bags ⟨e.1.2,hv⟩ := by
      obtain ⟨l,hl,he⟩:=(row_mem ha ⟨e.1.2,hv⟩ e.2).mp hs.2
      have he' : l=(⟨e.2,hc⟩ : Fin m) := Fin.ext he
      simpa only [he'] using hl
    have huv' : (⟨e.1.1,hu⟩ : Fin n)<⟨e.1.2,hv⟩ := huv
    let b : BagEdge bags:=⟨⟨(s((⟨e.1.1,hu⟩ : Fin n),⟨e.1.2,hv⟩),(⟨e.2,hc⟩ : Fin m)),by
      simp only [Sym2.mk_isDiag_iff]; exact ne_of_lt huv'⟩,by
      intro i hi
      rcases Sym2.mem_iff.mp hi with rfl|rfl
      · exact hcu'
      · exact hcv'⟩
    refine ⟨b,?_⟩
    simp only [key,b,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr huv'.le,sup_eq_right.mpr huv'.le]
  · rintro ⟨b,rfl⟩
    have hlt : b.val.val.1.inf<b.val.val.1.sup := lt_of_le_of_ne b.val.val.1.inf_le_sup (by
      intro h
      apply b.val.property
      rw [←sym_mk_inf_sup b.val.val.1,h]
      exact Sym2.mk_isDiag_iff.mpr rfl)
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_product.mpr
      constructor
      · apply List.mem_filter.mpr
        constructor
        · exact List.mem_product.mpr ⟨List.mem_range.mpr (by simpa only [hn] using b.val.val.1.inf.isLt),
            List.mem_range.mpr (by simpa only [hn] using b.val.val.1.sup.isLt)⟩
        · exact decide_eq_true hlt
      · exact List.mem_range.mpr b.val.val.2.isLt
    · apply decide_eq_true
      constructor
      · exact (row_mem ha _ _).mpr ⟨b.val.val.2,b.property _ (sym_inf_mem _),rfl⟩
      · exact (row_mem ha _ _).mpr ⟨b.val.val.2,b.property _ (sym_sup_mem _),rfl⟩
lemma storedCatalog_eq (ha : List.Forall₂ List.Perm a (orderedRep bags)) :
    storedCatalog (a,List.range m)=catalog bags := by
  have hpair : (storedCatalog (a,List.range m)).Pairwise (· < ·) := by
    apply List.Pairwise.filter
    exact pairwise_product (logicalEdges_pairwise a.length) List.pairwise_lt_range
  have hn := hpair.imp (fun h=>h.ne)
  have hc : (catalog bags).Nodup := List.nodup_ofFn.mpr
    ((key_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hp : (storedCatalog (a,List.range m)).Perm (catalog bags) := by
    apply (List.perm_ext_iff_of_nodup hn hc).mpr
    intro e
    rw [storedCatalog_mem ha]
    simp only [catalog,List.mem_ofFn]
    constructor
    · rintro ⟨b,rfl⟩; exact ⟨(orderedEnum _).symm b,by simp⟩
    · rintro ⟨i,rfl⟩; exact ⟨(orderedEnum _ i),rfl⟩
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂)
    (hpair.imp (fun h=>le_of_lt h))
  rw [catalog,show (fun i=>key (orderedEnum (BagEdge bags) i))=key ∘ orderedEnum (BagEdge bags) from rfl,
    ←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le _ _).mpr h)
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshNumbered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
lemma sourceKey_injective : Function.Injective (sourceKey (bags:=bags)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Sym2.sortEquiv.injective
    apply Subtype.ext
    apply Prod.ext
    · exact Numbered.index_injective (congrArg (fun z=>z.1.1) h)
    · exact Numbered.index_injective (congrArg (fun z=>z.1.2) h)
  · exact Numbered.index_injective (congrArg Prod.snd h)
lemma index_lt (a b : V) : Numbered.index a < Numbered.index b ↔ a<b := by
  rw [lt_iff_not_ge,lt_iff_not_ge,Numbered.index_le]
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLEProdOfLinearOrder_solutions_1
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTProdOfLinearOrder_solutions_1
local instance (priority := 2000) instPreorderProdOfLinearOrder_solutions_1_ra58985_1 {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTSym2OfLinearOrder_solutions_1
lemma sourceKey_le (e f : BagEdge bags) :
    @LE.le Key Transport.prodOrder.toLE (sourceKey e) (sourceKey f) ↔
      @LE.le _ Transport.bagEdgeOrder.toLE e f := by
  change toLex (sourceKey e)≤toLex (sourceKey f) ↔ toLex e.val.val≤toLex f.val.val
  simp only [Prod.Lex.le_iff,sourceKey,ofLex_toLex,Numbered.index_le]
  have hlt : (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)<
      (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔ e.val.val.1<f.val.val.1 := by
    change toLex (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)<
      toLex (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔
      toLex (Sym2.sortEquiv e.val.val.1).val<toLex (Sym2.sortEquiv f.val.val.1).val
    simp only [Prod.Lex.lt_iff,ofLex_toLex,index_lt,Numbered.index_injective.eq_iff]
    rfl
  have heq : (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)=
      (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔ e.val.val.1=f.val.val.1 := by
    constructor
    · intro h
      apply Sym2.sortEquiv.injective
      apply Subtype.ext
      exact Prod.ext (Numbered.index_injective (congrArg Prod.fst h))
        (Numbered.index_injective (congrArg Prod.snd h))
    · intro h; rw [h]
  rw [hlt,heq]
lemma sourceCatalog_index (e : BagEdge bags) :
    (sourceCatalog bags).idxOf (sourceKey e)=Numbered.index e := by
  let i := (orderedEnum (BagEdge bags)).symm e
  have hn : (sourceCatalog bags).Nodup := List.nodup_ofFn.mpr
    ((sourceKey_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hi : i.val<(sourceCatalog bags).length := by simp only [sourceCatalog,List.length_ofFn]; exact i.isLt
  dsimp only [sourceCatalog] at hi hn
  have h:=@List.Nodup.idxOf_getElem Key (inferInstance : BEq Key) inferInstance _ hn i.val hi
  have hh : (List.ofFn (fun j=>sourceKey (orderedEnum (BagEdge bags) j)))[i.val]'hi=sourceKey e := by
    rw [List.getElem_ofFn]
    simp only [Fin.eta,i,Equiv.apply_symm_apply]
  rw [hh] at h
  exact h
lemma sourceCatalog_pairwise : (sourceCatalog bags).Pairwise (· ≤ ·) := by
  rw [sourceCatalog,show (fun i=>sourceKey (orderedEnum (BagEdge bags) i))=
    sourceKey ∘ orderedEnum (BagEdge bags) from rfl,←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(sourceKey_le _ _).mpr h)
lemma key_downEdge (e : BagEdge bags) : key (downEdge e)=sourceKey e := by
  have h : (orderedEnum V).symm e.val.val.1.inf≤(orderedEnum V).symm e.val.val.1.sup := by
    change Numbered.index e.val.val.1.inf≤Numbered.index e.val.val.1.sup
    exact (Numbered.index_le _ _).mpr e.val.val.1.inf_le_sup
  simp only [key,downEdge,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr h,sup_eq_right.mpr h,sourceKey,Numbered.index]

lemma sourceKey_upEdge (e : BagEdge (numberedBags bags)) : sourceKey (upEdge e)=key e := by
  have h : orderedEnum V e.val.val.1.inf≤orderedEnum V e.val.val.1.sup := by
    exact ((Numbered.index_le _ _).mp (by simpa only [Numbered.index_orderedEnum,Fin.le_def] using e.val.val.1.inf_le_sup))
  simp only [sourceKey,upEdge,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr h,sup_eq_right.mpr h,Numbered.index_orderedEnum,key]

lemma sourceCatalog_eq : sourceCatalog bags=catalog (numberedBags bags) := by
  have ha : (sourceCatalog bags).Nodup := List.nodup_ofFn.mpr
    ((sourceKey_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hb : (catalog (numberedBags bags)).Nodup := List.nodup_ofFn.mpr
    ((key_injective (bags:=numberedBags bags)).comp (orderedEnum (BagEdge (numberedBags bags))).injective)
  have hp : (sourceCatalog bags).Perm (catalog (numberedBags bags)) := by
    apply (List.perm_ext_iff_of_nodup ha hb).mpr
    intro k
    simp only [sourceCatalog,catalog,List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨(orderedEnum _).symm (downEdge (orderedEnum _ i)),?_⟩
      rw [Equiv.apply_symm_apply,key_downEdge]
    · rintro ⟨i,rfl⟩
      refine ⟨(orderedEnum _).symm (upEdge (orderedEnum _ i)),?_⟩
      rw [Equiv.apply_symm_apply,sourceKey_upEdge]
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂) sourceCatalog_pairwise
  rw [catalog,show (fun i=>key (orderedEnum (BagEdge (numberedBags bags)) i))=
    key ∘ orderedEnum (BagEdge (numberedBags bags)) from rfl,←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le _ _).mpr h)
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
lemma index_min (a b : V) : Numbered.index (min a b)=min (Numbered.index a) (Numbered.index b) := by
  by_cases h : a≤b
  · rw [min_eq_left h,min_eq_left ((Numbered.index_le _ _).mpr h)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right ((Numbered.index_le _ _).mpr (le_of_not_ge h))]
lemma index_max (a b : V) : Numbered.index (max a b)=max (Numbered.index a) (Numbered.index b) := by
  by_cases h : a≤b
  · rw [max_eq_right h,max_eq_right ((Numbered.index_le _ _).mpr h)]
  · rw [max_eq_left (le_of_not_ge h),max_eq_left ((Numbered.index_le _ _).mpr (le_of_not_ge h))]

open TreePost Turing

end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRationalWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma fold_product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) (a : ℚ) (ha : 0≤a) :
    ((xs.map repr).foldl (fun a b=>mul (b,a)) (repr a))=repr (xs.prod*a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h : 0≤x:=hx x (by simp)
    simp only [List.map_cons,List.foldl_cons,mul_repr h ha]
    rw [ih (fun y hy=>hx y (by simp [hy])) (x*a) (mul_nonneg h ha)]
    congr 1
    simp only [List.prod_cons]
    ring
lemma product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) : product (xs.map repr)=repr xs.prod := by
  unfold product
  have h:=fold_product_repr xs hx 1 (by decide)
  simpa only [mul_one,show repr (1:ℚ)=(1,1) from rfl] using h
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped TreeFraction

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

variable (w : C×E→Fraction) (c : C) (q : E→ℚ) (hq : ∀ e,0≤q e)
    (hw : ∀ e,w (c,e)=TreeFraction.repr (q e))
omit [Codec E] [Codec C] in
include hq hw in
lemma weight_repr (s : Finset E) : weight w (c,s)=TreeFraction.repr (∏ e∈s,q e) := by
  unfold weight
  dsimp only
  simp only [hw]
  change product ((s.sort (·≤·)).map (TreeFraction.repr ∘ q))=_
  rw [←List.map_map,product_repr _ (by intro a ha; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha; exact hq b)]
  congr 1
  simpa only [Finset.sort_toFinset] using (List.prod_toFinset q (Finset.sort_nodup s (·≤·))).symm

end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma add_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    add (repr x,repr y)=repr (x+y) := by
  have h:=add_val (repr x) (repr y) x.pos.ne' y.pos.ne'
  rw [val_repr hx,val_repr hy] at h
  unfold add at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma repr_nat (n : ℕ) : repr (n:ℚ)=(n,1) := by simp [repr]

lemma fuelPower_repr (q : ℚ) (hq : 0≤q) (fuel : List Bool) :
    fuelPower (repr q,fuel)=repr (q^fuel.length) := by
  unfold fuelPower
  have he : fuel.map (fun _=>repr q)=(fuel.map (fun _=>q)).map repr := by simp
  rw [he,product_repr _ (by intro t ht; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht; exact hq)]
  congr 1
  simp
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_OnlineSampleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSample
open PhysicalStream

lemma mean_words (k N : ℕ) (h : List (List Bool) → ℚ) :
    (words (k,N)).mean h=qaverage (fun bs : Fin N → Bits k=>h (List.ofFn (fun i=>List.ofFn (bs i)))) := by
  unfold words
  rw [show List.replicate N k=List.ofFn (fun _ : Fin N=>k) by simp]
  exact mean_traverse_ofFn word N (fun _=>k) (fun _ b=>List.ofFn b) (fun _=>mean_word_qaverage k) h
lemma mean_local (k N : ℕ) (h : NumericLadder.Bits → ℚ) :
    (localWords (k,N)).mean h=qaverage (fun bs : LocalRandom N k=>h (localRep bs)) := by
  simp only [localWords,Experiment.mean_bind,Experiment.mean_map,mean_words,mean_word_qaverage]
  rw [qaverage_prod]
  rfl
lemma mean_scan (k N : ℕ) (h : List Bool×NumericLadder.Bits → ℚ) :
    (scan (k,N)).mean h=qaverage (fun bs : ScanRandom N k=>h (scanRep bs)) := by
  simp only [scan,Experiment.mean_bind,Experiment.mean_map,mean_local,mean_word_qaverage]
  rw [qaverage_prod]
  rfl
lemma mean_scans (k N r : ℕ) (h : List (List Bool×NumericLadder.Bits) → ℚ) :
    (scans ((k,N),r)).mean h=qaverage (fun bs : Fin r→ScanRandom N k=>h (List.ofFn (fun i=>scanRep (bs i)))) := by
  unfold scans
  rw [show List.replicate r (k,N)=List.ofFn (fun _ : Fin r=>(k,N)) by simp]
  exact mean_traverse_ofFn scan r (fun _=>(k,N)) (fun _ b=>scanRep b) (fun _=>mean_scan k N) h
lemma mean_marks (km m : ℕ) (keys : Fin m→ℕ) (h : List (ℕ×List Bool) → ℚ) :
    (marks (km,List.ofFn keys)).mean h=
      qaverage (fun bs : Fin m→Bits km=>h (List.ofFn (fun i=>(keys i,List.ofFn (bs i))))) := by
  simp only [marks,markRequests,List.map_ofFn]
  apply mean_traverse_ofFn markWord m (fun i=>(keys i,km)) (fun i b=>(keys i,List.ofFn b))
  intro i h
  simp only [markWord,Experiment.mean_map,mean_word_qaverage]

lemma mean_sample (N k r m km : ℕ) (keys : Fin m→ℕ) (h : NumericMarking.SampleBits → ℚ) :
    (sample (((k,N),r),(km,List.ofFn keys))).mean h=
      qaverage (fun bs : Random N k r m km=>h (sampleRep keys bs)) := by
  simp only [sample,Experiment.mean_bind,Experiment.mean_map,mean_marks,mean_scans]
  rw [qaverage_prod]
  rfl
lemma mean_many (S N k r m km : ℕ) (keys : Fin m→ℕ) (h : List NumericMarking.SampleBits → ℚ) :
    (many (S,(((k,N),r),(km,List.ofFn keys)))).mean h=
      qaverage (fun bs : Fin S→Random N k r m km=>h (List.ofFn (fun i=>sampleRep keys (bs i)))) := by
  unfold many
  rw [show List.replicate S (((k,N),r),(km,List.ofFn keys))=
    List.ofFn (fun _ : Fin S=>(((k,N),r),(km,List.ofFn keys))) by simp]
  exact mean_traverse_ofFn sample S (fun _=>(((k,N),r),(km,List.ofFn keys)))
    (fun _ b=>sampleRep keys b) (fun _=>mean_sample N k r m km keys) h
end MatchingFPRAS.OnlineSample

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeParentTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck

attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLinearOrderLabelFin_1
lemma index_key {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) :
    (labels (matrixRep B,xs)).idxOf (key a)=((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm a).val := by
  rw [labels_eq_ofFn B hB]
  let e := UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)
  let i := e.symm a
  have hn := List.nodup_ofFn.mpr ((key_injective B).comp e.injective)
  have hi : i.val < (List.ofFn (fun j=>key (e j))).length := by simpa only [List.length_ofFn] using i.isLt
  have he := @List.Nodup.idxOf_getElem LabelKey (inferInstance : BEq LabelKey) inferInstance _ hn i.val hi
  simp only [List.getElem_ofFn,Fin.eta,i,Function.comp_apply,Equiv.apply_symm_apply] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma parentKey_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) (ha : 0<a.1.val) :
    parentKey ((matrixRep B,xs),key a)=key (NumberedHierarchy.labelAt B hsym htri (H:=xs.length) ⟨a.1.val-1,by omega⟩ a.2.val) := by
  apply Prod.ext
  · rfl
  exact labelRoot_matrixRep B hB xs ⟨a.1.val-1,by omega⟩ a.2.val

lemma parentEntry_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) :
    parentEntry (((matrixRep B,xs),labels (matrixRep B,xs)),key a)=
      ExecutableDP.parentTag ((NumberedHierarchy.parent B hsym htri a).map
        (UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm) := by
  by_cases ha : 0<a.1.val
  · simp only [parentEntry,key,show ¬a.1.val=0 by omega,↓reduceIte,NumberedHierarchy.parent,ha,↓reduceDIte,Option.map_some,ExecutableDP.parentTag]
    rw [parentKey_eq B hB hsym htri xs a ha,index_key B hB]
  · have hz : a.1.val=0 := by omega
    simp [parentEntry,hz,NumberedHierarchy.parent,ExecutableDP.parentTag]

lemma parents_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) :
    parents (matrixRep B,xs)=ExecutableDP.parentRep (UnitRefresh.numberedParent (NumberedHierarchy.parent B hsym htri (H:=xs.length))) := by
  unfold parents
  rw [labels_eq_ofFn B hB,List.map_ofFn]
  unfold ExecutableDP.parentRep
  congr 1
  funext i
  simpa only [Function.comp_apply,←labels_eq_ofFn B hB,UnitRefresh.numberedParent] using parentEntry_eq B hB hsym htri xs (UnitRefresh.orderedEnum _ i)
lemma ranks_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b) (xs : List Bool) :
    ranks (matrixRep B,xs)=List.ofFn (UnitRefresh.numberedRank (fun a : NumberedHierarchy.Label B xs.length=>a.1.val)) := by
  unfold ranks
  rw [labels_eq_ofFn B hB,List.map_ofFn]
  rfl
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma edgeKey_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] (left right : E→Fin n) (e : E) :
    edgeKey ((matrixRep B,xs),((left e).val,(right e).val))=
      key (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e) := by
  unfold edgeKey
  rw [cell_matrixRep,level_repr _ _ (hB _ _)]
  apply Prod.ext
  · rfl
  exact labelRoot_matrixRep B hB xs (NumberedHierarchy.level xs.length (B (left e) (right e))) (left e)
attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLinearOrderLabelFin_2
lemma edgeIndex_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] (left right : E→Fin n) (e : E) :
    edgeIndex (((matrixRep B,xs),labels (matrixRep B,xs)),((left e).val,(right e).val))=
      ((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm
        (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)).val := by
  unfold edgeIndex
  rw [edgeKey_eq B hB hsym htri xs left right e]
  exact index_key B hB xs (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck

variable {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→Fin n)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,((left e).val,(right e).val)=p)

include hB hes
attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLinearOrderLabelFin_3
omit [DecidableEq E] in
lemma bag_members [DecidableEq E] (v : Fin n) (i : ℕ) :
    i∈bag (((matrixRep B,xs),es),v.val) ↔ ∃ e,(v=left e ∨ v=right e) ∧
      ((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm
        (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)).val=i := by
  simp only [bag,List.mem_dedup,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨p,⟨hp,hv⟩,hi⟩
    obtain ⟨e,rfl⟩ := (hes p).mp hp
    refine ⟨e,?_,?_⟩
    · simpa only [incident,decide_eq_true_eq,Fin.val_inj] using hv
    · rw [edgeIndex_eq B hB hsym htri xs left right e] at hi
      exact hi
  · rintro ⟨e,hv,hi⟩
    refine ⟨((left e).val,(right e).val),⟨(hes _).mpr ⟨e,rfl⟩,?_⟩,?_⟩
    · simpa only [incident,decide_eq_true_eq,Fin.val_inj] using hv
    · rw [edgeIndex_eq B hB hsym htri xs left right e]
      exact hi

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHierarchyReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A B : Type} [Fintype A] [Fintype B] [LinearOrder A] [LinearOrder B]
lemma index_orderIso (e : A≃o B) (a : A) : index (e a)=index a := by
  let h := Fintype.card_congr e.toEquiv
  have he : (orderedIso A).trans e=(Fin.castOrderIso h).trans (orderedIso B) := Subsingleton.elim _ _
  have hh:=congrArg (fun f : Fin (Fintype.card A)≃o B=>
    ((UnitRefresh.orderedEnum B).symm (f ((UnitRefresh.orderedEnum A).symm a))).val) he
  change ((UnitRefresh.orderedEnum B).symm
    (e (UnitRefresh.orderedEnum A ((UnitRefresh.orderedEnum A).symm a)))).val=
      ((UnitRefresh.orderedEnum B).symm
        (UnitRefresh.orderedEnum B (Fin.cast h ((UnitRefresh.orderedEnum A).symm a)))).val at hh
  simpa only [Equiv.apply_symm_apply,Equiv.symm_apply_apply,Fin.val_cast,index] using hh
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumberedHierarchy
open Finset

variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)

attribute [local instance] labelOrder

lemma labelReindex_index (H : ℕ) (l : Label (reindex B e) H) :
    TreeTyped.Numbered.index (labelReindex B e H l)=TreeTyped.Numbered.index l :=
  TreeTyped.Numbered.index_orderIso (labelOrderReindex B e H) l

open Finset

variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
variable (hsym : ∀ a b,B a b=B b a)
variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
lemma labelAt_reindex {H : ℕ} (k : Fin (H+1)) (x : V) :
    labelReindex B e H (labelAt (reindex B e) (reindex_symm B e hsym)
      (reindex_tri B e htri) k x)=labelAt B hsym htri k (e x) := by
  apply congrArg (Sigma.mk k)
  apply Subtype.ext
  exact root_reindex B e _ x
lemma edgeLabel_reindex {E : Type} [Fintype E] [DecidableEq E]
    (left right : E→W) (H : ℕ) (a : E) :
    labelReindex B e H (edgeLabel (reindex B e) (reindex_symm B e hsym)
      (reindex_tri B e htri) (e.symm ∘ left) (e.symm ∘ right) H a)=
      edgeLabel B hsym htri left right H a := by
  unfold edgeLabel
  simp only [reindex,Function.comp_apply,OrderIso.apply_symm_apply]
  rw [labelAt_reindex,OrderIso.apply_symm_apply]
end MatchingFPRAS.NumberedHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBags
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
attribute [local instance] NumberedHierarchy.labelOrder
variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,(index (left e),index (right e))=p)

include hB hes in
lemma arbitrary_bag_members (v : V) (i : ℕ) :
    i∈bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v) ↔
      ∃ e,(v=left e ∨ v=right e) ∧ index (edgeLabel B hsym htri left right xs.length e)=i := by
  let f:=orderedIso V
  have hh:=bag_members (reindex B f) (fun a b=>hB (f a) (f b))
    (reindex_symm B f hsym) (reindex_tri B f htri) xs (f.symm ∘ left) (f.symm ∘ right)
    es hes (f.symm v) i
  change i∈bag (((matrixRep (reindex B f),xs),es),index v) ↔ _ at hh
  rw [hh]
  apply exists_congr
  intro a
  have he:=labelReindex_index B f xs.length (edgeLabel (reindex B f)
    (reindex_symm B f hsym) (reindex_tri B f htri)
    (f.symm ∘ left) (f.symm ∘ right) xs.length a)
  rw [edgeLabel_reindex B f hsym htri] at he
  change (f.symm v=f.symm (left a) ∨ f.symm v=f.symm (right a)) ∧ _ ↔ _
  simp only [f.symm.injective.eq_iff]
  simpa only [index] using iff_of_eq (congrArg (fun j=>(v=left a ∨ v=right a) ∧ j=i) he.symm)

include hB hes in
lemma arbitrary_bag_perm (v : V) :
    (bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v)).Perm
      (ExecutableDP.bagRep (arbitraryNumberedBags B hsym htri xs left right v)) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_dedup _) ((Finset.nodup_toList _).map Fin.val_injective)).mpr
  intro i
  change i∈bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v) ↔ _
  rw [arbitrary_bag_members B hB hsym htri xs left right es hes]
  simp only [List.mem_map,Finset.mem_toList,arbitraryNumberedBags,
    Finset.mem_map,Equiv.toEmbedding_apply,NumberedHierarchy.mem_bags]
  constructor
  · rintro ⟨e,he,hi⟩
    exact ⟨_,⟨_,⟨e,he,rfl⟩,rfl⟩,hi⟩
  · rintro ⟨a,⟨l,⟨e,he,hel⟩,hla⟩,hai⟩
    subst l
    subst a
    exact ⟨e,he,hai⟩

include hB hes in
lemma arbitrary_bagTable :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (List.ofFn (fun i=>ExecutableDP.bagRep
        (arbitraryNumberedBags B hsym htri xs left right (UnitRefresh.orderedEnum V i)))) := by
  unfold bagTable
  rw [matrixRep_length,ExecutableDP.map_range_ofFn]
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp,?_⟩
  intro i hi _right_bound
  have hh:=arbitrary_bag_perm B hB hsym htri xs left right es hes
    (UnitRefresh.orderedEnum V ⟨i,by simpa using hi⟩)
  simpa only [List.get_eq_getElem,List.getElem_ofFn,index,Equiv.symm_apply_apply] using hh
include hB hes in
lemma arbitrary_bagTable_length (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (List.ofFn (fun i=>ExecutableDP.bagRep
        ((NumberedHierarchy.bags B hsym htri left right H (UnitRefresh.orderedEnum V i)).map
          (UnitRefresh.orderedEnum (Label B H)).symm.toEmbedding))) := by
  subst H
  exact arbitrary_bagTable B hB hsym htri xs left right es hes

include hB hes in
lemma arbitrary_bagTable_numbered (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) :=
  arbitrary_bagTable_length B hB hsym htri xs left right es hes H h

include hB hes in
lemma arbitrary_bagTable_enumerated (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) :=
  arbitrary_bagTable_numbered B hB hsym htri xs left right es hes H h

include hB hes in
lemma arbitrary_bagTable_fintype (H : ℕ) (h : xs.length=H)
    (F : Fintype (Label B H)) :
    letI := F
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) := by
  have hf : F=ordinaryLabelFintype B H := Subsingleton.elim _ _
  subst F
  exact arbitrary_bagTable_enumerated B hB hsym htri xs left right es hes H h

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeRankPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableDP Polynomial

lemma rankEntries_ofFn {m : ℕ} (rank : Fin m→ℕ) :
    rankEntries (List.ofFn rank)=List.ofFn (fun i=>(rank i,i.val)) := by
  unfold rankEntries
  rw [List.length_ofFn,map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  simp [List.getD]
lemma zipIdx_rankLE {m : ℕ} (rank : Fin m→ℕ) (a b : Fin m×ℕ) :
    List.zipIdxLE (fun x y=>decide (rank y ≤ rank x)) a b=
      decide (rankLe (rank a.1,a.2) (rank b.1,b.2)) := by
  apply Bool.eq_iff_iff.mpr
  by_cases hab : rank b.1 ≤ rank a.1 <;> by_cases hba : rank a.1 ≤ rank b.1 <;>
    simp only [List.zipIdxLE,decide_eq_true_eq,ite_true,ite_false,hab,hba]
  all_goals simp only [rankLe,Bool.false_eq_true]
  all_goals try simp only [true_iff,false_iff]
  all_goals omega
lemma zipIdx_ofFn_id (m : ℕ) :
    (List.ofFn (fun i : Fin m=>i)).zipIdx=List.ofFn (fun i : Fin m=>(i,i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_zipIdx,List.getElem_ofFn,Nat.zero_add]
lemma rankPlan_eq {m : ℕ} (rank : Fin m→ℕ) :
    rankPlan (List.ofFn rank)=(UnitRefresh.Materialized.plan rank).map Fin.val := by
  let xs := List.ofFn (fun i : Fin m=>i)
  let le := fun a b : Fin m=>decide (rank b ≤ rank a)
  let f := fun a : Fin m×ℕ=>(rank a.1,a.2)
  have hm := List.map_mergeSort (l:=xs.zipIdx) (r:=List.zipIdxLE le) (s:=fun a b=>decide (rankLe a b))
    (f:=f) (fun a _ha b _hb=>zipIdx_rankLE rank a b)
  have hz : xs.zipIdx.map f=List.ofFn (fun i=>(rank i,i.val)) := by
    rw [zipIdx_ofFn_id,List.map_ofFn]
    rfl
  have hfirst : ((xs.zipIdx).mergeSort (List.zipIdxLE le)).map (fun a=>a.1.val)=
      ((xs.zipIdx).mergeSort (List.zipIdxLE le)).map Prod.snd := by
    apply List.map_congr_left
    intro a ha
    rw [List.mem_mergeSort,zipIdx_ofFn_id,List.mem_ofFn] at ha
    obtain ⟨i,rfl⟩:=ha
    rfl
  unfold rankPlan
  rw [rankEntries_ofFn,←List.mergeSort_eq_insertionSort,←hz,←hm, List.map_map]
  change _=(xs.mergeSort le).map Fin.val
  have hm2 := congrArg (List.map Fin.val) (List.mergeSort_zipIdx (l:=xs) (le:=le))
  rw [List.map_map] at hm2
  simpa only [Function.comp_def,f] using hfirst.symm.trans hm2
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeOrderedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A B C : Type} [Fintype A] [Fintype B] [LinearOrder A] [LinearOrder B]
lemma ordered_lists_transport (e : A≃o B) (f : A→C) (g : B→C)
    (h : ∀ a,f a=g (e a)) :
    List.ofFn (fun i=>f (UnitRefresh.orderedEnum A i))=
      List.ofFn (fun i=>g (UnitRefresh.orderedEnum B i)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact Fintype.card_congr e.toEquiv
  · intro i hi hj
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn,h]
    congr 1
    apply index_injective
    rw [index_orderIso,index_orderedEnum,index_orderedEnum]
lemma parentTag_transport (e : A≃o B) (o : Option A) :
    ExecutableDP.parentTag (o.map (UnitRefresh.orderedEnum A).symm)=
      ExecutableDP.parentTag ((o.map e).map (UnitRefresh.orderedEnum B).symm) := by
  cases o with
  | none=>rfl
  | some a=>
    change (true,index a)=(true,index (e a))
    rw [index_orderIso]
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumberedHierarchy
variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
variable (hsym : ∀ a b,B a b=B b a)
variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
lemma parent_reindex {H : ℕ} (l : Label (reindex B e) H) :
    (parent (reindex B e) (reindex_symm B e hsym) (reindex_tri B e htri) l).map
      (labelReindex B e H)=parent B hsym htri (labelReindex B e H l) := by
  unfold parent
  change (if h : 0<l.1.val then some (labelAt (reindex B e) (reindex_symm B e hsym)
    (reindex_tri B e htri) ⟨l.1.val-1,by omega⟩ l.2.val) else none).map (labelReindex B e H)=
    if h : 0<l.1.val then some (labelAt B hsym htri ⟨l.1.val-1,by omega⟩ (e l.2.val)) else none
  split_ifs with h
  · rw [Option.map_some]
    exact congrArg some (labelAt_reindex B e hsym htri _ _)
  · rfl
end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
attribute [local instance] NumberedHierarchy.labelOrder
local instance (priority := 2000) instLELabel_ra58985_1 {U : Type} [Fintype U] [LinearOrder U] {H : ℕ}
    (C : U→U→ℚ) : LE (Label C H) := (labelOrder C H).toLE
include hB in
lemma arbitrary_parents (xs : List Bool) :
    parents (matrixRep (reindex B (orderedIso V)),xs)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent
        (NumberedHierarchy.parent B hsym htri (H:=xs.length))) := by
  let e:=orderedIso V
  rw [parents_eq _ (fun a b=>hB (e a) (e b)) (reindex_symm B e hsym) (reindex_tri B e htri)]
  unfold ExecutableDP.parentRep UnitRefresh.numberedParent
  exact ordered_lists_transport (labelOrderReindex B e xs.length)
    (fun a=>ExecutableDP.parentTag ((NumberedHierarchy.parent (reindex B e)
      (reindex_symm B e hsym) (reindex_tri B e htri) a).map
        (UnitRefresh.orderedEnum (Label (reindex B e) xs.length)).symm))
    (fun a=>ExecutableDP.parentTag ((NumberedHierarchy.parent B hsym htri a).map
      (UnitRefresh.orderedEnum (Label B xs.length)).symm)) (fun a=>by
    rw [parentTag_transport (labelOrderReindex B e xs.length)]
    change ExecutableDP.parentTag (Option.map (UnitRefresh.orderedEnum (Label B xs.length)).symm
      (Option.map (labelReindex B e xs.length)
        (NumberedHierarchy.parent (reindex B e) (reindex_symm B e hsym) (reindex_tri B e htri) a)))=_
    rw [parent_reindex B e hsym htri]
    rfl)
include hB in
lemma arbitrary_ranks (xs : List Bool) :
    ranks (matrixRep (reindex B (orderedIso V)),xs)=
      List.ofFn (UnitRefresh.numberedRank (fun a : Label B xs.length=>a.1.val)) := by
  let e:=orderedIso V
  rw [ranks_eq _ (fun a b=>hB (e a) (e b))]
  exact ordered_lists_transport (labelOrderReindex B e xs.length) (fun a=>a.1.val) (fun a=>a.1.val) (fun _=>rfl)
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableRefresh NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
include hB in
lemma arbitrary_labelIndices (xs : List Bool) :
    labelIndices (ExecutableBottleneck.matrixRep (reindex B (orderedIso V)),xs)=
      List.range (Fintype.card (Label B xs.length)) := by
  unfold labelIndices
  rw [labels_eq_ofFn _ (fun i j=>hB _ _),List.length_ofFn,
    Fintype.card_congr (labelReindex B (orderedIso V) xs.length)]

open TreePost Turing

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColoredIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)
include hB in
lemma arbitrary_edgeIndex (a : E) :
    edgeIndex (((matrixRep (reindex B (orderedIso V)),xs),
      labels (matrixRep (reindex B (orderedIso V)),xs)),(index (left a),index (right a)))=
      index (edgeLabel B hsym htri left right xs.length a) := by
  let e:=orderedIso V
  have h:=edgeIndex_eq (reindex B e) (fun a b=>hB (e a) (e b))
    (reindex_symm B e hsym) (reindex_tri B e htri) xs (e.symm ∘ left) (e.symm ∘ right) a
  change edgeIndex (((matrixRep (reindex B e),xs),labels (matrixRep (reindex B e),xs)),
    (index (left a),index (right a)))=index (edgeLabel (reindex B e)
      (reindex_symm B e hsym) (reindex_tri B e htri) (e.symm ∘ left) (e.symm ∘ right) xs.length a) at h
  rw [h,←labelReindex_index B e xs.length,edgeLabel_reindex B e hsym htri]

include hB in
lemma arbitrary_edgeIndex_fintype (H : ℕ) (hH : xs.length=H)
    (F : Fintype (Label B H)) (a : E) :
    letI := F
    edgeIndex (((matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),
      labels (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs)),
        (index (left a),index (right a)))=index (edgeLabel B hsym htri left right H a) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_edgeIndex B hB hsym htri xs left right a

omit [Fintype E] [DecidableEq E] in
include hB in
lemma arbitrary_labelIndices_fintype (H : ℕ) (hH : xs.length=H)
    (F : Fintype (Label B H)) :
    letI := F
    labelIndices (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i)
      (UnitRefresh.orderedEnum V j)),xs)=List.range (Fintype.card (Label B H)) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_labelIndices B hB xs

end MatchingFPRAS.ExecutableHierarchy

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered UnitRefresh Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
lemma sourceKey_mk (e : BagEdge bags) (a b : V) (l : L)
    (he : e.val.val=(s(a,b),l)) :
    sourceKey e=((min (index a) (index b),max (index a) (index b)),index l) := by
  unfold sourceKey
  rw [he]
  simp only [Sym2.inf_mk,Sym2.sup_mk,index_min,index_max]

lemma storedCatalog_source (a : ExecutableDP.Bags)
    (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags))) :
    storedCatalog (a,List.range (Fintype.card L))=sourceCatalog bags := by
  rw [storedCatalog_eq ha,sourceCatalog_eq]
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeEstimator
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma fold_sum_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) (a : ℚ) (ha : 0≤a) :
    ((xs.map repr).foldl (fun a b=>add (b,a)) (repr a))=repr (xs.sum+a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h : 0≤x:=hx x (by simp)
    simp only [List.map_cons,List.foldl_cons,add_repr h ha]
    rw [ih (fun y hy=>hx y (by simp [hy])) (x+a) (add_nonneg h ha)]
    congr 1
    simp only [List.sum_cons]
    ring
lemma sum_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) : sum (xs.map repr)=repr xs.sum := by
  unfold sum
  have h:=fold_sum_repr xs hx 0 (by decide)
  simpa only [add_zero,show repr (0:ℚ)=(0,1) from rfl] using h
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableEstimator
open TreeTyped TreeFraction

lemma mean_rep (xs : List ℚ) (hx : ∀ x∈xs,0≤x) :
    mean (xs.map TreeFraction.repr)=TreeFraction.repr (xs.sum/xs.length) := by
  unfold mean
  rw [sum_repr xs hx,List.length_map,←repr_nat xs.length,div_repr (List.sum_nonneg hx) (by positivity)]

lemma ratio_rep (a d : ℚ) (ha : 0≤a) (hd : 0≤d) :
    ratio (TreeFraction.repr a,TreeFraction.repr d)=TreeFraction.repr (Counting.ratioEstimate a d) := by
  unfold ratio Counting.ratioEstimate
  rw [show ((0,1) : Fraction)=TreeFraction.repr (0:ℚ) from rfl,
    less_val _ _ (by decide) a.pos,val_repr (by decide),val_repr ha]
  simp only [decide_eq_true_eq]
  split_ifs
  · exact div_repr hd ha
  · rfl

lemma upper_rep (D : ℕ) (d z : ℚ) (hd : 0≤d) (hz : 0≤z) :
    upper (D,(TreeFraction.repr d,TreeFraction.repr z))=TreeFraction.repr (Counting.upperEstimate D d z) := by
  have ha : ((1,100000) : Fraction)=TreeFraction.repr Counting.alpha := by norm_num [TreeFraction.repr,Counting.alpha]
  have ha0 : (0:ℚ)≤Counting.alpha := by norm_num [Counting.alpha]
  have h0 : ((0,1) : Fraction)=TreeFraction.repr (0:ℚ) := rfl
  have h3 : ((3,1) : Fraction)=TreeFraction.repr (3:ℚ) := rfl
  unfold upper Counting.upperEstimate
  rw [h0,less_val _ _ (by decide) d.pos,val_repr (by decide),val_repr hd]
  simp only [decide_eq_true_eq]
  split_ifs
  · rw [ha,h3,←repr_nat D,mul_repr (by positivity) hz,div_repr (by positivity) hd,
      add_repr (by positivity) ha0,minimum_repr (by decide) (by positivity),maximum_repr ha0 (by positivity)]
  · rfl
end MatchingFPRAS.ExecutableEstimator

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeScalingCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder

variable {n : ℕ}

lemma rowMax_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ) (v : Fin n→ℚ)
    (hG : ∀ i j,i≠j→0≤G i j) (hv : ∀ j,0≤v j) (i : Fin n) :
    rowMax ((matrixRep G,vectorRep v),i.val)=TreeFraction.repr (Counting.rowMaximum hn G v i) := by
  let js := (List.finRange n).filter (fun j=>decide (j≠i))
  let qs := js.map (fun j=>G i j/v j)
  have hj : ∀ j,j∈js↔j≠i := by intro j; simp [js]
  have hq : ∀ q∈qs,0≤q := by
    intro q h
    obtain ⟨j,hj',rfl⟩:=List.mem_map.mp h
    exact div_nonneg (hG i j ((hj j).mp hj').symm) (hv j)
  have he : ((vectorRep v).filter (fun z=>decide (z.1≠i.val))).map
      (fun z=>ratio ((matrixRep G,i.val),z))=qs.map TreeFraction.repr := by
    unfold vectorRep qs
    rw [List.ofFn_eq_map,List.filter_map,List.map_map,List.map_map]
    have hp : (fun j : Fin n=>decide ((j.val,TreeFraction.repr (v j)).1≠i.val))=
        (fun j=>decide (j≠i)) := by
      funext j
      simp only [ne_eq,Fin.val_inj]
    change List.map _ (List.filter _ (List.finRange n))=_
    rw [show ((fun z : ℕ×Fraction=>decide (z.1≠i.val)) ∘ (fun j : Fin n=>(j.val,TreeFraction.repr (v j))))=
        (fun j=>decide (j≠i)) from hp]
    apply List.map_congr_left
    intro j hj'
    dsimp only [Function.comp_apply,ratio]
    rw [cell_matrixRep,div_repr (hG i j ((hj j).mp hj').symm) (hv j)]
  unfold rowMax
  dsimp only
  rw [he,show ((0,1) : Fraction)=TreeFraction.repr (0:ℚ) from rfl,maximum_fold_repr qs 0 (by decide) hq]
  congr 1
  apply le_antisymm
  · apply fold_max_le
    · obtain ⟨j,hjj⟩:=Counting.others_nonempty hn i
      have hnz:=div_nonneg (hG i j (Finset.mem_erase.mp hjj).1.symm) (hv j)
      exact hnz.trans (Counting.ratio_le_rowMaximum hn G v i j (Finset.mem_erase.mp hjj).1)
    · intro q h
      obtain ⟨j,hj',rfl⟩:=List.mem_map.mp h
      exact Counting.ratio_le_rowMaximum hn G v i j ((hj j).mp hj')
  · apply Finset.sup'_le
    intro j hj'
    exact mem_le_fold_max qs 0 _ (List.mem_map.mpr ⟨j,(hj j).mpr (Finset.mem_erase.mp hj').1,rfl⟩)

lemma set_vectorRep (v : Fin n→ℚ) (i : Fin n) (a : ℚ) :
    setState (vectorRep v,(i.val,TreeFraction.repr a))=vectorRep (Function.update v i a) := by
  unfold setState vectorRep
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply,Function.update_apply,Fin.val_inj]
  split_ifs <;> rfl
lemma step_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ) (v : Fin n→ℚ)
    (hG : ∀ i j,i≠j→0≤G i j) (hv : ∀ j,0≤v j) (i : Fin n) :
    step (i.val,(matrixRep G,vectorRep v))=(matrixRep G,vectorRep (Counting.scaleUpdate hn G v i)) := by
  unfold step
  dsimp only
  rw [rowMax_rep hn G v hG hv i,set_vectorRep]
  rfl
lemma initial_rep (G : Fin n→Fin n→ℚ) : initial (matrixRep G)=(matrixRep G,vectorRep (fun _ : Fin n=>2)) := by
  unfold initial vectorRep
  rw [matrixRep_length]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rfl
lemma sweep_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ)
    (hsym : ∀ i j,G i j=G j i)
    (hG : ∀ i j,i≠j→ Counting.alpha≤G i j ∧ G i j≤3) (k : ℕ) (hk : k≤n) :
    (List.range k).foldl (fun s i=>step (i,s)) (initial (matrixRep G))=
      (matrixRep G,vectorRep (Counting.scalingTrace hn G k)) := by
  induction k with
  | zero=>exact initial_rep G
  | succ k ih=>
    rw [List.range_succ,List.foldl_append,ih (by omega)]
    simp only [List.foldl_cons,List.foldl_nil]
    have hp : ∀ j,0≤Counting.scalingTrace hn G k j := fun j=>
      ((Counting.scalingTrace_invariant hn G hsym hG k).1.pos j).le
    have hG' : ∀ i j,i≠j→0≤G i j := by
      intro i j hij
      exact (by norm_num [Counting.alpha] : (0:ℚ)≤Counting.alpha).trans (hG i j hij).1
    rw [step_rep hn G _ hG' hp (⟨k,by omega⟩ : Fin n)]
    congr 2
    simp only [Counting.scalingTrace,dite_eq_left (show k<n from by omega)]
lemma scale_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ)
    (hsym : ∀ i j,G i j=G j i)
    (hG : ∀ i j,i≠j→ Counting.alpha≤G i j ∧ G i j≤3) :
    scale (matrixRep G)=vectorRep (Counting.scalingTrace hn G n) := by
  unfold scale
  rw [matrixRep_length,sweep_rep hn G hsym hG n le_rfl]
end MatchingFPRAS.ExecutableScaling

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeProfile
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Polynomial

lemma profile_repr (fuel : List Bool) (B Hu Hv lam : ℚ)
    (hB : 0≤B) (hHu : 0≤Hu) (hHv : 0≤Hv) (_hlam : 0≤lam)
    (i : Fin (4*fuel.length+1)) :
    profile ((fuel,(TreeFraction.repr B,(TreeFraction.repr Hu,(TreeFraction.repr Hv,TreeFraction.repr lam)))),i.val)=
      TreeFraction.repr (RationalSource.profile fuel.length B Hu Hv lam i) := by
  unfold profile RationalSource.profile
  dsimp only
  split_ifs with h h'
  · have hi : i.val/2≤(fuel++fuel).length := by simp only [List.length_append]; omega
    rw [threshold_repr _ _ hi,div_repr hHu (by positivity),maximum_repr hB (by positivity)]
  · rfl
  · have hi : (4*fuel.length-i.val)/2≤(fuel++fuel).length := by simp only [List.length_append]; omega
    rw [threshold_repr _ _ hi,div_repr hHv (by positivity),maximum_repr hB (by positivity)]

lemma height_rep {n : ℕ} (hn : 2≤n) (B : Fin n→Fin n→ℚ) (hB : ∀ i j,0≤B i j) (i : Fin n) :
    height (matrixRep B,i.val)=TreeFraction.repr
      ((Finset.univ.erase i).sup' (Counting.others_nonempty hn i) (B i)) := by
  have he : (List.range (matrixRep B).length).map (fun i=>(i,((1,1) : Fraction)))=
      ExecutableScaling.vectorRep (fun _ : Fin n=>(1:ℚ)) := by
    rw [matrixRep_length]
    unfold ExecutableScaling.vectorRep
    rw [ExecutableDP.map_range_ofFn]
    rfl
  unfold height
  dsimp only
  rw [he,ExecutableScaling.rowMax_rep hn B (fun _=>1) (fun i j _=>hB i j) (by intro j; norm_num) i]
  simp only [Counting.rowMaximum,div_one]

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeWeights
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Polynomial Enlargement RealGeometry

lemma path_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : LogicalEdge (Fin n)) (i : Fin (4*fuel.length+1)) :
    path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),(logicalRepr e,i.val))=
      TreeFraction.repr (RationalSource.pathActivity w K e (Fin.cast (by rw [hf]) i)) := by
  have hB : ∀ a b,0≤RationalSource.logicalB w a b := by
    intro a b
    exact (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ a b)
  have hHt : ∀ a,0≤RationalSource.height w a := by
    intro a
    obtain ⟨b,hb⟩:=Counting.others_nonempty hn a
    exact (hB a b).trans (Finset.le_sup' _ hb)
  have hheight (a : Fin n) : height (matrixRep (RationalSource.logicalB w),a.val)=
      TreeFraction.repr (RationalSource.height w a) := by
    exact height_rep hn _ hB a
  rw [path,logicalRepr,cell_matrixRep,cell_matrixRep,hheight,hheight]
  rw [profile_repr fuel _ _ _ _ (hB _ _) (hHt _) (hHt _) (hw _ _) i]
  congr 1
  have he : BottleneckAlgorithm.edge w (source e) (target e)=w (source e) (target e) := by
    have hp : source e<target e := e.property
    simp only [BottleneckAlgorithm.edge,ite_eq_left hp]
  rw [RationalSource.pathActivity,he]
  simp only [RationalSource.profile,Fin.val_cast,hf,source,target]

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeWeightsCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

lemma logicalEdges_nodup {vs : List ℕ} (hv : vs.Nodup) : (logicalEdges vs).Nodup :=
  List.Nodup.filter _ (hv.product hv)
lemma realEdges_nodup {vs : List ℕ} (hv : vs.Nodup) (fuel : List Bool) :
    (realEdges (vs,fuel)).Nodup := (logicalEdges_nodup hv).product List.nodup_range
lemma realRepr_injective {n m : ℕ} : Function.Injective (realRepr (n:=n) (m:=m)) := by
  intro a b h
  exact Prod.ext (logicalRepr_injective (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

lemma realEdges_finset (n K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2) :
    (realEdges (List.range n,fuel)).toFinset=
      Finset.univ.image (realRepr (n:=n) (m:=4*(2*K+2))) := by
  ext e
  simp only [List.mem_toFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro he
    obtain ⟨⟨a,i⟩,hi⟩:=realEdges_complete fuel e he
    exact ⟨(a,Fin.cast (by rw [hf]) i),hi⟩
  · rintro ⟨⟨a,i⟩,rfl⟩
    exact realRepr_mem fuel (a,Fin.cast (by rw [hf]) i)

lemma sum_realEdges (n K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2) (f : RawReal→ℚ) :
    ((realEdges (List.range n,fuel)).map f).sum =
      ∑ e : SourceRealEdge (Fin n) K, f (realRepr e) := by
  rw [←List.sum_toFinset f (realEdges_nodup List.nodup_range fuel),realEdges_finset n K fuel hf]
  exact Finset.sum_image (fun a _ b _ h=>realRepr_injective h)

lemma path_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),realRepr e)=
      TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2) := by
  have h:=path_repr hn w hw K fuel hf e.1 (Fin.cast (by rw [hf]) e.2)
  simpa only [Fin.cast_cast,Fin.cast_refl,Fin.val_cast,realRepr,id] using h

lemma ends_source_repr {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    (left ((List.range n,fuel),realRepr e),right ((List.range n,fuel),realRepr e))=
    (vertexRepr (atVertex source target (4*(2*K+2)) e.1 e.2.castSucc),
     vertexRepr (atVertex source target (4*(2*K+2)) e.1 e.2.succ)) := by
  apply Prod.ext
  · unfold left internalCount
    dsimp only
    rw [hf]
    exact at_repr e.1 e.2.castSucc
  · unfold right internalCount
    dsimp only
    rw [hf]
    exact at_repr e.1 e.2.succ

lemma sameEnds_source {n : ℕ} (K : ℕ) (a b x y : SourceVertex (Fin n) K) :
    sameEnds ((vertexRepr x,vertexRepr y),(vertexRepr a,vertexRepr b))=
      decide (s(a,b)=s(x,y)) := by
  simp only [sameEnds,vertexRepr_injective.eq_iff]
  congr 1
  rw [Sym2.eq_iff]
  apply propext
  constructor
  · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · exact Or.inl ⟨h₁.symm,h₂.symm⟩
    · exact Or.inr ⟨h₂.symm,h₁.symm⟩
  · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · exact Or.inl ⟨h₁.symm,h₂.symm⟩
    · exact Or.inr ⟨h₂.symm,h₁.symm⟩

lemma contribution_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (x y : SourceVertex (Fin n) K) (e : SourceRealEdge (Fin n) K) :
    contribution ((vertexRepr x,vertexRepr y),
      pathRow ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),realRepr e))=
    TreeFraction.repr (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
      then RationalSource.pathActivity w K e.1 e.2 else 0) := by
  unfold contribution pathRow
  rw [path_source_repr hn w hw K fuel hf e,ends_source_repr K fuel hf e,
    sameEnds_source K]
  simp only [decide_eq_true_eq]
  change (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
       then TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2) else TreeFraction.repr (0:ℚ))=_
  split_ifs <;> rfl

lemma pathActivity_nonneg {n : ℕ} [Nontrivial (Fin n)] (_hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (e : LogicalEdge (Fin n)) (i : Fin (4*(2*K+2)+1)) :
    0≤RationalSource.pathActivity w K e i := by
  have hB : 0≤RationalSource.logicalB w (source e) (target e) :=
    (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ _ _)
  unfold RationalSource.pathActivity RationalSource.profile
  split_ifs
  · exact hB.trans (le_max_left _ _)
  · unfold BottleneckAlgorithm.edge
    split_ifs <;> exact hw _ _
  · exact hB.trans (le_max_left _ _)

lemma activity_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (x y : SourceVertex (Fin n) K) :
    activity (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),
      (vertexRepr x,vertexRepr y))=TreeFraction.repr (RationalSource.activity w K x y) := by
  let f : RawReal→ℚ := fun e=>
    if sameEnds ((vertexRepr x,vertexRepr y),
      (left ((List.range n,fuel),e),right ((List.range n,fuel),e))) then
        (path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),e)).1 /
          ((path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),e)).2 : ℚ)
      else 0
  let es:=realEdges (List.range n,fuel)
  let g : SourceRealEdge (Fin n) K→ℚ := fun e=>
    if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
      then RationalSource.pathActivity w K e.1 e.2 else 0
  have hg (e) : 0≤g e := by
    dsimp only [g]
    split_ifs
    · exact pathActivity_nonneg hn w hw K _ _
    · exact le_rfl
  have hre (e : SourceRealEdge (Fin n) K) : f (realRepr e)=g e := by
    dsimp only [f,g]
    rw [ends_source_repr K fuel hf e,sameEnds_source K,path_source_repr hn w hw K fuel hf e]
    simp only [decide_eq_true_eq]
    change (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
       then val (TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2)) else 0)=_
    split_ifs
    · exact val_repr (pathActivity_nonneg hn w hw K _ _)
    · rfl
  have hrow (e : RawReal) (he : e∈es) :
      contribution ((vertexRepr x,vertexRepr y),pathRow
        ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e))=
        TreeFraction.repr (f e) := by
    have hm : e∈(realEdges (List.range n,fuel)).toFinset:=List.mem_toFinset.mpr he
    rw [realEdges_finset n K fuel hf] at hm
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hm
    rw [hre]
    exact contribution_source_repr hn w hw K fuel hf x y a
  unfold activity pathTable
  rw [List.map_map]
  dsimp only [Function.comp,Prod.fst,Prod.snd]
  have hmap : (es.map fun e=>contribution ((vertexRepr x,vertexRepr y),pathRow
      ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e)))=
      (es.map f).map TreeFraction.repr := by
    rw [List.map_map]
    exact List.map_congr_left hrow
  change sum (es.map (fun e=>contribution ((vertexRepr x,vertexRepr y),pathRow
      ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e)))) = _
  rw [hmap,sum_repr]
  · congr 1
    rw [sum_realEdges n K fuel hf]
    exact Finset.sum_congr rfl (fun e _=>hre e)
  · intro q hq
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hq
    have hm : e∈(realEdges (List.range n,fuel)).toFinset:=List.mem_toFinset.mpr he
    rw [realEdges_finset n K fuel hf] at hm
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hm
    rw [hre]
    exact hg a
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMatrix
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

lemma activityMatrix_repr {N : ℕ} (vs : Fin N→RawVertex) (tab : List WeightedEdge)
    (w : Fin N→Fin N→ℚ) (hw : ∀ i j,activity (tab,(vs i,vs j))=TreeFraction.repr (w i j)) :
    activityMatrix (tab,List.ofFn vs)=matrixRep w := by
  unfold activityMatrix activityRow matrixRep
  simp only [List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  congr 1
  funext j
  exact hw i j

lemma activityMatrix_source_repr {n N : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (v : Fin N→SourceVertex (Fin n) K) :
    activityMatrix (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),
      List.ofFn (fun i=>vertexRepr (v i)))=
    matrixRep (fun i j=>RationalSource.activity w K (v i) (v j)) := by
  apply activityMatrix_repr
  intro i j
  exact activity_source_repr hn w hw K fuel hf (v i) (v j)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

lemma vertices_eq_ofFn_length (n : ℕ) (fuel : List Bool) (m : ℕ) (h : 4*fuel.length=m) :
    vertices (List.range n,fuel)=List.ofFn (fun i=>vertexRepr
      (UnitRefresh.orderedEnum (Vertex (Fin n) (LogicalEdge (Fin n)) m) i)) := by
  subst m
  exact vertices_eq_ofFn n fuel

lemma source_activity_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (a b : SourceVertex (Fin n) K) :
    0≤RationalSource.activity w K a b := by
  unfold RationalSource.activity
  apply Finset.sum_nonneg
  intro q _
  split_ifs
  · exact pathActivity_nonneg hn w hw K q.1 q.2
  · exact le_rfl

lemma buildMatrix_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    buildMatrix ((matrixRep w,List.replicate (2*K+2) false),List.range n)=
      matrixRep (fun i j=>RationalSource.activity w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)) := by
  unfold buildMatrix prepare materialize
  rw [close_matrixRep w hw]
  rw [show BottleneckAlgorithm.close w n=RationalSource.logicalB w by simp [RationalSource.logicalB]]
  change activityMatrix (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),
    List.replicate (2*K+2) false),List.range n),
    vertices (List.range n,List.replicate (2*K+2) false))=_
  have hv : vertices (List.range n,List.replicate (2*K+2) false)=
      List.ofFn (fun i=>vertexRepr (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)) := by
    exact vertices_eq_ofFn_length n _ _ (by simp)
  rw [hv]
  exact activityMatrix_source_repr hn w hw K _ (List.length_replicate ..) _

lemma buildClosure_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    buildClosure ((matrixRep w,List.replicate (2*K+2) false),List.range n)=
      matrixRep (fun i j=>RationalSource.realB w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)) := by
  unfold buildClosure
  rw [buildMatrix_repr hn w hw K,close_matrixRep _ (fun _ _=>source_activity_nonneg hn w hw K _ _)]
  rw [BottleneckAlgorithm.close_reindex (UnitRefresh.orderedEnum (SourceVertex (Fin n) K))
    UnitRefresh.orderedEnum_lt]
  rfl
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instBEqRawVertex
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLawfulBEqRawVertex
lemma index_vertices {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (v : SourceVertex (Fin n) K) : (vertices (List.range n,fuel)).idxOf (vertexRepr v)=index v := by
  rw [vertices_eq_ofFn_length n fuel _ (by rw [hf])]
  let e:=UnitRefresh.orderedEnum (SourceVertex (Fin n) K)
  let i:=e.symm v
  have hn : (List.ofFn (fun j=>vertexRepr (e j))).Nodup :=
    List.nodup_ofFn.mpr (vertexRepr_injective.comp e.injective)
  have hi : i.val<(List.ofFn (fun j=>vertexRepr (e j))).length := by simpa only [List.length_ofFn] using i.isLt
  have he:=@List.Nodup.idxOf_getElem RawVertex _ _ _ hn i.val hi
  simpa only [List.getElem_ofFn,Fin.eta,i,Equiv.apply_symm_apply,e,index] using he

lemma endpointEntry_source {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    endpointEntry (((List.range n,fuel),vertices (List.range n,fuel)),realRepr e)=
      (index (realLeft K e),index (realRight K e)) := by
  have h:=ends_source_repr K fuel hf e
  have hl:=congrArg Prod.fst h
  have hr:=congrArg Prod.snd h
  unfold endpointEntry
  dsimp only at hl hr ⊢
  rw [hl,hr,index_vertices K fuel hf,index_vertices K fuel hf]
  rfl

lemma endpointList_members {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (p : ℕ×ℕ) : p∈endpointList (List.range n,fuel) ↔
      ∃ e : SourceRealEdge (Fin n) K,(index (realLeft K e),index (realRight K e))=p := by
  have hm (e : RawReal) : e∈realEdges (List.range n,fuel) ↔
      ∃ a : SourceRealEdge (Fin n) K,realRepr a=e := by
    rw [←List.mem_toFinset,realEdges_finset n K fuel hf]
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
  simp only [endpointList,List.mem_map,hm]
  constructor
  · rintro ⟨e,⟨a,rfl⟩,hp⟩
    exact ⟨a,(endpointEntry_source K fuel hf a).symm.trans hp⟩
  · rintro ⟨e,he⟩
    exact ⟨realRepr e,⟨e,rfl⟩,(endpointEntry_source K fuel hf e).trans he⟩

lemma source_bagTable {n : ℕ} [Nontrivial (Fin n)]
    (w : Fin n→Fin n→ℚ) (K : ℕ) :
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>RationalSource.realB w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)),
        List.replicate (RationalSource.levels w K) false),
        endpointList (List.range n,List.replicate (2*K+2) false)))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags (RationalSource.bags w K))) := by
  exact arbitrary_bagTable_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (realLeft K) (realRight K)
    (endpointList (List.range n,List.replicate (2*K+2) false))
    (endpointList_members K _ (List.length_replicate ..))
    (RationalSource.levels w K) (List.length_replicate ..)
    (inferInstance : Fintype (RationalSource.Label w K))

lemma buildBags_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    List.Forall₂ List.Perm
      (buildBags (((matrixRep w,List.replicate (2*K+2) false),List.range n),
        List.replicate (RationalSource.levels w K) false))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags (RationalSource.bags w K))) := by
  unfold buildBags
  rw [buildClosure_repr hn w hw K]
  exact source_bagTable w K

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

lemma logicalB_nonneg {n : ℕ} (w : Fin n→Fin n→ℚ) (a b : Fin n) :
    0≤RationalSource.logicalB w a b :=
  (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ a b)
lemma sourceHeight_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (a : Fin n) : 0≤RationalSource.height w a := by
  obtain ⟨b,hb⟩:=Counting.others_nonempty hn a
  exact (logicalB_nonneg w a b).trans (Finset.le_sup' _ hb)
lemma sourceMaxHeight_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) : 0≤RationalSource.maxHeight w := by
  exact (sourceHeight_nonneg hn w ⟨0,by omega⟩).trans (Finset.le_sup' _ (Finset.mem_univ _))

lemma maxHeight_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    maxHeight (close (matrixRep w))=TreeFraction.repr (RationalSource.maxHeight w) := by
  rw [close_matrixRep w hw]
  have hc : BottleneckAlgorithm.close w n=RationalSource.logicalB w := by
    simp only [RationalSource.logicalB,Fintype.card_fin]
  rw [hc]
  unfold maxHeight
  have he : (List.range (matrixRep (RationalSource.logicalB w)).length).map
      (fun i=>height (matrixRep (RationalSource.logicalB w),i))=
      (List.ofFn (RationalSource.height w)).map TreeFraction.repr := by
    rw [matrixRep_length,ExecutableDP.map_range_ofFn,List.map_ofFn]
    congr 1
    funext i
    exact height_rep hn _ (logicalB_nonneg w) i
  rw [he]
  change ((List.ofFn (RationalSource.height w)).map TreeFraction.repr).foldl _ (TreeFraction.repr 0)=_
  rw [maximum_fold_repr _ 0 le_rfl (by
    intro x hx
    obtain ⟨a,rfl⟩:=List.mem_ofFn.mp hx
    exact sourceHeight_nonneg hn w a)]
  rw [fold_max_ofFn _ 0 ⟨0,by omega⟩]
  congr 1
  exact max_eq_right (sourceMaxHeight_nonneg hn w)

lemma hierarchyFuel_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    hierarchyFuel (matrixRep w,List.replicate (2*K) false)=
      List.replicate (RationalSource.levels w K) false := by
  unfold hierarchyFuel
  dsimp only
  rw [maxHeight_source hn w hw,List.length_replicate,level_repr _ _ (sourceMaxHeight_nonneg hn w)]
  rw [List.take_replicate]
  congr 1
  exact min_eq_left (Nat.findGreatest_le _)

attribute [local instance] NumberedHierarchy.labelOrder
lemma setupBags_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    List.Forall₂ List.Perm
      (setupBags (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags (RationalSource.bags w K))) := by
  unfold setupBags
  dsimp only
  rw [hierarchyFuel_source hn w hw K]
  exact buildBags_source hn w hw K

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceTables_catalog {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    (sourceTables (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)).1=
      sourceCatalog (RationalSource.bags w K) := by
  rw [sourceTables,refreshTables,setupHierarchy,
    buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  dsimp only
  rw [arbitrary_labelIndices_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (List.replicate (RationalSource.levels w K) false) (RationalSource.levels w K)
    (List.length_replicate ..) (inferInstance : Fintype (RationalSource.Label w K))]
  have catalog := storedCatalog_source (bags:=RationalSource.bags w K) _ (source_bagTable w K)
  exact catalog

lemma sourceRealKey_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : SourceRealEdge (Fin n) K) :
    sourceRealKey ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),realRepr e)=
      sourceKey (RationalSource.coloredReal w K e) := by
  unfold sourceRealKey setupHierarchy coloredKey
  dsimp only
  rw [buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K,
    endpointEntry_source K _ (List.length_replicate ..) e]
  dsimp only
  rw [arbitrary_edgeIndex_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (realLeft K) (realRight K)
    (RationalSource.levels w K) (List.length_replicate ..)
    (inferInstance : Fintype (RationalSource.Label w K)) e]
  exact (sourceKey_mk (RationalSource.coloredReal w K e) (realLeft K e) (realRight K e)
    (RationalSource.realLabel w K e) rfl).symm

lemma sourceRealIndex_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : SourceRealEdge (Fin n) K) :
    sourceRealIndex ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),realRepr e)=
      index (RationalSource.coloredReal w K e) := by
  unfold sourceRealIndex
  rw [sourceTables_catalog hn w hw K,sourceRealKey_source hn w hw K,sourceCatalog_index]

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePortion
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma coloredRow_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (a : SourceRealEdge (Fin n) K) :
    coloredRow ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),realRepr a)=
      (sourceKey (RationalSource.coloredReal w K a),TreeFraction.repr (RationalSource.pathActivity w K a.1 a.2)) := by
  unfold coloredRow
  rw [sourceRealKey_source hn w hw K]
  unfold prepare
  dsimp only
  rw [close_matrixRep w hw,show BottleneckAlgorithm.close w n=RationalSource.logicalB w by simp [RationalSource.logicalB]]
  rw [path_source_repr hn w hw K _ (List.length_replicate ..)]

lemma realPart_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    realPart ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),sourceKey e)=
      TreeFraction.repr (RationalSource.realPortion w K e) := by
  let x : BagBuildInput:=(((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)
  let es:=realEdges (List.range n,List.replicate (2*K+2) false)
  let f : RawReal→ℚ:=fun a=>if sourceRealKey (x,a)=sourceKey e then
    val (path ((prepare x.1).1,a)) else 0
  let g : SourceRealEdge (Fin n) K→ℚ:=fun a=>if RationalSource.coloredReal w K a=e then
    RationalSource.pathActivity w K a.1 a.2 else 0
  have hg (a) : 0≤g a := by
    dsimp only [g]
    split_ifs <;> first | exact pathActivity_nonneg hn w hw K _ _ | exact le_rfl
  have hrow (a : SourceRealEdge (Fin n) K) :
      colorContribution (sourceKey e,coloredRow (x,realRepr a))=TreeFraction.repr (g a) := by
    rw [coloredRow_source hn w hw K]
    simp only [colorContribution,sourceKey_injective.eq_iff]
    dsimp only [g]
    by_cases h : RationalSource.coloredReal w K a=e
    · simp only [h,ite_true]
    · simp only [h,Ne.symm h,ite_false]
      rfl
  have hf (a : SourceRealEdge (Fin n) K) : f (realRepr a)=g a := by
    have h:=coloredRow_source hn w hw K a
    have hp:=congrArg Prod.snd h
    change path ((prepare x.1).1,realRepr a)=_ at hp
    have hk:=congrArg Prod.fst h
    change sourceRealKey (x,realRepr a)=sourceKey (RationalSource.coloredReal w K a) at hk
    dsimp only [f,g]
    simp only [hk,sourceKey_injective.eq_iff,hp,val_repr (pathActivity_nonneg hn w hw K _ _)]
  have hmap : (es.map fun a=>colorContribution (sourceKey e,coloredRow (x,a)))=
      (es.map f).map TreeFraction.repr := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    have hm : a∈(realEdges (List.range n,List.replicate (2*K+2) false)).toFinset:=List.mem_toFinset.mpr ha
    rw [realEdges_finset n K _ (List.length_replicate ..)] at hm
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hm
    simpa only [Function.comp_apply,hf] using hrow b
  unfold realPart coloredRows
  rw [List.map_map]
  change sum (es.map (fun a=>colorContribution (sourceKey e,coloredRow (x,a))))=_
  rw [hmap,sum_repr]
  · congr 1
    rw [sum_realEdges n K _ (List.length_replicate ..)]
    exact Finset.sum_congr rfl (fun a _=>hf a)
  · intro q hq
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
    have hm : a∈(realEdges (List.range n,List.replicate (2*K+2) false)).toFinset:=List.mem_toFinset.mpr ha
    rw [realEdges_finset n K _ (List.length_replicate ..)] at hm
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hm
    rw [hf]
    exact hg b
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePhantom
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
variable {V : Type} [Fintype V] [LinearOrder V]
lemma arbitrary_ranks_fintype (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (xs : List Bool) (H : ℕ) (hH : xs.length=H) (F : Fintype (Label B H)) :
    letI := F
    ranks (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs)=
      List.ofFn (UnitRefresh.numberedRank (fun a : Label B H=>a.1.val)) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_ranks B hB xs
end MatchingFPRAS.ExecutableHierarchy

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceRanks_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceRanks (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      List.ofFn (UnitRefresh.numberedRank (fun a : RationalSource.Label w K=>a.1.val)) := by
  unfold sourceRanks setupHierarchy
  dsimp only
  rw [buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  exact arbitrary_ranks_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (List.replicate (RationalSource.levels w K) false) (RationalSource.levels w K)
    (List.length_replicate ..) (inferInstance : Fintype (RationalSource.Label w K))

lemma rankLookup {L : Type} [Fintype L] [LinearOrder L] (rank : L→ℕ) (l : L) :
    (List.ofFn (UnitRefresh.numberedRank rank)).getD (index l) 0=rank l := by
  simp only [UnitRefresh.numberedRank,index,List.getD,List.getElem?_ofFn,
    ((UnitRefresh.orderedEnum L).symm l).isLt,↓reduceDIte,Fin.eta,Option.getD_some,Equiv.apply_symm_apply]

lemma sourceRank_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceRank ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),sourceKey e)=
      e.color.1.val := by
  unfold sourceRank
  dsimp only
  rw [sourceRanks_source hn w hw K]
  exact rankLookup _ _

lemma phantomHeight_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    phantomHeight ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),sourceKey e)=
      TreeFraction.repr (RationalSource.bagHeight w K e.color) := by
  unfold phantomHeight
  dsimp only
  rw [sourceRank_source hn w hw K]
  apply threshold_repr
  rw [List.length_replicate]
  have h:=e.color.1.isLt
  have hh : RationalSource.levels w K≤2*K:=Nat.findGreatest_le _
  omega

lemma sourceBagWeight_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K D : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceBagWeight (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      TreeFraction.repr (RationalSource.bagWeight w K D e) := by
  unfold sourceBagWeight
  dsimp only
  rw [realPart_source hn w hw K,phantomHeight_source hn w hw K]
  have hreal : 0≤RationalSource.realPortion w K e := by
    unfold RationalSource.realPortion
    apply Finset.sum_nonneg
    intro a _
    split_ifs <;> first | exact pathActivity_nonneg hn w hw K _ _ | exact le_rfl
  have hh : 0≤RationalSource.bagHeight w K e.color := by unfold RationalSource.bagHeight; positivity
  have hD : ((D,1) : Fraction)=TreeFraction.repr (D:ℚ) := by simp [TreeFraction.repr]
  rw [hD,div_repr hh (Nat.cast_nonneg D),add_repr hreal (div_nonneg hh (Nat.cast_nonneg D))]
  rfl

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
variable {V : Type} [Fintype V] [LinearOrder V]
lemma arbitrary_parents_fintype (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (H : ℕ) (hH : xs.length=H) (F : Fintype (Label B H)) :
    letI := F
    parents (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent (NumberedHierarchy.parent B hsym htri (H:=H))) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_parents B hB hsym htri xs
end MatchingFPRAS.ExecutableHierarchy

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceParents_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceParents (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent (RationalSource.parent w K)) := by
  unfold sourceParents setupHierarchy
  dsimp only
  rw [buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  exact arbitrary_parents_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (RationalSource.levels w K)
    (List.length_replicate ..) (inferInstance : Fintype (RationalSource.Label w K))

lemma sourceTables_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    let x : BagBuildInput:=(((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)
    sourceTables x=(sourceCatalog (RationalSource.bags w K),
      ((setupBags x,ExecutableDP.parentRep (UnitRefresh.numberedParent (RationalSource.parent w K))),
        (UnitRefresh.Materialized.plan (UnitRefresh.numberedRank
          (fun l : RationalSource.Label w K=>l.1.val))).map Fin.val)) := by
  dsimp only
  apply Prod.ext
  · exact sourceTables_catalog hn w hw K
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact sourceParents_source hn w hw K
  change rankPlan (sourceRanks _)=_
  rw [sourceRanks_source hn w hw K,rankPlan_eq]
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeWeightTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceWeights_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K D : ℕ) :
    sourceWeights ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D)=
      List.ofFn (fun i=>TreeFraction.repr (RationalSource.bagWeight w K D
        (UnitRefresh.orderedEnum (Transport.BagEdge (RationalSource.bags w K)) i))) := by
  unfold sourceWeights
  dsimp only
  rw [sourceTables_catalog hn w hw K]
  unfold sourceCatalog
  rw [List.map_ofFn]
  congr 1
  funext i
  exact sourceBagWeight_source hn w hw K D _

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedPrepared
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma range_card_set (A : Type) [Fintype A] [LinearOrder A] :
    Finset.range (Fintype.card A)=Numbered.set (Finset.univ : Finset A) := by
  ext i
  simp only [Finset.mem_range,Numbered.set,Finset.mem_map,Finset.mem_univ,true_and,Numbered.embedding]
  constructor
  · intro h
    exact ⟨UnitRefresh.orderedEnum A ⟨i,h⟩,index_orderedEnum _⟩
  · rintro ⟨a,rfl⟩
    exact ((UnitRefresh.orderedEnum A).symm a).isLt

lemma sourceVertices_length {n : ℕ} (w : Fin n→Fin n→ℚ) (K : ℕ) :
    (sourceVertices (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)).length=
      Fintype.card (SourceVertex (Fin n) K) := by
  unfold sourceVertices
  dsimp only
  rw [vertices_eq_ofFn_length n _ (4*(2*K+2)) (by simp),List.length_ofFn]

lemma sourceCatalog_endpoints {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
    (bags : V→Finset L) : (sourceCatalog bags).map Prod.fst=
      List.ofFn (fun e=>ExecutablePair.endpointRep (UnitRefresh.orderedEnum (Transport.BagEdge bags) e).val.val.1) := by
  unfold sourceCatalog
  rw [List.map_ofFn]
  rfl
lemma sourceEdgeData_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceEdgeData (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      (List.ofFn (fun e=>ExecutablePair.endpointRep
        (UnitRefresh.orderedEnum (Transport.BagEdge (RationalSource.bags w K)) e).val.val.1),
       (Numbered.set (Finset.univ : Finset (SourceVertex (Fin n) K)),
        Numbered.set (Finset.univ : Finset (Transport.BagEdge (RationalSource.bags w K))))) := by
  unfold sourceEdgeData
  rw [sourceTables_catalog hn w hw K,sourceCatalog_endpoints]
  apply Prod.ext
  · rfl
  unfold rangeFromList
  rw [sourceVertices_length,List.toFinset_range,range_card_set]
  unfold sourceCatalog
  rw [List.length_ofFn,List.toFinset_range,range_card_set]

lemma generatedPrepared_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K D : ℕ) (ft fq : List Bool) :
    let x : BagBuildInput:=(((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)
    generatedPrepared ((x,D),(ft,fq))=
      sourcePrepared (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
        (RationalSource.bagWeight w K D) (setupBags x) ft fq := by
  dsimp only
  unfold generatedPrepared generatedTier
  dsimp only
  rw [sourceVertices_length,sourceWeights_source hn w hw K D,sourceEdgeData_source hn w hw K,
    sourceTables_source hn w hw K]
  unfold sourcePrepared
  rw [storedCatalog_source _ (setupBags_source hn w hw K)]

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeStart
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma mateIndex_source {n : ℕ} (he : Even n) (i : Fin n) :
    mateIndex i.val=(RationalSource.pairIndex he i).val := by
  simp only [mateIndex,RationalSource.pairIndex]
  split_ifs <;> rfl

lemma startSelected_source {n : ℕ} (K : ℕ) (he : Even n) (e : SourceRealEdge (Fin n) K) :
    startSelected (realRepr e)=Subdivision.alternating
      (RationalSource.selectMate (RationalSource.orderedMate he) e.1) e.2.val := by
  unfold startSelected realRepr logicalRepr
  rw [mateIndex_source he]
  congr 1
  change decide ((RationalSource.pairIndex he _).val=_)=decide (RationalSource.pairIndex he _=_)
  congr 1
  exact propext Fin.val_inj

lemma numbered_map_image {A B : Type} [Fintype A] [LinearOrder A] [DecidableEq B]
    (f : B↪A) (s : Finset B) : Numbered.set (s.map f)=s.image (fun b=>index (f b)) := by
  unfold Numbered.set
  rw [Finset.map_map]
  exact Finset.map_eq_image _ _

lemma startMatching_set {n : ℕ} [Nontrivial (Fin n)] (w : Fin n→Fin n→ℚ)
    (K : ℕ) (he : Even n) :
    Numbered.set (RationalSource.startMatching w K he).val=
      (RationalSource.startSet K he).image (fun a=>index (RationalSource.coloredReal w K a)) :=
  numbered_map_image _ _

lemma exactStart_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (he : Even n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    exactStart (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      Numbered.set (RationalSource.startMatching w K he).val := by
  rw [startMatching_set]
  ext i
  change i∈(((realEdges (List.range n,List.replicate (2*K+2) false)).filter startSelected).map
    (fun e=>sourceRealIndex ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),e))).toFinset ↔ _
  simp only [List.mem_toFinset,List.mem_map,List.mem_filter,Finset.mem_image,
    RationalSource.startSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,⟨he',hsel⟩,hi⟩
    have hre : e∈(realEdges (List.range n,List.replicate (2*K+2) false)).toFinset:=List.mem_toFinset.mpr he'
    rw [realEdges_finset n K _ (List.length_replicate ..)] at hre
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hre
    refine ⟨a,?_,?_⟩
    · exact (startSelected_source K he a).symm.trans hsel
    · exact (sourceRealIndex_source hn w hw K a).symm.trans hi
  · rintro ⟨a,ha,hai⟩
    refine ⟨realRepr a,⟨?_,?_⟩,?_⟩
    · apply List.mem_toFinset.mp
      rw [realEdges_finset n K _ (List.length_replicate ..)]
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    · exact (startSelected_source K he a).trans ha
    · exact (sourceRealIndex_source hn w hw K a).trans hai

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma bagWeight_nonneg {n : ℕ} [Nontrivial (Fin n)]
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ)
    (e : BagEdge (RationalSource.bags w K)) : 0≤RationalSource.bagWeight w K D e :=
  add_nonneg (RationalSource.realPortion_nonneg w hw K e)
    (div_nonneg (by unfold RationalSource.bagHeight; positivity) (Nat.cast_nonneg D))

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeProbe
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma centralKey_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : LogicalEdge (Fin n)) :
    centralKey ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),logicalRepr e)=
      sourceKey (RationalSource.centralEdge w K e) := by
  unfold centralKey
  dsimp only
  rw [List.length_replicate]
  exact sourceRealKey_source hn w hw K (e,⟨2*(2*K+2),by omega⟩)

lemma mem_centralKeys {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceKey e∈centralKeys (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false) ↔
      ∃ q,RationalSource.centralEdge w K q=e := by
  unfold centralKeys
  rw [List.mem_map]
  constructor
  · rintro ⟨q,hq,he⟩
    obtain ⟨a,rfl⟩:=logicalEdges_complete q hq
    rw [centralKey_source hn w hw K] at he
    exact ⟨a,sourceKey_injective he⟩
  · rintro ⟨q,rfl⟩
    exact ⟨logicalRepr q,logicalRepr_mem q,centralKey_source hn w hw K q⟩

lemma probePart_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K D : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    probePart (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      TreeFraction.repr (RationalSource.probePortion w K D e) := by
  unfold probePart isCentral
  dsimp only
  simp only [decide_eq_true_eq,RationalSource.probePortion]
  simp only [mem_centralKeys hn w hw K]
  split_ifs
  · have hD : ((D,1) : Fraction)=TreeFraction.repr (D:ℚ) := by simp [TreeFraction.repr]
    rw [hD]
    exact div_repr (by decide : (0:ℚ)≤1) (Nat.cast_nonneg D)
  · rfl
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMarkTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry ExecutableOptions

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma markPortions_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0<w i j) (K D : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    markPortions (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      (TreeFraction.repr (RationalSource.portions w K D e 0),
       (TreeFraction.repr (RationalSource.portions w K D e 1),TreeFraction.repr (RationalSource.portions w K D e 2))) := by
  have hnon:=fun a b=>(hw a b).le
  have hheight : 0≤RationalSource.bagHeight w K e.color := by
    unfold RationalSource.bagHeight
    positivity
  have hD : ((D,1) : Fraction)=TreeFraction.repr (D:ℚ) := by simp [TreeFraction.repr]
  have hp : 0≤RationalSource.probePortion w K D e := RationalSource.portions_nonneg w hw K D e 2
  have hsub : RationalSource.probePortion w K D e≤RationalSource.bagHeight w K e.color/D :=
    sub_nonneg.mp (RationalSource.portions_nonneg w hw K D e 1)
  unfold markPortions phantomPart
  dsimp only
  rw [realPart_source hn w hnon K,phantomHeight_source hn w hnon K,
    probePart_source hn w hnon K D,hD,div_repr hheight (Nat.cast_nonneg D),
    sub_repr (div_nonneg hheight (Nat.cast_nonneg D)) hp hsub]
  rfl

lemma sourceMarkRow_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceMarkRow (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      ExecutableOptions.repr Fin.val (RationalSource.markingTable w hw K D hD e) := by
  unfold sourceMarkRow
  rw [markPortions_source hn w hw K D,sourceBagWeight_source hn w (fun a b=>(hw a b).le) K D]
  have hp:=RationalSource.portions_nonneg w hw K D e
  have hb:=(RationalSource.bagWeight_pos w hw K D hD e).le
  simp only [threeOptions,List.map_cons,List.map_nil,div_repr (hp _) hb]
  simp only [ExecutableOptions.repr,RationalSource.markingTable,List.ofFn_succ,List.ofFn_zero]
  rfl

lemma sourceMarks_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D) :
    sourceMarks ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D)=
      NumericMarking.tableRep (RationalSource.markingTable w hw K D hD) := by
  unfold sourceMarks
  dsimp only
  rw [sourceTables_catalog hn w (fun a b=>(hw a b).le) K]
  unfold sourceCatalog NumericMarking.tableRep
  rw [List.map_ofFn]
  congr 1
  funext i
  exact sourceMarkRow_source hn w hw K D hD _

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma generatedMarked_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (he : Even n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    generatedMarked
      ((((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)),
       (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
         (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map (fun e=>(index e,List.ofFn (mb e)))))=
      numericMarks (ladderRun (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
        (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
        (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
        (RationalSource.parent_rank w K) hq (RationalSource.bagWeight w K D)
        (RationalSource.startMatching w K he) k r (fun _=>RationalSource.startMatching w K he) bits
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val
          (fun e=>(RationalSource.markingTable w hw K D hD e).draw km (mb e)) := by
  unfold generatedMarked generatedContext
  dsimp only
  rw [generatedPrepared_source hn w (fun a b=>(hw a b).le) K D ft fq,
    exactStart_source hn he w (fun a b=>(hw a b).le) K,
    sourceMarks_source hn w hw K D hD]
  exact sample_source (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
    (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
    (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
    (RationalSource.parent_rank w K) ft fq hq (RationalSource.bagWeight w K D)
    (bagWeight_nonneg w hw K D) (RationalSource.startMatching w K he) _
    (setupBags_source hn w (fun a b=>(hw a b).le) K) _ bits mb

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeObservablesCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped TreeFraction

variable {C E : Type} [LinearOrder E]

lemma zeroMarks_rep (s : Finset E) (m : E→Fin 3) :
    zeroMarks (marksRep s m)=true ↔ ∀ e∈s,m e=0 := by
  simp only [zeroMarks,marksRep,List.all_map,List.all_eq_true,Function.comp_apply,
    decide_eq_true_eq,Finset.mem_sort]
  constructor
  · intro h e he; exact Fin.ext (h e he)
  · intro h e he; exact congrArg Fin.val (h e he)

lemma probeFlag_rep (s : Finset E) (m : E→Fin 3) (e : E) :
    probeFlag (e,marksRep s m)=true ↔ e∈s ∧ ∀ a∈s,m a=if a=e then 2 else 0 := by
  simp only [probeFlag,marksRep,Bool.and_eq_true,List.any_map,List.all_map,List.any_eq_true,
    List.all_eq_true,Function.comp_def,probeExpected]
  constructor
  · rintro ⟨⟨a,ha,hae⟩,h⟩
    have hae' : a=e := of_decide_eq_true hae
    subst a
    refine ⟨(Finset.mem_sort (·≤·)).mp ha,fun b hb=>Fin.ext ?_⟩
    have hh:=of_decide_eq_true (h b ((Finset.mem_sort (·≤·)).mpr hb))
    by_cases hbe : b=e <;> simp [hbe] at hh ⊢ <;> exact hh
  · rintro ⟨he,h⟩
    refine ⟨⟨e,(Finset.mem_sort (·≤·)).mpr he,by simp⟩,fun b hb=>?_⟩
    apply decide_eq_true
    have hh:=congrArg Fin.val (h b ((Finset.mem_sort (·≤·)).mp hb))
    by_cases hbe : b=e <;> simp [hbe] at hh ⊢ <;> exact hh

lemma weighted_rep (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0 ≤ r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e))
    (s : Finset E) (m : E→Fin 3) :
    weighted q (c,marksRep s m)=TreeFraction.repr (∏ e∈s,r e) := by
  unfold weighted marksRep
  simp only [List.map_map]
  exact TreeTyped.SparseProgram.weight_repr q c r hr hq s

lemma eraseMark_rep (s : Finset E) (m : E→Fin 3) (e : E) :
    eraseMark (e,marksRep s m)=marksRep (s\{e}) m := by
  unfold eraseMark marksRep
  simp only [List.filter_map]
  congr 1
  apply List.Pairwise.eq_of_mem_iff (s.sortedLT_sort.pairwise.filter _) (Finset.sortedLT_sort _).pairwise
  intro a
  simp

lemma observableA_rep (s : Finset E) (m : E→Fin 3) :
    observableA (marksRep s m)=TreeFraction.repr (if ∀ e∈s,m e=0 then (1:ℚ) else 0) := by
  unfold observableA
  simp only [zeroMarks_rep]
  split_ifs <;> rfl
lemma observableD_rep (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0 ≤ r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e))
    (s : Finset E) (m : E→Fin 3) :
    observableD q (c,marksRep s m)=
      TreeFraction.repr (if ∀ e∈s,m e=0 then ∏ e∈s,r e else 0) := by
  unfold observableD
  simp only [zeroMarks_rep]
  split_ifs
  · exact weighted_rep q c r hr hq s m
  · rfl
lemma observableProbe_rep (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0 ≤ r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e))
    (s : Finset E) (m : E→Fin 3) (e : E) :
    observableProbe q (c,(e,marksRep s m))=
      TreeFraction.repr (if e∈s ∧ ∀ a∈s,m a=if a=e then 2 else 0 then ∏ a∈s\{e},r a else 0) := by
  unfold observableProbe
  simp only [probeFlag_rep]
  split_ifs
  · rw [eraseMark_rep]
    exact weighted_rep q c r hr hq _ m
  · rfl
end MatchingFPRAS.ExecutableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageStatisticsCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableEstimator
open TreeFraction

lemma mean_ofFn {S : ℕ} (f : Fin S→ℚ) (hf : ∀ i,0≤f i) :
    mean (List.ofFn (fun i=>TreeFraction.repr (f i)))=TreeFraction.repr ((∑ i,f i)/(S:ℚ)) := by
  have he : List.ofFn (fun i=>TreeFraction.repr (f i))=(List.ofFn f).map TreeFraction.repr :=
    by rw [List.map_ofFn]; rfl
  rw [he,mean_rep _ (by intro a ha; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha; exact hf i)]
  simp only [List.sum_ofFn,List.length_ofFn]
end MatchingFPRAS.ExecutableEstimator

namespace MatchingFPRAS.ExecutableStatistics
open TreeTyped TreeFraction ExecutableMarking ExecutableEstimator

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]
variable {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3)
omit [Codec C] [Codec E] [Inhabited E] [LinearOrder E] in
lemma scalarA_nonneg [LinearOrder E] (i : Fin S) : 0 ≤ scalarA s m i := by unfold scalarA; split_ifs <;> norm_num
omit [Codec C] [Codec E] [Inhabited E] [LinearOrder E] in
lemma scalarD_nonneg [LinearOrder E] (r : E→ℚ) (hr : ∀ e,0 ≤ r e) (i : Fin S) : 0 ≤ scalarD s m r i := by
  unfold scalarD; split_ifs; exact Finset.prod_nonneg (fun e _=>hr e); exact le_rfl
omit [Codec C] [Codec E] [Inhabited E] in
lemma scalarProbe_nonneg (r : E→ℚ) (hr : ∀ e,0 ≤ r e) (e : E) (i : Fin S) :
    0 ≤ scalarProbe s m r e i := by
  unfold scalarProbe; split_ifs; exact Finset.prod_nonneg (fun a _=>hr a); exact le_rfl

omit [Codec E] [Inhabited E] in
lemma averageA_rep [Codec E] [Inhabited E] :
    averageA (sampleRep s m)=TreeFraction.repr ((∑ i,scalarA s m i)/(S:ℚ)) := by
  unfold averageA sampleRep
  rw [List.map_ofFn]
  simp only [Function.comp_def,observableA_rep]
  exact mean_ofFn (scalarA s m) (scalarA_nonneg s m)
omit [Codec C] [Codec E] [Inhabited E] in
lemma averageD_rep [Codec C] [Codec E] [Inhabited E] (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0 ≤ r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e)) :
    averageD q (c,sampleRep s m)=TreeFraction.repr ((∑ i,scalarD s m r i)/(S:ℚ)) := by
  unfold averageD sampleRep
  dsimp only
  rw [List.map_ofFn]
  simp only [Function.comp_def,observableD_rep q c r hr hq]
  exact mean_ofFn (scalarD s m r) (scalarD_nonneg s m r hr)
omit [Codec C] [Codec E] [Inhabited E] in
lemma averageProbe_rep [Codec C] [Codec E] [Inhabited E] (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0 ≤ r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e)) (e : E) :
    averageProbe q ((c,e),sampleRep s m)=TreeFraction.repr ((∑ i,scalarProbe s m r e i)/(S:ℚ)) := by
  unfold averageProbe sampleRep
  dsimp only
  rw [List.map_ofFn]
  simp only [Function.comp_def,observableProbe_rep q c r hr hq]
  exact mean_ofFn (scalarProbe s m r e) (scalarProbe_nonneg s m r hr e)

end MatchingFPRAS.ExecutableStatistics

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericStatistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {E A : Type} [Fintype E] [LinearOrder E]
lemma extend_index (d : A) (f : E→A) (e : E) : extend d f (index e)=f e := by
  unfold extend index
  rw [dite_eq_left ((UnitRefresh.orderedEnum E).symm e).isLt]
  exact congrArg f ((UnitRefresh.orderedEnum E).apply_symm_apply e)
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics

variable {E : Type} [Fintype E] [LinearOrder E]
lemma numericMarks_eq (s : Finset E) (m : E→Fin 3) :
    numericMarks s m=marksRep (Numbered.set s) (extend 0 m) := by
  simp only [numericMarks,marksRep,sort_set,List.map_map,Function.comp_def,extend_index]

lemma zero_numbered (s : Finset E) (m : E→Fin 3) :
    (∀ a∈Numbered.set s,extend 0 m a=0) ↔ ∀ e∈s,m e=0 := by
  constructor
  · intro h e he
    have hh:=h (index e) (Finset.mem_map.mpr ⟨e,he,rfl⟩)
    simpa only [extend_index] using hh
  · intro h a ha
    obtain ⟨e,he,rfl⟩:=Finset.mem_map.mp ha
    exact (extend_index 0 m e).trans (h e he)
lemma scalarA_numbered {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3) (i : Fin S) :
    scalarA (fun j=>Numbered.set (s j)) (fun j=>extend 0 (m j)) i=scalarA s m i := by
  by_cases h : ∀ e∈s i,m i e=0
  · have hh := (zero_numbered (s i) (m i)).mpr h
    simp only [scalarA,ite_eq_left h,ite_eq_left hh]
  · have hh : ¬∀e∈Numbered.set (s i),extend 0 (m i) e=0 := fun hh=>h ((zero_numbered _ _).mp hh)
    simp only [scalarA,ite_eq_right h,ite_eq_right hh]

lemma scalarD_numbered {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3) (r : E→ℚ) (i : Fin S) :
    scalarD (fun j=>Numbered.set (s j)) (fun j=>extend 0 (m j)) (extend 1 r) i=scalarD s m r i := by
  by_cases h : ∀ e∈s i,m i e=0
  · have hh := (zero_numbered (s i) (m i)).mpr h
    simp only [scalarD,ite_eq_left h,ite_eq_left hh]
    simp only [Numbered.set,Finset.prod_map,Numbered.embedding,Function.Embedding.coeFn_mk,extend_index]
  · have hh : ¬∀e∈Numbered.set (s i),extend 0 (m i) e=0 := fun hh=>h ((zero_numbered _ _).mp hh)
    simp only [scalarD,ite_eq_right h,ite_eq_right hh]

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericStatisticsCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics ExecutableLadder UnitRefresh

variable {E : Type} [Fintype E] [LinearOrder E]
lemma probe_numbered (s : Finset E) (m : E→Fin 3) (e : E) :
    (index e∈Numbered.set s ∧ ∀ a∈Numbered.set s,extend 0 m a=if a=index e then 2 else 0) ↔
    (e∈s ∧ ∀ a∈s,m a=if a=e then 2 else 0) := by
  have hm : index e∈Numbered.set s ↔ e∈s := by
    simp only [Numbered.set,Finset.mem_map,Numbered.embedding,Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a,ha,he⟩
      exact index_injective he ▸ ha
    · intro h; exact ⟨e,h,rfl⟩
  rw [hm]
  apply and_congr_right
  intro _he
  constructor
  · intro h a ha
    have hh:=h (index a) (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
    simpa only [extend_index,index_injective.eq_iff] using hh
  · intro h a ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp ha
    simpa only [Numbered.embedding,Function.Embedding.coeFn_mk,extend_index,index_injective.eq_iff] using h b hb

lemma scalarProbe_numbered {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3)
    (r : E→ℚ) (e : E) (i : Fin S) :
    scalarProbe (fun j=>Numbered.set (s j)) (fun j=>extend 0 (m j)) (extend 1 r) (index e) i=
      scalarProbe s m r e i := by
  by_cases h : e∈s i ∧ ∀ a∈s i,m i a=if a=e then 2 else 0
  · have hh:=(probe_numbered (s i) (m i) e).mpr h
    simp only [scalarProbe,ite_eq_left h,ite_eq_left hh]
    have hs : Numbered.set (s i)\{index e}=Numbered.set (s i\{e}) := by
      simp only [Numbered.set,Finset.map_sdiff,Finset.map_singleton,Numbered.embedding,
        Function.Embedding.coeFn_mk]
    rw [hs]
    simp only [Numbered.set,Finset.prod_map,Numbered.embedding,Function.Embedding.coeFn_mk,extend_index]
  · have hh : ¬(index e∈Numbered.set (s i) ∧ ∀ a∈Numbered.set (s i),
      extend 0 (m i) a=if a=index e then 2 else 0) := fun hh=>h ((probe_numbered _ _ _).mp hh)
    simp only [scalarProbe,ite_eq_right h,ite_eq_right hh]

lemma reweight_rep (r : E→ℚ) (i : ℕ) :
    reweight (reweightsRep r,i)=TreeFraction.repr (extend 1 r i) := by
  by_cases h : i<Fintype.card E
  · let e := orderedEnum E ⟨i,h⟩
    have he : index e=i := by simp [e,index]
    change ExecutableLadder.lookup (1,1) (reweightsRep r,i)=_
    rw [←he]
    unfold reweightsRep
    rw [lookup_image (1,1) (List.ofFn (orderedEnum E)) index (fun e=>TreeFraction.repr (r e))
      index_injective e (List.mem_ofFn.mpr ⟨⟨i,h⟩,rfl⟩),extend_index]
  · have hoff : ∀ p∈reweightsRep r,p.1≠i := by
      intro p hp
      obtain ⟨e,_he,rfl⟩:=List.mem_map.mp hp
      intro heq
      have hi : index e<Fintype.card E := ((orderedEnum E).symm e).isLt
      exact h (heq ▸ hi)
    change lookup (1,1) (reweightsRep r,i)=_
    have hout : lookup (1,1) (reweightsRep r,i)=(1,1) := by
      unfold reweightsRep
      apply lookup_off
      intro e _he hi
      exact h (hi ▸ ((orderedEnum E).symm e).isLt)
    rw [hout]
    simp only [extend,dite_eq_right h]
    rfl

lemma extend_nonneg (r : E→ℚ) (hr : ∀ e,0 ≤ r e) : ∀ i,0≤extend 1 r i := by
  intro i
  unfold extend
  split_ifs
  · exact hr _
  · norm_num

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeReweightTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
lemma lookup_valid {A E B : Type} [DecidableEq E] (d : B) (xs : List A)
    (key : A→E) (value : A→B) (e : E) (b : B)
    (hv : ∀ a∈xs,key a=e→value a=b)
    (hd : (∀ a∈xs,key a≠e)→d=b) :
    lookup d (xs.map (fun a=>(key a,value a)),e)=b := by
  induction xs with
  | nil => simpa [lookup] using hd (by simp)
  | cons a xs ih =>
    by_cases h : key a=e
    · simpa [lookup,h] using hv a (by simp) h
    · have hm:=ih (fun z hz=>hv z (by simp [hz]))
        (fun hh=>hd (by intro z hz; rcases List.mem_cons.mp hz with rfl|hz; exact h; exact hh z hz))
      simpa [lookup,h] using hm
end MatchingFPRAS.ExecutableLadder

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry ExecutableLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceReweightValue_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w w₁ : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (hw₁ : ∀ a b,0≤w₁ a b)
    (K : ℕ) (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceReweightValue (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),matrixRep w₁),sourceKey e)=
      TreeFraction.repr (RationalSource.bagReweight w w₁ K e) := by
  unfold sourceReweightValue sourceReweightRows reweightTable reweightRow sourceReweightData
  dsimp only
  apply lookup_valid
  · intro a ha he
    have hm : a∈(realEdges (List.range n,List.replicate (2*K+2) false)).toFinset:=List.mem_toFinset.mpr ha
    rw [realEdges_finset n K _ (List.length_replicate ..)] at hm
    obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hm
    rw [sourceRealKey_source hn w hw K] at he
    have hq:=sourceKey_injective he
    change rawReweight (((matrixRep w,matrixRep w₁),List.replicate (2*K+2) false),
      (logicalRepr q.1,q.2.val))=_
    rw [rawReweight_rep w w₁ hw hw₁ K _ (List.length_replicate ..)]
    rw [←hq,RationalSource.bagReweight_on]
  · intro hoff
    have he : ¬∃q,RationalSource.coloredReal w K q=e := by
      rintro ⟨q,hq⟩
      have hm : realRepr q∈realEdges (List.range n,List.replicate (2*K+2) false) := by
        apply List.mem_toFinset.mp
        rw [realEdges_finset n K _ (List.length_replicate ..)]
        exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
      have hh:=hoff (realRepr q) hm
      apply hh
      rw [sourceRealKey_source hn w hw K,hq]
    rw [RationalSource.bagReweight_off w w₁ K e he]
    rfl

lemma sourceReweights_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w w₁ : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (hw₁ : ∀ a b,0≤w₁ a b) (K : ℕ) :
    sourceReweights ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),matrixRep w₁)=
      NumericMarking.reweightsRep (RationalSource.bagReweight w w₁ K) := by
  unfold sourceReweights NumericMarking.reweightsRep
  dsimp only
  rw [sourceTables_catalog hn w hw K]
  unfold sourceCatalog
  rw [List.map_ofFn,List.map_ofFn]
  congr 1
  funext i
  unfold sourceReweightEntry
  dsimp only [Function.comp_apply]
  rw [sourceTables_catalog hn w hw K,sourceCatalog_index,
    sourceReweightValue_source hn w w₁ hw hw₁ K]

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeAdaptiveArithmetic
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableBottleneck ExecutableScaling ExecutableEstimator ExecutableLadder

lemma orderedPair_fin {n : ℕ} (i j : Fin n) (h : i≠j) :
    orderedPair (i.val,j.val)=ExecutableSource.logicalRepr (Enlargement.pairEdge i j h) := by
  unfold orderedPair Enlargement.pairEdge ExecutableSource.logicalRepr
  by_cases hij : i<j
  · simp [show i.val<j.val from hij,min_eq_left hij.le,max_eq_right hij.le]
  · have hji : j ≤ i :=le_of_not_gt hij
    simp [show ¬ i.val<j.val from hij,min_eq_right hji,max_eq_left hji]
lemma probeValue_rep {n : ℕ} (z : Enlargement.LogicalEdge (Fin n)→ℚ) (tab : ProbeTable)
    (ht : ∀ e,lookup (0,1) (tab,ExecutableSource.logicalRepr e)=TreeFraction.repr (z e))
    (i j : Fin n) :
    probeValue (tab,(i.val,j.val))=TreeFraction.repr (FiniteTrial.probeMatrix z i j) := by
  unfold probeValue FiniteTrial.probeMatrix
  by_cases he : i=j
  · subst j; simp; rfl
  · have hv : i.val≠j.val:=fun h=>he (Fin.ext h)
    simp only [ite_eq_right hv,dite_eq_right he]
    rw [orderedPair_fin i j he,ht]

lemma estimateMatrix_rep {n : ℕ} (D : ℕ) (d : ℚ) (hd : 0≤d)
    (z : Enlargement.LogicalEdge (Fin n)→ℚ) (hz : ∀ e,0≤z e) (tab : ProbeTable)
    (ht : ∀ e,lookup (0,1) (tab,ExecutableSource.logicalRepr e)=TreeFraction.repr (z e)) :
    estimateMatrix (((D,TreeFraction.repr d),tab),List.range n)=
      matrixRep (FiniteTrial.estimateMatrix D d z) := by
  unfold estimateMatrix estimateRow matrixRep
  simp only [ExecutableDP.map_range_ofFn]
  congr 1
  funext i
  congr 1
  funext j
  unfold estimateCell
  rw [probeValue_rep z tab ht i j]
  apply upper_rep _ _ _ hd
  unfold FiniteTrial.probeMatrix
  split_ifs
  · exact le_rfl
  · exact hz _

lemma multiplyVector_rep {n : ℕ} (a b : Fin n→ℚ) (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) :
    multiplyVector (vectorRep a,vectorRep b)=vectorRep (fun i=>a i*b i) := by
  unfold multiplyVector vectorRep
  rw [List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  congr 1
  rw [List.ofFn_eq_map,lookup_image (1,1) (List.finRange n) Fin.val
    (fun j=>TreeFraction.repr (b j)) Fin.val_injective i (by simp),mul_repr (ha i) (hb i)]

lemma updateVector_rep {n : ℕ} (hn : 2≤n) (G : Fin n→Fin n→ℚ)
    (hsym : ∀ i j,G i j=G j i)
    (hG : ∀ i j,i≠j→ Counting.alpha≤G i j ∧ G i j≤3)
    (a : Fin n→ℚ) (ha : ∀ i,0≤a i) :
    updateVector (matrixRep G,vectorRep a)=vectorRep (fun i=>a i*Counting.scalingTrace hn G n i) := by
  unfold updateVector
  rw [scale_rep hn G hsym hG]
  apply multiplyVector_rep a _ ha
  intro i
  exact ((Counting.scalingTrace_invariant hn G hsym hG n).1.pos i).le
end MatchingFPRAS.ExecutableAdaptive

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericSummaries
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder ExecutableEstimator

lemma summaries_rep {E : Type} [Fintype E] [LinearOrder E] {S : ℕ}
    (s : Fin S→Finset E) (m : Fin S→E→Fin 3)
    (r : E→ℚ) (hr : ∀ e,0 ≤ r e) (D : ℕ) (keys : List E) :
    summaries ((reweightsRep r,(D,keys.map index)),List.ofFn (fun i=>numericMarks (s i) (m i)))=
      ((TreeFraction.repr (Counting.ratioEstimate ((∑ i,scalarA s m i)/(S:ℚ))
        ((∑ i,scalarD s m r i)/(S:ℚ))),TreeFraction.repr ((∑ i,scalarD s m r i)/(S:ℚ))),
       keys.map (fun e=>(index e,TreeFraction.repr ((∑ i,scalarProbe s m r e i)/(S:ℚ))))) := by
  have hs : List.ofFn (fun i=>numericMarks (s i) (m i))=
      sampleRep (fun i=>Numbered.set (s i)) (fun i=>extend 0 (m i)) := by
    simp only [sampleRep,numericMarks_eq]
  rw [summaries,hs]
  dsimp only
  rw [averageA_rep,averageD_rep _ _ reweight (reweightsRep r) (extend 1 r)
    (extend_nonneg r hr) (reweight_rep r)]
  simp only [scalarA_numbered,scalarD_numbered]
  have ha (i : Fin S) : 0 ≤ scalarA s m i := by
    unfold scalarA; split_ifs <;> norm_num
  have hd (i : Fin S) : 0 ≤ scalarD s m r i := by
    unfold scalarD; split_ifs
    · exact Finset.prod_nonneg (fun e _=>hr e)
    · exact le_rfl
  rw [ratio_rep _ _ (div_nonneg (Finset.sum_nonneg (fun i _=>ha i)) (Nat.cast_nonneg _))
    (div_nonneg (Finset.sum_nonneg (fun i _=>hd i)) (Nat.cast_nonneg _))]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro e _he
  unfold rawProbe
  dsimp only [Function.comp_def]
  rw [averageProbe_rep _ _ reweight (reweightsRep r) (extend 1 r)
    (extend_nonneg r hr) (reweight_rep r)]
  simp only [scalarProbe_numbered]

lemma logicalProbes_rep {E : Type} [Fintype E] [LinearOrder E] {n : ℕ}
    (c : Enlargement.LogicalEdge (Fin n)→E) (keys : List E) (hk : ∀ e,e∈keys) (z : E→ℚ) :
    logicalProbes ((List.ofFn (UnitRefresh.orderedEnum (Enlargement.LogicalEdge (Fin n)))).map
        (fun e=>(ExecutableSource.logicalRepr e,index (c e))),
      keys.map (fun e=>(index e,TreeFraction.repr (z e))))=
      (List.ofFn (UnitRefresh.orderedEnum (Enlargement.LogicalEdge (Fin n)))).map
        (fun e=>(ExecutableSource.logicalRepr e,TreeFraction.repr (z (c e)))) := by
  unfold logicalProbes
  rw [List.map_map]
  apply List.map_congr_left
  intro e _he
  dsimp only [Function.comp_def]
  rw [lookup_image (0,1) keys index (fun e=>TreeFraction.repr (z e)) index_injective (c e) (hk _)]

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStatistics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource
open Finset Transport Enlargement

variable {E : Type} [DecidableEq E]
lemma selectedMarks_on (s : Finset E) (m : ↥s→Fin 3) (e : ↥s) :
    selectedMarks s m e.val=m e := dite_eq_left e.property
lemma selectedMarks_eq (s : Finset E) (m : ↥s→Fin 3) (r : E→Fin 3) :
    (∀ e∈s,selectedMarks s m e=r e) ↔ m=(fun e=>r e.val) := by
  constructor
  · intro h; funext e; exact (selectedMarks_on s m e).symm.trans (h e.val e.property)
  · intro h e he; subst m; simp only [selectedMarks,he,↓reduceDIte]

variable {V : Type} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqSourceLabelCastReal_ra58985_1 (w : V→V→ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
lemma reweight_nonneg (w w₁ : V→V→ℚ) (hw : ∀ i j,0≤w i j)
    (hw₁ : ∀ i j,0≤w₁ i j) (K : ℕ) (e : BagEdge (RationalSource.bags w K)) :
    0≤RationalSource.bagReweight w w₁ K e := by
  classical
  by_cases h : ∃ q,RationalSource.coloredReal w K q=e
  · obtain ⟨q,rfl⟩:=h
    rw [RationalSource.bagReweight_on]
    unfold RationalSource.rawReweight
    split_ifs
    · apply div_nonneg
      · unfold BottleneckAlgorithm.edge; split_ifs <;> apply hw₁
      · unfold BottleneckAlgorithm.edge; split_ifs <;> apply hw
    · exact zero_le_one
  · rw [RationalSource.bagReweight_off w w₁ K e h]; exact zero_le_one

variable (w w₁ : V→V→ℚ) (K : ℕ) {S : ℕ}
    (x : Fin S→RationalSource.Marked w K)
lemma scalarA_source (i : Fin S) :
    scalarA (fun j=>(x j).1.val) (fun j=>selectedMarks (x j).1.val (x j).2) i=
      RationalSource.observableA w K (x i) := by
  unfold scalarA RationalSource.observableA
  simp only [selectedMarks_eq]
lemma scalarD_source (i : Fin S) :
    scalarD (fun j=>(x j).1.val) (fun j=>selectedMarks (x j).1.val (x j).2)
      (RationalSource.bagReweight w w₁ K) i=RationalSource.observableD w w₁ K (x i) := by
  unfold scalarD RationalSource.observableD
  simp only [selectedMarks_eq]
lemma scalarProbe_source (e : LogicalEdge V) (i : Fin S) :
    scalarProbe (fun j=>(x j).1.val) (fun j=>selectedMarks (x j).1.val (x j).2)
      (RationalSource.bagReweight w w₁ K) (RationalSource.centralEdge w K e) i=
      RationalSource.observableProbe w w₁ K e (x i) := by
  unfold scalarProbe RationalSource.observableProbe
  simp only [selectedMarks_eq]
  simp only [singleton_subset_iff,mem_singleton]
  congr 3
  · funext a
    split_ifs <;> rfl
  · congr 1
    exact Subsingleton.elim _ _

noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_ra58985_1 (w : V→V→ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
lemma mem_sourceKeys (e : BagEdge (RationalSource.bags w K)) : e∈sourceKeys w K :=
  List.mem_ofFn.mpr ⟨(UnitRefresh.orderedEnum _).symm e,Equiv.apply_symm_apply _ _⟩

lemma summaries_source (hw : ∀ i j,0≤w i j) (hw₁ : ∀ i j,0≤w₁ i j) (D : ℕ) :
    summaries ((reweightsRep (RationalSource.bagReweight w w₁ K),(D,(sourceKeys w K).map index)),
      sourceSamples w K x)=
      ((TreeFraction.repr (Counting.ratioEstimate
          (FiniteTrial.sampleAverage (RationalSource.observableA w K) x)
          (FiniteTrial.sampleAverage (RationalSource.observableD w w₁ K) x)),
        TreeFraction.repr (FiniteTrial.sampleAverage (RationalSource.observableD w w₁ K) x)),
       (sourceKeys w K).map (fun e=>(index e,TreeFraction.repr
        ((∑ i,scalarProbe (fun j=>(x j).1.val) (fun j=>selectedMarks (x j).1.val (x j).2)
          (RationalSource.bagReweight w w₁ K) e i)/(S:ℚ))))) := by
  unfold sourceSamples
  rw [summaries_rep _ _ _ (reweight_nonneg w w₁ hw hw₁ K)]
  simp only [scalarA_source,scalarD_source,FiniteTrial.sampleAverage]
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma sourceAllIndices_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceAllIndices (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map index := by
  unfold sourceAllIndices
  rw [sourceTables_catalog hn w hw K]
  unfold sourceCatalog
  rw [List.map_ofFn,List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_apply,tableIndex]
  rw [sourceTables_catalog hn w hw K,sourceCatalog_index]

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageUpdateCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource
lemma finishUpdate_rep {E : Type} [Fintype E] [LinearOrder E] {n : ℕ} (hn : 2≤n)
    (c : Enlargement.LogicalEdge (Fin n)→E) (keys : List E) (hk : ∀ e,e∈keys)
    (z : E→ℚ) (hz : ∀ e,0≤z e) (D : ℕ) (d q : ℚ) (hd : 0≤d)
    (a : Fin n→ℚ) (ha : ∀ i,0≤a i) :
    finishUpdate (((D,List.range n),
        ((List.ofFn (UnitRefresh.orderedEnum (Enlargement.LogicalEdge (Fin n)))).map
          (fun e=>(logicalRepr e,index (c e))),vectorRep a)),
      ((TreeFraction.repr q,TreeFraction.repr d),keys.map (fun e=>(index e,TreeFraction.repr (z e)))))=
      (TreeFraction.repr q,vectorRep (fun i=>a i*
        Counting.scalingTrace hn (FiniteTrial.estimateMatrix D d (z ∘ c)) n i)) := by
  unfold finishUpdate
  dsimp only
  rw [logicalProbes_rep c keys hk z]
  have ht (e : Enlargement.LogicalEdge (Fin n)) :
      lookup (0,1) ((List.ofFn (UnitRefresh.orderedEnum (Enlargement.LogicalEdge (Fin n)))).map
        (fun e=>(logicalRepr e,TreeFraction.repr (z (c e)))),logicalRepr e)=
          TreeFraction.repr ((z ∘ c) e) := by
    apply lookup_image (0,1) _ logicalRepr (fun e=>TreeFraction.repr (z (c e))) logicalRepr_injective
    exact List.mem_ofFn.mpr ⟨(UnitRefresh.orderedEnum _).symm e,Equiv.apply_symm_apply _ _⟩
  rw [estimateMatrix_rep D d hd (z ∘ c) (fun e=>hz (c e)) _ ht,
    updateVector_rep hn _ (FiniteTrial.estimateMatrix_symm D d (z ∘ c))
      (fun i j _=>FiniteTrial.estimateMatrix_bounds D d (z ∘ c) i j) a ha]

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeScaleStateUpdate
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource
open Finset Transport Enlargement

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqSourceLabelFinNCastReal_ra58985_1 (w : Fin G.n→Fin G.n→ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelCastRealSourceBags_ra58985_1 (w : Fin G.n→Fin G.n→ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
lemma scaleState_update_rep (hn : 2≤G.n) (s : FiniteTrial.ScaleState G j)
    (x : Fin S→RationalSource.Marked s.activity K) :
    finishUpdate (sourceUpdateConfig s K,summaries (sourceStatisticsInput s K x))=
      (TreeFraction.repr (s.ratioEstimate x),vectorRep (s.update hn x).scale) := by
  unfold sourceStatisticsInput
  rw [summaries_source s.activity s.nextActivity K x
    (fun i j=>(s.activity_pos i j).le) (fun i j=>(s.nextActivity_pos i j).le)]
  let z := fun e=>(∑ i,scalarProbe (fun j=>(x j).1.val)
    (fun j=>selectedMarks (x j).1.val (x j).2)
    (RationalSource.bagReweight s.activity s.nextActivity K) e i)/(S:ℚ)
  have hr := reweight_nonneg s.activity s.nextActivity
    (fun i j=>(s.activity_pos i j).le) (fun i j=>(s.nextActivity_pos i j).le) K
  have hz : ∀ e,0≤z e := by
    intro e
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    unfold scalarProbe
    split_ifs
    · exact Finset.prod_nonneg (fun a _=>hr a)
    · exact le_rfl
  have hd : 0≤FiniteTrial.sampleAverage (RationalSource.observableD s.activity s.nextActivity K) x := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    unfold RationalSource.observableD
    split_ifs
    · exact Finset.prod_nonneg (fun a _=>hr a)
    · exact le_rfl
  change finishUpdate (((FiniteTrial.sourceD (G:=G) K,List.range G.n),
    ((List.ofFn (UnitRefresh.orderedEnum (LogicalEdge (Fin G.n)))).map
      (fun e=>(logicalRepr e,index (RationalSource.centralEdge s.activity K e))),vectorRep s.scale)),
    ((TreeFraction.repr (s.ratioEstimate x),TreeFraction.repr
      (FiniteTrial.sampleAverage (RationalSource.observableD s.activity s.nextActivity K) x)),
      (sourceKeys s.activity K).map (fun e=>(index e,TreeFraction.repr (z e)))))=_
  rw [finishUpdate_rep hn (RationalSource.centralEdge s.activity K) (sourceKeys s.activity K)
    (mem_sourceKeys s.activity K) z hz _ _ _ hd s.scale (fun i=>(s.positive i).le)]
  have he : z ∘ RationalSource.centralEdge s.activity K=
      (fun e=>FiniteTrial.sampleAverage (RationalSource.observableProbe s.activity s.nextActivity K e) x) := by
    funext e
    simp only [z,Function.comp_def,scalarProbe_source,FiniteTrial.sampleAverage]
  rw [he]
  rfl
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBindings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder ExecutableLadder NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLEProdOfLinearOrder_solutions_1
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLTProdOfLinearOrder_solutions_1
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instPreorderProdOfLinearOrder_solutions_1
lemma logicalEdges_eq_ofFn (n : ℕ) : logicalEdges (List.range n)=
    (List.ofFn (UnitRefresh.orderedEnum (LogicalEdge (Fin n)))).map logicalRepr := by
  classical
  rw [UnitRefresh.ofFn_orderedEnum]
  have ha : (logicalEdges (List.range n)).Pairwise (· ≤ ·) :=
    (logicalEdges_pairwise n).imp (fun h=>le_of_lt h)
  have hb : (((Finset.univ : Finset (LogicalEdge (Fin n))).sort (· ≤ ·)).map logicalRepr).Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(logicalRepr_le _ _).mpr h)
  have hn : (logicalEdges (List.range n)).Nodup := (logicalEdges_pairwise n).imp (fun h=>h.ne)
  have hm := (Finset.sort_nodup (Finset.univ : Finset (LogicalEdge (Fin n))) (· ≤ ·)).map logicalRepr_injective
  have hp : (logicalEdges (List.range n)).Perm
      (((Finset.univ : Finset (LogicalEdge (Fin n))).sort (· ≤ ·)).map logicalRepr) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext e
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
    constructor
    · exact logicalEdges_complete e
    · rintro ⟨a,rfl⟩; exact logicalRepr_mem a
  exact hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂) ha hb

lemma sourceBindings_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    sourceBindings (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      (List.ofFn (UnitRefresh.orderedEnum (LogicalEdge (Fin n)))).map
        (fun e=>(logicalRepr e,index (RationalSource.centralEdge w K e))) := by
  unfold sourceBindings
  rw [logicalEdges_eq_ofFn,List.map_map]
  apply List.map_congr_left
  intro e _he
  dsimp only [Function.comp_def,centralBinding,centralIndex]
  rw [centralKey_source hn w hw K]
  unfold tableIndex
  dsimp only
  rw [sourceTables_catalog hn w hw K,sourceCatalog_index]

lemma generatedUpdateConfig_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    {j : ℕ} (s : FiniteTrial.ScaleState G j) (K : ℕ) :
    generatedUpdateConfig (((((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),
      List.replicate (2*K) false),FiniteTrial.sourceD (G:=G) K),ExecutableScaling.vectorRep s.scale)=
      sourceUpdateConfig s K := by
  unfold generatedUpdateConfig sourceUpdateConfig
  dsimp only
  rw [sourceBindings_source hn s.activity (fun i j=>(s.activity_pos i j).le) K]
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedUpdate
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

variable {n : ℕ} [Nontrivial (Fin n)]

lemma numericMarks_selected {E : Type} [Fintype E] [LinearOrder E]
    (s : Finset E) (m : E→Fin 3) (de : DecidableEq E) :
    numericMarks s (@selectedMarks E de s (fun e=>m e.val))=numericMarks s m := by
  unfold numericMarks
  apply List.map_congr_left
  intro e he
  have hm : e∈s := (Finset.mem_sort _).mp he
  simp only [selectedMarks,hm,↓reduceDIte]

lemma generatedMarked_sourceSample (hn : 2≤n) (he : Even n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    let x := generatedSourceSample he w hw K D hD hu ft fq hq bits mb
    generatedMarked
      ((((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)),
       (List.ofFn (fun z=>(List.ofFn (bits z).1,localBitsRep (bits z).2)),
         (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map (fun e=>(index e,List.ofFn (mb e)))))=
      numericMarks x.1.val (selectedMarks x.1.val x.2) := by
  dsimp only
  rw [generatedMarked_source hn he w hw K D hD hu ft fq hq bits mb]
  dsimp only [generatedSourceSample,TableMarking.reveal]
  exact (numericMarks_selected (E:=BagEdge (RationalSource.bags w K)) _ _ _).symm

lemma generatedSamples_source (hn : 2≤n) (he : Even n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {S k r km : ℕ}
    (bits : Fin S→Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : Fin S→BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    sampleMany
      (generatedContext (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)),
       List.ofFn (fun i=>(List.ofFn (fun z=>(List.ofFn (bits i z).1,localBitsRep (bits i z).2)),
         (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map (fun e=>(index e,List.ofFn (mb i e))))))=
      sourceSamples w K (fun i=>generatedSourceSample he w hw K D hD hu ft fq hq (bits i) (mb i)) := by
  unfold sampleMany sourceSamples
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have hm := generatedMarked_sourceSample hn he w hw K D hD hu ft fq hq (bits i) (mb i)
  simpa only [generatedMarked,Function.comp_def] using hm

lemma generatedUpdate_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j) (K : ℕ)
    (hD : 0<FiniteTrial.sourceD (G:=G) K)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {S k r km : ℕ}
    (bits : Fin S→Fin r→ScanBits (SourceVertex (Fin G.n) K) k)
    (mb : Fin S→BagEdge (RationalSource.bags s.activity K)→Fin km→Bool) :
    let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
      (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bits i) (mb i)
    let keys := List.ofFn (orderedEnum (BagEdge (RationalSource.bags s.activity K)))
    generatedUpdate
      ((((((((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),List.replicate (2*K) false),
        FiniteTrial.sourceD (G:=G) K),(ft,fq)),matrixRep s.nextActivity),vectorRep s.scale),
       List.ofFn (fun i=>(List.ofFn (fun z=>(List.ofFn (bits i z).1,localBitsRep (bits i z).2)),
         keys.map (fun e=>(index e,List.ofFn (mb i e))))))=
      (TreeFraction.repr (s.ratioEstimate x),vectorRep (s.update hn x).scale) := by
  dsimp only
  let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
    (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bits i) (mb i)
  unfold generatedUpdate generatedUpdateSetup
  rw [generatedUpdateConfig_source hn s K]
  unfold stageUpdate generatedStageSetup
  dsimp only
  rw [generatedSamples_source hn he s.activity s.activity_pos K (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq bits mb]
  unfold generatedObservables
  dsimp only
  rw [sourceReweights_source hn s.activity s.nextActivity (fun a b=>(s.activity_pos a b).le)
      (fun a b=>(s.nextActivity_pos a b).le) K,
    sourceAllIndices_source hn s.activity (fun a b=>(s.activity_pos a b).le) K]
  exact scaleState_update_rep hn s x

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageActivity
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableLadder

lemma lookup_vectorRep {n : ℕ} (v : Fin n→ℚ) (i : Fin n) (d : Fraction) :
    lookup d (vectorRep v,i.val)=TreeFraction.repr (v i) := by
  unfold vectorRep
  rw [List.ofFn_eq_map]
  exact lookup_image d (List.finRange n) Fin.val (fun j=>TreeFraction.repr (v j))
    Fin.val_injective i (by simp)
end MatchingFPRAS.ExecutableScaling

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableBottleneck ExecutableScaling ExecutableLadder ExecutableSource

lemma cooling_rep (n : ℕ) : cooling n=TreeFraction.repr (FiniteTrial.cooling n) := by
  unfold cooling FiniteTrial.cooling
  rw [←repr_nat n,show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,
    div_repr (by decide) (by positivity),add_repr (by decide) (by positivity),
    div_repr (by decide) (by positivity),one_div]

lemma orderedPair_minmax (a b : ℕ) : orderedPair (a,b)=(min a b,max a b) := by
  unfold orderedPair
  by_cases h : a<b
  · simp [h,min_eq_left h.le,max_eq_right h.le]
  · simp [h,min_eq_right (le_of_not_gt h),max_eq_left (le_of_not_gt h)]
lemma edge_mem_graphRep (G : GraphInput) (i j : Fin G.n) :
    orderedPair (i.val,j.val)∈(graphRep G).2 ↔ (min i j,max i j)∈G.edges := by
  rw [orderedPair_minmax]
  simp only [graphRep,List.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨⟨a,b⟩,hab,he⟩
    have ha : a=min i j := Fin.ext (congrArg Prod.fst he)
    have hb : b=max i j := Fin.ext (congrArg Prod.snd he)
    simpa [ha,hb] using hab
  · intro h
    exact ⟨(min i j,max i j),h,rfl⟩
lemma rawCell_rep (G : GraphInput) (fuel : List Bool) (a : Fin G.n→ℚ) (i j : Fin G.n) :
    rawCell (cellData ((graphRep G,fuel),vectorRep a),(i.val,j.val))=
      TreeFraction.repr (FiniteTrial.raw G fuel.length i j) := by
  unfold rawCell cellData
  dsimp only
  simp only [edge_mem_graphRep]
  unfold FiniteTrial.raw
  split_ifs
  · rfl
  · rw [show (graphRep G).1.length=G.n by simp [graphRep],cooling_rep,
      fuelPower_repr _ (by unfold FiniteTrial.cooling; positivity)]
lemma stageMatrix_rep (G : GraphInput) (fuel : List Bool) (a : Fin G.n→ℚ) (ha : ∀ i,0 ≤ a i) :
    stageMatrix ((graphRep G,fuel),vectorRep a)=
      matrixRep (fun i j=>FiniteTrial.raw G fuel.length i j*a i*a j) := by
  have hr (i j : Fin G.n) : 0 ≤ FiniteTrial.raw G fuel.length i j := by
    unfold FiniteTrial.raw FiniteTrial.cooling
    split_ifs <;> positivity
  unfold stageMatrix stageRow matrixRep
  change (List.range G.n).map _=(List.ofFn _)
  simp only [ExecutableDP.map_range_ofFn]
  congr 1
  funext i
  change (List.range G.n).map _=List.ofFn _
  rw [ExecutableDP.map_range_ofFn]
  congr 1
  funext j
  unfold stageCell
  rw [rawCell_rep,show (cellData ((graphRep G,fuel),vectorRep a)).2=vectorRep a from rfl,
    lookup_vectorRep a i,lookup_vectorRep a j,mul_repr (hr i j) (ha i),
    mul_repr (mul_nonneg (hr i j) (ha i)) (ha j)]
end MatchingFPRAS.ExecutableAdaptive

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseStage
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma sparseUpdateData_source {G : GraphInput} {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K D : ℕ) (ft fq : List Bool) :
    sparseUpdateData (((graphRep G,List.replicate j false),
      (((List.replicate (2*K+2) false,List.replicate (2*K) false),D),(ft,fq))),vectorRep s.scale)=
      (((((((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),List.replicate (2*K) false),D),(ft,fq)),
       matrixRep s.nextActivity),vectorRep s.scale) := by
  unfold sparseUpdateData sparseGeneratedInput sparseBagInput sparseCurrentMatrix sparseNextMatrix currentActivityArg nextActivityArg
  dsimp only
  rw [stageMatrix_rep G _ s.scale (fun i=>(s.positive i).le),stageMatrix_rep G _ s.scale (fun i=>(s.positive i).le)]
  simp only [List.length_replicate,List.length_cons]
  rfl

lemma sparseStage_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j) (K : ℕ)
    (hD : 0<FiniteTrial.sourceD (G:=G) K)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {S k r km : ℕ}
    (bits : Fin S→Fin r→ScanBits (SourceVertex (Fin G.n) K) k)
    (mb : Fin S→BagEdge (RationalSource.bags s.activity K)→Fin km→Bool) :
    let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
      (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bits i) (mb i)
    let keys := List.ofFn (orderedEnum (BagEdge (RationalSource.bags s.activity K)))
    sparseStage
      ((((graphRep G,List.replicate j false),
        (((List.replicate (2*K+2) false,List.replicate (2*K) false),FiniteTrial.sourceD (G:=G) K),(ft,fq))),vectorRep s.scale),
       List.ofFn (fun i=>(List.ofFn (fun z=>(List.ofFn (bits i z).1,localBitsRep (bits i z).2)),
         keys.map (fun e=>(index e,List.ofFn (mb i e))))))=
      (TreeFraction.repr (s.ratioEstimate x),vectorRep (s.update hn x).scale) := by
  dsimp only
  unfold sparseStage
  rw [sparseUpdateData_source]
  exact generatedUpdate_source hn he s K hD hu ft fq hq bits mb

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineStage
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma source_mean_oai (hn : 2≤G.n) (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K : ℕ) (hD : 0<FiniteTrial.sourceD (G:=G) K)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) (S k r km : ℕ)
    (h : Fraction×Vector → ℚ) :
    let E := BagEdge (RationalSource.bags s.activity K)
    let keys := fun i : Fin (Fintype.card E)=>index (orderedEnum E i)
    let req : OnlineSample.Request :=
      (((k,Fintype.card (SourceVertex (Fin G.n) K)),r),(km,List.ofFn keys))
    (execute (data s K (FiniteTrial.sourceD (G:=G) K) ft fq,(S,req))).mean h=
      qaverage (fun bs : Fin S→OnlineSample.Random (Fintype.card (SourceVertex (Fin G.n) K)) k r (Fintype.card E) km=>
        let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
          (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bs i).1
          (fun e=>(bs i).2 ((orderedEnum E).symm e))
        h (repr (s.ratioEstimate x),vectorRep (s.update hn x).scale)) := by
  dsimp only
  rw [execute,Experiment.mean_map,OnlineSample.mean_many]
  apply qaverage_congr
  intro bs
  have hs:=sparseStage_source hn he s K hD hu ft fq hq (fun i=>(bs i).1)
    (fun i e=>(bs i).2 ((orderedEnum (BagEdge (RationalSource.bags s.activity K))).symm e))
  dsimp only at hs
  have rows : List.ofFn (fun i=>OnlineSample.sampleRep
        (fun e=>index (orderedEnum (BagEdge (RationalSource.bags s.activity K)) e)) (bs i)) =
      List.ofFn (fun i=>(List.ofFn (fun z=>(List.ofFn ((bs i).1 z).1,localBitsRep ((bs i).1 z).2)),
        (List.ofFn (orderedEnum (BagEdge (RationalSource.bags s.activity K)))).map
          (fun e=>(index e,List.ofFn ((bs i).2 ((orderedEnum _).symm e)))))) := by
    simp only [OnlineSample.sampleRep,OnlineSample.scanRep,OnlineSample.localRep,List.map_ofFn,
      Function.comp_def,Equiv.symm_apply_apply,localBitsRep]
  rw [rows]
  exact congrArg h hs
end MatchingFPRAS.OnlineStage

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.OnlineStage.source_mean_oai := @OAI.MatchingFPRAS.OnlineStage.source_mean_oai

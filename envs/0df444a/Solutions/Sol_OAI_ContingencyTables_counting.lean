-- Prove2me | solution 1 for OAI.ContingencyTables.counting
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:59:02.522348+00:00
-- url     : https://prove2.me/submissions/d9977ab2-b44d-49b3-8022-2ae6b0168829

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009
import Definitions.Def_OAIQ089A010
import Theorems.Thm_OAI_ContingencyTables_ComputedCountingZero_zero_success
import Theorems.Thm_OAI_ContingencyTables_CountingExecutedMachine_positive_success
import Theorems.Thm_OAI_ContingencyTables_CountingExecutedMachine_public_time
import Theorems.Thm_OAI_ContingencyTables_CountingPositiveProgram_value_source_sameLaw
import Theorems.Thm_OAI_ContingencyTables_RootedEstimatorWordProgram_output_scheduled

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

namespace FiniteChain

open scoped Classical BigOperators
variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma variance_formula (f : X → ℝ) : C.variance f = C.inner f f-(C.mean f)^2 := by
  rw [variance,C.inner_sub_left,C.inner_sub_right,C.inner_sub_right]
  have h₁ : C.inner f (fun _ => C.mean f) = (C.mean f)^2 := by
    unfold inner
    rw [← Finset.sum_mul]
    change C.mean f*C.mean f = (C.mean f)^2
    ring
  have h₂ : C.inner (fun _ => C.mean f) (fun _ => C.mean f) = (C.mean f)^2 := by
    simp only [inner,← Finset.sum_mul,C.normalized,one_mul,pow_two]
  rw [h₁,C.inner_symm (fun _ => C.mean f) f,h₁,h₂]
  ring

end FiniteChain

open Set

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

end

section

open scoped BigOperators Classical
lemma uniformAverage_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformAverage (fun x => f (e x))=uniformAverage f := by
  rw [uniformAverage,uniformAverage,e.sum_comp,Fintype.card_congr e]
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
lemma uniformAverage_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun y => f (x,y))) := by
  simp only [uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← Finset.sum_div]
  ring
lemma uniformAverage_fin_succ {X : Type*} [Fintype X] (D : ℕ)
    (f : (Fin (D+1) → X) → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun rest => f (Fin.cons x rest))) := by
  rw [← uniformAverage_equiv (Fin.consEquiv (fun _ : Fin (D+1) => X)) f,uniformAverage_prod]
  rfl

open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

section CanonicalFair
open scoped BigOperators Classical
lemma uniformAverage_independent_eq {X Y Z : Type*} [Fintype X] [Fintype Y]
    (f : X → Z) (g : Y → Z)
    (h : ∀ φ : Z → ℝ,uniformAverage (fun x => φ (f x))=uniformAverage (fun y => φ (g y)))
    (k : ℕ) (F : (Fin k → Z) → ℝ) :
    uniformAverage (fun xs : Fin k → X => F (fun i => f (xs i)))=
      uniformAverage (fun ys : Fin k → Y => F (fun i => g (ys i))) := by
  induction k with
  | zero =>
    have hf : ∀ xs : Fin 0 → X,(fun i => f (xs i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro xs; funext i; exact Fin.elim0 i
    have hg : ∀ ys : Fin 0 → Y,(fun i => g (ys i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro ys; funext i; exact Fin.elim0 i
    simp_rw [hf,hg,uniformAverage_const]
  | succ k ih =>
    have hf (x : X) (xs : Fin k → X) :
        (fun i : Fin (k+1) => f ((Fin.cons x xs : Fin (k+1) → X) i))=Fin.cons (f x) (fun i => f (xs i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hg (y : Y) (ys : Fin k → Y) :
        (fun i : Fin (k+1) => g ((Fin.cons y ys : Fin (k+1) → Y) i))=Fin.cons (g y) (fun i => g (ys i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp_rw [hf,hg]
    have hi (x : X) := ih (fun zs => F (Fin.cons (f x) zs))
    simp_rw [hi]
    exact h (fun z => uniformAverage (fun ys : Fin k → Y => F (Fin.cons z (fun i => g (ys i)))))
end CanonicalFair

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

end CommonBasesFPRAS

open CommonBasesFPRAS

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_GuardMachineBase
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.MachineCost
open Turing

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma statementCost_le_programCost [Fintype Λ] (l : Λ) :
    statementCost (M l)≤programCost M := Finset.le_sup (f:=fun l=>statementCost (M l)) (Finset.mem_univ l)
end MatchingFPRAS.MachineCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_StackCompilerCost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackCost
open Turing Turing.TM2to1 Turing.TM2to1.Λ' MachineCost

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

omit [DecidableEq K] in
lemma accesses_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    accesses (stRun o q)=accesses q+1 := by cases o <;> rfl
variable (M : Λ → TM2.Stmt Γ Λ σ)
lemma go_time {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k,Option (Γ k))}
    (hL : L.map (proj k)=ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n≤S.length) :
    MachineCost.run (TM1.step (tr M)) n ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩=
      ⟨some (go k o q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=n+1 from rfl,run_add,ih (by omega)]
    simp only [MachineCost.run,advance,TM1.step]
    rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
      stk_nth_val _ hL,List.getElem?_eq_getElem (by simpa using (show n<S.length by omega))]
    simp only [Option.isNone_some,Bool.cond_false,TM1.stepAux,Option.getD_some]
    rw [Function.iterate_succ_apply']
lemma action_bound {S : ∀ k,List (Γ k)} {H : ℕ} (hS : StackBound S H)
    {k : K} (o : StAct K Γ σ k) (v : σ) :
    StackBound (Function.update S k (stWrite v (S k) o)) (H+1) := by
  intro j
  by_cases hj : j=k
  · subst j
    rw [Function.update_self]
    have hk:=hS k
    cases o <;> simp only [stWrite,List.length_cons,List.length_tail] <;> omega
  · rw [Function.update_of_ne hj]
    exact (hS j).trans (by omega)
lemma stepAux_bound (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (H : ℕ) (hS : StackBound S H) : StackBound (TM2.stepAux q v S).stk (H+accesses q) := by
  induction q using stmtStRec generalizing v S H with
  | run k o q ih =>
    rw [step_run,accesses_run]
    have hh:=ih (stVar v (S k) o) _ (H+1) (action_bound hS o v)
    convert hh using 1; omega
  | load a q ih => exact ih (a v) S H hS
  | branch p q r ihq ihr =>
    cases hp:p v
    · simp only [TM2.stepAux,hp,Bool.cond_false,accesses]
      exact fun k=>(ihr v S H hS k).trans (Nat.add_le_add_left (le_max_right _ _) H)
    · simp only [TM2.stepAux,hp,Bool.cond_true,accesses]
      exact fun k=>(ihq v S H hS k).trans (Nat.add_le_add_left (le_max_left _ _) H)
  | goto f => simpa only [TM2.stepAux,accesses,Nat.add_zero] using hS
  | halt => simpa only [TM2.stepAux,accesses,Nat.add_zero] using hS

lemma advance_bound (A : ℕ) (hA : ∀ l,accesses (M l)≤A)
    (c : TM2.Cfg Γ Λ σ) (H : ℕ) (hS : StackBound c.stk H) :
    StackBound (advance (TM2.step M) c).stk (H+A) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => exact fun k=>(hS k).trans (Nat.le_add_right H A)
  | some l =>
    have hh:=stepAux_bound (M l) v S H hS
    exact fun k=>(hh k).trans (Nat.add_le_add_left (hA l) H)
end MatchingFPRAS.StackCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_BoolPostCompiler
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BoolPostCompiler
open Turing MachineCost
open scoped Classical

lemma down_up (b : Bool) : down (up b)=b := by cases b <;> decide
end MatchingFPRAS.BoolPostCompiler

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_SupportedCompiler
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SupportedCompiler
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma cost_le {l : Λ} (hl : l ∈ S) : statementCost (M l) ≤ cost M S := Finset.le_sup (f:=fun l=>statementCost (M l)) hl
include hS
omit [Inhabited σ] in
lemma advance_supported {c : TM1.Cfg Γ Λ σ} (hc : c.l ∈ S.insertNone) :
    (advance (TM1.step M) c).l ∈ S.insertNone := by
  cases he:TM1.step M c with
  | none => simpa only [advance,he,Option.getD_none] using hc
  | some c' =>
    simpa only [advance,he,Option.getD_some] using TM1.step_supports M hS he hc
end MatchingFPRAS.SupportedCompiler

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_FixedEncoding
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FixedEncoding
variable (Γ : Type*) [Fintype Γ] [Inhabited Γ]
lemma injective : Function.Injective (enc Γ) := by
  classical
  intro a b hab
  by_cases ha : a=default
  · by_cases hb : b=default
    · exact ha.trans hb.symm
    · have hh:=congrArg (fun v : List.Vector Bool (Fintype.card Γ)=>v.get (Fintype.equivFin Γ b)) hab
      simp [enc,ha,hb] at hh
  · have hh:=congrArg (fun v : List.Vector Bool (Fintype.card Γ)=>v.get (Fintype.equivFin Γ a)) hab
    simp only [enc,List.Vector.get_ofFn] at hh
    have ht : decide (b≠default ∧ Fintype.equivFin Γ b=Fintype.equivFin Γ a)=true := by
      simpa [ha] using hh.symm
    exact ((Fintype.equivFin Γ).injective (of_decide_eq_true ht).2).symm
lemma left_inverse (a : Γ) : dec Γ (enc Γ a)=a :=
  Function.leftInverse_invFun (injective Γ) a
end MatchingFPRAS.FixedEncoding

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_StackWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackWords
open Turing MachineCost

variable {K : Type*} {Γ : K → Type*}
lemma rows_projection (S : ∀ k,List (Γ k)) (H : ℕ) (hS : StackCost.StackBound S H)
    (k : K) : (ListBlank.mk (rows S H)).map (proj k)=ListBlank.mk ((S k).map some).reverse := by
  apply ListBlank.ext
  intro i
  rw [ListBlank.nth_map,ListBlank.nth_mk,List.getI_eq_getElem?_getD]
  simp only [rows,List.getElem?_ofFn,proj,PointedMap.mk_val]
  rw [←List.map_reverse,ListBlank.nth_mk,List.getI_eq_getElem?_getD,List.getElem?_map]
  by_cases hi : i<H
  · simp only [hi,Option.getD_some,dite_true]
    cases (S k).reverse[i]? <;> rfl
  · have hlen : (S k).reverse.length ≤ i := by simpa using (hS k).trans (Nat.le_of_not_gt hi)
    simp [hi,List.getElem?_eq_none hlen]
lemma word_blank (S : ∀ k,List (Γ k)) (H : ℕ) :
    ListBlank.mk (word S H)=TM2to1.addBottom (ListBlank.mk (rows S H)) := by
  simp only [word,TM2to1.addBottom,ListBlank.head_mk,ListBlank.tail_mk,
    ListBlank.map_mk]
  exact (ListBlank.cons_mk _ _).symm
lemma unique_rows (S : ∀ k,List (Γ k)) (H : ℕ) (hS : StackCost.StackBound S H)
    (L : ListBlank (∀ k,Option (Γ k)))
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    L=ListBlank.mk (rows S H) := by
  apply ListBlank.ext
  intro i
  funext k
  rw [TM2to1.stk_nth_val i (hL k),TM2to1.stk_nth_val i (rows_projection S H hS k)]
end MatchingFPRAS.StackWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

lemma normalize_den_pos (x : Fraction) : 0<(normalize x).2 := by
  rw [normalize_repr]; exact (val x).pos

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
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomial
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma weight_pos (a : A) : 0<weight a := by
  change 0<TreeFunction.size (encode a)
  cases encode a <;> simp only [size_nil,size_cons] <;> omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the companion's retained small-cell capacities

The program scans the rectangular cell list determined by the two
margin-list lengths, then tests the binary cell bound against W. It
does not enumerate up to the numeric value of a capacity.
-/

namespace ContingencyTables.CompanionCellCatalog

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma capacities_eq (A : Instance (Fin m) (Fin n)) :
    capacities (input A)=List.ofFn (fun i => A.b ((cellEquiv A) i).val.1 ((cellEquiv A) i).val.2) := by
  apply List.ext_getElem
  · simp only [capacities,List.length_map,List.length_ofFn]
  · intro i hi hj
    have hi' : i<(catalog (input A)).length := by simpa only [List.length_ofFn] using hj
    simp only [capacities,List.getElem_map,List.getElem_ofFn]
    have he := catalogCell_coordinates A ⟨i,hi'⟩
    change entry (input A,(catalog (input A))[i]'hi')=
      A.b (catalogCell A ⟨i,hi'⟩).val.1 (catalogCell A ⟨i,hi'⟩).val.2
    rw [←he]
    exact entry_input A _ _

end
end ContingencyTables.CompanionCellCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual root residuals of the integral forest completion

Summing a root-path flow gives the prescribed demand minus the total
demand in the component. This formula also applies at roots and on
singleton components, where the nonroot-only margin lemma is vacuous.
-/

namespace ContingencyTables.ForestRootPenalty

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestPhysicalCompletion ForestLiteralCount

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Absolute component totals sum to at most the total absolute demand.
Each vertex is counted in one component, including isolated vertices. -/
theorem sum_abs_componentTotal (root : V → V) (r : V → ℝ) :
    (∑ a, |∑ v, if root v=a then r v else 0|)≤∑ v, |r v| := by
  calc
    _ ≤ ∑ a, ∑ v, |if root v=a then r v else 0| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      have he (a v : V) : |if root v=a then r v else 0|=
          if root v=a then |r v| else 0 := by split_ifs <;> simp
      simp_rw [he]
      rw [Finset.sum_comm]
      simp

end Generic

end ContingencyTables.ForestRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the actual scaled forest-penalty Lipschitz bound -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma intervalCost_change (x y : ℝ) : |intervalCost x-intervalCost y| ≤ |x-y| := by
  have hsub (x y : ℝ) : intervalCost x ≤ intervalCost y+|x-y| := by
    unfold intervalCost
    apply max_le
    · linarith [le_max_left (0:ℝ) (max (-y) (y-1)),abs_nonneg (x-y)]
    · apply max_le
      · have hh : -y ≤ max 0 (max (-y) (y-1)) :=
          (le_max_left _ _).trans (le_max_right _ _)
        linarith [neg_le_abs (x-y)]
      · have hh : y-1 ≤ max 0 (max (-y) (y-1)) :=
          (le_max_right _ _).trans (le_max_right _ _)
        linarith [le_abs_self (x-y)]
  apply abs_le.mpr
  constructor
  · have hh := hsub y x
    rw [abs_sub_comm y x] at hh
    linarith
  · linarith [hsub x y]

lemma tree_card_le (A : Instance I J) : Fintype.card (TreeCell A.T) ≤ A.d := by
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledIdentification
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer free assignments use the original scaled affine tree values -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma intervalCost_div (x b : ℝ) (hb : 0 < b) :
    intervalCost (x/b)=max 0 (max (-x) (x-b))/b := by
  unfold intervalCost
  have he : x/b-1=(x-b)/b := by field_simp [hb.ne']
  rw [he,← neg_div, max_div_div_right hb.le]
  simpa only [zero_div] using max_div_div_right hb.le (0:ℝ) (max (-x) (x-b))

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual continuous forest penalty stays within the source allowance -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty
open ForestCountIdentification BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rowCounts_bounds (A : Instance I J) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (i : I) (j : J) (hs : A.small i j=true) :
    0 ≤ rowCounts A z i j ∧ rowCounts A z i j ≤ A.b i j := by
  refine ⟨Nat.cast_nonneg _,?_⟩
  have hh : smallX A.small z i j ≤ A.b i j := by
    simpa only [smallX,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,false)
  change (smallX A.small z i j:ℤ) ≤ (A.b i j:ℤ)
  exact_mod_cast hh

lemma columnCounts_bounds (A : Instance I J) (z : View A → ℕ) (i : I) (j : J) :
    0 ≤ columnCounts A z i j ∧ columnCounts A z i j ≤ A.b i j := by
  unfold columnCounts
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast Nat.sub_le (A.b i j) (smallY A.small z i j)⟩

lemma integerCube_zero (A : Instance I J) (B : ℝ) : integerCube A B (zeroAssignment A)=0 := by
  funext a
  simp only [integerCube,zeroAssignment,Nat.cast_zero,mul_zero,zero_div,Pi.zero_apply]

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal weight-evaluator density on its finite-dimensional bin cube -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma binWidth_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < binWidth A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold binWidth
  positivity

lemma height_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < height A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold height
  positivity

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded Boolean draws for the companion correction experiment -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The bin-dependent interval length only chooses a prefix of the
fixed per-coordinate word. This preserves the analyzed quotient law. -/
theorem binWordDraw_law (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) :
    mapLaw (uniformLaw (α := BinWords A h)) (binWordDraw A K hK hW v h)=
      approximateBinLaw A K hK hW v h := by
  unfold binWordDraw approximateBinLaw
  rw [←mapLaw_comp,←pi_uniformLaw]
  rw [pi_mapLaw (fun i : Fin (dimension A) =>
    uniformLaw (α := Fin (offsetBitLength (freeRange A (index A i)) h A.d) → Bool))
    (fun i bits => scaledBitInteger (binSize A K v i)
      (offsetBitLength (binSize A K v i) h A.d) (binSize_positive A K hK hW v i)
      (prefixWord (binBits_le A K hK v h i) bits))]
  congr 1
  congr 1
  funext i
  rw [padded_draw_law]
  exact scaledBitIntegerLaw_eq _ _ _

lemma flatBinDraw_law (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (binWordBits A h) → Bool)) (flatBinDraw A K hK hW v h)=
      approximateBinLaw A K hK hW v h := by
  unfold flatBinDraw
  rw [←map_equiv (binWordEquiv A h),uniform_equiv,binWordDraw_law]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteLawMoments
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expectations of concrete finite-word output laws -/

namespace ContingencyTables.FiniteLawMoments

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma expectation_map [DecidableEq Y] (p : RationalLaw X) (draw : X → Y) (g : Y → ℝ) :
    expectation (mapLaw p draw) g=expectation p (fun x => g (draw x)) := by
  unfold expectation mapLaw
  simp only [Rat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = ∑ y : Y,if draw x=y then (p.mass x:ℝ)*g y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = _ := by simp

lemma expectation_uniform [Nonempty X] (g : X → ℝ) :
    expectation (uniformLaw (α := X)) g=uniformAverage g := by
  unfold expectation uniformLaw uniformMass uniformAverage
  simp only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  rw [←Finset.mul_sum]
  ring

lemma word_expectation [Nonempty X] [DecidableEq Y] (draw : X → Y) (g : Y → ℝ) :
    uniformAverage (fun x => g (draw x))=expectation (mapLaw (uniformLaw (α := X)) draw) g := by
  rw [expectation_map,expectation_uniform]

end ContingencyTables.FiniteLawMoments

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleSchedule
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit accuracy and sample-count parameters for the weight oracle -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma sampleCount_positive (j : ℕ) (delta failure : ℚ) (hdelta : 0 < delta)
    (hfailure : 0 < failure) : 0 < sampleCount j delta failure := by
  have hh := Nat.le_ceil (65536*(j+1:ℚ)/(failure*delta^2))
  have hp : (0:ℚ) < sampleCount j delta failure := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast hp

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEstimatorConfidence
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma innerTolerance_pos (epsilon : ℚ) (j : ℕ) (he : 0 < epsilon) :
    0 < innerTolerance epsilon j := by unfold innerTolerance; positivity

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCut
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit endpoint on the side away from a selected root

One reachability test in the edge-deleted forest selects the endpoint.
No choice of a component representative or of a cut vertex is needed.
-/

namespace ContingencyTables.RootedCut

open scoped BigOperators Classical
open SimpleGraph MaximumForest RootedCompletion GraphCompletionCounts ForestCut
open ForestCapacity

variable {V : Type*}

theorem selected_nonroot (T : SimpleGraph V) (S : Selection T) (hT : T.IsAcyclic)
    {u v a : V} (ht : T.Adj u v) (ha : cut T u v (S.root u) a=true) : a≠S.root a := by
  intro he
  have hp := away_properties T hT ht (S.root u) (S.reachable u).symm
  have hreach : (T.deleteEdges {s(u,v)}).Reachable (away T u v (S.root u)) a := by
    simpa only [cut,side,decide_eq_true_eq] using ha
  have hcomp := hp.1.trans (hreach.mono (T.deleteEdges_le {s(u,v)}))
  have hsame : S.root a=S.root u :=
    (S.constant hcomp).symm.trans (S.idempotent u)
  have hae : a=S.root u := he.trans hsame
  have hbad : cut T u v (S.root u) (S.root u)=true := by simpa only [hae] using ha
  exact Bool.false_ne_true (hp.2.1.symm.trans hbad)

variable {I J : Type*}

lemma treeCut_nonroot (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) (v : I⊕J) (hv : treeCut T S t v=true) : v≠S.root v :=
  selected_nonroot T S hT t.property hv

lemma sign_abs_le_one (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) : |sign T S t a|≤1 := by
  unfold sign
  cases treeCut T S t (.inl a.1) <;> cases treeCut T S t (.inr a.2) <;>
    norm_num [indicator]

lemma other_tree_sign_zero (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) (ha : T.Adj (.inl a.1) (.inr a.2)) (hne : a≠t.val) :
    sign T S t a=0 := by
  have hh := side_eq_of_tree_edge T (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (away T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1))) ha
    (by intro he; exact hne (cell_edge_injective he))
  exact sub_eq_zero.mpr (congrArg indicator hh)

end ContingencyTables.RootedCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedAffine
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cut coefficients for an explicitly selected forest root

The same signed cut calculation applies to the executed root selector.
In particular, coefficient size and the maximum-forest capacity bound
do not depend on a classical choice of cut representative.
-/

namespace ContingencyTables.RootedAffine

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedCut GraphCompletionCounts
open ForestCapacity ForestCut MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

lemma coefficient_abs_le_one (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : |coefficient A S t a|≤1 := by
  unfold coefficient
  split_ifs
  · rw [abs_div,abs_neg,sign_abs_self A.T S A.hT,div_one]
    exact sign_abs_le_one A.T S t a
  · norm_num

lemma capacity_le_of_coefficient_ne_zero (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) (ha : coefficient A S t a≠0) :
    A.b a.1 a.2≤A.b t.val.1 t.val.2 := by
  have hf : A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2) := by
    by_contra hn
    exact ha (by simp only [coefficient,hn,ite_false])
  have hcross : treeCut A.T S t (.inl a.1)≠treeCut A.T S t (.inr a.2) := by
    intro he
    apply ha
    simp [coefficient,hf,sign,he]
  have h := crossing_free_edge_le (cellGraph A.small) A.T (capacity A.b)
    A.hTG A.hT A.hmax (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (by simpa using t.property)
    (away A.T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1)))
    (show (cellGraph A.small).Adj (.inl a.1) (.inr a.2) from hf.1) hf.2 hcross
  simpa only [capacity_cell] using h

theorem normalized_coefficient_bound (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) (B : ℝ) (hB : 0<B) :
    |coefficient A S t a*((A.b a.1 a.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)|≤2/B := by
  have hb : (1:ℝ)≤A.b t.val.1 t.val.2 := by
    exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
  by_cases ha : coefficient A S t a=0
  · simp only [ha,zero_mul,zero_div,abs_zero]
    positivity
  have hcap : (A.b a.1 a.2:ℝ)≤A.b t.val.1 t.val.2 := by
    exact_mod_cast capacity_le_of_coefficient_ne_zero A S t a ha
  rw [abs_div,abs_div,abs_mul,abs_of_pos hB,
    abs_of_pos (by linarith : (0:ℝ)<A.b t.val.1 t.val.2),
    abs_of_nonneg (by positivity : (0:ℝ)≤(A.b a.1 a.2:ℝ)+1)]
  apply (div_le_iff₀ (by linarith : (0:ℝ)<A.b t.val.1 t.val.2)).mpr
  rw [div_le_iff₀ hB]
  have hh := mul_le_mul_of_nonneg_right (coefficient_abs_le_one A S t a)
    (by positivity : (0:ℝ)≤(A.b a.1 a.2:ℝ)+1)
  field_simp [hB.ne']
  nlinarith

theorem affine_of_nonroot_equations (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q z : I → J → ℝ)
    (hr : ∀ i,Sum.inl i≠S.root (.inl i) →
      rowDifference A.small x z (fun i j => (A.X i j:ℝ)) i=0)
    (hc : ∀ j,Sum.inr j≠S.root (.inr j) →
      columnDifference A.small q z (fun i j => (A.X i j:ℝ)) j=0) :
    z t.val.1 t.val.2=affineTree A S t x q (fun a => z a.1 a.2) := by
  let f : I×J → ℝ := fun a => cutTerm A.small
    (fun i => treeCut A.T S t (.inl i)) (fun j => treeCut A.T S t (.inr j))
    x q z (fun i j => (A.X i j:ℝ)) a.1 a.2
  have hsum : (∑ a,f a)=0 := by
    rw [Fintype.sum_prod_type]
    exact cut_sum_zero A.small _ _ x q z _
      (fun i hi => hr i (treeCut_nonroot A.T S A.hT t (.inl i) hi))
      (fun j hj => hc j (treeCut_nonroot A.T S A.hT t (.inr j) hj))
  have hterm (a : I×J) : f a=
      (if a=t.val then sign A.T S t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)+
      (if A.small a.1 a.2 then
        indicator (treeCut A.T S t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          indicator (treeCut A.T S t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0)-
      sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2) := by
    by_cases he : a=t.val
    · subst a
      have hs : A.small t.val.1 t.val.2=false := A.hTG t.property
      simp only [f,cutTerm,hs,Bool.false_eq_true,ite_false,ite_true, if_true,coefficient,t.property,
        not_true_eq_false,and_false,sign,mul_zero,zero_mul,add_zero,sub_zero]
    · by_cases hs : A.small a.1 a.2=true
      · simp [f,cutTerm,hs,he,coefficient]
      · have hs' : A.small a.1 a.2=false := Bool.eq_false_iff.mpr hs
        by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
        · have hz := other_tree_sign_zero A.T S t a ht he
          simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_true_eq_false,and_false,zero_add,mul_zero,zero_mul,sub_zero]
          change sign A.T S t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=0
          rw [hz,zero_mul]
        · simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_false_eq_true,and_self,ite_true, if_true,zero_add,zero_sub]
          change sign A.T S t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=
            -(sign A.T S t t.val*(-sign A.T S t a/sign A.T S t t.val)*
              (z a.1 a.2-A.X a.1 a.2))
          field_simp [sign_self_ne_zero A.T S A.hT t]
  simp_rw [hterm] at hsum
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hsum
  have hsingle : (∑ a : I×J,
      if a=t.val then sign A.T S t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)=
      sign A.T S t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2) := by simp
  rw [hsingle] at hsum
  change sign A.T S t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2)+
    smallContribution A S t x q-
    (∑ a : I×J,sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2))=0 at hsum
  have hprod : (∑ a : I×J,sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2))=
      sign A.T S t t.val*((∑ a : I×J,coefficient A S t a*z a.1 a.2)-
        ∑ a : I×J,coefficient A S t a*(A.X a.1 a.2:ℝ)) := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hprod] at hsum
  unfold affineTree AffinePenalty.affineValue offset
  apply mul_left_cancel₀ (sign_self_ne_zero A.T S A.hT t)
  rw [mul_add,mul_sub,mul_sub,←mul_div_assoc,
    mul_div_cancel_left₀ _ (sign_self_ne_zero A.T S A.hT t)]
  nlinarith [hsum]

end ContingencyTables.RootedAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalCompletion
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residual completion for the executed root convention

The row and column small views remain distinct. The explicit selected
roots determine which incidence equations are enforced; the resulting
integral completion is exactly the selected-cut affine formula.
-/

namespace ContingencyTables.RootedPhysicalCompletion

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedAffine GraphCompletionCounts ForestCut
open ForestPhysicalCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The cut-defined coefficients evaluate the actual integral solution
for this root convention, including every unbalanced small profile. -/
theorem solved_eq_affine (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T)
    (x q free : I → J → ℤ) :
    (solved A S x q free t.val.1 t.val.2:ℝ)=
      affineTree A S t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
        (fun a => (free a.1 a.2:ℝ)) := by
  let z : I → J → ℝ := fun i j => (completed A S x q free i j:ℝ)
  have hh := affine_of_nonroot_equations A S t (fun i j => (x i j:ℝ))
    (fun i j => (q i j:ℝ)) z (by
      intro i hi
      have hr := row_completed_sum A S x q free i hi
      unfold rowDifference
      have he : (∑ j,if A.small i j then (x i j:ℝ) else z i j)=(A.r i:ℝ) := by
        dsimp only [z]
        exact_mod_cast hr
      have hX : (∑ j,(A.X i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast A.hXr i
      calc
        _=(∑ j,if A.small i j then (x i j:ℝ) else z i j)-(∑ j,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self]) (by
      intro j hj
      have hc := column_completed_sum A S x q free j hj
      unfold columnDifference
      have he : (∑ i,if A.small i j then (q i j:ℝ) else z i j)=(A.c j:ℝ) := by
        dsimp only [z]
        exact_mod_cast hc
      have hX : (∑ i,(A.X i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast A.hXc j
      calc
        _=(∑ i,if A.small i j then (q i j:ℝ) else z i j)-(∑ i,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self])
  have hz : z t.val.1 t.val.2=(solved A S x q free t.val.1 t.val.2:ℝ) := by
    simp only [z,completed,t.property,ite_true, if_true]
  rw [hz] at hh
  rw [hh]
  unfold affineTree AffinePenalty.affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
  · simp only [coefficient,ht,not_true_eq_false,and_false,ite_false,zero_mul]
  · simp only [z,completed,ht,ite_false]

end ContingencyTables.RootedPhysicalCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root discrepancy is independent of the free entries

Every large-cell edge stays in a maximum-forest component.  Its two
incidences therefore cancel in the selected-root component sum.
-/

namespace ContingencyTables.RootedRootPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open ForestPhysicalCompletion (rowResidual columnResidual fixedRow fixedColumn)
open ForestRootPenalty (residualDemand smallDemand)

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma componentSum_decidable (A : Instance I J) (S : Selection A.T)
    (d : I⊕J → ℤ) (a : I⊕J) :
    (∑ v,@ite ℤ (S.root v=a) (Classical.propDecidable _) (d v) 0)=
      ∑ v,if S.root v=a then d v else 0 := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : S.root v=a <;> simp only [h,ite_true, if_true,ite_false]

lemma root_eq_large (A : Instance I J) (S : Selection A.T) (i : I) (j : J)
    (hs : A.small i j=false) : S.root (.inl i)=S.root (.inr j) := by
  have hcap : ∀ e∈(ForestCapacity.cellGraph A.small).edgeSet,0<ForestCapacity.capacity A.b e := by
    intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    have hg : (ForestCapacity.cellGraph A.small).Adj u v := by simpa using he
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim hg
      | inr j => exact (A.hlarge i j hg).2
    | inr j =>
      cases v with
      | inl i => exact (A.hlarge i j hg).2
      | inr j' => exact False.elim hg
  have hspans := MaximumForest.maximum_spans (ForestCapacity.cellGraph A.small) A.T
    (ForestCapacity.capacity A.b) A.hTG A.hT A.hmax hcap
  apply S.constant
  rw [hspans]
  exact (show (ForestCapacity.cellGraph A.small).Adj (.inl i) (.inr j) from hs).reachable

lemma componentTotal_residual (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (a : I⊕J) :
    componentTotal A S (residualDemand A.small A.T A.r A.c x q free) a=
      componentTotal A S (smallDemand A.small A.X x q) a := by
  let R : I → ℤ := fun i => if S.root (.inl i)=a then 1 else 0
  let C : J → ℤ := fun j => if S.root (.inr j)=a then 1 else 0
  have hrow (i : I) : R i*rowResidual A.small A.T A.r x free i=
      ∑ j,R i*(A.X i j-fixedRow A.small A.T x free i j) := by
    rw [rowResidual,←A.hXr i,←Finset.sum_sub_distrib,Finset.mul_sum]
  have hcol (j : J) : C j*(-columnResidual A.small A.T A.c q free j)=
      ∑ i,C j*(fixedColumn A.small A.T q free i j-A.X i j) := by
    rw [columnResidual,←A.hXc j,neg_sub,←Finset.sum_sub_distrib,Finset.mul_sum]
  unfold componentTotal residualDemand smallDemand
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  change (∑ i,R i*rowResidual A.small A.T A.r x free i)+
      (∑ j,C j*(-columnResidual A.small A.T A.c q free j))=
    (∑ i,R i*(∑ j,if A.small i j then A.X i j-x i j else 0))+
      ∑ j,C j*(∑ i,if A.small i j then q i j-A.X i j else 0)
  simp_rw [hrow,hcol,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => C j*(fixedColumn A.small A.T q free i j-A.X i j)),
    Finset.sum_comm (f := fun j i => C j*(if A.small i j then q i j-A.X i j else 0)),
    ←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : A.small i j=true
  · simp [fixedRow,fixedColumn,hs]
  · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
    have he : R i=C j := by unfold R C; rw [root_eq_large A S i j hs']
    rw [he]
    simp only [fixedRow,fixedColumn,hs',Bool.false_eq_true,ite_false]
    ring

lemma table_row_all (A : Instance I J) (S : Selection A.T)
    (r : I → ℤ) (c : J → ℤ) (i : I) :
    (∑ j,table A.T S r c i j)=
      r i-∑ v,if S.root v=Sum.inl i then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := flow_divergence_all S (Sum.elim r (fun j => -c j)) (.inl i)
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ i',flow S (Sum.elim r (fun j => -c j)) (.inl i) (.inl i'))=0 := by
    apply Finset.sum_eq_zero
    intro i' _
    apply flow_supported
    intro h
    exact A.hTG h
  simp only [hz,zero_add,Sum.elim_inl] at hs
  rw [componentSum_decidable] at hs
  simpa only [table] using hs

lemma table_column_all (A : Instance I J) (S : Selection A.T)
    (r : I → ℤ) (c : J → ℤ) (j : J) :
    -(∑ i,table A.T S r c i j)=
      -c j-∑ v,if S.root v=Sum.inr j then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := flow_divergence_all S (Sum.elim r (fun j => -c j)) (.inr j)
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ j',flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inr j'))=0 := by
    apply Finset.sum_eq_zero
    intro j' _
    apply flow_supported
    intro h
    exact A.hTG h
  have hskew : (∑ i,flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inl i))=
      -(∑ i,table A.T S r c i j) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact flow_skew S _ _ _
  simp only [hz,add_zero,Sum.elim_inr,hskew] at hs
  rw [componentSum_decidable] at hs
  exact hs

theorem signedResidual_eq_small (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (a : I⊕J) :
    signedResidual A S x q free a=-componentTotal A S (smallDemand A.small A.X x q) a := by
  suffices he : signedResidual A S x q free a=
      -componentTotal A S (residualDemand A.small A.T A.r A.c x q free) a by
    rw [he,componentTotal_residual]
  have htotal : ∀ d : I⊕J → ℤ,
      (∑ v,if S.root v=a then d v else 0)=componentTotal A S d a := by
    intro d
    simp [componentTotal,ite_mul]
  cases a with
  | inl i =>
    simp only [signedResidual,Sum.elim_inl]
    simp_rw [row_pointwise]
    rw [Finset.sum_add_distrib]
    have hr := table_row_all A S (rowResidual A.small A.T A.r x free)
      (columnResidual A.small A.T A.c q free) i
    change (∑ j,solved A S x q free i j)=_ at hr
    rw [hr,htotal]
    unfold residualDemand rowResidual columnResidual
    ring
  | inr j =>
    simp only [signedResidual,Sum.elim_inr]
    simp_rw [column_pointwise]
    rw [Finset.sum_add_distrib]
    have hc := table_column_all A S (rowResidual A.small A.T A.r x free)
      (columnResidual A.small A.T A.c q free) j
    change -(∑ i,solved A S x q free i j)=_ at hc
    have hc' : (∑ i,solved A S x q free i j)=columnResidual A.small A.T A.c q free j+
        ∑ v,if S.root v=Sum.inr j then
          Sum.elim (rowResidual A.small A.T A.r x free)
            (fun j => -columnResidual A.small A.T A.c q free j) v else 0 := by linarith
    rw [hc',htotal]
    unfold residualDemand rowResidual columnResidual
    ring

end ContingencyTables.RootedRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the physical scaled Lipschitz bound for selected roots -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedRootPenalty
open ForestScaledPenalty (intervalCost intervalCost_nonnegative intervalCost_change
  free_card_le tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem penalty_change (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (x q : I → J → ℤ)
    (v w : FreeCell A.small A.T → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ f,|v f-w f|≤ r) :
    |penalty A S C B x q v-penalty A S C B x q w|≤(2*C*(A.d:ℝ)^2/B)*r := by
  have hterm (t : TreeCell A.T) :
      |intervalCost (scaledTree A S B x q v t)-intervalCost (scaledTree A S B x q w t)|≤
        (A.d:ℝ)*(2/B)*r := by
    apply (intervalCost_change _ _).trans
    have hh := AffinePenalty.affineValue_change (normalizedOffset A S t x q)
      (normalizedCoefficient A S B t) v w (2/B) r (by positivity)
      (fun f => normalized_coefficient_bound A S t f.val B hB) hvw
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast free_card_le A) (by positivity : (0:ℝ)≤2/B)) hr)
  have he : penalty A S C B x q v-penalty A S C B x q w=
      C*∑ t : TreeCell A.T,(intervalCost (scaledTree A S B x q v t)-
        intervalCost (scaledTree A S B x q w t)) := by
    unfold penalty
    rw [Finset.sum_sub_distrib]
    ring
  rw [he,abs_mul,abs_of_nonneg hC]
  calc
    _≤ C*∑ t : TreeCell A.T,|intervalCost (scaledTree A S B x q v t)-
      intervalCost (scaledTree A S B x q w t)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hC
    _≤ C*∑ _t : TreeCell A.T,(A.d:ℝ)*(2/B)*r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hterm t)) hC
    _=C*((Fintype.card (TreeCell A.T):ℝ)*((A.d:ℝ)*(2/B)*r)) := by simp
    _≤ C*((A.d:ℝ)*((A.d:ℝ)*(2/B)*r)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by exact_mod_cast tree_card_le A) (by positivity)) hC
    _=_ := by ring

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root geometric density is the literal completion weight -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedPhysicalCompletion RootedRootPenalty
open ForestScaledPenalty (integerCube intervalCost intervalCost_div )

variable {I J : Type*} [Fintype I] [Fintype J]

lemma free_coefficient_sum (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (F : I×J → ℝ) :
    (∑ f : FreeCell A.small A.T,coefficient A S t f.val*F f.val)=
      ∑ a : I×J,coefficient A S t a*F a := by
  let p : I×J → Prop := fun a => A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  calc
    _=∑ a ∈ Finset.univ.filter p,coefficient A S t a*F a :=
      (Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun _ => by simp)
        (fun a => coefficient A S t a*F a)).symm
    _=_ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ ha
      have hp : ¬p a := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using ha
      change ¬(A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)) at hp
      simp only [coefficient,hp,ite_false,zero_mul]

theorem scaledTree_integer (A : Instance I J) (S : Selection A.T) (B : ℝ) (hB : 0<B)
    (x q : I → J → ℤ) (f : FreeIndex A.small A.T A.b) (t : TreeCell A.T) :
    scaledTree A S B x q (integerCube A B f) t=
      (solved A S x q (fun i j => (freeTable A.small A.T A.b f i j:ℤ))
        t.val.1 t.val.2:ℝ)/(A.b t.val.1 t.val.2:ℝ) := by
  let F : I×J → ℝ := fun a => (freeTable A.small A.T A.b f a.1 a.2:ℝ)
  have hterm (a : FreeCell A.small A.T) :
      normalizedCoefficient A S B t a*integerCube A B f a=
        coefficient A S t a.val*F a.val/(A.b t.val.1 t.val.2:ℝ) := by
    have hN : (A.b a.val.1 a.val.2:ℝ)+1≠0 := by positivity
    have hbt : (A.b t.val.1 t.val.2:ℝ)≠0 := by
      exact_mod_cast (Nat.ne_of_gt (A.hlarge _ _ (A.hTG t.property)).2)
    have hF : F a.val=(f a).val := by simp [F,freeTable,a.property]
    rw [hF]
    unfold normalizedCoefficient integerCube
    field_simp [hB.ne',hN,hbt]
  unfold scaledTree AffinePenalty.affineValue normalizedOffset
  simp_rw [hterm]
  rw [←Finset.sum_div,free_coefficient_sum,←add_div]
  have hh := solved_eq_affine A S t x q (fun i j => (freeTable A.small A.T A.b f i j:ℤ))
  unfold affineTree AffinePenalty.affineValue at hh
  apply congrArg (fun z : ℝ => z/(A.b t.val.1 t.val.2:ℝ))
  simpa only [F,Int.cast_natCast] using hh.symm

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source height bounds the entire selected-root density cube -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedRootPenalty RootedPhysicalCompletion BalancedBox
open ForestScaledPenalty (rowCounts columnCounts rowCounts_bounds columnCounts_bounds
  intervalCost intervalCost_div integerCube integerCube_zero zeroAssignment tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rootConstant_bound (A : Instance I J) (S : Selection A.T)
    (z : View A → ℕ) (hz : InBox (bounds A) z) :
    rootConstant A S (rowCounts A z) (columnCounts A z)≤2*(A.d:ℝ)*A.W := by
  let d := ForestRootPenalty.smallDemand A.small A.X (rowCounts A z) (columnCounts A z)
  have he (a : I⊕J) : (signedResidual A S (rowCounts A z) (columnCounts A z) 0 a:ℝ)=
      -(∑ v,if S.root v=a then (d v:ℝ) else 0) := by
    rw [signedResidual_eq_small]
    unfold componentTotal
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : S.root v=a <;> simp [hv,d]
  have hrow (i : I) : |((∑ j,if A.small i j then A.X i j-rowCounts A z i j else 0:ℤ):ℝ)|≤
      ∑ j,if A.small i j then (A.b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hs : A.small i j=true
    · simp only [hs,ite_true, if_true]
      have hh : |A.X i j-rowCounts A z i j|≤(A.b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(rowCounts_bounds A z hz i j hs).1,
          (rowCounts_bounds A z hz i j hs).2,(A.hX i j).1,(A.hX i j).2]
      exact_mod_cast hh
    · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hcol (j : J) : |((∑ i,if A.small i j then columnCounts A z i j-A.X i j else 0:ℤ):ℝ)|≤
      ∑ i,if A.small i j then (A.b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    by_cases hs : A.small i j=true
    · simp only [hs,ite_true, if_true]
      have hh : |columnCounts A z i j-A.X i j|≤(A.b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(columnCounts_bounds A z i j).1,
          (columnCounts_bounds A z i j).2,(A.hX i j).1,(A.hX i j).2]
      exact_mod_cast hh
    · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hdemand : (∑ a,|(d a:ℝ)|)≤2*∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0 := by
    rw [Fintype.sum_sum_type]
    change (∑ i,|((∑ j,if A.small i j then A.X i j-rowCounts A z i j else 0:ℤ):ℝ)|)+
      (∑ j,|((∑ i,if A.small i j then columnCounts A z i j-A.X i j else 0:ℤ):ℝ)|)≤_
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
    have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcol j)
    rw [Finset.sum_comm] at hc
    linarith
  have hsmall : (∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0)≤(A.d:ℝ)*A.W := by
    calc
      _≤∑ _i : I,∑ _j : J,(A.W:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        cases hs : A.small i j
        · simp only [Bool.false_eq_true,ite_false]
          positivity
        · simp only [ite_true, if_true]
          exact_mod_cast (A.hsmall i j hs).le
      _=(Fintype.card I*Fintype.card J:ℕ)*(A.W:ℝ) := by simp; ring
      _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast A.hcard) (Nat.cast_nonneg _)
  unfold rootConstant
  calc
    _≤∑ a,|(signedResidual A S (rowCounts A z) (columnCounts A z) 0 a:ℝ)| := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs <;> first | exact le_rfl | exact abs_nonneg _
    _=∑ a,|∑ v,if S.root v=a then (d v:ℝ) else 0| := by simp_rw [he,abs_neg]
    _≤∑ v,|(d v:ℝ)| := ForestRootPenalty.sum_abs_componentTotal S.root (fun v => (d v:ℝ))
    _≤_ := hdemand.trans (by linarith)

lemma zero_tree_bound (A : Instance I J) (S : Selection A.T) (B : ℝ) (hB : 0<B)
    (z : View A → ℕ) (hz : InBox (bounds A) z) (t : TreeCell A.T) :
    intervalCost (scaledTree A S B (rowCounts A z) (columnCounts A z) 0 t)≤10*(A.d:ℝ) := by
  have hzero : (fun i j => (freeTable A.small A.T A.b (zeroAssignment A) i j:ℤ))=0 := by
    funext i j
    unfold freeTable zeroAssignment
    split_ifs <;> rfl
  have hinterval := RootedIntervals.solved_in_intervals A S
    (rowCounts A z) (columnCounts A z) 0
    (by intro i j hs; exact ⟨rowCounts_bounds A z hz i j hs,columnCounts_bounds A z i j⟩)
    (by intro i j _ _; exact ⟨le_rfl,Nat.cast_nonneg _⟩)
    t.val.1 t.val.2 t.property
  rw [←integerCube_zero A B,scaledTree_integer A S B hB,hzero,intervalCost_div]
  · have hb : (0:ℝ)<A.b t.val.1 t.val.2 := by exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
    rw [div_le_iff₀ hb]
    have hlo : -(10*(A.d:ℝ)*A.b t.val.1 t.val.2)≤
        (solved A S (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ) := by
      exact_mod_cast hinterval.1
    have hup : (solved A S (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ)≤
        10*(A.d:ℝ)*A.b t.val.1 t.val.2 := by exact_mod_cast hinterval.2
    apply max_le
    · positivity
    · apply max_le <;> linarith
  · exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2

theorem penalty_cube_bound (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (v : FreeCell A.small A.T → ℝ) (hv : ∀ f,0≤ v f ∧ v f≤ B) :
    0≤ penalty A S C B (rowCounts A z) (columnCounts A z) v ∧
      penalty A S C B (rowCounts A z) (columnCounts A z) v≤ C*(10*(A.d:ℝ)^2*((A.W:ℝ)+1)) := by
  have hzero : penalty A S C B (rowCounts A z) (columnCounts A z) 0≤
      C*(2*(A.d:ℝ)*A.W+10*(A.d:ℝ)^2) := by
    unfold penalty
    apply mul_le_mul_of_nonneg_left _ hC
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => zero_tree_bound A S B hB z hz t)
    have ht : (∑ t : TreeCell A.T,intervalCost (scaledTree A S B (rowCounts A z) (columnCounts A z) 0 t))≤
        10*(A.d:ℝ)^2 := by
      calc
        _≤(Fintype.card (TreeCell A.T):ℝ)*(10*(A.d:ℝ)) := by simpa using hsum
        _≤(A.d:ℝ)*(10*(A.d:ℝ)) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast tree_card_le A) (by positivity)
        _=_ := by ring
    linarith [rootConstant_bound A S z hz]
  have hchange := (le_abs_self _).trans (penalty_change A S C B hC hB
    (rowCounts A z) (columnCounts A z) v 0 B hB.le (by
      intro f
      simpa only [Pi.zero_apply,sub_zero,abs_of_nonneg (hv f).1] using (hv f).2))
  have hcancel : (2*C*(A.d:ℝ)^2/B)*B=2*C*(A.d:ℝ)^2 := div_mul_cancel₀ _ hB.ne'
  rw [hcancel] at hchange
  have hd : (1:ℝ)≤ A.d := by exact_mod_cast A.hd
  have hW : (2:ℝ)≤ A.W := by exact_mod_cast A.hW
  have hscalar : 2*(A.d:ℝ)*A.W+12*(A.d:ℝ)^2≤10*(A.d:ℝ)^2*((A.W:ℝ)+1) := by
    have hdd : (A.d:ℝ)≤(A.d:ℝ)^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hdd (by positivity : (0:ℝ)≤ A.W)
    have hp' := mul_le_mul_of_nonneg_left hW (sq_nonneg (A.d:ℝ))
    nlinarith
  refine ⟨penalty_nonnegative A S C B hC _ _ v,?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hscalar hC]

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root evaluator density on its actual finite bin cube -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit
open CompanionOracleDensity (dimension index pull binWidth height)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem D_bounds (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Fin (dimension A) → ℝ) (hv : ∀ i,0≤ v i ∧ v i≤ binWidth A C) :
    0≤ D A S C z v ∧ D A S C z v≤ height A C := by
  have hh := RootedScaledPenalty.penalty_cube_bound A S C (binWidth A C) hC.le
    (CompanionOracleDensity.binWidth_positive A C hC) z hz (pull A v)
    (fun f => hv ((index A).symm f))
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  unfold height
  ring

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational grid transitions for the selected-root evaluator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open CompanionOracleDensity (dimension height binWidth height_positive oracleProposalRat oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem gridExponent_upper (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    gridExponent A R C a z v ≤ a := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have hD := D_bounds A R C hCR z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  have hH := height_positive A C hCR
  have hbound : (a:ℝ)/height A C*D A R C z (realCorner v) ≤ a := by
    calc
      _ ≤ (a:ℝ)/height A C*height A C :=
        mul_le_mul_of_nonneg_left hD.2 (div_nonneg (Nat.cast_nonneg _) hH.le)
      _ = _ := div_mul_cancel₀ _ hH.ne'
  have he := gridExponent_eq_floor A R C a z v
  have hh := (Int.floor_le ((a:ℝ)/height A C*D A R C z (realCorner v))).trans hbound
  rw [←he] at hh
  exact_mod_cast hh

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFiniteStep
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed Boolean words realize the selected-root grid chain -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity (dimension binWidth rationalHeight rationalHeight_cast oracleStepBits oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_acceptance_finite_coin (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v w : Grid (I := Fin (dimension A)) K) :
    ((Finset.univ.filter (acceptDyadic
      (gridExponent A R C a z w-gridExponent A R C a z v) (rationalHeight A C))).card:ℝ)/
        (2:ℝ)^rationalHeight A C=
      min 1 (gridWeight A R C a z w/gridWeight A R C a z v) := by
  rw [acceptDyadic_probability]
  · rw [gridWeight_eq_dyadic,gridWeight_eq_dyadic,dyadic_ratio_min]
  · exact (Nat.sub_le _ _).trans ((gridExponent_upper A R C a hC z hz hKB w).trans haH)

/-- Every valid direction has one code; unused directions, boundary
proposals and failed dyadic tests stay at the starting vertex. -/
theorem finiteOracleStepLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    finiteOracleStepLaw A R C a z v=oracleTransitionLaw A R C a z hK v := by
  apply RationalLaw.eq_of_off_diagonal _ _ v
  intro w hwv
  apply Rat.cast_injective (α := ℝ)
  change ((finiteAcceptLaw v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (gridExponent A R C a z w-gridExponent A R C a z v)
      (rationalHeight A C))).mass w:ℝ)=(oracleTransition A R C a z v w:ℝ)
  rw [finiteAcceptLaw_off_diagonal v w _ _ hwv.symm,
    axisCodeStep_count (dense_proposal_code_bound A.d (dimension A) (ForestScaledPenalty.free_card_le A))]
  simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  push_cast
  rw [Finset.filter_congr_decidable (Finset.univ : Finset (Fin (2^rationalHeight A C)))
    (acceptDyadic (gridExponent A R C a z w-gridExponent A R C a z v) (rationalHeight A C))
    (fun bits => Classical.propDecidable _)]
  rw [oracle_acceptance_finite_coin A R C a hC haH z hz hKB v w]
  unfold oracleTransition
  rw [ite_eq_right hwv.symm,add_zero,oracleMove_cast]
  unfold MetropolisChain.move binProposal
  by_cases hvw : Neighbor v w <;> simp [hvw]

lemma oracleBitStepLaw_eq_finite (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    oracleBitStepLaw A R C a z v=finiteOracleStepLaw A R C a z v := by
  let E := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)
  let f := finiteAcceptStep v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (gridExponent A R C a z w-gridExponent A R C a z v) (rationalHeight A C))
  have hf : oracleBitStep A R C a z v=fun bits => f (E bits) := by
    funext bits
    dsimp [oracleBitStep,f,E,finiteAcceptStep]
    simp only [acceptDyadic]
    cases axisCodeStep v ((pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)) bits).1 with
    | none => rfl
    | some w => dsimp only; split_ifs <;> rfl
  unfold oracleBitStepLaw
  rw [hf]
  change mapLaw (uniformLaw (α := Fin (Nat.clog 2 (8*A.d)+rationalHeight A C) → Bool))
    (fun bits => f (E bits))=_
  rw [←map_equiv E,uniform_equiv,←uniform_product]
  rfl

theorem oracleBitStepLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    oracleBitStepLaw A R C a z v=oracleTransitionLaw A R C a z hK v := by
  rw [oracleBitStepLaw_eq_finite]
  exact finiteOracleStepLaw_eq A R C a hC haH z hz hK hKB v

/-- A fixed rectangular Boolean array realizes the complete independent
finite walk whose mixing estimate was proved for the real chain. -/
theorem oracleBitWalkLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    oracleBitWalkLaw A R C a z v n=oracleWalkLaw A R C a z hK v n := by
  unfold oracleBitWalkLaw oracleWalkLaw
  rw [wordWalkLaw_eq]
  have he : (fun w : Grid (I := Fin (dimension A)) K =>
      mapLaw (uniformLaw (α := Fin (oracleStepBits A C) → Bool)) (oracleBitStep A R C a z w))=
      oracleTransitionLaw A R C a z hK := by
    funext w
    exact oracleBitStepLaw_eq A R C a hC haH z hz hK hKB w
  rw [he]

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual fixed-word corrected draws for the selected-root count -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma flatOracleWalk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*oracleStepBits A C) → Bool)) (flatOracleWalk A R C a z v n)=
      oracleBitWalkLaw A R C a z v n := by
  unfold flatOracleWalk
  rw [←map_equiv (oracleWalkWordEquiv n (oracleStepBits A C)),uniform_equiv]
  rfl

/-- One fixed Boolean word drives the bin walk and then the integer draw.
The bin-dependent interval length never changes the reserved word length. -/
theorem oracleIntegerDraw_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) :
    mapLaw (uniformLaw (α := Fin (oracleIntegerBits A C n h) → Bool))
      (oracleIntegerDraw A R C a z K hK hW v n h)=sampledIntegerLaw A R C a z K hK hW v n h := by
  unfold oracleIntegerDraw oracleIntegerBits
  dsimp only
  rw [←map_equiv (splitWordEquiv (n*oracleStepBits A C) (binWordBits A h))
    (uniformLaw (α := Fin (n*oracleStepBits A C+binWordBits A h) → Bool))
    (fun draws => flatBinDraw A K (by omega) hW (flatOracleWalk A R C a z v n draws.1) h draws.2),
    uniform_equiv,←uniform_product]
  rw [mapLaw_product_finish
    (uniformLaw (α := Fin (n*oracleStepBits A C) → Bool))
    (uniformLaw (α := Fin (binWordBits A h) → Bool))
    (flatOracleWalk A R C a z v n) (fun w bits => flatBinDraw A K (by omega) hW w h bits),
    flatOracleWalk_law]
  unfold sampledIntegerLaw
  congr 1
  funext w
  exact flatBinDraw_law A K (by omega) hW w h

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FinitePaddedAverage
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Observables of a padded and reindexed finite Boolean word -/

namespace ContingencyTables.FairBits

open CommonBasesFPRAS FirstSuccess ResidualMixture FiniteLawMoments
open scoped BigOperators Classical

noncomputable section

lemma padded_equiv_average {k N : ℕ} (hk : k ≤ N) {X : Type*} [Fintype X]
    (e : (Fin k → Bool) ≃ X) (f : X → ℝ) :
    uniformAverage (fun bits : Fin N → Bool => f (e (prefixWord hk bits)))=
      uniformAverage f := by
  have hp := word_expectation (prefixWord hk) (fun bits => f (e bits))
  rw [prefixWord_uniform,expectation_uniform] at hp
  exact hp.trans (uniformAverage_equiv e f)

end
end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the terminal coefficient without real logarithms

The source's ceiling of log₂(1/epsilon) is exactly the natural ceiling
logarithm of ceil(1/epsilon). All terminal metadata can therefore be
computed with natural and rational arithmetic.
-/

namespace ContingencyTables.CountingTerminalSchedule

open CompanionFactorialApplication CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

lemma finalPhase_eq (A : Instance I J) (L : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    CompanionTerminalApplication.finalPhase A L (epsilon:ℝ)=
      rationalHeight A (coefficient L A.d epsilon) := by
  rw [CompanionTerminalApplication.finalPhase,←coefficient_eq L A.d A.hd epsilon he]
  rfl

end
end ContingencyTables.CountingTerminalSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingParameters
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting schedules computed from the original bounded margins

The capacity-bit sum is formed after the executed endpoint translation.
All remaining dimensions, precisions, cutoffs and phase counts use the
proved rational/natural formulas. No numeric schedule hypothesis is
left to an external caller.
-/

namespace ContingencyTables.ComputedCountingParameters

open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma data_dimension (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (data hEK r c b hne epsilon he).d=dimensionAllowance (m:=m) (n:=n) := rfl

lemma binCount_cast (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (binCount r c b epsilon:ℝ)=binWidth (data hEK r c b hne epsilon he)
      (coefficient r c b epsilon) := by
  simp only [binCount,binWidth,data_dimension,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]

lemma phases_final (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    phases r c b epsilon=CompanionTerminalApplication.finalPhase
      (data hEK r c b hne epsilon he) (capacityBits r c b) ((epsilon/2:ℚ):ℝ) := by
  rw [CountingTerminalSchedule.finalPhase_eq _ _ (epsilon/2) (by positivity)]
  rfl

lemma phases_height (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    phases r c b epsilon=rationalHeight (data hEK r c b hne epsilon he)
      (coefficient r c b epsilon) := rfl

end
end ContingencyTables.ComputedCountingParameters

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial conversion between flat and rectangular grid encodings -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma flatten_matrixCode {m n : ℕ} (f : Fin (m*n) → ℕ) :
    (matrixCode (fun i j => f (finProdFinEquiv (i,j)))).flatten=List.ofFn f := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply Fin.ext
  change j.val+n*i.val=i.val*n+j.val
  ac_rfl

lemma sliceRow_ofFn {m n : ℕ} (f : Fin (m*n) → ℕ) (i : Fin m) :
    sliceRow ((n,List.ofFn f),i.val)=
      List.ofFn (fun j : Fin n => f (finProdFinEquiv (i,j))) := by
  have hbound : n ≤ m*n-i.val*n := by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul, Nat.add_comm] using h
  apply List.ext_getElem
  · simp only [sliceRow,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [sliceRow,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg f
    apply Fin.ext
    change i.val*n+j=j+n*i.val
    ac_rfl

theorem unflattenGrid_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (f : Fin (m*n) → ℕ) :
    unflattenGrid ((marginCode R,marginCode P),List.ofFn f)=
      matrixCode (fun i j => f (finProdFinEquiv (i,j))) := by
  have hrows : layoutRows ((marginCode R,marginCode P),List.ofFn f)=List.range m := by
    simp only [layoutRows,marginCode,List.tail_cons,List.length_ofFn]
  have hcols : (marginCode P).tail.length=n := by
    simp only [marginCode,List.tail_cons,List.length_ofFn]
  unfold unflattenGrid matrixCode
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,layoutRow,hcols]
    exact sliceRow_ofFn f ⟨i,him⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingCoefficientProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal coefficient computed with binary natural arithmetic -/

namespace ContingencyTables.CountingCoefficientProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial
open OffsetCountPrograms DensePrograms

lemma precision_val (e : Fraction) (hn : 0 < e.1) :
    precision e=CountingTerminalSchedule.precision (val e) := by
  unfold precision CountingTerminalSchedule.precision
  rw [ceilQuotient_eq e.2 e.1 hn]
  congr 2
  simp only [val,one_div,inv_div]

lemma allowance_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) :
    allowance ((L,d),e)=CountingTerminalSchedule.allowance L d (val e) := by
  simp only [allowance,CountingTerminalSchedule.allowance,precision_val e hn]

lemma coefficient_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) (hd : 0 < e.2) :
    coefficient ((L,d),e)=CountingTerminalSchedule.coefficient L d (val e) := by
  unfold coefficient
  rw [ceilQuotient_eq _ _ hn]
  unfold CountingTerminalSchedule.coefficient
  rw [←allowance_val L d e hn]
  congr 1
  simp only [numerator,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,val]
  field_simp

end ContingencyTables.CountingCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBaseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the capacity-bit and dimension inputs to the counting schedule -/

namespace ContingencyTables.CountingBaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open NetworkVertexCode

lemma half_val (e : TreeFraction.Fraction) : TreeFraction.val (half e)=TreeFraction.val e/2 := by
  simp only [half,TreeFraction.val,Nat.cast_mul,Nat.cast_ofNat]
  ring

lemma capacityBits_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    capacityBits (data r c b)=ComputedCountingParameters.capacityBits r c b := by
  unfold capacityBits
  rw [TightenedInputProgram.compute_code]
  simp only [data,ResidualGraphProgram.natCode,List.map_flatten,List.map_ofFn,Function.comp_def,
    List.sum_flatten,List.sum_ofFn,cellBits,ComputedCountingParameters.capacityBits,
    Fintype.sum_prod_type]

lemma dimension_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    dimension (data r c b)=ComputedCountingParameters.dimensionAllowance (m:=m) (n:=n) := by
  simp only [dimension,data,List.length_ofFn,ComputedCountingParameters.dimensionAllowance]

lemma coefficient_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    coefficient (data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.coefficient r c b epsilon := by
  unfold coefficient frame
  rw [capacityBits_data,dimension_data]
  have hn : 0 < (half (TreeFraction.repr epsilon)).1 := by
    change 0 < epsilon.num.natAbs
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr he))
  have hd : 0 < (half (TreeFraction.repr epsilon)).2 := by
    change 0 < 2*epsilon.den
    exact Nat.mul_pos (by decide) epsilon.pos
  rw [CountingCoefficientProgram.coefficient_val _ _ _ hn hd,half_val,
    TreeFraction.val_repr he.le]
  rfl

end ContingencyTables.CountingBaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BooleanChunkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial partition of a supplied Boolean word into fixed-width rows -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma wordChunk_ofFn {n k : ℕ} (bits : Fin (n*k) → Bool) (i : Fin n) :
    wordChunk ((k,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j))) := by
  have hbound : k ≤ n*k-i.val*k := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul,Nat.add_comm] using
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
  apply List.ext_getElem
  · simp only [wordChunk,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [wordChunk,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change i.val*k+j=j+k*i.val
    ac_rfl

theorem wordChunks_ofFn {n k : ℕ} (hk : 0<k) (bits : Fin (n*k) → Bool) :
    wordChunks (k,List.ofFn bits)=
      List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j)))) := by
  have hrows : completeWordRows (k,List.ofFn bits)=List.range n := by
    simp only [completeWordRows,List.length_ofFn,Nat.mul_div_cancel _ hk]
  unfold wordChunks
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hin : i<n := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact wordChunk_ofFn bits ⟨i,hin⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingLabelCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the actual number of factorial labels

Only retained capacities are summed; the program does not expand any
capacity into a list of labels to obtain the phase controls.
-/

namespace ContingencyTables.CountingLabelCountProgram
open MatchingFPRAS.TreeTyped

open CompanionFactorialApplication
open scoped BigOperators Classical
variable {m n : ℕ}

lemma catalogInput_data (A : Instance (Fin m) (Fin n)) :
    catalogInput (RootedForestCatalog.data A)=CompanionCellCatalog.input A := rfl

lemma count_data (A : Instance (Fin m) (Fin n)) :
    count (RootedForestCatalog.data A)=Fintype.card (Labels A) := by
  rw [count,capacities,catalogInput_data,CompanionCellCatalog.capacities_eq,List.sum_ofFn]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fintype.sum_equiv (CompanionCellCatalog.cellEquiv A) _ _ (fun _ => rfl)

end ContingencyTables.CountingLabelCountProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the counting oracle sample schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma ceiling_val (e : Fraction) : ceiling e=⌈TreeFraction.val e⌉₊ := by
  by_cases h : e.2=0
  · simp only [ceiling,OffsetCountPrograms.ceilQuotient,TreeFraction.val,h,Nat.div_zero,
      Nat.cast_zero,div_zero,Nat.ceil_zero]
  · exact OffsetCountPrograms.ceilQuotient_eq e.1 e.2 (Nat.pos_of_ne_zero h)

lemma natural_val (n : ℕ) : TreeFraction.val (natural n)=(n:ℚ) := by
  simp only [natural,TreeFraction.val,Nat.cast_one,div_one]

lemma sampleCount_val (j : ℕ) (delta failure : Fraction) :
    sampleCount (j,(delta,failure))=
      CompanionOracleDensity.sampleCount j (TreeFraction.val delta) (TreeFraction.val failure) := by
  rw [sampleCount,ceiling_val,sampleRatio,TreeFraction.div_val,sampleBase,natural_val,
    sampleDenominator,TreeFraction.mul_val,TreeFraction.mul_val]
  unfold CompanionOracleDensity.sampleCount
  congr 1
  push_cast
  ring

lemma offsetAccuracy_val (d : ℕ) (delta : Fraction) :
    offsetAccuracy (d,delta)=⌈4096*(d:ℚ)/TreeFraction.val delta⌉₊ := by
  rw [offsetAccuracy,ceiling_val,offsetRatio,TreeFraction.div_val,offsetBase,natural_val]
  simp only [Nat.cast_mul,Nat.cast_ofNat]


lemma oracleTime_val (M B : ℕ) (theta : Fraction) :
    oracleTime ((M,B),theta)=⌈(M:ℚ)*((B:ℚ)+16/TreeFraction.val theta)⌉₊ := by
  have he : (timeExtra ((M,B),theta)).2 ≠ 0 := by
    exact (TreeFraction.normalize_den_pos _).ne'
  rw [oracleTime,ceiling_val,timeTotal,TreeFraction.add_val _ _ (by change (1:ℕ) ≠ 0; decide) he,
    timeBase,natural_val,timeExtra,TreeFraction.div_val,timeNumerator,natural_val]
  congr 1
  push_cast
  ring

lemma oracleTime_instance {I J : Type} [Fintype I] [Fintype J]
    (A : CompanionFactorialApplication.Instance I J) (C K : ℕ) (theta : Fraction) :
    oracleTime ((2*(10000*A.d^2*K)^2,
      CompanionOracleDensity.rationalHeight A C+A.d*K+2),theta)=
      CompanionOracleDensity.oracleTime A C K 1 (TreeFraction.val theta) := by
  rw [oracleTime_val,CompanionOracleDensity.oracleTime]
  rw [←CountingTerminalSchedule.natCeil_ratCast]
  congr 1
  simp only [CompanionOracleDensity.mixingConstant,CompanionOracleDensity.rationalHeight,
    CompanionOracleDensity.height,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,
    Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_pow]
  ring

end ContingencyTables.CountingOracleScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the scalar counting schedules

These circuits only read a fixed finite list and perform binary addition
and multiplication. Their syntax describes the fixed program, not a
numeric loop selected by the input.
-/

namespace ContingencyTables.ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

lemma Expr.eval_pow (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a.pow n).eval xs=(a.eval xs)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Expr.pow,Expr.eval,ih,pow_succ]


@[simp] lemma Expr.eval_power (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a^n).eval xs=(a.eval xs)^n := Expr.eval_pow a n xs


end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed terminal grid width, cutoff and phase count -/

namespace ContingencyTables.CountingTerminalProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma binCount_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    binCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.binCount r c b epsilon := by
  unfold binCount base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data]
  unfold ComputedCountingParameters.binCount
  ring

lemma cutoff_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    cutoff (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.cutoff r c b epsilon := by
  unfold cutoff
  rw [CountingBaseProgram.dimension_data,binCount_data r c b epsilon he]
  rfl

lemma phases_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    phases (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.phases r c b epsilon := by
  unfold phases base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data,cutoff_data r c b epsilon he]
  unfold ComputedCountingParameters.phases
  ring

end ContingencyTables.CountingTerminalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedForestCode
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed forest retains its literal adjacency-list code -/

namespace ContingencyTables.ComputedLargeForest
open SimpleGraph MaximumForest ForestCapacity ForestGreedySemantics
open FiniteGraphRootProgram LargeEdgeCatalogProgram
open scoped Classical

variable {m n : ℕ}

private lemma code_congr {N : ℕ} (G H : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G=H) : graphCode G=graphCode H := by
  subst H
  apply congrArg (@graphCode N G)
  exact Subsingleton.elim _ _

lemma computed_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (hW : 1 ≤ W) :
    graphCode ((computed r c b W).comap finSumFinEquiv.symm)=
      ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W) := by
  obtain ⟨F,hF,_⟩ := iterate_optimal (graph b W) ⊥ (capacities b)
    (catalog (NetworkVertexCode.data r c b,W)) (catalog_correct r c b W)
    (capacity_positive b W hW) (MaximumForestExchange.bottom_extendible _ _)
    ((m+n)*(m+n)) (by
      have hb := unordered_pair_budget (n:=m+n)
      omega)
  have hzero (d : DecidableRel (⊥ : SimpleGraph (Fin (m+n))).Adj) :
      @graphCode (m+n) ⊥ d=ForestGreedyProgram.emptyGraph (NetworkVertexCode.data r c b,W) := by
    symm
    simp only [ForestGreedyProgram.emptyGraph,vertexCount_code,DirectedBFSCode.range_eq_map,
      ←List.ofFn_eq_map,List.map_ofFn,graphCode]
    apply congrArg List.ofFn
    funext v
    simp [adjacencyRow]
  have hout : ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)=graphCode F := by
    unfold ForestGreedyProgram.forest ForestGreedyProgram.prepare
    rw [←hzero (fun a b => Classical.propDecidable _),execute_iterate,graphCode_length]
    exact congrArg Prod.fst hF
  have hc : (computed r c b W).comap finSumFinEquiv.symm=
      decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)) := by
    ext u v
    change (decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))).Adj
      (vertexEquiv (finSumFinEquiv.symm u)) (vertexEquiv (finSumFinEquiv.symm v)) ↔ _
    simp only [vertexEquiv,Equiv.apply_symm_apply]
  have he : (computed r c b W).comap finSumFinEquiv.symm=F := by
    simpa only [hout,decoded_graphCode] using hc
  exact (code_congr _ _ he).trans hout.symm

end ContingencyTables.ComputedLargeForest

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedRootedInput
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rooted-oracle metadata from the executed original-input preprocessing -/

namespace ContingencyTables.ComputedRootedInput
open MatchingFPRAS MatchingFPRAS.TreeTyped
open DensePrograms NetworkVertexCode

open scoped Classical
variable {m n : ℕ}

lemma catalogData_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    catalogData (data r c b,W)=RootedForestCatalog.data
      (ComputedCompanionInstance.instanceData hEK r c b hne W hW) := by
  unfold catalogData forestFrame
  rw [TightenedInputProgram.compute_code]
  unfold RootedForestCatalog.data ComputedCompanionInstance.instanceData
  rw [ComputedLargeForest.computed_code _ _ _ W (by omega)]
  simp only [data,Int.toNat_natCast,ResidualGraphProgram.natCode,matrixCode]

lemma baseline_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    TightenedInputProgram.baseline (data r c b)=matrixCode
      (fun i j => ((ComputedCompanionInstance.instanceData hEK r c b hne W hW).X i j).toNat) := by
  obtain ⟨Y,hY,_,_⟩ := TightenedInputProgram.baseline_correct hEK r c b hne
  rw [hY]
  unfold matrixCode
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [ComputedCompanionInstance.instanceData,ComputedCompanionInstance.baseline,
    hY,ResidualGraphProgram.natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta,Int.toNat_natCast]

end ContingencyTables.ComputedRootedInput

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingComputedSettings
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every scalar control from the original bounded table -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingPhaseScalarProgram

open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma catalog_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedForestCatalog.data (ComputedCountingParameters.data hEK r c b hne epsilon he) := by
  unfold catalog
  rw [CountingTerminalProgram.cutoff_data r c b epsilon he]
  exact ComputedRootedInput.catalogData_instance hEK r c b hne _ _

lemma labelCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    labelCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) := by
  rw [labelCount,catalog_data hEK r c b hne epsilon he,CountingLabelCountProgram.count_data]

end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogGrid
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed catalog coordinates for the oracle grid

The executable free-cell order need not agree with `Fintype.equivFin`.
Explicit reindexing identifies the grid exponent evaluated from the
catalog-ordered list.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion
open scoped Classical

noncomputable section
variable {m n : ℕ}

lemma gridEquiv_apply (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) (i : Fin (freeCount A)) :
    gridEquiv A K v (coordinateEquiv A i)=v i := by
  change v ((coordinateEquiv A).symm (coordinateEquiv A i))=v i
  rw [Equiv.symm_apply_apply]

lemma gridEdge_iff (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v w : Grid (I := Fin (freeCount A)) K) (i : Fin (freeCount A)) :
    IsGridEdge (gridEquiv A K v,gridEquiv A K w,coordinateEquiv A i) ↔
      IsGridEdge (v,w,i) := by
  constructor
  · rintro ⟨hstep,hrest⟩
    refine ⟨?_,?_⟩
    · simpa only [corner,gridEquiv_apply] using hstep
    · intro j hj
      have hji : coordinateEquiv A j≠coordinateEquiv A i :=
        fun h => hj ((coordinateEquiv A).injective h)
      simpa only [gridEquiv_apply] using hrest (coordinateEquiv A j) hji
  · rintro ⟨hstep,hrest⟩
    refine ⟨?_,?_⟩
    · simpa only [corner,gridEquiv_apply] using hstep
    · intro j hj
      have hji : (coordinateEquiv A).symm j≠i := by
        intro h
        exact hj ((Equiv.apply_symm_apply (coordinateEquiv A) j).symm.trans
          (congrArg (coordinateEquiv A) h))
      exact hrest ((coordinateEquiv A).symm j) hji

theorem neighbor_iff (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v w : Grid (I := Fin (freeCount A)) K) :
    Neighbor (gridEquiv A K v) (gridEquiv A K w) ↔ Neighbor v w := by
  constructor
  · rintro ⟨i,side,hi⟩
    refine ⟨(coordinateEquiv A).symm i,side,?_⟩
    cases side with
    | false =>
      change IsGridEdge (gridEquiv A K w,gridEquiv A K v,i) at hi
      apply (gridEdge_iff A K w v ((coordinateEquiv A).symm i)).mp
      simpa only [Equiv.apply_symm_apply] using hi
    | true =>
      change IsGridEdge (gridEquiv A K v,gridEquiv A K w,i) at hi
      apply (gridEdge_iff A K v w ((coordinateEquiv A).symm i)).mp
      simpa only [Equiv.apply_symm_apply] using hi
  · rintro ⟨i,side,hi⟩
    refine ⟨coordinateEquiv A i,side,?_⟩
    cases side with
    | false => exact (gridEdge_iff A K w v i).mpr hi
    | true => exact (gridEdge_iff A K v w i).mpr hi

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogStep
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual oracle transition in computed catalog order

Axis proposals are uniform over a bounded dyadic code space. Changing
the coordinate order preserves their frequencies, even though it need
not preserve the value obtained from an individual proposal word.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity (oracleStepBits rationalHeight)
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma freeCount_eq (A : Instance (Fin m) (Fin n)) :
    freeCount A=CompanionOracleDensity.dimension A := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (RootedForestCatalog.freeEquiv A)

lemma freeCount_le (A : Instance (Fin m) (Fin n)) : freeCount A≤A.d := by
  rw [freeCount_eq]
  exact ForestScaledPenalty.free_card_le A

theorem finiteStepLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    finiteStepLaw A C a z v=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.finiteOracleStepLaw A (rowColumn A.T) C a z (gridEquiv A K v)) := by
  apply RationalLaw.eq_of_off_diagonal _ _ v
  intro w hw
  have hvw : v≠w := Ne.symm hw
  have he : gridEquiv A K v≠gridEquiv A K w :=
    fun h => hvw ((gridEquiv A K).injective h)
  change (finiteAcceptLaw v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun b => acceptDyadic (exponent A C a z b-exponent A C a z v)
      (rationalHeight A C))).mass w=
    (RootedOracleDensity.finiteOracleStepLaw A (rowColumn A.T) C a z
      (gridEquiv A K v)).mass (gridEquiv A K w)
  rw [finiteAcceptLaw_off_diagonal v w _ _ hvw,
    RootedOracleDensity.finiteOracleStepLaw,
    finiteAcceptLaw_off_diagonal (gridEquiv A K v) (gridEquiv A K w) _ _ he,
    axisCodeStep_count (dense_proposal_code_bound A.d (freeCount A) (freeCount_le A)),
    axisCodeStep_count (dense_proposal_code_bound A.d (CompanionOracleDensity.dimension A)
      (ForestScaledPenalty.free_card_le A)),neighbor_iff]
  rfl

lemma bitStepLaw_eq_finite (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    bitStepLaw A C a z v=finiteStepLaw A C a z v := by
  let E := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)
  let f := finiteAcceptStep v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (exponent A C a z w-exponent A C a z v) (rationalHeight A C))
  have hf : bitStep A C a z v=fun bits => f (E bits) := by
    funext bits
    dsimp [bitStep,f,E,finiteAcceptStep]
    simp only [acceptDyadic]
    cases axisCodeStep v ((pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)) bits).1 with
    | none => rfl
    | some w => dsimp only; split_ifs <;> rfl
  unfold bitStepLaw
  rw [hf]
  change mapLaw (uniformLaw (α := Fin (Nat.clog 2 (8*A.d)+rationalHeight A C) → Bool))
    (fun bits => f (E bits))=_
  rw [←map_equiv E,uniform_equiv,←uniform_product]
  rfl

/-- The actual catalog-order finite-word experiment has the exact
transition law of the oracle mixing theorem. -/
theorem bitStepLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) :
    bitStepLaw A C a z v=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK (gridEquiv A K v)) := by
  rw [bitStepLaw_eq_finite,finiteStepLaw_eq,
    RootedOracleDensity.finiteOracleStepLaw_eq A (rowColumn A.T) C a hC haH z hz hK hKB]

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPreparedState
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the immutable rooted state from the public bounded input -/

namespace ContingencyTables.CountingPreparedState
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

open CompanionFactorialApplication ForestAssignmentSplit
open scoped Classical
variable {m n : ℕ}

lemma demand_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    demand (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedDemandProgram.data (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (fun _ _ => 0) (ComputedCountingParameters.data hEK r c b hne epsilon he).b := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hc : catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=RootedForestCatalog.data A :=
    CountingComputedSettings.catalog_data hEK r c b hne epsilon he
  have hb : baseline (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      matrixCode (fun i j => (A.X i j).toNat) := by
    exact ComputedRootedInput.baseline_instance hEK r c b hne _ (ComputedCountingParameters.cutoff_two r c b epsilon he)
  have hcap : capacity (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode A.b := by
    rw [capacity,hc]
    rfl
  have hz : zeroMatrix (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode (fun (_ : Fin m) (_ : Fin n) => 0) := by
    rw [zeroMatrix,hcap]
    simp only [matrixCode,List.map_ofFn,Function.comp_def]
  unfold demand RootedDemandProgram.data
  rw [hc,hb,hz,hcap]

lemma state_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    state (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedOracleWalkProgram.data A C 0 K (fun _ => 0)
        (start A K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hp : parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)) := by
    unfold parameters
    rw [CountingBaseProgram.dimension_data,CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingBaseProgram.coefficient_data r c b epsilon he]
    rfl
  have hz : ForestCountIdentification.smallX A.small (fun _ => 0)=(fun _ _ => 0) := by
    funext i j
    simp [ForestCountIdentification.smallX]
  have hq : (fun i j => A.b i j-ForestCountIdentification.smallY A.small (fun _ => 0) i j)=A.b := by
    funext i j
    simp [ForestCountIdentification.smallY]
  unfold state RootedOracleWalkProgram.data
  rw [CountingTerminalProgram.binCount_data r c b epsilon he,hp,hz,hq,demand_data hEK r c b hne epsilon he]
  apply congrArg (fun coords => ((ComputedCountingParameters.binCount r c b epsilon,
    (((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)),
      RootedDemandProgram.data A (fun _ _ => 0) A.b)),coords))
  unfold zeroGrid catalog
  rw [CountingComputedSettings.catalog_data hEK r c b hne epsilon he]
  simp [DensePrograms.gridNatCode,start,GridBoundary.corner,RootedCatalogGrid.freeCount]

lemma start_transport (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let K := ComputedCountingParameters.binCount r c b epsilon
    RootedCatalogGrid.gridEquiv A K
      (start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))=
        ComputedCountingParameters.start hEK r c b hne epsilon he := by
  rfl

end ContingencyTables.CountingPreparedState

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionRepetitionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the confidence repetition count on a rational input -/
namespace ContingencyTables.FractionRepetitionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma count_val (x : TreeFraction.Fraction) : count x=CommonBasesFPRAS.repetitionCount (TreeFraction.val x) := by
  simp only [count,TreeFraction.normalize_repr,TreeFraction.repr,CommonBasesFPRAS.repetitionCount]
end ContingencyTables.FractionRepetitionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MedianFractionProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary fraction median with polynomial running time -/

namespace ContingencyTables.MedianFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial

lemma insert_fold (q : Fraction) (xs : List Fraction) :
    xs.reverse.foldl (fun s x => step (x,s)) (q,([],[q])) = (q,(xs,insertRaw q xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil]
    rfl

lemma insert_eq (q : Fraction) (xs : List Fraction) : insert (q,xs)=insertRaw q xs := by
  unfold insert
  rw [insert_fold]

lemma insert_pos (q : Fraction) (xs : List Fraction) (hq : 0 < q.2)
    (hx : ∀ x∈xs,0 < x.2) : ∀ y∈insertRaw q xs,0 < y.2 := by
  induction xs with
  | nil => simpa only [insertRaw,List.mem_singleton] using fun y hy => hy ▸ hq
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [insertRaw]
    split <;> intro y hy <;> simp only [List.mem_cons] at hy
    · rcases hy with rfl|hy
      · exact hxx
      · exact ht y hy
    · rcases hy with rfl|rfl|hy
      · exact hq
      · exact hxx
      · exact hx y (by simp [hy])

lemma insert_map (q : Fraction) (xs : List Fraction) (hq : 0 < q.2)
    (hx : ∀ x∈xs,0 < x.2) :
    (insertRaw q xs).map val=(xs.map val).orderedInsert (·≤·) (val q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [insertRaw,List.map_cons,List.orderedInsert_cons,TreeFraction.less_val x q hxx hq]
    by_cases h : val x < val q
    · simp [h,not_le.mpr h,ht]
    · simp [h,le_of_not_gt h]

lemma sort_cons (x : Fraction) (xs : List Fraction) : sort (x::xs)=insert (x,sort xs) := by
  simp only [sort,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma sort_pos (xs : List Fraction) (hx : ∀ x∈xs,0 < x.2) : ∀ y∈sort xs,0 < y.2 := by
  induction xs with
  | nil => simp [sort]
  | cons x xs ih =>
    rw [sort_cons,insert_eq]
    exact insert_pos x (sort xs) (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))

lemma sort_map (xs : List Fraction) (hx : ∀ x∈xs,0 < x.2) :
    (sort xs).map val=(xs.map val).mergeSort (·≤·) := by
  rw [List.mergeSort_eq_insertionSort]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ y∈xs,0 < y.2 := fun y hy => hx y (by simp [hy])
    rw [sort_cons,insert_eq,insert_map x (sort xs) (hx x (by simp)) (sort_pos xs ht),ih ht]
    rfl

lemma median_val (xs : List Fraction) :
    val (median xs)=CommonBasesFPRAS.rationalMedian (xs.map val) := by
  have hs := sort_map (xs.map TreeFraction.normalize) (by
    intro y hy
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
    exact normalize_den_pos x)
  have hm : (xs.map TreeFraction.normalize).map val=xs.map val := by
    simp only [List.map_map,Function.comp_def,normalize_val]
  rw [hm] at hs
  unfold median CommonBasesFPRAS.rationalMedian
  rw [←hs,List.length_map]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (sort (xs.map TreeFraction.normalize))[xs.length/2]? <;> simp only [Option.getD_none,Option.map_none,Option.getD_some,Option.map_some,val, Nat.cast_zero,zero_div]

end ContingencyTables.MedianFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinVectorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed independent bin-coordinate draws

Each coordinate reserves a width determined by its full range, and
uses only the prefix needed by the selected interval. The implementation
splits one Boolean list and performs binary arithmetic per coordinate.
-/

namespace ContingencyTables.BinVectorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators

lemma take_ofFn_prefix {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) :
    (List.ofFn bits).take k=List.ofFn (FirstSuccess.prefixWord hk bits) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,min_eq_left hk]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn,FirstSuccess.prefixWord,Fin.castLE]

end ContingencyTables.BinVectorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinDrawLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed bin program has the analysed independent law

The execution order is the computed free-cell catalog.  The mathematical
law uses another enumeration.  Dependent word equivalences identify their
independent Boolean inputs, while preserving each physical cell's draw.
-/

namespace ContingencyTables.RootedBinDrawLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

attribute [local instance] OAI.ContingencyTables.RootedBinDrawLaw.freeCellDecidableEq
lemma wordBits_eq (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    wordBits A h=binWordBits A h := by
  unfold wordBits binWordBits
  apply Fintype.sum_equiv (RootedCatalogGrid.coordinateEquiv A)
  intro i
  simp only [RootedCatalogGrid.coordinateEquiv,Equiv.trans_apply,
    Equiv.apply_symm_apply]

lemma draw_law (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) :
    mapLaw (uniformLaw (α := Words A h)) (draw A K hK hW v h)=
      approximateBinLaw A K hK hW (RootedCatalogGrid.gridEquiv A K v) h := by
  have he := binWordDraw_law A K hK hW (RootedCatalogGrid.gridEquiv A K v) h
  unfold draw
  rw [←FairBits.map_equiv (reindexWords A h),FairBits.uniform_equiv]
  apply RationalLaw.ext
  funext f
  exact congrArg (fun p => p.mass f) he

theorem flatDraw_law (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (wordBits A h) → Bool)) (flatDraw A K hK hW v h)=
      approximateBinLaw A K hK hW (RootedCatalogGrid.gridEquiv A K v) h := by
  unfold flatDraw
  rw [←FairBits.map_equiv (wordEquiv A h),FairBits.uniform_equiv,draw_law]

end
end ContingencyTables.RootedBinDrawLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogWalk
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing of the executed catalog-order oracle walk -/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion ResidualMixture FirstSuccess
open CompanionOracleDensity (rationalHeight oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

theorem walkLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) (N : ℕ) :
    FirstSuccess.walkLaw (bitStepLaw A C a z) v N=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK (gridEquiv A K v) N) := by
  induction N with
  | zero =>
    apply RationalLaw.ext
    funext w
    simp only [RootedOracleDensity.oracleWalkLaw,FirstSuccess.walkLaw,equivLaw,pointLaw,
      Equiv.symm_symm,Equiv.apply_eq_iff_eq]
  | succ N ih =>
    have hm (b : Grid (I := Fin (freeCount A)) K) :
        (FirstSuccess.walkLaw (bitStepLaw A C a z) v N).mass b=
          (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK
            (gridEquiv A K v) N).mass (gridEquiv A K b) :=
      congrArg (fun p => p.mass b) ih
    have hk (b w : Grid (I := Fin (freeCount A)) K) :
        (bitStepLaw A C a z b).mass w=
          (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK
            (gridEquiv A K b)).mass (gridEquiv A K w) :=
      congrArg (fun p => p.mass w) (bitStepLaw_eq A C a hC haH z hz hK hKB b)
    apply RationalLaw.ext
    funext w
    change (∑ b,(FirstSuccess.walkLaw (bitStepLaw A C a z) v N).mass b*
        (bitStepLaw A C a z b).mass w)=
      ∑ b,(RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK
        (gridEquiv A K v) N).mass b*
        (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK b).mass
          (gridEquiv A K w)
    simp_rw [hm,hk]
    exact Fintype.sum_equiv (gridEquiv A K) _ _ (fun _ => rfl)

theorem wordWalkLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) (N : ℕ) :
    FirstSuccess.wordWalkLaw (bitStep A C a z) v N=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK (gridEquiv A K v) N) := by
  rw [FirstSuccess.wordWalkLaw_eq]
  exact walkLaw_eq A C a hC haH z hz hK hKB v N

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFlatProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial flat-word program for the actual oracle walk -/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

noncomputable section
variable {m n : ℕ}

lemma stepWidth_pos (A : Instance (Fin m) (Fin n)) (C : ℕ) (hC : 0 < C) :
    0 < CompanionOracleDensity.oracleStepBits A C := by
  have hd : 0 < A.d := lt_of_lt_of_le Nat.zero_lt_one A.hd
  have hh : 0 < CompanionOracleDensity.rationalHeight A C := by
    unfold CompanionOracleDensity.rationalHeight
    positivity
  exact hh.trans_le (Nat.le_add_left _ _)

lemma flatGridWalk_law (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ) :
    mapLaw (uniformLaw (α := Fin (N*CompanionOracleDensity.oracleStepBits A C) → Bool))
      (flatGridWalk A C a z v N)=wordWalkLaw (RootedCatalogGrid.bitStep A C a z) v N := by
  unfold flatGridWalk
  rw [←FairBits.map_equiv (gridWordEquiv N (CompanionOracleDensity.oracleStepBits A C)),
    FairBits.uniform_equiv]
  rfl

end
end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law of the executed correction sample

The two coordinate enumerations need not agree on a fixed bit string.
Their independent finite-word laws agree, which preserves every real
observable of the computed rational sample.
-/

namespace ContingencyTables.RootedCorrectionSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FairBits
open CommonBasesFPRAS FiniteLawMoments
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

attribute [local instance] OAI.ContingencyTables.RootedCorrectionSampleLaw.freeCellDecidableEq
private lemma bind_equiv {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (p : RationalLaw X) (e : X ≃ Y) (f : Y → RationalLaw Z) :
    bindLaw (equivLaw e p) f=bindLaw p (fun x => f (e x)) := by
  apply RationalLaw.ext
  funext z
  change (∑ y,p.mass (e.symm y)*(f y).mass z)=∑ x,p.mass x*(f (e x)).mass z
  symm
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Equiv.symm_apply_apply])

lemma integerDraw_law (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hKB : (K:ℝ) ≤ binWidth A C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ) :
    mapLaw (uniformLaw (α := Words A C N h)) (integerDraw A C a K hK hW z v N h)=
      RootedOracleDensity.sampledIntegerLaw A (RootedCompletion.rowColumn A.T) C a z K hK hW
        (RootedCatalogGrid.gridEquiv A K v) N h := by
  unfold integerDraw
  rw [←uniform_product]
  rw [mapLaw_product_finish
    (uniformLaw (α := Fin (N*oracleStepBits A C) → Bool))
    (uniformLaw (α := Fin (RootedBinDrawLaw.wordBits A h) → Bool))
    (RootedOracleWalkProgram.flatGridWalk A C a z v N)
    (fun w bits => RootedBinDrawLaw.flatDraw A K (by omega) hW w h bits)]
  rw [RootedOracleWalkProgram.flatGridWalk_law]
  have hb (w : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :=
    RootedBinDrawLaw.flatDraw_law A K (by omega) hW w h
  simp_rw [hb]
  rw [RootedCatalogGrid.wordWalkLaw_eq A C a hC haH z hz hK hKB]
  rw [bind_equiv]
  unfold RootedOracleDensity.sampledIntegerLaw
  rw [RootedOracleDensity.oracleBitWalkLaw_eq A (RootedCompletion.rowColumn A.T)
    C a hC haH z hz hK hKB]
  congr 1
  funext w
  simp only [Equiv.apply_symm_apply]

/-- Equality for arbitrary observables is exact equality in distribution
of the executed rational sample and the analysed correction sample. -/
theorem sample_average (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hKB : (K:ℝ) ≤ binWidth A C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z) (sigma : ℚ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ) (g : ℚ → ℝ) :
    uniformAverage (fun bits : Words A C N h => g (sample A C a K hK hW z sigma v N h bits))=
      uniformAverage (fun bits : Fin (oracleIntegerBits A C N h) → Bool =>
        g (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T) C a z K
          hK hW sigma (RootedCatalogGrid.gridEquiv A K v) N h bits)) := by
  let obs := fun f : FreeIndex A.small A.T A.b =>
    g (RootedOracleDensity.computedCorrection A (RootedCompletion.rowColumn A.T) C a z K
      (by omega) sigma f)
  have hleft := word_expectation (integerDraw A C a K hK hW z v N h) obs
  have hright := word_expectation
    (RootedOracleDensity.oracleIntegerDraw A (RootedCompletion.rowColumn A.T) C a z K hK hW
      (RootedCatalogGrid.gridEquiv A K v) N h) obs
  rw [integerDraw_law A C a K hC haH hK hW hKB z hz v N h] at hleft
  rw [RootedOracleDensity.oracleIntegerDraw_law] at hright
  exact hleft.trans hright.symm

end
end ContingencyTables.RootedCorrectionSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteObservableTransport
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transport of finite experiments with rational outputs

Output values need not form a finite type. Equality against every real
observable is preserved by deterministic postprocessing and by the
independent arrays used in the counting estimator.
-/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

noncomputable section
variable {X Y U V Z W : Type*}
variable [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

lemma SameLaw.map {f : X → Z} {g : Y → Z} (h : SameLaw f g) (F : Z → W) :
    SameLaw (fun x => F (f x)) (fun y => F (g y)) := by
  intro phi
  exact h (fun z => phi (F z))

lemma SameLaw.prod {f : X → Z} {g : Y → Z} {a : U → W} {b : V → W}
    (hfg : SameLaw f g) (hab : SameLaw a b) :
    SameLaw (fun x : X×U => (f x.1,a x.2)) (fun y : Y×V => (g y.1,b y.2)) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hinner (x : X) :
      uniformAverage (fun u : U => phi (f x,a u))=
        uniformAverage (fun v : V => phi (f x,b v)) :=
    hab (fun w => phi (f x,w))
  simp_rw [hinner]
  exact hfg (fun z => uniformAverage (fun v : V => phi (z,b v)))

lemma SameLaw.independent {f : X → Z} {g : Y → Z} (h : SameLaw f g) (N : ℕ) :
    SameLaw (fun xs : Fin N → X => fun i => f (xs i))
      (fun ys : Fin N → Y => fun i => g (ys i)) := by
  intro phi
  exact uniformAverage_independent_eq f g h N phi

lemma indexed (N : ℕ) (f : Fin N → X → Z) (g : Fin N → Y → Z)
    (h : ∀ i,SameLaw (f i) (g i)) :
    SameLaw (fun xs : Fin N → X => fun i => f i (xs i))
      (fun ys : Fin N → Y => fun i => g i (ys i)) := by
  intro phi
  induction N with
  | zero =>
    have hf (xs : Fin 0 → X) : (fun i => f i (xs i))=(fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    have hg (ys : Fin 0 → Y) : (fun i => g i (ys i))=(fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    simp_rw [hf,hg,uniformAverage_const]
  | succ N ih =>
    have hf (x : X) (xs : Fin N → X) :
        (fun i => f i ((Fin.cons x xs : Fin (N+1) → X) i))=Fin.cons (f 0 x) (fun i => f i.succ (xs i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hg (y : Y) (ys : Fin N → Y) :
        (fun i => g i ((Fin.cons y ys : Fin (N+1) → Y) i))=Fin.cons (g 0 y) (fun i => g i.succ (ys i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp_rw [hf,hg]
    have htail (x : X) := ih (fun i => f i.succ) (fun i => g i.succ)
      (fun i => h i.succ) (fun zs => phi (Fin.cons (f 0 x) zs))
    simp_rw [htail]
    exact h 0 (fun z => uniformAverage (fun ys : Fin N → Y =>
      phi (Fin.cons z (fun i => g i.succ (ys i)))))

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSampleLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed ratio sample has the exact analysed law -/

namespace ContingencyTables.RootedRatioSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FiniteLawMoments
open CommonBasesFPRAS FiniteObservableTransport
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

private lemma expectation_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : RationalLaw X) (f : Y → ℝ) :
    expectation (equivLaw e p) f=expectation p (fun x => f (e x)) := by
  unfold expectation equivLaw
  symm
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Equiv.symm_apply_apply])

theorem sameLaw (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ) :
    SameLaw (sample A C a z v N)
      (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) N) := by
  intro g
  let obs := fun w : Grid (I := Fin (dimension A)) K =>
    g (RootedOracleDensity.rationalRatioObservable A (RootedCompletion.rowColumn A.T) C a z w)
  have hl := word_expectation (RootedOracleWalkProgram.flatGridWalk A C a z v N)
    (fun w => obs (RootedCatalogGrid.gridEquiv A K w))
  rw [RootedOracleWalkProgram.flatGridWalk_law,
    RootedCatalogGrid.wordWalkLaw_eq A C a hC haH z hz hK hKB,expectation_equiv] at hl
  simp only [Equiv.apply_symm_apply] at hl
  have hr := word_expectation
    (wordWalk (RootedOracleDensity.oracleBitStep A (RootedCompletion.rowColumn A.T) C a z)
      (RootedCatalogGrid.gridEquiv A K v) N) obs
  change uniformAverage (fun bits => g (RootedOracleDensity.ratioSample A
    (RootedCompletion.rowColumn A.T) C a z (RootedCatalogGrid.gridEquiv A K v) N bits))=
      expectation (RootedOracleDensity.oracleBitWalkLaw A (RootedCompletion.rowColumn A.T)
        C a z (RootedCatalogGrid.gridEquiv A K v) N) obs at hr
  rw [RootedOracleDensity.oracleBitWalkLaw_eq A (RootedCompletion.rowColumn A.T)
    C a hC haH z hz hK hKB] at hr
  exact hl.trans hr.symm

end
end ContingencyTables.RootedRatioSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComputedEstimator
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed blocks have the complete estimator law

Only the physical sample programs differ from the original enumeration.
Exact independent-observable transport identifies their whole product
estimator, including every event used by the confidence proof.
-/

namespace ContingencyTables.RootedComputedEstimator

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FiniteObservableTransport
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

private lemma ratioAverage_law (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (a : Fin j) :
    SameLaw (ratioAverage A C K j a.val delta failure z v)
      (fun draws : CompanionOracleDensity.RatioBlock A C K j delta failure =>
        rationalAverage (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T)
          C a.val z (RootedCatalogGrid.gridEquiv A K v) (oracleTime A C K 1 delta))
            (sampleCount j delta failure) draws) := by
  have hsample := RootedRatioSampleLaw.sameLaw A C a.val K hC
    (show a.val ≤ rationalHeight A C from Nat.le_trans (Nat.le_of_lt a.isLt) hj)
    hK hB.le z hz v (oracleTime A C K 1 delta)
  exact (hsample.independent (sampleCount j delta failure)).map
    (fun qs : Fin (sampleCount j delta failure) → ℚ => (∑ i,qs i)/sampleCount j delta failure)

private lemma correctionAverage_law (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    SameLaw (correctionAverage A C K j hK hW delta failure z v)
      (fun draws : CompanionOracleDensity.CorrectionBlock A C K j delta failure =>
        rationalAverage (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T)
          C j z K hK hW (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
          (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
            (sampleCount j delta failure) draws) := by
  have hsample : SameLaw
      (RootedCorrectionSampleLaw.sample A C j K hK hW z (roundingTolerance delta) v
        (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
      (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T) C j z K hK hW
        (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
        (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)) :=
    RootedCorrectionSampleLaw.sample_average A C j K hC hj hK hW hB.le z hz
      (roundingTolerance delta) v _ _
  exact (hsample.independent (sampleCount j delta failure)).map
    (fun qs : Fin (sampleCount j delta failure) → ℚ => (∑ i,qs i)/sampleCount j delta failure)

/-- Exact equality of the whole rational estimator law; no extra oracle
or confidence hypothesis is introduced at the implementation boundary. -/
theorem sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    SameLaw (estimate A C K j hK hW delta failure z v)
      (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
        delta failure (RootedCatalogGrid.gridEquiv A K v)) := by
  let originalRatio := fun (a : Fin j) (draws : CompanionOracleDensity.RatioBlock A C K j delta failure) =>
    rationalAverage (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T) C a.val z
      (RootedCatalogGrid.gridEquiv A K v) (oracleTime A C K 1 delta))
      (sampleCount j delta failure) draws
  let originalCorrection := fun draws : CompanionOracleDensity.CorrectionBlock A C K j delta failure =>
    rationalAverage (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T)
      C j z K hK hW (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
      (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
      (sampleCount j delta failure) draws
  have hr := FiniteObservableTransport.indexed j
    (fun a : Fin j => ratioAverage A C K j a.val delta failure z v) originalRatio
    (fun a => ratioAverage_law A C K j hC hj hK hB delta failure z hz v a)
  have hc := correctionAverage_law A C K j hC hj hK hW hB delta failure z hz v
  have ht := (hr.prod hc).map (fun p : (Fin j → ℚ)×ℚ => (assignmentCount A:ℚ)*(∏ a,p.1 a)*p.2)
  have ho (draws : EstimatorInput A C K j delta failure) :
      (assignmentCount A:ℚ)*(∏ a,originalRatio a (draws.1 a))*originalCorrection draws.2=
        RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
          delta failure (RootedCatalogGrid.gridEquiv A K v) draws := by
    rw [RootedOracleDensity.estimateValue,Fintype.prod_option]
    simp only [RootedOracleDensity.observedFactor,originalRatio,originalCorrection]
    ring
  intro phi
  have hh := ht phi
  change uniformAverage (fun draws : Inputs A C K j delta failure =>
      phi (estimate A C K j hK hW delta failure z v draws)) =
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      phi ((assignmentCount A:ℚ)*(∏ a,originalRatio a (draws.1 a))*
        originalCorrection draws.2)) at hh
  exact hh.trans (congrArg uniformAverage (funext (fun draws => congrArg phi (ho draws))))

end
end ContingencyTables.RootedComputedEstimator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-word law of the executed selected-root weight oracle -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma scheduledWordWidth (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    wordWidth (scheduledContext A C K j delta failure z v)=
      estimatorWordBits A C K j delta failure := by
  change j*(sampleCount j delta failure*ratioWidth
    (scheduledContext A C K j delta failure z v))+
    sampleCount j delta failure*(correctionWalkWidth
      (scheduledContext A C K j delta failure z v)+
        RootedEstimatorLayoutProgram.binWidth (scheduledContext A C K j delta failure z v))=_
  simp only [scheduledContext,ratioWidth_data,correctionWalkWidth_data,binWidth_data,
    RootedBinDrawLaw.wordBits_eq,estimatorWordBits,oracleIntegerBits]

private lemma oracleTime_positive (A : Instance (Fin m) (Fin n)) (C K : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (theta : ℝ) (htheta : 0 < theta) :
    0 < oracleTime A C K 1 theta := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one A.hd)
  have hk : (0:ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hh := height_positive A C (by exact_mod_cast hC)
  have hm : 0 < mixingConstant A K := by unfold mixingConstant; positivity
  have hp : 0 < mixingConstant A K*(height A C+A.d*K+16*1/theta+2) := by positivity
  have hn := Nat.le_ceil (mixingConstant A K*(height A C+A.d*K+16*1/theta+2))
  have hc : (0:ℝ) < oracleTime A C K 1 theta := by
    simpa only [oracleTime,Nat.cast_one] using hp.trans_le hn
  exact_mod_cast hc

theorem scheduledWidth_positive (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    0 < wordWidth (scheduledContext A C K j delta failure z v) := by
  have hdelta : (0:ℝ) < delta := by exact_mod_cast hd
  have htime := oracleTime_positive A C K hC hK (correctionTheta delta)
    (by unfold correctionTheta; positivity)
  have hstep := RootedOracleWalkProgram.stepWidth_pos A C hC
  have hs := sampleCount_positive j delta failure hd hf
  have ht : 0 < correctionWalkWidth (scheduledContext A C K j delta failure z v) := by
    rw [scheduledContext,correctionWalkWidth_data]
    exact Nat.mul_pos htime hstep
  have hc : 0 < correctionWidth (scheduledContext A C K j delta failure z v) := by
    unfold correctionWidth
    omega
  have hp := Nat.mul_pos hs hc
  change 0 < _ + sampleCount j delta failure*
    correctionWidth (scheduledContext A C K j delta failure z v)
  omega

theorem sameLaw_estimateValue (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta)) :
    FiniteObservableTransport.SameLaw
      (fun bits => TreeFraction.val (output (input
        (scheduledContext A C K j delta failure z v) (degree,depth) bits)))
      (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
        delta failure (RootedCatalogGrid.gridEquiv A K v)) := by
  intro phi
  let test := fun draws : RootedComputedEstimator.Inputs A C K j delta failure =>
    phi (RootedComputedEstimator.estimate A C K j hK hW delta failure z v draws)
  have hp := output_scheduled A C K j hC hj hK hW hB delta failure hd hf z hz v
    degree depth hdegree hdepth
  have he := uniformAverage_equiv (scheduledEquiv A C K j delta failure z v) test
  have ho : uniformAverage (fun bits => phi (TreeFraction.val (output (input
      (scheduledContext A C K j delta failure z v) (degree,depth) bits))))=
      uniformAverage (fun bits => test (scheduledEquiv A C K j delta failure z v bits)) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (hp bits)
  exact ho.trans (he.trans (RootedComputedEstimator.sameLaw A C K j hC hj hK hW hB
    delta failure z hz v phi))

theorem sameLaw_word (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon failure : ℚ) (he : 0 < epsilon) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance epsilon j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance epsilon j))) :
    FiniteObservableTransport.SameLaw
      (fun bits => TreeFraction.val (output (input
        (scheduledContext A C K j (innerTolerance epsilon j) failure z v) (degree,depth) bits)))
      (RootedOracleDensity.wordEstimate A (RootedCompletion.rowColumn A.T) C z K hK hW j
        epsilon failure (RootedCatalogGrid.gridEquiv A K v)) := by
  intro phi
  have hs := sameLaw_estimateValue A C K j hC hj hK hW hB (innerTolerance epsilon j)
    failure (innerTolerance_pos epsilon j he) hf z hz v degree depth hdegree hdepth phi
  have he := uniformAverage_equiv (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure)
    (fun draws => phi (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T)
      C z K hK hW j (innerTolerance epsilon j) failure (RootedCatalogGrid.gridEquiv A K v) draws))
  exact hs.trans he.symm

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing independent complete estimators and their rational median -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

attribute [local irreducible] samples

open GridBoundary CommonBasesFPRAS
open scoped Classical

theorem output_ofFn (c : Context) (R : ℕ) (hw : 0 < wordWidth c)
    (markers : List Bool×List Bool) (bits : Fin (R*wordWidth c) → Bool) :
    TreeFraction.val (output ((c,R),(markers,List.ofFn bits)))=
      rationalMedian (List.ofFn (fun i : Fin R => TreeFraction.val
        (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input c markers
          (gridWordEquiv R (wordWidth c) bits i))))) := by
  rw [output,MedianFractionProgram.median_val]
  have hwords : words ((c,R),(markers,List.ofFn bits))=
      List.ofFn (fun i : Fin R => List.ofFn (gridWordEquiv R (wordWidth c) bits i)) := by
    change (wordChunks (wordWidth c,List.ofFn bits)).take R=_
    rw [wordChunks_ofFn hw]
    exact List.take_of_length_le (by simp)
  unfold samples
  rw [hwords]
  simp only [List.map_ofFn]
  rfl

end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed inner median is the analysed amplified weight oracle -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open FiniteObservableTransport
open scoped Classical

noncomputable section
variable {m n : ℕ}

/-- Exact observable transport, including the outputs on inaccurate
sample histories, lets the original median analysis apply unchanged. -/
theorem sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon delta : ℚ) (he : 0 < epsilon)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance (epsilon/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance (epsilon/2) j))) :
    SameLaw (value A C K j epsilon delta z v degree depth)
      (RootedOracleDensity.medianEstimate A (RootedCompletion.rowColumn A.T) C z K hK hW j
        epsilon delta (RootedCatalogGrid.gridEquiv A K v)) := by
  have heh : 0 < epsilon/2 := by positivity
  have hs := RootedEstimatorWordProgram.sameLaw_word A C K j hC hj hK hW hB
    (epsilon/2) 1 heh (by norm_num) z hz v degree depth hdegree hdepth
  have hp := (hs.independent (repetitionCount delta)).map
    (fun qs : Fin (repetitionCount delta) → ℚ => rationalMedian (List.ofFn qs))
  have hw := RootedEstimatorWordProgram.scheduledWidth_positive A C K j hC hK
    (innerTolerance (epsilon/2) j) 1 (innerTolerance_pos (epsilon/2) j heh)
      (by norm_num) z v
  intro phi
  have hleft := uniformAverage_equiv
    (gridWordEquiv (repetitionCount delta) (wordWidth (context A C K j epsilon z v)))
    (fun xs => phi (rationalMedian (List.ofFn (fun i => TreeFraction.val
      (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input
        (context A C K j epsilon z v) (degree,depth) (xs i)))))))
  have hright := uniformAverage_equiv
    (oracleWalkWordEquiv (repetitionCount delta)
      (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1))
    (fun xs => phi (rationalMedian (List.ofFn (fun i => RootedOracleDensity.wordEstimate A
      (RootedCompletion.rowColumn A.T) C z K hK hW j (epsilon/2) 1
        (RootedCatalogGrid.gridEquiv A K v) (xs i)))))
  have hout : uniformAverage (fun bits => phi (value A C K j epsilon delta z v degree depth bits))=
      uniformAverage (fun bits => phi (rationalMedian (List.ofFn (fun i : Fin (repetitionCount delta) =>
        TreeFraction.val (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input
          (context A C K j epsilon z v) (degree,depth)
            (gridWordEquiv (repetitionCount delta) (wordWidth (context A C K j epsilon z v)) bits i))))))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (output_ofFn (context A C K j epsilon z v) (repetitionCount delta)
      hw (degree,depth) bits)
  exact hout.trans (hleft.trans ((hp phi).trans hright.symm))

end
end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase's physical oracle configuration

Numeric schedules use binary arithmetic. The supplied reserve bounds
the two materialized precision markers; no binary natural controls an
unbounded list allocation.
-/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingOracleScheduleProgram DensePrograms

attribute [local irreducible] output

attribute [local irreducible] context

attribute [local irreducible] contextWidth

noncomputable section
open CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
variable {m n : ℕ}

lemma fields_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    fields (data A C K j xi z v reserve)=[A.d,K,rationalHeight A C,j] := by
  have hh : 10*(C*(A.d*A.d))*(A.W+1)=10*C*A.d^2*(A.W+1) := by ring
  exact congrArg (fun h => [A.d,K,h,j]) hh

lemma inner_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    TreeFraction.val (inner (data A C K j xi z v reserve))=
      innerTolerance (TreeFraction.val xi/2) j := by
  rw [inner,TreeFraction.div_val,natural_val,scalar,fields_data]
  simp only [relativeDenominator,phase,Expr.eval,List.getD_cons_zero,List.getD_cons_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  unfold innerTolerance
  dsimp only [data]
  field_simp
  ring

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

lemma natWord_eq (n : ℕ) : natWord n=encodeNat n := rfl

lemma ratWord_repr (q : ℚ) (hq : 0≤q) : ratWord (TreeFraction.repr q)=encodeRat q := by
  have hn : ¬q.num<0 := not_lt.mpr (Rat.num_nonneg.mpr hq)
  simp only [ratWord,TreeFraction.repr,natWord_eq,encodeRat,encodeInt,ite_eq_right hn,List.singleton_append]
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Parse
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

lemma bits_fold (n : ℕ) (ns : List ℕ) :
    (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=n::ns := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn,List.map_cons,List.foldr_cons,ih]
    cases b <;> simp [fromBit,numStep,Nat.bit]
lemma encodeNat_fold (n : ℕ) (ns : List ℕ) :
    (encodeNat n).foldr (fun a ns=>numStep (a,ns)) ns=n::ns := by
  change (n.bits.map fromBit++[3]).foldr _ ns=_
  rw [List.foldr_append]
  change (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=_
  exact bits_fold n ns
lemma encodeInt_fold (z : ℤ) (ns : List ℕ) :
    (encodeInt z).foldr (fun a ns=>numStep (a,ns)) ns=z.natAbs::ns := by
  unfold encodeInt
  rw [List.foldr_append,encodeNat_fold]
  split_ifs <;> simp [numStep]
lemma encodeRat_fold (q : ℚ) (ns : List ℕ) :
    (encodeRat q).foldr (fun a ns=>numStep (a,ns)) ns=q.num.natAbs::q.den::ns := by
  rw [encodeRat,List.foldr_append,encodeNat_fold,encodeInt_fold]
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public margins and printing the greedy matrix

All operations are existing binary list programs. The bounded take and
drop operations also terminate polynomially on malformed headers.
-/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS TreeTyped LiteralCodec LiteralParse
open scoped BigOperators

lemma natWords_fold (ns tail : List ℕ) :
    (ns.flatMap encodeNat).foldr (fun a ns => numStep (a,ns)) tail=ns++tail := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold,List.cons_append]

lemma encodeMargins_natWords {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Algorithms.encodeMargins r c=
      (m::n::(List.ofFn r++List.ofFn c)).flatMap encodeNat := by
  simp only [Algorithms.encodeMargins,List.flatMap_cons,List.flatMap_append]
  simp only [List.ofFn_comp',List.flatMap_def,List.append_assoc]

lemma marginLists_spec (m n : ℕ) (rs cs tail : List ℕ)
    (hr : rs.length=m) (hc : cs.length=n) :
    marginLists (m::n::(rs++cs++tail))=(rs,cs) := by
  simp only [marginLists,List.headD_cons,List.tail_cons]
  rw [←hr,←hc]
  simp only [List.append_assoc,List.take_left,List.drop_left]

lemma printMatrix_ofFn {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    printMatrix (List.ofFn (fun i => List.ofFn (X i)))=Algorithms.encodeMatrix X := by
  simp only [printMatrix,Algorithms.encodeMatrix,List.flatMap_def,List.ofFn_comp',List.map_map,
    Function.comp_def]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingInputParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public cell-bounded counting input

Dimensions only delimit bounded list slices. The matrix layout uses the
lengths of the parsed margin lists, so malformed headers do not create
unbounded numeric loops. Positive rational parameters use their natural
numerator and denominator, exactly as in the public tape encoding.
-/

namespace ContingencyTables.CountingInputParser
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse
open MatchingFPRAS.TreeFraction DensePrograms

lemma decode_blocks (rs cs flat tail : List ℕ) (hf : flat.length=rs.length*cs.length) :
    decode (rs.length::cs.length::(rs++cs++flat++tail))=
      (( (rs,cs),unflattenGrid ((0::rs,0::cs),flat)),fractionPair tail) := by
  have hm := GreedyFeasibleTable.marginLists_spec rs.length cs.length rs cs (flat++tail) rfl rfl
  have hr : rest (rs.length::cs.length::(rs++cs++flat++tail))=flat++tail := by
    simp only [rest,offset,List.headD_cons,List.tail_cons]
    rw [show 2+rs.length+cs.length=(rs.length+cs.length)+1+1 by omega]
    simp only [List.drop_succ_cons,List.append_assoc]
    rw [←List.drop_drop,List.drop_left,List.drop_left]
  have hc : cells (rs.length::cs.length::(rs++cs++flat++tail))=flat.length := by
    unfold cells
    rw [show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc],hm]
    exact hf.symm
  simp only [decode,capacityFrame,parameters]
  rw [show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc],hm]
  rw [←show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc]]
  rw [hr,hc,List.take_left,List.drop_left]

lemma encodeMatrix_words {m n : ℕ} (b : Fin m→Fin n→ℕ) :
    Algorithms.encodeMatrix b=
      (List.ofFn (fun i => List.ofFn (b i))).flatten.flatMap encodeNat := by
  rw [←GreedyFeasibleTable.printMatrix_ofFn]
  unfold GreedyFeasibleTable.printMatrix
  generalize List.ofFn (fun i => List.ofFn (b i))=rows
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons,List.flatten_cons,List.flatMap_append,ih]

lemma parse_public {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    parse (Algorithms.encodeCountingInput r c b epsilon delta)=
      m::n::(List.ofFn r++List.ofFn c++
        (List.ofFn (fun i => List.ofFn (b i))).flatten++
          [epsilon.num.natAbs,epsilon.den,delta.num.natAbs,delta.den]) := by
  unfold Algorithms.encodeCountingInput parse
  rw [GreedyFeasibleTable.encodeMargins_natWords,encodeMatrix_words]
  simp only [List.foldr_append,encodeRat_fold]
  rw [GreedyFeasibleTable.natWords_fold,GreedyFeasibleTable.natWords_fold]
  simp only [List.cons_append,List.append_assoc]

lemma public_spec {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    parseInput (Algorithms.encodeCountingInput r c b epsilon delta)=
      (NetworkVertexCode.data r c b,(TreeFraction.repr epsilon,TreeFraction.repr delta)) := by
  unfold parseInput
  rw [parse_public]
  have hf : (List.ofFn (fun i => List.ofFn (b i))).flatten.length=
      (List.ofFn r).length*(List.ofFn c).length := by
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn,
      List.sum_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hh := decode_blocks (List.ofFn r) (List.ofFn c)
    (List.ofFn (fun i => List.ofFn (b i))).flatten
    [epsilon.num.natAbs,epsilon.den,delta.num.natAbs,delta.den] hf
  simp only [List.length_ofFn] at hh
  rw [hh]
  change (( (List.ofFn r,List.ofFn c),_),_)=( ( (List.ofFn r,List.ofFn c),_),_)
  congr 2
  let f : Fin (m*n)→ℕ := fun k => b (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have he : (List.ofFn (fun i => List.ofFn (b i))).flatten=List.ofFn f := by
    simpa only [f,Equiv.symm_apply_apply,matrixCode] using flatten_matrixCode f
  rw [he]
  simpa only [marginCode,f,Equiv.symm_apply_apply,matrixCode,ResidualGraphProgram.natCode,Option.elim_none,Option.elim_some]
    using unflattenGrid_code (fun i : Option (Fin m) => i.elim 0 r)
      (fun j : Option (Fin n) => j.elim 0 c) f

end ContingencyTables.CountingInputParser

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionOutputProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical nonnegative rational output on the public tape -/

namespace ContingencyTables.FractionOutputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec

lemma output_eq (x : TreeFraction.Fraction) : output x=encodeRat (TreeFraction.val x) := by
  rw [output,TreeFraction.normalize_repr,ratWord_repr _ (TreeFraction.val_nonneg x)]

lemma natWord_symbols (n : ℕ) (a : Symbol) (ha : a∈natWord n) : a≠0 ∧ a≠6 ∧ a≠7 := by
  simp only [natWord,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩ | rfl
  · cases b <;> decide
  · decide

lemma output_symbols (x : TreeFraction.Fraction) (a : Symbol) (ha : a∈output x) :
    a≠0 ∧ a≠6 ∧ a≠7 := by
  simp only [output,ratWord,List.mem_cons,List.mem_append] at ha
  rcases ha with (rfl | ha) | ha
  · decide
  · exact natWord_symbols _ a ha
  · exact natWord_symbols _ a ha

end ContingencyTables.FractionOutputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public dispatch for the two counting branches

The positive-label evaluator is a program parameter, instantiated by the
adaptive estimator. Feasibility and the zero-label branch are computed from
the same parsed input used by the complete public machine.
-/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

attribute [local irreducible] feasible direct

section Evaluator
variable (positive : Input → TreeFraction.Fraction) (F : Realizer positive)

attribute [local irreducible] feasibleOutput

attribute [local irreducible] output

lemma publicOutput_eq (z : List Symbol×List Bool) :
    publicOutput positive z=encodeRat (TreeFraction.val (output positive (parsedInput z))) :=
  FractionOutputProgram.output_eq _

lemma publicOutput_symbols (z : List Symbol×List Bool) (a : Symbol)
    (ha : a∈publicOutput positive z) : a≠0 ∧ a≠6 ∧ a≠7 :=
  FractionOutputProgram.output_symbols _ a ha

end Evaluator

end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact schedules in the computed weight-oracle configuration -/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma scalar_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool) (e : ScalarScheduleProgram.Expr) :
    scalar e (data A C K j xi z v reserve)=e.eval [A.d,K,rationalHeight A C,j] := by
  rw [scalar,fields_data]

lemma timeInput_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    timeInput (data A C K j xi z v reserve)=
      (2*(10000*A.d^2*K)^2,rationalHeight A C+A.d*K+2) := by
  simp only [timeInput,scalar_data,mixing,allowance,dim,grid,height,
    ScalarScheduleProgram.Expr.eval_power,ScalarScheduleProgram.Expr.eval,List.getD_cons_zero,List.getD_cons_succ]

lemma correction_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    TreeFraction.val (correction (data A C K j xi z v reserve))=
      correctionTheta (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [correction,TreeFraction.div_val,inner_data]
  simp only [TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one,correctionTheta,Rat.cast_div,Rat.cast_ofNat]

lemma samples_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    samples (data A C K j xi z v reserve)=sampleCount j (innerTolerance (TreeFraction.val xi/2) j) 1 := by
  unfold samples
  rw [CountingOracleScheduleProgram.sampleCount_val,inner_data]
  simp only [data,TreeFraction.val,Nat.cast_one,div_one]

lemma ratioTime_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    ratioTime (data A C K j xi z v reserve)=
      oracleTime A C K 1 (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [ratioTime,timeInput_data,CountingOracleScheduleProgram.oracleTime_instance,inner_data]

lemma correctionTime_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    correctionTime (data A C K j xi z v reserve)=
      oracleTime A C K 1 (correctionTheta (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [correctionTime,timeInput_data,CountingOracleScheduleProgram.oracleTime_instance,correction_data]

lemma offsetAccuracy_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    offsetAccuracy (data A C K j xi z v reserve)=
      CompanionOracleDensity.offsetAccuracy A (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [offsetAccuracy,CountingOracleScheduleProgram.offsetAccuracy_val,inner_data,scalar_data]
  rfl

lemma context_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    context (data A C K j xi z v reserve)=
      RootedEstimatorMedianProgram.context A C K j (TreeFraction.val xi) z v := by
  unfold context output schedule
  rw [samples_data,ratioTime_data,correctionTime_data,offsetAccuracy_data]
  rfl

lemma rootDegree_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    rootDegree (data A C K j xi z v reserve)=
      PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [rootDegree,CountingOracleScheduleProgram.ceiling_val,TreeFraction.div_val,inner_data]
  unfold PowerOfTwoApproximation.rootDegree roundingTolerance
  congr 1
  simp only [TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one,div_div_eq_mul_div]
  ring

lemma depth_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    depth (data A C K j xi z v reserve)=
      PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [depth,rootDegree_data]
  rfl

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The direct binary evaluator uses the original counting parameters -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma accuracy_value (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0 < epsilon) (bits : List Bool) :
    TreeFraction.val (accuracy (request r c b epsilon delta,bits))=(epsilon/2)/2 := by
  change TreeFraction.val (CountingBaseProgram.half (CountingBaseProgram.half (TreeFraction.repr epsilon)))=_
  rw [CountingBaseProgram.half_val,CountingBaseProgram.half_val,TreeFraction.val_repr he.le]

lemma oracleInput_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    let H := ComputedCountingParameters.phases r c b epsilon
    oracleInput (request r c b epsilon delta,bits)=
      RootedOracleConfigProgram.data A C K H
        (accuracy (request r c b epsilon delta,bits)) (fun _ => 0)
        (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))
        (bits.map (fun _ => false)) := by
  dsimp only
  unfold oracleInput request
  rw [CountingPreparedState.state_data hEK r c b hne epsilon he,
    CountingTerminalProgram.phases_data r c b epsilon he]
  rfl

lemma context_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    let H := ComputedCountingParameters.phases r c b epsilon
    context (request r c b epsilon delta,bits)=
      RootedEstimatorMedianProgram.context A C K H ((epsilon/2)/2) (fun _ => 0)
        (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  change RootedOracleConfigProgram.context (oracleInput (request r c b epsilon delta,bits))=_
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.context_data,accuracy_value r c b epsilon delta he bits]

lemma wordWidth_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) (hd : 0 < delta)
    (bits : List Bool) :
    wordWidth (request r c b epsilon delta,bits)=
      ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta := by
  have hr : repeats (request r c b epsilon delta,bits)=CommonBasesFPRAS.repetitionCount delta := by
    change FractionRepetitionProgram.count (TreeFraction.repr delta)=_
    rw [FractionRepetitionProgram.count_val,TreeFraction.val_repr hd.le]
  rw [wordWidth,hr,contextWidth]
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.contextWidth,RootedOracleConfigProgram.context_data,
    accuracy_value r c b epsilon delta he bits]
  rw [RootedEstimatorMedianProgram.context,RootedEstimatorWordProgram.scheduledWordWidth]
  unfold ComputedCountingZero.zeroBits medianEstimatorBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]

lemma degree_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    RootedOracleConfigProgram.rootDegree (oracleInput (request r c b epsilon delta,bits))=
      degree r c b epsilon := by
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.rootDegree_data,accuracy_value r c b epsilon delta he bits]
  rfl

lemma depth_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    RootedOracleConfigProgram.depth (oracleInput (request r c b epsilon delta,bits))=
      depth r c b epsilon := by
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.depth_data,accuracy_value r c b epsilon delta he bits]
  rfl

lemma budget_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    budget (request r c b epsilon delta)=
      ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta+degree r c b epsilon+depth r c b epsilon := by
  unfold budget padding empty
  rw [wordWidth_data hEK r c b hne epsilon delta he hd [],
    degree_data hEK r c b hne epsilon delta he [],depth_data hEK r c b hne epsilon delta he []]
  omega

lemma markers_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (N : ℕ) (hdegree : degree r c b epsilon ≤ N) (hdepth : depth r c b epsilon ≤ N)
    (bits : Fin N→Bool) :
    markers (request r c b epsilon delta,List.ofFn bits)=
      (List.replicate (degree r c b epsilon) false,List.replicate (depth r c b epsilon) false) := by
  change RootedOracleConfigProgram.markers
    (oracleInput (request r c b epsilon delta,List.ofFn bits))=_
  rw [RootedOracleConfigProgram.markers,
    degree_data hEK r c b hne epsilon delta he (List.ofFn bits),
    depth_data hEK r c b hne epsilon delta he (List.ofFn bits)]
  simp only [oracleInput,reserve,List.map_ofFn,Function.comp_def,List.ofFn_const,
    List.take_replicate,min_eq_left hdegree,min_eq_left hdepth]

end
end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The public counting dispatch preserves the original bounded input -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS CompanionFactorialApplication
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma parsedInput_public (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (bits : List Bool) :
    parsedInput (Algorithms.encodeCountingInput r c b epsilon delta,bits)=
      (CountingDirectProgram.request r c b epsilon delta,bits) := by
  unfold parsedInput
  rw [CountingInputParser.public_spec]
  rfl

lemma feasible_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    feasible (CountingDirectProgram.request r c b epsilon delta)=true ↔
      ∃ X,TableTightening.Feasible r c b X := by
  exact NetworkFeasibilityProgram.test_correct hEK r c b

lemma count_zero_iff_rejected (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    Algorithms.count r c b=0 ↔ feasible (CountingDirectProgram.request r c b epsilon delta)=false := by
  constructor
  · intro hz
    apply Bool.eq_false_iff.mpr
    intro hf
    obtain ⟨X,hX⟩ := (feasible_data hEK r c b epsilon delta).mp hf
    have hp : 0 < Fintype.card (BoundedTable r c b) :=
      Fintype.card_pos_iff.mpr ⟨⟨⟨X,hX.1⟩,hX.2⟩⟩
    exact (Nat.ne_of_gt hp) hz
  · intro hf
    have hn : ¬∃ X,TableTightening.Feasible r c b X := by
      intro hx
      have ht := (feasible_data hEK r c b epsilon delta).mpr hx
      rw [hf] at ht
      exact Bool.false_ne_true ht
    have hEmpty : IsEmpty (BoundedTable r c b) := ⟨fun X => hn ⟨X.val.val,X.val.property,X.property⟩⟩
    let := hEmpty
    exact Fintype.card_eq_zero

lemma direct_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    direct (CountingDirectProgram.request r c b epsilon delta)=true ↔
      Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he))=0 := by
  unfold direct CountingDirectProgram.request
  rw [CountingComputedSettings.labelCount_data hEK r c b hne epsilon he]
  simp only [decide_eq_true_eq]

lemma output_rejected (positive : Input→TreeFraction.Fraction) (req : Request)
    (h : feasible req=false) (bits : List Bool) : output positive (req,bits)=(0,1) := by
  simp only [output,h,Bool.false_eq_true,ite_false]

lemma output_direct (positive : Input→TreeFraction.Fraction) (req : Request)
    (hf : feasible req=true) (hd : direct req=true) (bits : List Bool) :
    output positive (req,bits)=CountingDirectProgram.output (req,bits) := by
  simp only [output,feasibleOutput,hf,hd,ite_true, if_true]

lemma output_positive (positive : Input→TreeFraction.Fraction) (req : Request)
    (hf : feasible req=true) (hd : direct req=false) (bits : List Bool) :
    output positive (req,bits)=positive (req,bits) := by
  simp only [output,feasibleOutput,hf,hd,ite_true, if_true,Bool.false_eq_true,ite_false]

lemma budget_direct (positive : Request→ℕ) (req : Request)
    (hf : feasible req=true) (hd : direct req=true) :
    budget positive req=CountingDirectProgram.budget req := by
  simp only [budget,feasibleBudget,hf,hd,ite_true, if_true]

lemma budget_positive (positive : Request→ℕ) (req : Request)
    (hf : feasible req=true) (hd : direct req=false) : budget positive req=positive req := by
  simp only [budget,feasibleBudget,hf,hd,ite_true, if_true,Bool.false_eq_true,ite_false]

end
end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixEncoding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The public matrix encoding uniquely identifies a fixed-shape table -/

namespace ContingencyTables.Algorithms
open MatchingFPRAS MatchingFPRAS.LiteralParse Turing

lemma encodeMatrix_flat {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    encodeMatrix X=((List.ofFn fun i => List.ofFn (X i)).flatten).flatMap encodeNat := by
  rw [←GreedyFeasibleTable.printMatrix_ofFn]
  simp only [GreedyFeasibleTable.printMatrix,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq]

end ContingencyTables.Algorithms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_AdaptiveStream
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma run_cost (p : Experiment α) (b : Stream) : (p.run b).2≤p.cost := by
  induction p generalizing b with
  | done a => rfl
  | read p ih =>
    simp only [run,cost]
    have h:=ih (b 0) (shift 1 b)
    cases hb : b 0 <;> simp only [hb] at h <;> omega
  | delay n p ih => exact Nat.add_le_add_left (ih (shift n b)) n

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
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_ExperimentSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
lemma all_run (p : Experiment α) (P : α → Prop) (h : All p P) (b : Stream) : P (p.run b).1 := by
  induction p generalizing b with
  | done a => exact h
  | read p ih =>
    cases hb : b 0 <;> simp only [run,hb] <;> apply ih <;> first | exact h.1 | exact h.2
  | delay n p ih => exact ih h (shift n b)
lemma all_bind (p : Experiment α) (q : α → Experiment β) (P : β → Prop) :
    All (p.bind q) P ↔ All p (fun a=>All (q a) P) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,All,ih]
  | delay n p ih => exact ih
lemma all_map (p : Experiment α) (f : α → β) (P : β → Prop) :
    All (p.map f) P ↔ All p (fun a=>P (f a)) := by
  rw [map,all_bind]; rfl

end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalPost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R : Type} [Inhabited Γ]

lemma execute_add (M : Table Γ Q) (n m : ℕ) (c : Cfg Γ Q) (b : Stream) :
    execute M (n+m) c b=execute M m (execute M n c b) (shift n b) := by
  induction n generalizing c b with
  | zero => simp only [execute,Nat.zero_add,shift_zero]
  | succ n ih =>
    rw [Nat.succ_add,execute,ih,execute]
    congr 1
    funext i
    simp only [shift]
    congr 1
    omega

lemma execute_halted (M : Table Γ Q) (n : ℕ) (T : Tape Γ) (b : Stream) :
    execute M n ⟨none,T⟩ b=⟨none,T⟩ := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => exact ih (shift 1 b)

variable [Fintype Q] [Inhabited Q]

lemma tick_seal (M : Table Symbol Q) (c : Cfg Symbol Q) (b : Bool) :
    MatchingFPRAS.tick (machine M) (sealCfg M c) b=sealCfg M (tick M c b) := by
  cases c with
  | mk s T => cases s with
    | none => rfl
    | some q =>
      simp only [MatchingFPRAS.tick,sealCfg,machine,Option.map_some,Equiv.symm_apply_apply,tick]
      cases h:M q T.head b with
      | none => rfl
      | some qa => rcases qa with ⟨q',a⟩; cases a <;> rfl

omit [Fintype Q] [Inhabited Q] in
lemma execute_list (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Bits n) :
    execute M n c (extend b)=(List.ofFn b).foldl (tick M) c := by
  induction n generalizing c with
  | zero => simp [execute]
  | succ n ih =>
    rw [execute,List.ofFn_succ,List.foldl_cons]
    have h0 : extend b 0=b 0 := by simp [extend]
    rw [h0,←ih]
    have he : ∀ i, i<n → shift 1 (extend b) i=extend (fun j : Fin n=>b j.succ) i := by
      intro i hi
      simp only [shift,extend,dite_eq_left hi,dite_eq_left (by omega : 1+i<n+1)]
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hc : ∀ (k : ℕ) (a d : Stream), (∀ i,i<k→a i=d i) →
        ∀ c, execute M k c a=execute M k c d := by
      intro k
      induction k with
      | zero => intros; rfl
      | succ k hk =>
        intro a d had c
        simp only [execute,had 0 (by omega)]
        apply hk
        intro i hi
        exact had (1+i) (by omega)
    exact hc n _ _ he _

lemma foldl_seal (M : Table Symbol Q) (bs : List Bool) (c : Cfg Symbol Q) :
    bs.foldl (MatchingFPRAS.tick (machine M)) (sealCfg M c)=sealCfg M (bs.foldl (tick M) c) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => rw [List.foldl_cons,tick_seal,ih,List.foldl_cons]

lemma initial_seal (M : Table Symbol Q) (input : List Symbol) :
    sealCfg M ⟨some default,Tape.mk₁ input⟩=MatchingFPRAS.initial (machine M) input := by
  change (⟨some (enumeration default),Tape.mk₁ input⟩ : Configuration (machine M))=⟨some 0,Tape.mk₁ input⟩
  rw [enumeration_default]
  rfl

theorem run_seal (M : Table Symbol Q) (input : List Symbol) (n : ℕ) (b : Bits n) :
    MatchingFPRAS.run (machine M) input b=
      sealCfg M (execute M n ⟨some default,Tape.mk₁ input⟩ (extend b)) := by
  unfold MatchingFPRAS.run
  rw [←initial_seal,foldl_seal,execute_list]

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_CoinTM1
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

lemma execute_first_eq (M : PhysicalPost.Table Γ (State Γ Λ σ))
    (x y : PhysicalPost.Cfg Γ (State Γ Λ σ)) (h : ∀ b,PhysicalPost.tick M x b=PhysicalPost.tick M y b)
    {n : ℕ} (hn : 0 < n) (b : Stream) : PhysicalPost.execute M n x b=PhysicalPost.execute M n y b := by
  cases n with
  | zero => omega
  | succ n => simp only [PhysicalPost.execute,h]

theorem statement_ticks (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ k,0 < k ∧ k ≤ statementCost q ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (pending q v T) b=trCfg (TM1.stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih v (T.move d)
    refine ⟨k+1,by omega,by simp only [statementCost]; omega,fun b=>?_⟩
    simpa only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux] using he (shift 1 b)
  | write f q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih v (T.write (f T.head v))
    refine ⟨k+1,by omega,by simp only [statementCost]; omega,fun b=>?_⟩
    simpa only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux] using he (shift 1 b)
  | load f q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih (f T.head v) T
    refine ⟨k,hk,hc,fun b=>?_⟩
    rw [execute_first_eq (table M coin) (pending (.load f q) v T) (pending q (f T.head v) T) (fun _=>rfl) hk]
    exact he b
  | branch f q r ihq ihr =>
    cases h:f T.head v with
    | false =>
      obtain ⟨k,hk,hc,he⟩:=ihr v T
      refine ⟨k,hk,hc.trans (le_max_right _ _),fun b=>?_⟩
      rw [execute_first_eq (table M coin) (pending (.branch f q r) v T) (pending r v T) (fun _=>by
        simp only [PhysicalPost.tick,pending,table,aux,h,Bool.false_eq_true,ite_false]) hk]
      simpa only [TM1.stepAux,h,Bool.cond_false] using he b
    | true =>
      obtain ⟨k,hk,hc,he⟩:=ihq v T
      refine ⟨k,hk,hc.trans (le_max_left _ _),fun b=>?_⟩
      rw [execute_first_eq (table M coin) (pending (.branch f q r) v T) (pending q v T) (fun _=>by
        simp only [PhysicalPost.tick,pending,table,aux,h,ite_true, if_true]) hk]
      simpa only [TM1.stepAux,h,Bool.cond_true] using he b
  | goto f =>
    refine ⟨1,by omega,le_rfl,fun b=>?_⟩
    simp only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux,trCfg,Option.map_some,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,le_rfl,fun b=>?_⟩
    rfl

lemma entry_ticks (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (l : Λ) (v : σ) (T : Tape Γ) (hl : coin l=none) :
    ∃ k,0 < k ∧ k ≤ statementCost (M l) ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (trCfg ⟨some l,v,T⟩) b=
        trCfg (TM1.stepAux (M l) v T) := by
  obtain ⟨k,hk,hc,he⟩:=statement_ticks M coin (M l) v T
  refine ⟨k,hk,hc,fun b=>?_⟩
  rw [execute_first_eq (table M coin) (trCfg ⟨some l,v,T⟩) (pending (M l) v T) (fun _=>by
    simp only [PhysicalPost.tick,trCfg,Option.map_some,table,hl,pending]) hk]
  exact he b

lemma coin_tick (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (l : Λ) (v : σ) (T : Tape Γ) (f : Bool → Λ) (hl : coin l=some f) (b : Bool) :
    PhysicalPost.tick (table M coin) (trCfg ⟨some l,v,T⟩) b=trCfg ⟨some (f b),v,T⟩ := by
  simp only [PhysicalPost.tick,trCfg,Option.map_some,table,hl,Tape.write_self]

end MatchingFPRAS.CoinTM1

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalRestriction
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q : Type} [Inhabited Γ]

lemma tick_lift (M : Table Γ Q) (S : Finset Q) (h : Supported M S)
    (c : Cfg Γ {q // q∈S}) (b : Bool) :
    tick M (liftCfg S c) b=liftCfg S (tick (restrict M S h) c b) := by
  cases c with
  | mk state T => cases state with
    | none => rfl
    | some q =>
      cases e:M q.val T.head b with
      | none => simp only [tick,liftCfg,Option.map_some,restrict,e,Option.map_none]
      | some qa =>
        rcases qa with ⟨q',act⟩
        have hq' : q'∈S:=h q.val q.property T.head b q' act e
        simp only [tick,liftCfg,Option.map_some,restrict,e,dite_eq_left hq']

lemma execute_lift (M : Table Γ Q) (S : Finset Q) (h : Supported M S)
    (n : ℕ) (c : Cfg Γ {q // q∈S}) (b : Stream) :
    execute M n (liftCfg S c) b=liftCfg S (execute (restrict M S h) n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_lift,ih,execute]

lemma restrictedMachine_run (M : Table Symbol Q) (S : Finset Q)
    (h : Supported M S) (q₀ : Q) (hq₀ : q₀∈S)
    (input : List Symbol) (n : ℕ) (b : Bits n) :
    letI : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
    MatchingFPRAS.run (restrictedMachine M S h q₀ hq₀) input b=
      sealCfg (restrict M S h)
        (execute (restrict M S h) n ⟨some default,Tape.mk₁ input⟩ (extend b)) :=
by
  let : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
  exact run_seal (restrict M S h) input n b

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_SafeTrace
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SafeTrace
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

namespace Path
variable {M : Λ → TM1.Stmt Γ Λ σ} {safe : Λ → Prop}
lemma single (c : TM1.Cfg Γ Λ σ) (hc : ∀ l,c.l=some l→safe l) :
    Path M safe 1 c (advance (TM1.step M) c) := .cons hc (.refl _)
lemma trans {n m : ℕ} {a b c : TM1.Cfg Γ Λ σ}
    (h : Path M safe n a b) (g : Path M safe m b c) : Path M safe (n+m) a c := by
  induction h with
  | refl a => simpa only [Nat.zero_add] using g
  | @cons n a b ha hr ih => simpa only [Nat.succ_add] using Path.cons ha (ih g)
lemma of_run (n : ℕ) (c : TM1.Cfg Γ Λ σ)
    (h : ∀ i,i<n→∀ l,(MachineCost.run (TM1.step M) i c).l=some l→safe l) :
    Path M safe n c (MachineCost.run (TM1.step M) n c) := by
  induction n generalizing c with
  | zero => exact .refl _
  | succ n ih =>
    refine .cons (h 0 (by omega)) (ih _ ?_)
    intro i hi l hl
    exact h (i+1) (by omega) l hl

theorem physical {n : ℕ} {a b : TM1.Cfg Γ Λ σ} (h : Path M safe n a b)
    (coin : CoinTM1.Coins Λ) (hcoin : ∀ l,safe l→coin l=none)
    (C : ℕ) (hC : ∀ l,safe l→statementCost (M l)≤C) :
    ∃ k,k≤n*C ∧ ∀ bits : Stream,
      PhysicalPost.execute (CoinTM1.table M coin) k (CoinTM1.trCfg a) bits=CoinTM1.trCfg b := by
  induction h with
  | refl a => exact ⟨0,by simp,fun _=>rfl⟩
  | @cons n c d hc hr ih =>
    obtain ⟨k,hk,he⟩:=ih
    rcases c with ⟨l,v,T⟩
    cases l with
    | none =>
      refine ⟨k,le_trans hk ?_,he⟩
      exact Nat.mul_le_mul_right C (by omega)
    | some l =>
      have hs:=hc l rfl
      obtain ⟨j,hj,hjc,hje⟩:=CoinTM1.entry_ticks M coin l v T (hcoin l hs)
      refine ⟨j+k,?_,fun bits=>?_⟩
      · have hb:=hC l hs
        calc j+k≤C+n*C := Nat.add_le_add (hjc.trans hb) hk
             _=(n+1)*C := by ring
      · rw [PhysicalPost.execute_add,hje]
        exact he (shift j bits)
end Path
end MatchingFPRAS.SafeTrace

namespace MatchingFPRAS.SafeTrace.Path
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ]
lemma with_support {M : Λ → TM1.Stmt Γ Λ σ} {safe : Λ → Prop} {S : Finset Λ}
    (hS : TM1.Supports M S) {n : ℕ} {a b : TM1.Cfg Γ Λ σ}
    (h : Path M safe n a b) (ha : ∀ l,a.l=some l→l∈S) :
    Path M (fun l=>safe l ∧ l∈S) n a b := by
  induction h with
  | refl c => exact .refl _
  | @cons n c d hc hr ih =>
    refine .cons (fun l hl=>⟨hc l hl,ha l hl⟩) (ih ?_)
    intro l hl
    rcases c with ⟨lc,v,T⟩
    cases lc with
    | none => simp [advance,TM1.step] at hl
    | some lc =>
      have hs:=TM1.step_supports M hS (c:=⟨some lc,v,T⟩) (c':=TM1.stepAux (M lc) v T) rfl (by
        simp only [Finset.some_mem_insertNone]; exact ha lc rfl)
      simp only [advance,TM1.step,Option.getD_some] at hl
      exact Finset.some_mem_insertNone.mp (hl ▸ hs)
end MatchingFPRAS.SafeTrace.Path

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinAlphabet
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing TM1 TM1to1 MachineCost SafeTrace

variable {Γ Λ σ : Type} [Inhabited Γ]

variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
  (enc0 : enc default=List.Vector.replicate n false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)

include encdec

theorem statement_path (p : Λ → Prop) (q : TM1.Stmt Γ Λ σ) (v : σ) (L R : ListBlank Γ) :
    ∃ t,t≤AlphabetCost.writesCount q ∧
      Path (tr enc dec M) (safe p) t
        (stepAux (trNormal dec q) v (trTape' enc0 L R))
        (trCfg enc enc0 (stepAux q v (Tape.mk' L R))) := by
  induction q generalizing v L R with
  | move d q ih =>
    cases d <;>
      simp only [trNormal,stepAux_move,stepAux,Tape.move_left_mk',
        trTape'_move_left enc0,trTape'_move_right enc0,AlphabetCost.writesCount] <;>
      apply ih
  | write f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,AlphabetCost.writesCount]
    obtain ⟨a,R,rfl⟩:=R.exists_cons
    obtain ⟨t,ht,he⟩:=ih v L (R.cons (f a v))
    refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
    apply Path.cons (by intro l hl; cases hl; trivial)
    simp only [advance,TM1.step,tr,Option.getD_some,Tape.mk'_head,ListBlank.head_cons]
    rw [stepAux_write enc0,stepAux_move,trTape'_move_left enc0]
    simpa using he
  | load f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,AlphabetCost.writesCount]
    exact ih _ _ _
  | branch p' q r ihq ihr =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,Tape.mk'_head,AlphabetCost.writesCount]
    cases h:p' R.head v
    · simp only [Bool.cond_false]
      obtain ⟨t,ht,he⟩:=ihr v L R
      exact ⟨t,ht.trans (le_max_right _ _),he⟩
    · simp only [Bool.cond_true]
      obtain ⟨t,ht,he⟩:=ihq v L R
      exact ⟨t,ht.trans (le_max_left _ _),he⟩
  | goto f =>
    refine ⟨0,le_rfl,?_⟩
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,trCfg,trTape_mk',Tape.mk'_head,Option.map_some]
    exact .refl _
  | halt =>
    refine ⟨0,le_rfl,?_⟩
    simp only [trNormal,stepAux,trCfg,trTape_mk',Option.map_none]
    exact .refl _

lemma one_step_path (p : Λ → Prop) (c : TM1.Cfg Γ Λ σ) (hc : ∀ l,c.l=some l→p l) :
    ∃ t,t≤(match c.l with | none=>0 | some l=>AlphabetCost.writesCount (M l)+1) ∧
      Path (tr enc dec M) (safe p) t (trCfg enc enc0 c)
        (trCfg enc enc0 (advance (TM1.step M) c)) := by
  rcases c with ⟨l,v,T⟩
  obtain ⟨L,R,rfl⟩:=T.exists_mk'
  cases l with
  | none => exact ⟨0,le_rfl,.refl _⟩
  | some l =>
    obtain ⟨t,ht,he⟩:=statement_path enc dec enc0 encdec M p (M l) v L R
    refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
    apply Path.cons (by intro l' hl; cases hl; exact hc l rfl)
    simpa only [advance,TM1.step,Option.map_some,trCfg,tr,Option.getD_some,trTape_mk'] using he

theorem path_supported [Inhabited Λ] [Inhabited σ] (S : Finset Λ) (hS : TM1.Supports M S)
    {p : Λ → Prop} {k : ℕ} {a b : TM1.Cfg Γ Λ σ}
    (h : Path M p k a b) (ha : a.l∈S.insertNone) :
    ∃ t,t≤k*(AlphabetCost.supportedWrites M S+1) ∧
      Path (tr enc dec M) (safe p) t (trCfg enc enc0 a) (trCfg enc enc0 b) := by
  classical
  induction h with
  | refl a => exact ⟨0,by simp,.refl _⟩
  | @cons k a b hs hr ih =>
    obtain ⟨i,hi,hiP⟩:=one_step_path enc dec enc0 encdec M p a hs
    obtain ⟨j,hj,hjP⟩:=ih (SupportedCompiler.advance_supported M S hS ha)
    have hi' : i≤AlphabetCost.supportedWrites M S+1 := by
      rcases a with ⟨l,v,T⟩
      cases l with
      | none => dsimp at hi; omega
      | some l =>
        have hl:=Finset.some_mem_insertNone.mp ha
        have hw : AlphabetCost.writesCount (M l)≤AlphabetCost.supportedWrites M S :=
          Finset.le_sup (f:=fun l=>AlphabetCost.writesCount (M l)) hl
        dsimp at hi
        omega
    refine ⟨i+j,?_,hiP.trans hjP⟩
    calc i+j≤(AlphabetCost.supportedWrites M S+1)+k*(AlphabetCost.supportedWrites M S+1) := Nat.add_le_add hi' hj
         _=(k+1)*(AlphabetCost.supportedWrites M S+1) := by ring

omit [Inhabited Γ] encdec in
lemma coins_none {c : CoinTM1.Coins Λ} {l : Λ' Γ Λ σ}
    (h : safe (fun l=>c l=none) l) : coins c l=none := by
  cases l with
  | normal l => simp only [coins,safe] at *; rw [h]; rfl
  | write a q => rfl
end MatchingFPRAS.CoinAlphabet

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinStack
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinStack
open Turing TM2to1 TM2to1.Λ' MachineCost StackCost SafeTrace

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

variable (M : Λ → TM2.Stmt Γ Λ σ) (p : Λ → Prop)
lemma go_path {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k,Option (Γ k))}
    (hL : L.map (proj k)=ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n≤ S.length) :
    Path (tr M) (safe p) n ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  rw [←go_time M o q v hL n hn]
  apply Path.of_run
  intro i hi l hl
  rw [go_time M o q v hL i (by omega)] at hl
  cases hl
  trivial

lemma return_path (q : TM2.Stmt Γ Λ σ) (v : σ) (L : ListBlank (∀ k,Option (Γ k))) (n : ℕ) :
    Path (tr M) (safe p) n
      ⟨some (ret q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    apply Path.cons (by intro l hl; cases hl; trivial)
    have hs : advance (TM1.step (tr M))
        ⟨some (ret q),v,(Tape.move .right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩=
        ⟨some (ret q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [advance,TM1.step,tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
        addBottom_nth_succ_fst,Bool.cond_false]
      rw [Function.iterate_succ_apply',Tape.move_right_left]
      rfl
    rw [hs]
    exact ih

theorem statement_path (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (L : ListBlank (∀ k,Option (Γ k))) (H : ℕ) (hS : StackBound S H)
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤ 2*accesses q*(H+accesses q+1) ∧ TrCfg (TM2.stepAux q v S) b ∧
      Path (tr M) (safe p) t
        (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) b := by
  induction q using stmtStRec generalizing v S L H with
  | run k o q ih =>
    let v':=stVar v (S k) o
    let S':=Function.update S k (stWrite v (S k) o)
    have hS' : StackBound S' (H+1):=action_bound hS o v
    obtain ⟨L',hL',hact⟩:=tr_respects_aux₂
      (q:=TM1.Stmt.goto fun _ _=>ret q) hL o
    obtain ⟨t,b,ht,hb,he⟩:=ih v' S' L' (H+1) hS' hL'
    have hgo:=go_path M p o q v (hL k) (S k).length le_rfl
    have hs : advance (TM1.step (tr M))
        ⟨some (go k o q),v,(Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩=
        ⟨some (ret q),v',(Tape.move .right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
      simp only [advance,TM1.step]
      rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
        stk_nth_val _ (hL k),List.getElem?_eq_none (le_of_eq List.length_reverse)]
      simp only [Option.isNone_none,Bool.cond_true]
      rw [hact]
      rfl
    have hstep:=Path.single (M:=tr M) (safe:=safe p)
      (⟨some (go k o q),v,(Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩)
      (by intro l hl; cases hl; trivial)
    rw [hs] at hstep
    have hret:=return_path M p q v' L' (S' k).length
    have hlast:=Path.single (M:=tr M) (safe:=safe p)
      (⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩)
      (by intro l hl; cases hl; trivial)
    have hf : advance (TM1.step (tr M)) ⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩=
        TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L')) := by
      simp only [advance,TM1.step,tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst,
        Bool.cond_true,Option.getD_some]
    rw [hf] at hlast
    refine ⟨(S k).length+1+(S' k).length+1+t,b,?_,?_,?_⟩
    · rw [accesses_run]
      have h₁:=hS k
      have h₂:=hS' k
      nlinarith
    · simpa only [step_run] using hb
    · simpa only [trNormal_run,TM1.stepAux] using (((hgo.trans hstep).trans hret).trans hlast).trans he
  | load a q ih => exact ih (a v) S L H hS hL
  | branch f q r ihq ihr =>
    cases hp:f v
    · obtain ⟨t,b,ht,hb,he⟩:=ihr v S L H hS hL
      refine ⟨t,b,ht.trans ?_,?_,?_⟩
      · simp only [accesses]; gcongr <;> exact le_max_right _ _
      · simpa only [TM2.stepAux,hp,Bool.cond_false] using hb
      · simpa only [trNormal,TM1.stepAux,hp,Bool.cond_false] using he
    · obtain ⟨t,b,ht,hb,he⟩:=ihq v S L H hS hL
      refine ⟨t,b,ht.trans ?_,?_,?_⟩
      · simp only [accesses]; gcongr <;> exact le_max_left _ _
      · simpa only [TM2.stepAux,hp,Bool.cond_true] using hb
      · simpa only [trNormal,TM1.stepAux,hp,Bool.cond_true] using he
  | goto f => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩
  | halt => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩

lemma one_step_path (A : ℕ) (hA : ∀ l,accesses (M l)≤ A)
    {c : TM2.Cfg Γ Λ σ} {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hca : TrCfg c a) (hc : ∀ l,c.l=some l→p l) (H : ℕ) (hS : StackBound c.stk H) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤ 1+2*A*(H+A+1) ∧ TrCfg (advance (TM2.step M) c) b ∧ Path (tr M) (safe p) t a b := by
  rcases hca with ⟨L,hL⟩
  rename_i l v S
  cases l with
  | none => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩
  | some l =>
    obtain ⟨t,b,ht,hb,he⟩:=statement_path M p (M l) v S L H hS hL
    refine ⟨t+1,b,?_,hb,?_⟩
    · have hh : 2*accesses (M l)*(H+accesses (M l)+1)≤ 2*A*(H+A+1) := by
        gcongr <;> exact hA l
      omega
    · apply Path.cons (by intro l' hl; cases hl; exact hc l rfl)
      simpa only [advance,TM1.step,Option.map_some,tr,Option.getD_some] using he

omit [DecidableEq K] in
lemma coins_none {c : CoinTM1.Coins Λ} {l : Λ' K Γ Λ σ}
    (h : safe (fun l=>c l=none) l) : coins c l=none := by
  cases l with
  | normal l => simp only [coins,safe] at *; rw [h]; rfl
  | go k o q => rfl
  | ret q => rfl
end MatchingFPRAS.CoinStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing
open scoped Classical

variable {Γ Λ σ : Type} [Inhabited Γ] [Fintype Γ]
lemma cfg_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    {n : ℕ} (enc : Γ → List.Vector Bool n) (enc0 : enc default=List.Vector.replicate n false)
    (c : TM1.Cfg Γ Λ σ) (hc : c.l∈S.insertNone) :
    (TM1to1.trCfg enc enc0 c).l∈(TM1to1.trSupp M S).insertNone := by
  rcases c with ⟨l,v,T⟩
  cases l with
  | none => simp [TM1to1.trCfg]
  | some l => simpa only [TM1to1.trCfg,Option.map_some,Finset.some_mem_insertNone,normal_mem] using hc
end MatchingFPRAS.CoinAlphabet

namespace MatchingFPRAS.CoinStack
open Turing TM2to1
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
omit [DecidableEq K] in
lemma cfg_supported (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ)
    {c : TM2.Cfg Γ Λ σ} {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hca : TrCfg c a) (hc : c.l∈S.insertNone) : a.l∈(trSupp M S).insertNone := by
  rcases hca with ⟨L,hL⟩
  rename_i l v S'
  cases l with
  | none => simp
  | some l => simpa only [Option.map_some,Finset.some_mem_insertNone,normal_mem] using hc
end MatchingFPRAS.CoinStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProcess
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q α β : Type} [Inhabited Γ]

namespace Implements
variable {M : Table Γ Q} {out : α → Cfg Γ Q} {c : Cfg Γ Q} {p : Experiment α}

lemma execution (h : Implements M out c p) (b : Stream) :
    execute M (p.run b).2 c b=out (p.run b).1 := by
  induction h generalizing b with
  | done a => rfl
  | read c f h ih =>
    simp only [Experiment.run,execute_add]
    exact ih (b 0) (shift 1 b)
  | delay c d n p hs hr ih =>
    simp only [Experiment.run,execute_add,hs]
    exact ih (shift n b)

lemma padded_execution (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost ≤ n) (b : Stream) :
    execute M n c b=out (p.run b).1 := by
  have hb : (p.run b).2 ≤ n:=(Experiment.run_cost p b).trans hn
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hb
  rw [hk,execute_add,h.execution b]
  have he : out (p.run b).1=⟨none,(out (p.run b).1).tape⟩ := by
    cases e:out (p.run b).1 with
    | mk state tape =>
      have hstate := halt (p.run b).1
      rw [e] at hstate
      change state = none at hstate
      subst state
      rfl
  rw [he,execute_halted]

theorem fair_law (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost ≤ n) (f : Cfg Γ Q → ℚ) :
    average (fun b : Bits n=>f (execute M n c (extend b)))=p.mean (fun a=>f (out a)) := by
  simp_rw [h.padded_execution halt n hn]
  exact Experiment.average_run p (fun a=>f (out a)) n hn

end Implements
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PhysicalAlphabet
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream BoolPostCompiler

variable {Q : Type}

lemma tick_up (M : Table Bool Q) (c : Cfg Bool Q) (b : Bool) :
    tick (liftBool M) (upCfg c) b=upCfg (tick M c b) := by
  rcases c with ⟨s,T⟩
  cases s with
  | none => rfl
  | some q =>
    simp only [tick,upCfg,liftBool,(show (T.map up).head=up T.head from rfl),down_up]
    cases e:M q T.head b with
    | none => rfl
    | some qa =>
      rcases qa with ⟨q',act⟩
      cases act with
      | move d => simp only [Option.map_some,TM0.Stmt.map,Tape.map_move]
      | write a => simp only [Option.map_some,TM0.Stmt.map,Tape.map_write]
lemma execute_up (M : Table Bool Q) (n : ℕ) (c : Cfg Bool Q) (b : Stream) :
    execute (liftBool M) n (upCfg c) b=upCfg (execute M n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_up,ih,execute]
lemma Implements.up {α : Type} {M : Table Bool Q} {out : α → Cfg Bool Q}
    {c : Cfg Bool Q} {p : Experiment α} (h : Implements M out c p) :
    Implements (liftBool M) (fun a=>upCfg (out a)) (upCfg c) p := by
  induction h with
  | done a => exact .done a
  | read c f h ih =>
    apply Implements.read
    intro b
    rw [tick_up]
    exact ih b
  | delay c d n p hs hr ih =>
    apply Implements.delay (upCfg c) (upCfg d) n p _ ih
    intro b
    rw [execute_up,hs]
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineStackCompiler
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream SafeTrace
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
omit [DecidableEq K] [∀ k,Fintype (Γ k)] in
lemma height_bound (S : ∀ k,List (Γ k)) : StackCost.StackBound S (height S) :=
  fun k=>Finset.le_sup (f:=fun k=>(S k).length) (Finset.mem_univ k)
omit [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ] in
lemma stackCfg_spec [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
    [Inhabited σ] [Fintype σ] (c : TM2.Cfg Γ Λ σ) : TM2to1.TrCfg c (stackCfg c) := by
  rcases c with ⟨l,v,S⟩
  have h:=TM2to1.TrCfg.mk (Λ:=Λ) (σ:=σ) (q:=l) (v:=v)
    (ListBlank.mk (StackWords.rows S (height S))) (StackWords.rows_projection S _ (height_bound S))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [stackCfg,Tape.mk₁,Tape.mk₂,StackWords.word_blank]
  rfl
omit [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ] in
lemma stackCfg_unique [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
    [Inhabited σ] [Fintype σ] {c : TM2.Cfg Γ Λ σ}
    {a : TM1.Cfg (Alpha K Γ) (L1 K Γ Λ σ) σ} (h : TM2to1.TrCfg c a) : a=stackCfg c := by
  rcases h with ⟨L,hL⟩
  rename_i l v S
  rw [StackWords.unique_rows S (height S) (height_bound S) L hL]
  simp only [stackCfg,Tape.mk₁,Tape.mk₂,StackWords.word_blank]
  rfl

variable (M : Λ → TM2.Stmt Γ Λ σ) (coin : CoinTM1.Coins Λ)
lemma encdec (a : Alpha K Γ) : dec (enc a)=a := FixedEncoding.left_inverse _ a
omit [DecidableEq K] [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ]
  [Inhabited σ] [Fintype σ] in
lemma accesses_bound (l : Λ) : StackCost.accesses (M l)≤accesses M :=
  Finset.le_sup (f:=fun l=>StackCost.accesses (M l)) (Finset.mem_univ l)

theorem deterministic (c : TM2.Cfg Γ Λ σ) (hc : ∀ l,c.l=some l→coin l=none)
    (H : ℕ) (hH : StackCost.StackBound c.stk H) :
    ∃ k,k≤overhead M*(1+2*accesses M*(H+accesses M+1)) ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (cfg c) b=cfg (advance (TM2.step M) c) := by
  obtain ⟨i,a,hi,ha,hpath⟩:=CoinStack.one_step_path M (fun l=>coin l=none)
    (accesses M) (accesses_bound M) (stackCfg_spec c) hc H hH
  have hc1 : (stackCfg c).l∈(support1 M).insertNone :=
    CoinStack.cfg_supported M Finset.univ (stackCfg_spec c) (by simp)
  obtain ⟨j,hj,hpath2⟩:=CoinAlphabet.path_supported enc dec enc0 encdec (program1 M)
    (support1 M) (supports1 M) hpath hc1
  have hc2 : (TM1to1.trCfg enc enc0 (stackCfg c)).l∈(support2 M).insertNone :=
    CoinAlphabet.cfg_supported (program1 M) (support1 M) enc enc0 (stackCfg c) hc1
  have hh:=hpath2.with_support (supports2 M) (fun l hl=>Finset.some_mem_insertNone.mp (hl ▸ hc2))
  obtain ⟨k,hk,he⟩:=hh.physical (coin2 coin)
    (fun l hl=>CoinAlphabet.coins_none (by
      cases l with
      | normal l => exact CoinStack.coins_none hl.1
      | write a q => trivial))
    (SupportedCompiler.cost (program2 M) (support2 M)) (fun l hl=>SupportedCompiler.cost_le _ _ hl.2)
  refine ⟨k,?_,fun b=>?_⟩
  · calc
      k≤(i*(AlphabetCost.supportedWrites (program1 M) (support1 M)+1))*
          SupportedCompiler.cost (program2 M) (support2 M) := hk.trans (Nat.mul_le_mul_right _ hj)
      _=overhead M*i := by unfold overhead; ring
      _≤overhead M*(1+2*accesses M*(H+accesses M+1)) := Nat.mul_le_mul_left _ hi
  · rw [stackCfg_unique ha] at he
    exact he b

omit [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ] in
lemma random [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (l : Λ) (v : σ) (S : ∀ k,List (Γ k)) (f : Bool → Λ) (hf : coin l=some f) (b : Bool) :
    PhysicalPost.tick (table M coin) (cfg ⟨some l,v,S⟩) b=cfg ⟨some (f b),v,S⟩ := by
  apply CoinTM1.coin_tick
  simp only [coin2,CoinAlphabet.coins,CoinStack.coins,hf,Option.map_some]

end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Online
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream

variable {K Λ σ α : Type} {Γ : K → Type} [DecidableEq K]

namespace Executes
variable {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
  {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}

variable [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ]

omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma factor_mono [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (H H' n n' : ℕ) (hH : H≤H') (hn : n≤n') :
    factor M H n ≤ factor M H' n' := by unfold factor; gcongr
omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma factor_shift [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (H n : ℕ) : factor M (H+accesses M) n=factor M H (1+n) := by
  unfold factor
  congr 3; ring

theorem compile (h : Executes M coin out c p) (H : ℕ) (hH : StackCost.StackBound c.stk H) :
    ∃ q : Experiment α,
      PhysicalPost.Implements (table M coin) (fun a=>cfg (out a)) (cfg c) q ∧
      (∀ f : α → ℚ,q.mean f=p.mean f) ∧ q.cost ≤ p.cost*factor M H p.cost := by
  induction h generalizing H with
  | done a => exact ⟨.done a,.done a,fun _=>rfl,by simp [Experiment.cost]⟩
  | read l v S f p hf rest ih =>
    choose q hq hmean hcost using fun b=>ih b H hH
    refine ⟨.read q,.read _ q (fun b=>?_),?_,?_⟩
    · rw [random M coin l v S f hf b]
      exact hq b
    · intro g
      simp only [Experiment.mean,hmean]
    · have hn0 : (p false).cost≤1+max (p false).cost (p true).cost := by omega
      have hn1 : (p true).cost≤1+max (p false).cost (p true).cost := by omega
      have hc0 := (hcost false).trans (Nat.mul_le_mul_left (p false).cost (factor_mono (M:=M) H H _ _ le_rfl hn0))
      have hc1 := (hcost true).trans (Nat.mul_le_mul_left (p true).cost (factor_mono (M:=M) H H _ _ le_rfl hn1))
      have hp : 1≤factor M H (1+max (p false).cost (p true).cost) := by unfold factor; omega
      simp only [Experiment.cost]
      have hf0 := Nat.mul_le_mul_right (factor M H (1+max (p false).cost (p true).cost)) (le_max_left (p false).cost (p true).cost)
      have hf1 := Nat.mul_le_mul_right (factor M H (1+max (p false).cost (p true).cost)) (le_max_right (p false).cost (p true).cost)
      calc
        1+max (q false).cost (q true).cost ≤ 1+max (p false).cost (p true).cost*factor M H (1+max (p false).cost (p true).cost) := by omega
        _≤ (1+max (p false).cost (p true).cost)*factor M H (1+max (p false).cost (p true).cost) := by nlinarith
  | step l v S p safe rest ih =>
    let c : TM2.Cfg Γ Λ σ:=⟨some l,v,S⟩
    have hs : ∀ u,c.l=some u→coin u=none := by intro u hu; cases hu; exact safe
    obtain ⟨k,hk,he⟩:=deterministic M coin c hs H hH
    obtain ⟨q,hq,hm,hc⟩:=ih (H+accesses M) (StackCost.advance_bound M _ (accesses_bound M) c H hH)
    refine ⟨.delay k q,.delay _ _ k q he hq,hm,?_⟩
    simp only [Experiment.cost]
    rw [factor_shift] at hc
    have hfac : k≤factor M H (1+p.cost) := by
      apply hk.trans
      unfold factor
      have hh : H+accesses M+1≤H+(1+p.cost)*accesses M+1 := by nlinarith
      have hb : overhead M*(1+2*accesses M*(H+accesses M+1))≤
        overhead M*(1+2*accesses M*(H+(1+p.cost)*accesses M+1)) := by gcongr
      omega
    nlinarith
end Executes
end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalSequential
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R α β : Type} [Inhabited Γ]

lemma tick_left (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (q : Q) (T : Tape Γ) (b : Bool) :
    tick (seq M N r₀) (leftCfg r₀ ⟨some q,T⟩) b=leftCfg r₀ (tick M ⟨some q,T⟩ b) := by
  cases h : M q T.head b with
  | none => simp only [tick,leftCfg,seq,h,Option.elim_some,Option.elim_none,Tape.write_self]
  | some qa => rcases qa with ⟨q',act⟩;cases act <;> simp only [tick,leftCfg,seq,h,Option.elim_some]
lemma tick_right (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (c : Cfg Γ R) (b : Bool) :
    tick (seq M N r₀) (rightCfg c) b=rightCfg (tick N c b) := by
  rcases c with ⟨s,T⟩
  cases s with
  | none => rfl
  | some r =>
    cases h:N r T.head b with
    | none => simp only [tick,rightCfg,Option.map_some,seq,h,Option.map_none]
    | some ra => rcases ra with ⟨r',act⟩;cases act <;> simp only [tick,rightCfg,seq,h,Option.map_some]
lemma execute_right (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (n : ℕ) (c : Cfg Γ R) (b : Stream) :
    execute (seq M N r₀) n (rightCfg c) b=rightCfg (execute N n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_right,ih,execute]
lemma Implements.right {M : Table Γ Q} {N : Table Γ R} (r₀ : R) {out : α→Cfg Γ R}
    {c : Cfg Γ R} {p : Experiment α} (h : Implements N out c p) :
    Implements (seq M N r₀) (rightCfg ∘ out) (rightCfg c) p := by
  induction h with
  | done a => exact .done a
  | read c f h ih => apply Implements.read;intro b;rw [tick_right];exact ih b
  | delay c d n p hs hr ih =>
    exact .delay _ _ n _ (fun b=>by rw [execute_right,hs]) ih

lemma early_cost (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) : (early M n c).cost≤n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    cases h:c.state <;> simp only [early,h,Experiment.cost]
    · omega
    · have h0:=ih (tick M c false); have h1:=ih (tick M c true); omega
lemma early_run (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Stream) :
    ((early M n c).run b).1=execute M n c b := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => rw [execute_halted];rfl
    | some q => simp only [early,Experiment.run,execute];exact ih _ _
lemma early_mean (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (f : Cfg Γ Q→ℚ) :
    (early M n c).mean f=average (fun b : Bits n=>f (execute M n c (extend b))) := by
  simpa only [early_run] using (Experiment.average_run (early M n c) f n (early_cost M n c)).symm
lemma early_left (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (n : ℕ) (c : Cfg Γ Q) :
    Implements (seq M N r₀) (leftCfg r₀) (leftCfg r₀ c) (early M n c) := by
  induction n generalizing c with
  | zero => exact .done c
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => exact .done _
    | some q =>
      apply Implements.read
      intro b
      rw [tick_left]
      exact ih _
lemma Implements.early_mean {M : Table Γ Q} {out : α→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment α} (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost≤n) (f : Cfg Γ Q→ℚ) :
    (early M n c).mean f=p.mean (fun a=>f (out a)) := by
  rw [PhysicalPost.early_mean]
  exact h.fair_law halt n hn f
lemma Implements.bind_all {M : Table Γ Q} {out : α→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment α} (h : Implements M out c p) (q : α→Experiment β) (out' : β→Cfg Γ Q)
    (hq : p.All (fun a=>Implements M out' (out a) (q a))) :
    Implements M out' c (p.bind q) := by
  induction h with
  | done a => exact hq
  | read c f h ih => exact .read c _ (fun b=>by cases b;exact ih false hq.1;exact ih true hq.2)
  | delay c d n p hs hr ih => exact .delay c d n _ hs (ih hq)
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TapeTools
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
lemma mk₂_left_nil (R : List Γ) :
    (Tape.mk₂ [] R).move .left=Tape.mk₂ [] (default::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk,ListBlank.tail_mk,ListBlank.head_mk]
lemma blank_zero (n : ℕ) : (ListBlank.mk (List.replicate n (default : Γ)))=ListBlank.mk [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,←ListBlank.cons_mk,ih]; exact ListBlank.cons_head_tail (ListBlank.mk [])
lemma blank_append_zero (L : List Γ) (n : ℕ) :
    ListBlank.mk (L++List.replicate n default)=ListBlank.mk L := by
  induction L with
  | nil => exact blank_zero n
  | cons a L ih => rw [List.cons_append,←ListBlank.cons_mk,ih,ListBlank.cons_mk]

lemma Exec.refl (M : Λ→TM1.Stmt Γ Λ σ) (c : TM1.Cfg Γ Λ σ) : Exec M c c 0 := ⟨0,le_rfl,rfl⟩
lemma Exec.step (M : Λ→TM1.Stmt Γ Λ σ) (l : Λ) (v : σ) (T : Tape Γ) :
    Exec M ⟨some l,v,T⟩ (TM1.stepAux (M l) v T) 1 := ⟨1,le_rfl,rfl⟩
lemma Exec.trans {M : Λ→TM1.Stmt Γ Λ σ} {c d e : TM1.Cfg Γ Λ σ} {s t : ℕ}
    (h : Exec M c d s) (g : Exec M d e t) : Exec M c e (s+t) := by
  obtain ⟨i,hi,he⟩:=h
  obtain ⟨j,hj,hf⟩:=g
  exact ⟨i+j,Nat.add_le_add hi hj,by rw [MachineCost.run_add,he,hf]⟩
lemma Exec.mono {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {s t : ℕ}
    (h : Exec M c d s) (hst : s≤t) : Exec M c d t :=
  let ⟨k,hk,he⟩:=h; ⟨k,hk.trans hst,he⟩

lemma select_step [DecidableEq σ] (vs : List σ) (f : σ→TM1.Stmt Γ Λ σ)
    (fallback : TM1.Stmt Γ Λ σ) (v : σ) (hv : v∈vs) (T : Tape Γ) :
    TM1.stepAux (select vs f fallback) v T=TM1.stepAux (f v) v T := by
  induction vs with
  | nil => simp at hv
  | cons a as ih =>
    simp only [List.mem_cons] at hv
    simp only [select,List.foldr_cons,TM1.stepAux]
    by_cases h:v=a
    · simp only [h,decide_true,Bool.cond_true]
    · simp only [h,decide_false,Bool.cond_false]
      exact ih (hv.resolve_left h)

lemma writeLeft_step (xs : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) (R : List Γ) :
    TM1.stepAux (writeLeft xs q) v (Tape.mk₂ [] (default::R))=
      TM1.stepAux q v (Tape.mk₂ [] (default::xs.reverse++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons b bs ih =>
    simp only [writeLeft,List.foldr_cons,TM1.stepAux,mk₂_write,mk₂_left_nil]
    rw [show List.foldr (fun a tail=>TM1.Stmt.write (fun _ _=>a) (.move .left tail)) q bs=writeLeft bs q from rfl,ih]
    simp only [List.reverse_cons,List.cons_append,List.append_assoc,List.nil_append]

lemma eraseToLeft_step (xs L R : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    TM1.stepAux (eraseToLeft xs.length q) v (Tape.mk₂ (xs++L) R)=
      TM1.stepAux q v (Tape.mk₂ L (List.replicate xs.length default++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,eraseToLeft,TM1.stepAux,List.cons_append,mk₂_left,mk₂_write]
    rw [show Nat.rec q (fun _ tail=>TM1.Stmt.move .left (.write (fun _ _=>default) tail)) xs.length=eraseToLeft xs.length q from rfl,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]

variable {I : Type} [DecidableEq I]
lemma grab_step (is : List I) (f v : I→Γ) (q : TM1.Stmt Γ Λ (I→Γ)) (L R : List Γ) :
    TM1.stepAux (grab is q) v (Tape.mk₂ L (is.map f++R))=
      TM1.stepAux q (is.foldl (fun v i=>Function.update v i (f i)) v)
        (Tape.mk₂ ((is.map f).reverse++L) R) := by
  induction is generalizing v L with
  | nil => rfl
  | cons i is ih =>
    simp only [grab,List.foldr_cons,List.map_cons,List.cons_append,TM1.stepAux,mk₂_head,mk₂_right,List.foldl_cons]
    rw [show List.foldr (fun i tail=>TM1.Stmt.load (fun a v=>Function.update v i a) (.move .right tail)) q is=grab is q from rfl,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
omit [Inhabited Γ] in
lemma fold_updates (is : List I) (f v : I→Γ) (i : I) :
    (is.foldl (fun v i=>Function.update v i (f i)) v) i=if i∈is then f i else v i := by
  induction is generalizing v with
  | nil => simp
  | cons a is ih =>
    rw [List.foldl_cons,ih]
    by_cases hi:i∈is <;> by_cases ha:i=a <;> simp [hi,ha]
lemma grab_fin (n : ℕ) (f v : Fin n→Γ) (q : TM1.Stmt Γ Λ (Fin n→Γ)) (L R : List Γ) :
    TM1.stepAux (grab (List.finRange n) q) v (Tape.mk₂ L (List.ofFn f++R))=
      TM1.stepAux q f (Tape.mk₂ ((List.ofFn f).reverse++L) R) := by
  have he : (List.finRange n).map f=List.ofFn f := List.ofFn_eq_map.symm
  rw [←he,grab_step]
  have hf : (List.finRange n).foldl (fun v i=>Function.update v i (f i)) v=f := by
    funext i
    rw [fold_updates]
    simp
  rw [hf]
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Physical
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Fintype Λ] [Fintype σ] [Inhabited σ]
omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
lemma Exec.physical {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {t : ℕ}
    (h : Exec M c d t) : ∃ k,k≤t*programCost M ∧ ∀ b : Stream,
      PhysicalPost.execute (table M) k (CoinTM1.trCfg c) b=CoinTM1.trCfg d := by
  obtain ⟨n,hn,he⟩:=h
  have hp:=SafeTrace.Path.of_run (safe:=fun _=>True) (M:=M) n c (fun _ _ _ _=>trivial)
  rw [he] at hp
  obtain ⟨k,hk,hb⟩:=hp.physical (fun _=>none) (fun _ _=>rfl) (programCost M)
    (fun l _=>statementCost_le_programCost M l)
  exact ⟨k,hk.trans (Nat.mul_le_mul_right _ hn),hb⟩
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A : Type}
lemma mean_congr_all (p : Experiment A) (f g : A→ℚ) (h : p.All (fun a=>f a=g a)) : p.mean f=p.mean g := by
  induction p with
  | done a => exact h
  | delay n p ih => exact ih h
  | read p ih => simp only [mean,ih false h.1,ih true h.2]
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q A B : Type} [Inhabited Γ]
lemma Implements.map_all {M : Table Γ Q} {out : A→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (f : A→B) (out' : B→Cfg Γ Q)
    (he : p.All (fun a=>out a=out' (f a))) : Implements M out' c (p.map f) := by
  induction h with
  | done a => rw [he];exact .done (f a)
  | read c p h ih => exact .read _ _ (fun b=>by cases b;exact ih false he.1;exact ih true he.2)
  | delay c d n p hs hr ih => exact .delay _ _ n _ hs (ih he)
lemma early_implements (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) : Implements M id c (early M n c) := by
  induction n generalizing c with
  | zero => exact .done c
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => exact .done _
    | some q => exact .read _ _ (fun b=>ih _)
lemma Implements.early_all {M : Table Γ Q} {out : A→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost≤n) : (early M n c).All (fun d=>d.state=none) := by
  apply Experiment.all_of_mean_eq (p:=(p.map out)) (fun f=>by rw [Experiment.mean_map];exact h.early_mean halt n hn f)
  rw [Experiment.all_map]
  exact (Experiment.all_true _).mono (fun a _=>halt a)

namespace Program
lemma earlyTapes_cost (P : Program) (n : ℕ) (T : Tape Symbol) : (P.earlyTapes n T).cost≤n := by
  rw [earlyTapes,Experiment.cost_map];exact early_cost _ _ _
lemma Realizes.early {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (h : P.Realizes input f N) :
    Implements P.table P.final (P.initial input) (P.earlyTapes N input) ∧
      (∀ w,(P.earlyTapes N input).mean w=f.mean w) := by
  obtain ⟨p,hp,hm,hc⟩:=h
  refine ⟨?_,fun w=>?_⟩
  · apply (early_implements P.table N (P.initial input)).map_all Cfg.tape P.final
    exact (hp.early_all (fun _=>rfl) N hc).mono (by intro d hd;cases d; simp only [id_eq,final] at *;cases hd;rfl)
  · rw [earlyTapes,Experiment.mean_map,hp.early_mean (fun _=>rfl) N hc]
    exact hm w
lemma seq_realizes (P R : Program) (input : Tape Symbol) (f : Experiment (Tape Symbol))
    (g : Tape Symbol→Experiment (Tape Symbol)) (N S : ℕ)
    (hP : P.Realizes input f N) (hR : f.All (fun T=>R.Realizes T (g T) S)) :
    (P.seq R).Realizes input (f.bind g) (N+S) := by
  let p:=early P.table N (P.initial input)
  let q:=fun c : Cfg Symbol P.State=>R.earlyTapes S c.tape
  have hmean (h : Cfg Symbol P.State→ℚ) : p.mean h=f.mean (fun T=>h (P.final T)) := by
    obtain ⟨v,hv,hm,hc⟩:=hP
    rw [hv.early_mean (fun _=>rfl) N hc]
    exact hm _
  have hall : p.All (fun c=>c.state=none ∧ R.Realizes c.tape (g c.tape) S) := by
    apply Experiment.all_of_mean_eq (p:=f.map P.final) (fun h=>by rw [Experiment.mean_map];exact hmean h)
    rw [Experiment.all_map]
    exact hR.mono (fun T hT=>⟨rfl,hT⟩)
  have himpl : Implements (P.seq R).table (fun T=>rightCfg (R.final T))
      ((P.seq R).initial input) (p.bind q) := by
    apply (early_left P.table R.table R.entry N (P.initial input)).bind_all q _
    exact hall.mono (by
      intro c hc
      have hq:=(hc.2.early).1.right (M:=P.table) R.entry
      have he:leftCfg R.entry c=rightCfg (R.initial c.tape) := by
        rcases c with ⟨s,T⟩;simp only at hc;cases hc.1;rfl
      rw [he]
      exact hq)
  refine ⟨p.bind q,himpl,?_,?_⟩
  · intro w
    rw [Experiment.mean_bind,hmean,Experiment.mean_bind]
    apply Experiment.mean_congr_all
    exact hR.mono (fun T hT=>hT.early.2 w)
  · exact (Experiment.cost_bind_le p q S (fun c=>earlyTapes_cost R S c.tape)).trans
      (Nat.add_le_add_right (early_cost _ N _) S)

lemma realizes_TM1 {Λ σ : Type} [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (v v' : σ) (input output : Tape Symbol) (n : ℕ)
    (he : LiteralTape.Exec M ⟨some l,v,input⟩ ⟨none,v',output⟩ n) :
    (ofTM1 M l v).Realizes input (.done output) (n*MachineCost.programCost M) := by
  obtain ⟨k,hk,hb⟩:=he.physical
  refine ⟨.delay k (.done output),?_,fun _=>rfl,by simpa only [Experiment.cost,Nat.add_zero] using hk⟩
  exact .delay _ _ k _ hb (.done output)
end Program
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreePostRealization
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc Turing Polynomial

lemma inputStacks_bound {A : Type} [Codec A] (a : A) : StackCost.StackBound (inputStacks a) (weight a) := by
  intro i
  have h:=weight_pos a
  cases i with
  | inr i => simp [inputStacks,encodeEnv]
  | inl i =>
    simp only [inputStacks,encodeEnv,env]
    split_ifs <;> first
    | exact le_rfl
    | simpa only [TreeData.encode,List.length_singleton] using (Nat.succ_le_iff.mpr h)

end MatchingFPRAS.TreePost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlinePhysicalProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing TreeTyped TreeData TreeFunction TreeMachine TreePost PhysicalPost PhysicalStream

lemma input_height {A : Type} [Codec A] (a : A) : OnlineStack.height (inputStacks a)=weight a := by
  apply le_antisymm
  · exact Finset.sup_le (fun k _=>inputStacks_bound a k)
  · have h:=OnlineStack.height_bound (inputStacks a) (Sum.inl (0 : Reg))
    simpa only [inputStacks,encodeEnv,env,ite_true, if_true,weight,TreeFunction.size] using h

lemma cfg_packed {A : Type} [Codec A] (P : OnlineProc.Proc (K Reg)) (a : A) (l : Option P.Label) :
    upCfg (OnlineStack.cfg (⟨l,none,inputStacks a⟩ : StoreCfg P))=
      ⟨l.map (fun u=>(Sum.inl (TM1to1.Λ'.normal (TM2to1.Λ'.normal u)),none)),Tape.mk₁ (packed a)⟩ := by
  simp only [upCfg,OnlineStack.cfg,OnlineStack.stackCfg,input_height,CoinTM1.trCfg,
    TM1to1.trCfg,TM1to1.trTape,TM1to1.trTape',Tape.mk₁,Tape.mk₂,Tape.mk'_left,Tape.mk'_right₀,
    ListBlank.flatMap_mk,List.flatMap_nil,Option.map_map]
  rw [Tape.map_mk']
  rfl

lemma physical_realizes {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) (a : A) :
    (physicalProgram F).Realizes (Tape.mk₁ (packed a))
      ((f a).map (fun b=>Tape.mk₁ (packed b))) (physicalCost F a) := by
  obtain ⟨p,hp,hm,hc⟩:=F.correct a .nil
  obtain ⟨q,hq,hqm,hqc⟩:=hp.compile (weight a) (inputStacks_bound a)
  have he:=hq.up
  have hi : upCfg (OnlineStack.cfg (initial F.program (encode a) .nil))=
      (physicalProgram F).initial (Tape.mk₁ (packed a)) := cfg_packed F.program a (some default)
  have ho (b : B) : upCfg (OnlineStack.cfg (final F.program (encode b) .nil))=
      (physicalProgram F).final (Tape.mk₁ (packed b)) := cfg_packed F.program b none
  rw [hi] at he
  simp_rw [ho] at he
  refine ⟨q.map (fun b=>Tape.mk₁ (packed b)),?_,?_,?_⟩
  · exact he.map_all _ _ (Experiment.all_true _ |>.mono (fun _ _=>rfl))
  · intro w
    rw [Experiment.mean_map,hqm,hm,Experiment.mean_map]
  · rw [Experiment.cost_map]
    exact hqc.trans (Nat.mul_le_mul hc (OnlineStack.Executes.factor_mono _ _ _ _ le_rfl hc))
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgramMap
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost.Program
open Turing PhysicalStream

lemma Realizes.congr {P : Program} {input : Tape Symbol} {f g : Experiment (Tape Symbol)} {N : ℕ}
    (h : P.Realizes input f N) (he : ∀ w,f.mean w=g.mean w) : P.Realizes input g N := by
  obtain ⟨p,hp,hm,hc⟩:=h
  exact ⟨p,hp,fun w=>(hm w).trans (he w),hc⟩
lemma Realizes.mono {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N S : ℕ}
    (h : P.Realizes input f N) (hn : N≤S) : P.Realizes input f S := by
  obtain ⟨p,hp,hm,hc⟩:=h
  exact ⟨p,hp,hm,hc.trans hn⟩
lemma seq_realizes_map {A : Type} (P R : Program) (input : Tape Symbol) (f : Experiment A)
    (enc : A→Tape Symbol) (g : A→Experiment (Tape Symbol)) (N S : ℕ)
    (hP : P.Realizes input (f.map enc) N) (hR : f.All (fun a=>R.Realizes (enc a) (g a) S)) :
    (P.seq R).Realizes input (f.bind g) (N+S) := by
  have hR' : (f.map enc).All (fun T=>R.Realizes T (R.earlyTapes S T) S) := by
    rw [Experiment.all_map]
    exact hR.mono (fun a ha=>⟨R.earlyTapes S (enc a),ha.early.1,fun _=>rfl,earlyTapes_cost R S (enc a)⟩)
  apply (seq_realizes P R input (f.map enc) (R.earlyTapes S) N S hP hR').congr
  intro w
  rw [Experiment.mean_bind,Experiment.mean_map,Experiment.mean_bind]
  exact f.mean_congr_all _ _ (hR.mono (fun a ha=>ha.early.2 w))
end MatchingFPRAS.PhysicalPost.Program

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgramSeal
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost.Program
open Turing PhysicalStream

lemma run_tape (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).tape=
      (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).tape := by
  let : Inhabited {q //q∈P.states}:=⟨⟨P.entry,P.entry_mem⟩⟩
  rw [machine,restrictedMachine_run]
  exact (congrArg Cfg.tape (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))).symm
lemma run_halted (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n)
    (h : (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=none) :
    (MatchingFPRAS.run P.machine input b).state=none := by
  let : Inhabited {q //q∈P.states}:=⟨⟨P.entry,P.entry_mem⟩⟩
  have he:=congrArg Cfg.state (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))
  have hs : (execute (restrict P.table P.states P.supported) n
      ⟨some default,Tape.mk₁ input⟩ (extend b)).state=none := by
    exact Option.map_eq_none_iff.mp (he.symm.trans h)
  rw [machine,restrictedMachine_run]
  change ((execute (restrict P.table P.states P.supported) n
    ⟨some default,Tape.mk₁ input⟩ (extend b)).state.map enumeration)=none
  rw [hs,Option.map_none]
lemma Realizes.run_all {P : Program} {input : List Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (hP : P.Realizes (Tape.mk₁ input) f N) (R : Tape Symbol→Prop) (hf : f.All R)
    (n : ℕ) (hn : N≤n) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).state=none ∧
      R (MatchingFPRAS.run P.machine input b).tape := by
  obtain ⟨p,hp,hm,hc⟩:=hP
  have hex:=hp.padded_execution (fun _=>rfl) n (hc.trans hn) (extend b)
  have ht : (MatchingFPRAS.run P.machine input b).tape=(p.run (extend b)).1 := by
    rw [run_tape,hex];rfl
  refine ⟨run_halted P input n b (by rw [hex];rfl),?_⟩
  rw [ht]
  exact p.all_run R (Experiment.all_of_mean_eq hm R hf) (extend b)
lemma Realizes.run_mean {P : Program} {input : List Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (hP : P.Realizes (Tape.mk₁ input) f N) (w : Tape Symbol→ℚ)
    (n : ℕ) (hn : N≤n) :
    average (fun b : Bits n=>w (MatchingFPRAS.run P.machine input b).tape)=f.mean w := by
  obtain ⟨p,hp,hm,hc⟩:=hP
  simp_rw [run_tape]
  exact (hp.fair_law (fun _=>rfl) n (hc.trans hn) (fun c=>w c.tape)).trans (hm w)
end MatchingFPRAS.PhysicalPost.Program

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_BlockMap
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Λ σ : Type}
lemma scan_left (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (mark : Symbol)
    (hs : ∀ v T,T.head≠mark→TM1.stepAux (M l) v T=⟨some l,v,T.move .left⟩)
    (xs L R : List Symbol) (v : σ) (hx : ∀ a∈xs,a≠mark) :
    Exec M ⟨some l,v,(Tape.mk₂ (xs++mark::L) R).move .left⟩
      ⟨some l,v,Tape.mk₂ L (mark::(xs.reverse++R))⟩ xs.length := by
  induction xs generalizing R with
  | nil => simpa using Exec.refl M (⟨some l,v,Tape.mk₂ L (mark::R)⟩ : TM1.Cfg Symbol Λ σ)
  | cons a xs ih =>
    simp only [List.cons_append,mk₂_left]
    have h1:=Exec.step M l v (Tape.mk₂ (xs++mark::L) (a::R))
    rw [hs v _ (by simpa using hx a (by simp))] at h1
    have h2:=ih (a::R) (fun b hb=>hx b (by simp [hb]))
    have h:=h1.trans h2
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm] using h
lemma scan_right (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (mark : Symbol)
    (hs : ∀ v T,T.head≠mark→TM1.stepAux (M l) v T=⟨some l,v,T.move .right⟩)
    (xs L R : List Symbol) (v : σ) (hx : ∀ a∈xs,a≠mark) :
    Exec M ⟨some l,v,Tape.mk₂ L (xs++mark::R)⟩
      ⟨some l,v,Tape.mk₂ (xs.reverse++L) (mark::R)⟩ xs.length := by
  induction xs generalizing L with
  | nil => exact Exec.refl M _
  | cons a xs ih =>
    simp only [List.cons_append]
    have h1:=Exec.step M l v (Tape.mk₂ L (a::(xs++mark::R)))
    rw [hs v _ (by simpa using hx a (by simp)),mk₂_right] at h1
    have h2:=ih (a::L) (fun b hb=>hx b (by simp [hb]))
    have h:=h1.trans h2
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm] using h
end MatchingFPRAS.LiteralTape

namespace MatchingFPRAS.LiteralBlockMap
open Turing LiteralTape

variable (w : ℕ) (h : Block w→List Symbol) (header : List Symbol)
local notation "M" => code w h header
lemma seek_path (v : Block w) (T : Tape Symbol) (ht : T.head≠6) :
    TM1.stepAux (M .seek) v T=⟨some .seek,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma back_path (v : Block w) (T : Tape Symbol) (ht : T.head≠7) :
    TM1.stepAux (M .back) v T=⟨some .back,v,T.move .right⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma stopSep_path (v : Block w) (T : Tape Symbol) (ht : T.head≠7) :
    TM1.stepAux (M .stopSep) v T=⟨some .stopSep,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma stopOut_path (v : Block w) (T : Tape Symbol) (ht : T.head≠6) :
    TM1.stepAux (M .stopOut) v T=⟨some .stopOut,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]

lemma start_step (input : List Symbol) (v : Block w) :
    Exec M ⟨some .start,v,Tape.mk₁ input⟩ ⟨some .read,v,working [] 0 input⟩ 1 := by
  have hh:=Exec.step M .start v (Tape.mk₁ input)
  simpa only [code,TM1.stepAux,Tape.mk₁,mk₂_left_nil,mk₂_write,mk₂_right,working,List.replicate_zero,
    List.reverse_nil,List.nil_append] using hh

lemma seek_write (v : Block w) (R : List Symbol) :
    Exec M ⟨some .seek,v,Tape.mk₂ [] (6::R)⟩
      ⟨some .back,v,Tape.mk₂ [6] (h v++R)⟩ 1 := by
  have hh:=Exec.step M .seek v (Tape.mk₂ [] (6::R))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true] at hh
  rw [select_step _ _ _ v (by simp)] at hh
  have hs:=writeLeft_step (Γ:=Symbol) (h v).reverse
    (.write (fun _ _=>6) (.move .right (.goto (fun _ _=>Label.back)))) v R
  simp only [Fin.default_eq_zero,List.reverse_reverse,List.cons_append,TM1.stepAux,mk₂_write,mk₂_right] at hs
  simpa only [TM1.stepAux,mk₂_write,hs] using hh
lemma stopOut_write (v : Block w) (R : List Symbol) :
    Exec M ⟨some .stopOut,v,Tape.mk₂ [] (6::R)⟩
      ⟨none,v,Tape.mk₂ [0] (header++R)⟩ 1 := by
  have hh:=Exec.step M .stopOut v (Tape.mk₂ [] (6::R))
  have hs:=writeLeft_step (Γ:=Symbol) header.reverse
    (.write (fun _ _=>0) (.move .right (.halt : TM1.Stmt Symbol Label (Block w)))) v R
  simp only [Fin.default_eq_zero,List.reverse_reverse,List.cons_append,TM1.stepAux,mk₂_write,mk₂_right] at hs
  simpa only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_write,hs] using hh

lemma read_block (hw : 0<w) (b v : Block w) (hb : b≠fun _=>0)
    (out input : List Symbol) (gap : ℕ) :
    Exec M ⟨some .read,v,working out gap (List.ofFn b++input)⟩
      ⟨some .seek,b,(Tape.mk₂ (List.replicate gap 0++out.reverse++[6])
        (List.replicate w 0++7::input)).move .left⟩ 1 := by
  have hh:=Exec.step M .read v (working out gap (List.ofFn b++input))
  change Exec M _ (TM1.stepAux (grab _ _) v _) 1 at hh
  rw [working,grab_fin] at hh
  simp only [TM1.stepAux,hb,decide_false,Bool.cond_false] at hh
  cases hr : (List.ofFn b).reverse with
  | nil => have hl:=congrArg List.length hr; simp at hl; omega
  | cons a xs =>
    have hl : (xs++[7]).length=w := by
      have hh:=congrArg List.length hr
      simp only [List.length_reverse,List.length_ofFn,List.length_cons] at hh
      simp only [List.length_append,List.length_singleton]; omega
    rw [hr] at hh
    simp only [List.cons_append,mk₂_left,mk₂_write] at hh
    rw [show xs++7::(List.replicate gap 0++out.reverse++[6])=
      (xs++[7])++(List.replicate gap 0++out.reverse++[6]) by simp] at hh
    have ht:=eraseToLeft_step (xs++[7]) (List.replicate gap 0++out.reverse++[6]) (7::input)
      (.move .left (.goto (fun _ _=>Label.seek))) b
    rw [hl] at ht
    rw [ht] at hh
    exact hh
lemma cycle (hw : 0<w) (b v : Block w) (hb : b≠fun _=>0)
    (out input : List Symbol) (gap : ℕ)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) (hh : ∀ a∈h b,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap (List.ofFn b++input)⟩
      ⟨some .read,b,working (h b++out) (gap+w) input⟩
      (3+2*(out.length+gap)+(h b).length+w) := by
  have ha:=read_block w h header hw b v hb out input gap
  have hx : ∀ a∈List.replicate gap (0:Symbol)++out.reverse,a≠6 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have := (List.eq_of_mem_replicate ha); subst a; decide
    · exact (ho a (List.mem_reverse.mp ha)).1
  have hs:=scan_left M .seek 6 (seek_path w h header)
    (List.replicate gap 0++out.reverse) [] (List.replicate w 0++7::input) b hx
  have he : (List.replicate gap (0:Symbol)++out.reverse).reverse++(List.replicate w 0++7::input)=
      out++List.replicate (gap+w) 0++7::input := by
    simp only [List.reverse_append,List.reverse_reverse,List.reverse_replicate,List.replicate_add,List.append_assoc]
  rw [he] at hs
  have ht:=seek_write w h header b (out++List.replicate (gap+w) 0++7::input)
  have hy : ∀ a∈h b++out++List.replicate (gap+w) (0:Symbol),a≠7 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · rcases List.mem_append.mp ha with ha|ha
      · exact (hh a ha).2
      · exact (ho a ha).2
    · have := List.eq_of_mem_replicate ha; subst a; decide
  have hu:=scan_right M .back 7 (back_path w h header)
    (h b++out++List.replicate (gap+w) 0) [6] input b hy
  have hv:=Exec.step M .back b
    (Tape.mk₂ ((h b++out++List.replicate (gap+w) 0).reverse++[6]) (7::input))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_right] at hv
  simp only [List.append_assoc] at ha hs ht hu hv
  have hh:=((ha.trans hs).trans ht).trans (hu.trans hv)
  simp only [working,List.append_assoc,List.reverse_append,List.reverse_replicate,List.length_append,
    List.length_replicate,List.length_reverse] at hh ⊢
  apply Exec.mono hh
  omega

lemma mk₂_blanks (L R : List Symbol) (n : ℕ) :
    Tape.mk₂ L (R++List.replicate n 0)=Tape.mk₂ L R := by
  simp only [Tape.mk₂,show (0:Symbol)=default from rfl,blank_append_zero]
lemma mk₂_replicate (L : List Symbol) (n : ℕ) :
    Tape.mk₂ L (List.replicate n 0)=Tape.mk₂ L [] := by
  simpa only [List.nil_append] using mk₂_blanks L [] n
lemma mk₂_zero_left (R : List Symbol) : Tape.mk₂ [0] R=Tape.mk₁ R := by
  change Tape.mk' (ListBlank.mk (List.replicate 1 (default:Symbol))) _=Tape.mk' (ListBlank.mk []) _
  rw [blank_zero]

lemma finish (v : Block w) (out : List Symbol) (gap : ℕ)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap []⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++out)⟩ (3+w+gap+out.length) := by
  have hz : List.ofFn (fun _ : Fin w=>(0:Symbol))=List.replicate w 0 := by simp
  have ha:=Exec.step M .read v (working out gap [])
  change Exec M _ (TM1.stepAux (grab _ _) v _) 1 at ha
  rw [working,←mk₂_blanks _ [] w] at ha
  simp only [List.nil_append,←hz] at ha
  rw [show List.ofFn (fun _ : Fin w=>(0:Symbol))=
    List.ofFn (fun _ : Fin w=>(0:Symbol))++[] by simp,grab_fin] at ha
  simp only [TM1.stepAux,decide_true,Bool.cond_true,hz,List.reverse_replicate] at ha
  have hs:=scan_left M .stopSep 7 (stopSep_path w h header) (List.replicate w 0)
    (List.replicate gap 0++out.reverse++[6]) [] (fun _=>0)
    (by intro a ha; have := List.eq_of_mem_replicate ha; subst a; decide)
  have ht:=Exec.step M .stopSep (fun _ : Fin w=>(0:Symbol))
    (Tape.mk₂ (List.replicate gap 0++out.reverse++[6]) (7::List.replicate w 0))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_write] at ht
  have hx : ∀ a∈List.replicate gap (0:Symbol)++out.reverse,a≠6 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have := List.eq_of_mem_replicate ha; subst a; decide
    · exact (ho a (List.mem_reverse.mp ha)).1
  have hu:=scan_left M .stopOut 6 (stopOut_path w h header)
    (List.replicate gap 0++out.reverse) [] (0::List.replicate w 0) (fun _=>0) hx
  have hv:=stopOut_write w h header (fun _=>0)
    (out++List.replicate (gap+1+w) 0)
  have he : (List.replicate gap (0:Symbol)++out.reverse).reverse++(0::List.replicate w 0)=
      out++List.replicate (gap+1+w) 0 := by
    simp only [List.reverse_append,List.reverse_reverse,List.reverse_replicate,List.replicate_add,List.append_assoc,List.replicate_one,List.singleton_append]
  rw [he] at hu
  simp only [List.length_replicate,List.reverse_replicate,List.append_nil] at hs
  have hb:=((ha.trans hs).trans ht).trans (hu.trans hv)
  rw [←List.append_assoc,mk₂_blanks,mk₂_zero_left] at hb
  simp only [List.append_assoc,List.length_append,List.length_reverse,List.length_replicate] at hb
  simp only [List.append_nil,mk₂_replicate] at hb
  simp only [working,List.append_assoc]
  apply Exec.mono hb
  omega

lemma blocks (hw : 0<w) (bs : List (Block w)) (v : Block w) (out : List Symbol) (gap H : ℕ)
    (hb : ∀ b∈bs,b≠fun _=>0)
    (hh : ∀ b∈bs,∀ a∈h b,a≠6 ∧ a≠7)
    (hH : ∀ b∈bs,(h b).length≤H)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap (bs.flatMap List.ofFn)⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++bs.reverse.flatMap h++out)⟩
      (budget w H bs.length (out.length+gap)) := by
  induction bs generalizing v out gap with
  | nil =>
    simpa only [List.flatMap_nil,List.reverse_nil,List.append_nil,List.nil_append]
      using (finish w h header v out gap ho).mono (by simp only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.add_zero,Nat.one_mul]; omega)
  | cons b bs ih =>
    have ha:=cycle w h header hw b v (hb b (by simp)) out (bs.flatMap List.ofFn) gap ho (hh b (by simp))
    have hs:=ih b (h b++out) (gap+w)
      (fun a ha=>hb a (by simp [ha])) (fun a ha=>hh a (by simp [ha]))
      (fun a ha=>hH a (by simp [ha]))
      (by intro a ha; rcases List.mem_append.mp ha with ha|ha; exact hh b (by simp) a ha; exact ho a ha)
    have he:=ha.trans hs
    simp only [List.reverse_cons,List.flatMap_append,List.append_assoc,
      List.flatMap_cons] at he ⊢
    apply he.mono
    have hlen:=hH b (by simp)
    simp only [budget,List.length_cons,List.length_append]
    nlinarith

lemma computes (hw : 0<w) (bs : List (Block w)) (H : ℕ)
    (hb : ∀ b∈bs,b≠fun _=>0)
    (hh : ∀ b∈bs,∀ a∈h b,a≠6 ∧ a≠7)
    (hH : ∀ b∈bs,(h b).length≤H) :
    Exec M ⟨some .start,(fun _=>0),Tape.mk₁ (bs.flatMap List.ofFn)⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++bs.reverse.flatMap h)⟩
      (1+budget w H bs.length 0) := by
  have ha:=start_step w h header (bs.flatMap List.ofFn) (fun _=>0)
  have hs:=blocks w h header hw bs (fun _=>0) [] 0 H hb hh hH (by simp)
  simpa only [List.append_nil,List.length_nil,Nat.zero_add] using ha.trans hs

end MatchingFPRAS.LiteralBlockMap

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

lemma rows_eq {A : Type} [Codec A] (a : A) (bs : List Bool)
    (hs : (TreeData.encode (TreeTyped.encode a)).reverse=false::bs) :
    StackWords.rows (inputStacks a) (weight a)=baseRow::bs.map bitRow := by
  have hw : weight a=bs.length+1 := by
    have h:=congrArg List.length hs
    simpa only [List.length_reverse,List.length_cons,weight,TreeFunction.size] using h
  apply List.ext_getElem
  · simp only [StackWords.rows,List.length_ofFn,List.length_cons,List.length_map,hw]
  · intro i hi hj
    simp only [StackWords.rows,List.getElem_ofFn]
    funext k
    cases k with
    | inr k =>
      cases i <;> simp [inputStacks,encodeEnv,baseRow,bitRow]
    | inl r =>
      by_cases hr:r=0
      · subst r
        simp only [inputStacks,encodeEnv,env,ite_true, if_true,hs]
        cases i <;> simp [baseRow,bitRow]
      · have hn : env (TreeTyped.encode a) .nil .nil r=.nil := by simp [env,hr]
        simp only [inputStacks,encodeEnv,hn,TreeData.encode,List.reverse_singleton]
        cases i <;> simp [baseRow,bitRow,hr]
lemma word_eq {A : Type} [Codec A] (a : A) (bs : List Bool)
    (hs : (TreeData.encode (TreeTyped.encode a)).reverse=false::bs) :
    StackWords.word (inputStacks a) (weight a)=bottom::bs.map letter := by
  rw [StackWords.word,rows_eq a bs hs]
  simp only [List.headI_cons,List.tail_cons]
  change (true,baseRow)::(bs.map bitRow).map (fun a=>(false,a)) = (true,baseRow)::bs.map LiteralPacked.letter
  rw [List.map_map]
  rfl

lemma list_bits (as : List Symbol) :
    (TreeData.encode (TreeTyped.encode as)).reverse=false::as.reverse.flatMap symbolBits := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [TreeTyped.encode_list_cons,TreeData.encode,List.reverse_cons,List.reverse_append,ih,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,symbolBits,
      List.cons_append,List.append_assoc]

lemma packed_eq (as : List Symbol) : TreePost.packed as=header++as.reverse.flatMap chunk := by
  unfold TreePost.packed StackWords.encoded FixedAlphabetCompiler.word FixedAlphabetCompiler.bitsWord
  rw [word_eq as _ (list_bits as)]
  simp only [List.flatMap_cons,List.map_append,List.flatMap_map,List.map_flatMap,
    List.flatMap_assoc,LiteralPacked.header,LiteralPacked.block]
  rfl
lemma block_alphabet (a : Alphabet) (s : Symbol) (hs : s∈block a) : s=0 ∨ s=1 := by
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hs
  cases b <;> simp [BoolPostCompiler.up]
lemma chunk_alphabet (a s : Symbol) (hs : s∈chunk a) : s≠6 ∧ s≠7 := by
  obtain ⟨b,_,hb⟩:=List.mem_flatMap.mp hs
  rcases block_alphabet _ _ hb with rfl|rfl <;> decide
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TreeEncodingInjective
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
lemma encode_prefix_injective (a : Data) : ∀ b xs ys,
    encode a++xs=encode b++ys → a=b ∧ xs=ys := by
  induction a with
  | nil=>
    intro b xs ys h
    cases b with
    | nil=>simpa [encode] using h
    | cons b c=>simp [encode] at h
  | cons a c ia ic=>
    intro b xs ys h
    cases b with
    | nil=>simp [encode] at h
    | cons b d=>
      simp only [encode,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      obtain ⟨hab,he⟩:=ia b _ _ h
      obtain ⟨hcd,hxy⟩:=ic d xs ys he
      exact ⟨congrArg₂ Data.cons hab hcd,hxy⟩
lemma encode_injective : Function.Injective encode := by
  intro a b h
  exact (encode_prefix_injective a b [] [] (by simpa using h)).1
lemma ofList_injective : Function.Injective ofList := by
  intro a
  induction a with
  | nil=>intro b h; cases b <;> simp_all [ofList]
  | cons a as ih=>
    intro b h
    cases b with
    | nil=>simp [ofList] at h
    | cons b bs=>
      obtain ⟨rfl,he⟩:=Data.cons.inj h
      rw [ih he]
lemma bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeTyped
open TreeData

lemma list_encode_injective {A : Type} [Codec A] (hf : Function.Injective (encode (A:=A))) :
    Function.Injective (encode (A:=List A)) := by
  intro a b h
  exact (List.map_injective_iff.mpr hf) (ofList_injective h)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedInverse
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreePost

lemma symbol_encode_injective : Function.Injective (TreeTyped.encode (A:=Symbol)) := by
  intro a b h
  have hh : TreeTyped.encode (LiteralCodec.parts a)=TreeTyped.encode (LiteralCodec.parts b) := h
  have he := (TreeData.Data.cons.inj hh).1
  have hs : (LiteralCodec.parts a).1=(LiteralCodec.parts b).1 :=
    list_encode_injective (show Function.Injective (TreeTyped.encode (A:=Bool)) from bit_injective) he
  apply Fin.ext
  simpa only [LiteralCodec.parts,List.length_replicate] using congrArg List.length hs
lemma symbolBits_injective : Function.Injective symbolBits := by
  intro a b h
  have h1:=List.append_cancel_right (show _++[true]=_++[true] from h)
  exact symbol_encode_injective (TreeData.encode_injective (List.reverse_injective h1))
lemma encoding_injective (Γ : Type) [Fintype Γ] [Inhabited Γ] :
    Function.Injective (fun a : Γ=>(FixedEncoding.enc Γ a).toList.map BoolPostCompiler.up) := by
  intro a b h
  have hb : (FixedEncoding.enc Γ a).toList=(FixedEncoding.enc Γ b).toList :=
    List.map_injective_iff.mpr (Function.LeftInverse.injective BoolPostCompiler.down_up) h
  exact FixedEncoding.injective Γ (Subtype.ext hb)
lemma block_injective : Function.Injective block := encoding_injective Alphabet
lemma flatMap_injective_fixed {A B : Type} (f : A→List B) (w : ℕ) (hw : 0<w)
    (hl : ∀ a,(f a).length=w) (hi : Function.Injective f) : Function.Injective (List.flatMap f) := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => rfl
    | cons b bs => have hh:=congrArg List.length h;simp only [List.flatMap_nil,List.flatMap_cons,List.length_nil,List.length_append,hl] at hh;omega
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => have hh:=congrArg List.length h;simp only [List.flatMap_nil,List.flatMap_cons,List.length_nil,List.length_append,hl] at hh;omega
    | cons b bs =>
      have h1 := List.append_inj_left h ((hl a).trans (hl b).symm)
      have h2 := List.append_inj_right h ((hl a).trans (hl b).symm)
      exact congrArg₂ List.cons (hi h1) (ih h2)
lemma width_pos : 0<width := Fintype.card_pos
lemma letter_injective : Function.Injective letter := by
  intro a b h
  have hh:=congrArg (fun x : Alphabet=>x.2 (Sum.inl 0)) h
  simpa only [letter,bitRow,ite_true, if_true,Option.some.injEq] using hh
lemma chunk_injective : Function.Injective chunk := by
  intro a b h
  have hi : Function.Injective (fun b=>block (letter b)) := by
    intro b c he
    exact letter_injective (block_injective he)
  have hh : (symbolBits a).flatMap (fun b=>block (letter b)) =
      (symbolBits b).flatMap (fun b=>block (letter b)) := h
  exact symbolBits_injective (flatMap_injective_fixed (fun b=>block (letter b)) width width_pos
    (fun b=>block_length (letter b)) hi hh)
lemma encoding_blank (Γ : Type) [Fintype Γ] [Inhabited Γ] :
    (FixedEncoding.enc Γ default).toList.map BoolPostCompiler.up=
      List.replicate (Fintype.card Γ) (0:Symbol) := by
  rw [FixedEncoding.blank]
  change (List.replicate (Fintype.card Γ) false).map _ = _
  rw [List.map_replicate]
  rfl
lemma block_blank : block default=List.replicate width 0 := encoding_blank Alphabet
lemma block_ne_zero (a : Alphabet) (ha : a≠default) : block a≠List.replicate width 0 := by
  intro he
  exact ha (block_injective (he.trans block_blank.symm))
lemma chunk_nonzero (a : Symbol) : ∃ s∈chunk a,s≠0 := by
  classical
  by_contra h
  push Not at h
  have h1 : ∀ s∈block (letter true),s=(0:Symbol) := by
    intro s hs
    exact h s (List.mem_flatMap.mpr ⟨true,by simp [symbolBits],hs⟩)
  have he : block (letter true)=List.replicate width 0 := by
    rw [←block_length (letter true)]
    exact List.eq_replicate_of_mem h1
  apply block_ne_zero (letter true) _ he
  intro h2
  have hh:=congrArg (fun x : Alphabet=>x.2 (Sum.inl 0)) h2
  change (some true : Option Bool)=none at hh
  exact Option.some_ne_none true hh
lemma chunkFn_word (a : Symbol) : List.ofFn (chunkFn a)=chunk a := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,chunk_length]
  · intro i hi hj; simp only [List.getElem_ofFn,chunkFn]
lemma unchunk_chunkFn (a : Symbol) : unchunk (chunkFn a)=[a] := by
  rw [unchunk,chunkFn_word,Function.leftInverse_invFun chunk_injective]
lemma chunkFn_nonzero (a : Symbol) : chunkFn a≠fun _=>0 := by
  intro he
  have hh:=congrArg List.ofFn he
  rw [chunkFn_word,List.ofFn_const] at hh
  obtain ⟨s,hs,hn⟩:=chunk_nonzero a
  rw [hh] at hs
  exact hn (List.eq_of_mem_replicate hs)
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open Turing LiteralTape LiteralBlockMap

lemma singletonBlock_word (a : Symbol) : List.ofFn (singletonBlock a)=[a] := by simp [singletonBlock,List.ofFn_succ]
lemma pack_exec (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    Exec packCode ⟨some .start,(fun _=>0),Tape.mk₁ as⟩
      ⟨none,(fun _=>0),Tape.mk₁ (TreePost.packed as)⟩
      (1+LiteralBlockMap.budget 1 (18*width) as.length 0) := by
  have h:=LiteralBlockMap.computes 1 (fun b=>chunk (b 0)) header (by decide)
    (as.map singletonBlock) (18*width) ?_ ?_ ?_
  · simpa only [packCode,List.flatMap_map,singletonBlock_word,List.flatMap_singleton,List.flatMap_singleton',List.length_map,
      ←List.map_reverse,singletonBlock,←packed_eq] using h
  · intro b hb
    obtain ⟨a,ha',rfl⟩:=List.mem_map.mp hb
    intro he
    exact ha a ha' (congrFun he 0)
  · intro b _ a had
    exact chunk_alphabet _ _ had
  · intro b _
    exact (chunk_length _).le
lemma unpack_exec (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    Exec unpackCode ⟨some .start,(fun _=>0),Tape.mk₁ (as.reverse.flatMap chunk)⟩
      ⟨none,(fun _=>0),Tape.mk₁ as⟩
      (1+LiteralBlockMap.budget (18*width) 1 as.length 0) := by
  have h:=LiteralBlockMap.computes (18*width) unchunk [] (Nat.mul_pos (by decide) width_pos)
    (as.reverse.map chunkFn) 1 ?_ ?_ ?_
  · simpa only [unpackCode,List.flatMap_map,chunkFn_word,←List.map_reverse,List.reverse_reverse,
      unchunk_chunkFn,List.flatMap_singleton,List.flatMap_singleton',List.nil_append,List.length_map,List.length_reverse] using h
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    exact chunkFn_nonzero a
  · intro b hb a had
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hb
    rw [unchunk_chunkFn,List.mem_singleton] at had
    subst a
    exact ha c (List.mem_reverse.mp hc)
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    rw [unchunk_chunkFn];rfl
end MatchingFPRAS.LiteralPacked

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
lemma eraseRight_step (xs L R : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    TM1.stepAux (eraseRight xs.length q) v (Tape.mk₂ L (xs++R))=
      TM1.stepAux q v (Tape.mk₂ (List.replicate xs.length default++L) R) := by
  induction xs generalizing L with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,eraseRight,TM1.stepAux,List.cons_append,mk₂_write,mk₂_right]
    rw [show Nat.rec q (fun _ tail=>TM1.Stmt.write (fun _ _=>default) (.move .right tail)) xs.length=eraseRight xs.length q from rfl,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
lemma erase_exec (xs R : List Symbol) :
    Exec (eraseCode xs.length) ⟨some (),(),Tape.mk₁ (xs++R)⟩ ⟨none,(),Tape.mk₁ R⟩ 1 := by
  have h:=Exec.step (eraseCode xs.length) () () (Tape.mk₁ (xs++R))
  change Exec _ _ (TM1.stepAux (eraseRight xs.length .halt) () (Tape.mk₂ [] (xs++R))) 1 at h
  rw [eraseRight_step] at h
  have he : Tape.mk₂ (List.replicate xs.length (0:Symbol)++[]) R=Tape.mk₁ R := by
    simp only [List.append_nil,Tape.mk₂,Tape.mk₁]
    rw [show (ListBlank.mk (List.replicate xs.length (0:Symbol)))=ListBlank.mk [] from blank_zero xs.length]
  change Exec _ _ (TM1.stepAux (.halt : TM1.Stmt Symbol Unit Unit) () (Tape.mk₂ (List.replicate xs.length (0:Symbol)++[]) R)) 1 at h
  simpa only [TM1.stepAux,he] using h
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LiteralProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public binary input and output for typed finite programs

Literal packing is independent of the counting algorithm. Its cost includes every packing, execution, and printing step.
-/

namespace ContingencyTables.LiteralProgram
open MatchingFPRAS Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped Polynomial

lemma postTime_mono {n m : ℕ} (h : n ≤ m) : postTime n ≤ postTime m := by
  unfold postTime LiteralBlockMap.budget
  gcongr

lemma pack_realizes (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    pack.Realizes (Tape.mk₁ as) (.done (Tape.mk₁ (TreePost.packed as))) (packTime as.length) :=
  Program.realizes_TM1 _ _ _ _ _ _ _ (pack_exec as ha)

lemma post_realizes (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    post.Realizes (Tape.mk₁ (TreePost.packed as)) (.done (Tape.mk₁ as)) (postTime as.length) := by
  have h1 : erase.Realizes (Tape.mk₁ (TreePost.packed as))
      (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
      (MachineCost.programCost (LiteralTape.eraseCode header.length)) := by
    rw [packed_eq]
    exact (Program.realizes_TM1 _ _ _ _ _ _ _
      (LiteralTape.erase_exec header (as.reverse.flatMap chunk))).mono (by simp only [Nat.one_mul]; rfl)
  have h2 : unpack.Realizes (Tape.mk₁ (as.reverse.flatMap chunk)) (.done (Tape.mk₁ as))
      ((1+LiteralBlockMap.budget (18*width) 1 as.length 0)*MachineCost.programCost unpackCode) :=
    Program.realizes_TM1 _ _ _ _ _ _ _ (unpack_exec as ha)
  exact Program.seq_realizes erase unpack _ (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
    (fun _ => .done (Tape.mk₁ as)) _ _ h1 h2

private lemma experiment_all_and {A : Type} {p : Experiment A} {P Q : A → Prop}
    (hp : p.All P) (hq : p.All Q) : p.All (fun a => P a ∧ Q a) := by
  induction p with
  | done a => exact ⟨hp,hq⟩
  | read p ih => exact ⟨ih false hp.1 hq.1,ih true hp.2 hq.2⟩
  | delay n p ih => exact ih hp hq

lemma wrap_realizes {f : List Symbol → Experiment (List Symbol)}
    (F : OnlineTree.Realizer f) (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : (f as).All (fun bs => ∀ b∈bs,b≠6 ∧ b≠7)) :
    (wrap F).Realizes (Tape.mk₁ as) ((f as).map Tape.mk₁) (wrapTime F as) := by
  have h1 : (pack.seq (OnlineTree.physicalProgram F)).Realizes (Tape.mk₁ as)
      ((f as).map (fun bs => Tape.mk₁ (TreePost.packed bs)))
      (packTime as.length+OnlineTree.physicalCost F as) :=
    Program.seq_realizes pack (OnlineTree.physicalProgram F) _ (.done (Tape.mk₁ (TreePost.packed as)))
      (fun _ => (f as).map (fun bs => Tape.mk₁ (TreePost.packed bs))) _ _
      (pack_realizes as ha) (OnlineTree.physical_realizes F as)
  exact Program.seq_realizes_map _ _ _ (f as) (fun bs => Tape.mk₁ (TreePost.packed bs))
    (fun bs => .done (Tape.mk₁ bs)) _ _ h1
    ((experiment_all_and hout (Experiment.all_worst (f as) List.length)).mono
      (fun bs hbs => (post_realizes bs hbs.1).mono (postTime_mono hbs.2)))

end ContingencyTables.LiteralProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicMachine
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The greedy initializer on the public binary tape -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS Turing
open scoped BigOperators

private lemma encodeNat_nonzero (n : ℕ) (a : Symbol) (ha : a∈encodeNat n) : a≠0 := by
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide

lemma encodeMargins_nonzero {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    ∀ a∈Algorithms.encodeMargins r c,a≠0 := by
  rw [encodeMargins_natWords]
  intro a ha
  obtain ⟨n,_,ha⟩ := List.mem_flatMap.mp ha
  exact encodeNat_nonzero n a ha

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingInputSymbols
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The public counting input contains no tape blanks -/

namespace ContingencyTables.CountingInputSymbols
open MatchingFPRAS Algorithms

lemma nat_nonzero (n : ℕ) (a : MatchingFPRAS.Symbol) (ha : a∈encodeNat n) : a≠0 :=
  (FractionOutputProgram.natWord_symbols n a ha).1

lemma int_nonzero (n : ℤ) (a : MatchingFPRAS.Symbol) (ha : a∈encodeInt n) : a≠0 := by
  simp only [encodeInt,List.mem_append] at ha
  rcases ha with ha | ha
  · split_ifs at ha <;> simp only [List.mem_singleton] at ha <;> subst a <;> decide
  · exact nat_nonzero _ a ha

lemma rat_nonzero (q : ℚ) (a : MatchingFPRAS.Symbol) (ha : a∈encodeRat q) : a≠0 := by
  simp only [encodeRat,List.mem_append] at ha
  rcases ha with ha | ha
  · exact int_nonzero _ a ha
  · exact nat_nonzero _ a ha

lemma matrix_nonzero {m n : ℕ} (X : Fin m→Fin n→ℕ)
    (a : MatchingFPRAS.Symbol) (ha : a∈encodeMatrix X) : a≠0 := by
  rw [encodeMatrix_flat] at ha
  obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp ha
  exact nat_nonzero k a hk

lemma counting_nonzero {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    ∀ a∈encodeCountingInput r c b epsilon delta,a≠0 := by
  intro a ha
  simp only [encodeCountingInput,List.mem_append] at ha
  rcases ha with ((ha | ha) | ha) | ha
  · exact GreedyFeasibleTable.encodeMargins_nonzero r c a ha
  · exact matrix_nonzero b a ha
  · exact rat_nonzero epsilon a ha
  · exact rat_nonzero delta a ha

end ContingencyTables.CountingInputSymbols

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineWord
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing a computed finite Boolean sampler

The program reads a fresh word on the physical online machine, preserves
the input, and runs the deterministic binary sampler on that word.
-/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Polynomial

variable {A B : Type} [TreeTyped.Codec A] [TreeTyped.Codec B]

omit [TreeTyped.Codec A] [TreeTyped.Codec B] in

theorem experiment_mean (n : A → ℕ) (f : A×List Bool → B) (a : A) (g : B → ℚ) :
    (experiment n f a).mean g=
      average (fun bits : Bits (n a) => g (f (a,List.ofFn bits))) := by
  unfold experiment source
  rw [Experiment.mean_map,OnlineWord.mean_prepend_nil]

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordMachine
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single physical machine for a computed finite-word algorithm -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open TreeTyped Polynomial

variable {n : List Symbol → ℕ} {f : List Symbol×List Bool → List Symbol}

private lemma output_alphabet (as : List Symbol)
    (hout : ∀ bs,∀ b∈f (as,bs),b≠6 ∧ b≠7) :
    (experiment n f as).All (fun bs => ∀ b∈bs,b≠6 ∧ b≠7) := by
  unfold experiment
  rw [Experiment.all_map]
  exact (Experiment.all_true _).mono (fun bs _ => hout bs)

/-- Every run halts within the physical execution bound. Its output law
is exactly the law obtained by feeding an independent uniform word to f. -/
theorem machine_law (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ b∈f (as,bs),b≠6 ∧ b≠7)
    (t : ℕ) (ht : machineTime N F as≤t) :
    (∀ bits : Bits t,(run (machine N F) as bits).state=none) ∧
    ∀ g : Tape Symbol → ℚ,
      average (fun bits : Bits t => g (run (machine N F) as bits).tape)=
        average (fun bits : Bits (n as) => g (Tape.mk₁ (f (as,List.ofFn bits)))) := by
  have hr := LiteralProgram.wrap_realizes (realizer N F) as ha (output_alphabet as hout)
  constructor
  · intro bits
    exact (hr.run_all (fun _ => True) (Experiment.all_true _) t ht bits).1
  · intro g
    have hm := hr.run_mean g t ht
    rw [Experiment.mean_map] at hm
    exact hm.trans (experiment_mean n f as (fun bs => g (Tape.mk₁ bs)))

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordOutput
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every-path output properties of the finite-word machine -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open scoped BigOperators Classical

variable {n : List Symbol → ℕ} {f : List Symbol×List Bool → List Symbol}

/-- A property verified for every finite source word holds on every actual
machine tape once the fixed execution bound has elapsed. -/
theorem machine_all (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈f (as,bs),a≠6 ∧ a≠7)
    (P : Tape Symbol → Prop)
    (hf : ∀ bits : Bits (n as),P (Tape.mk₁ (f (as,List.ofFn bits))))
    (t : ℕ) (ht : machineTime N F as≤t) :
    ∀ bits : Bits t,P (run (machine N F) as bits).tape := by
  let g : Tape Symbol → ℚ := fun tape => if P tape then 0 else 1
  have hm := (machine_law N F as ha hout t ht).2 g
  have hz : average (fun bits : Bits t => g (run (machine N F) as bits).tape)=0 := by
    rw [hm]
    have he : (fun bits : Bits (n as) => g (Tape.mk₁ (f (as,List.ofFn bits))))=
        (fun _ => (0:ℚ)) := by
      funext bits
      exact ite_eq_left (hf bits)
    rw [he,average_const]
  have hpow : (2:ℚ)^t≠0 := pow_ne_zero _ (by norm_num)
  have hs : ∑ bits : Bits t,g (run (machine N F) as bits).tape=0 := by
    have h := congrArg (fun a : ℚ => a*(2:ℚ)^t) hz
    simpa only [average,div_mul_cancel₀ _ hpow,zero_mul] using h
  have hnonneg (bits : Bits t) : 0≤g (run (machine N F) as bits).tape := by
    dsimp only [g]
    split_ifs <;> norm_num
  intro bits
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg b)).mp hs bits (Finset.mem_univ bits)
  by_contra hn
  have hbad : (1:ℚ)=0 := by simpa only [g,ite_eq_right hn] using hb
  norm_num at hbad

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordRationalLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring rational-output events to the fixed public machine -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open scoped BigOperators Classical
noncomputable section
variable {n : List Symbol → ℕ} {f : List Symbol×List Bool → List Symbol}

/-- An event verified on the rational value survives literal output and
finite-word compilation, without requiring a decoding oracle. -/
theorem machine_rational_event (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈f (as,bs),a≠6 ∧ a≠7)
    (draw : Bits (n as) → ℚ) (hf : ∀ bits,f (as,List.ofFn bits)=encodeRat (draw bits))
    (P : ℚ → Prop) (t : ℕ) (ht : machineTime N F as≤t) :
    average (fun bits : Bits (n as) => if P (draw bits) then 1 else 0) ≤
      ((Finset.univ.filter (fun bits : Bits t =>
        ∃ q : ℚ,Outputs (machine N F) as bits q ∧ P q)).card:ℚ)/(2:ℚ)^t := by
  let g : Tape Symbol → ℚ := fun tape =>
    if ∃ q : ℚ,tape.right₀=ListBlank.mk (encodeRat q) ∧ P q then 1 else 0
  obtain ⟨hh,hm⟩ := machine_law N F as ha hout t ht
  have hsource : average (fun bits : Bits (n as) => if P (draw bits) then 1 else 0) ≤
      average (fun bits : Bits (n as) => g (Tape.mk₁ (f (as,List.ofFn bits)))) := by
    unfold average
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro bits _
    by_cases hp : P (draw bits)
    · have hg : ∃ q : ℚ,(Tape.mk₁ (f (as,List.ofFn bits))).right₀=
          ListBlank.mk (encodeRat q) ∧ P q := by
        refine ⟨draw bits,?_,hp⟩
        simp only [hf,Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]
      simp only [hp,ite_true, if_true,g,hg]
      exact le_rfl
    · simp only [hp,ite_false]
      dsimp only [g]
      split_ifs <;> norm_num
  rw [←hm g] at hsource
  simpa only [average,g,Outputs,hh,true_and,Finset.sum_boole] using hsource

/-- All finite source words have a rational output satisfying P, so the
compiled machine has that property on every random tape. -/
theorem machine_rational_all (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈f (as,bs),a≠6 ∧ a≠7)
    (draw : Bits (n as) → ℚ) (hf : ∀ bits,f (as,List.ofFn bits)=encodeRat (draw bits))
    (P : ℚ → Prop) (hP : ∀ bits,P (draw bits))
    (t : ℕ) (ht : machineTime N F as≤t) :
    ∀ bits : Bits t,∃ q : ℚ,Outputs (machine N F) as bits q ∧ P q := by
  have hp := machine_all N F as ha hout (fun tape =>
    ∃ q : ℚ,tape.right₀=ListBlank.mk (encodeRat q) ∧ P q) (fun bits => by
      refine ⟨draw bits,?_,hP bits⟩
      simp only [hf,Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]) t ht
  have hh := (machine_law N F as ha hout t ht).1
  intro bits
  obtain ⟨q,hq,hPq⟩ := hp bits
  exact ⟨q,⟨hh bits,hq⟩,hPq⟩

end
end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingMachineEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the counting experiment's real probability bound to public tapes -/
namespace ContingencyTables.CountingMachineEvents
open MatchingFPRAS MatchingFPRAS.PhysicalStream CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

lemma average_cast (n : ℕ) (f : Bits n→ℚ) :
    (average f:ℝ)=uniformAverage (fun bits => (f bits:ℝ)) := by
  simp only [average,uniformAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_pow,Rat.cast_ofNat,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

variable {wordCount : List Symbol→ℕ} {output : List Symbol×List Bool→List Symbol}

theorem success (N : TreeTyped.Realizer wordCount) (F : TreeTyped.Realizer output)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈output (as,bs),a≠6 ∧ a≠7)
    (draw : Bits (wordCount as)→ℚ) (hf : ∀ bits,output (as,List.ofFn bits)=encodeRat (draw bits))
    (P : ℚ→Prop) (delta : ℚ)
    (hs : 1-(delta:ℝ) ≤ uniformAverage (fun bits : Bits (wordCount as) => if P (draw bits) then 1 else 0))
    (t : ℕ) (ht : FiniteWordExecution.machineTime N F as ≤ t) :
    1-delta ≤ ((Finset.univ.filter (fun bits : Bits t =>
      ∃ q : ℚ,Outputs (FiniteWordExecution.machine N F) as bits q ∧ P q)).card:ℚ)/(2:ℚ)^t := by
  have hm := FiniteWordExecution.machine_rational_event N F as ha hout draw hf P t ht
  apply le_trans ?_ hm
  have hc : ((1-delta:ℚ):ℝ) ≤
      ((average (fun bits : Bits (wordCount as) => if P (draw bits) then (1:ℚ) else 0)):ℝ) := by
    rw [average_cast]
    simpa only [Rat.cast_sub,Rat.cast_one,apply_ite,Rat.cast_zero] using hs
  exact_mod_cast hc

end
end ContingencyTables.CountingMachineEvents

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public-machine output guarantees for the counting dispatcher -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open scoped Classical
noncomputable section

variable (positive : Input→TreeFraction.Fraction) (F : Realizer positive)
variable (width : Request→ℕ) (N : Realizer width)

lemma sourceValue_nonnegative (as : List Symbol) (bits : Bits (publicBudget width as)) :
    0 ≤ sourceValue positive width as bits := TreeFraction.val_nonneg _

lemma sourceValue_output (as : List Symbol) (bits : Bits (publicBudget width as)) :
    publicOutput positive (as,List.ofFn bits)=encodeRat (sourceValue positive width as bits) :=
  publicOutput_eq positive _

variable {m n : ℕ}

/-- Every random tape halts with a nonnegative rational, including on
statistically unsuccessful histories of the positive-label branch. -/
theorem outputs_nonnegative (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (t : ℕ)
    (ht : machineTime positive F width N (Algorithms.encodeCountingInput r c b epsilon delta) ≤ t) :
    ∀ bits : Bits t, ∃ q : ℚ, 0 ≤ q ∧
      Outputs (machine positive F width N) (Algorithms.encodeCountingInput r c b epsilon delta) bits q := by
  have hh := FiniteWordExecution.machine_rational_all
    (publicBudgetRealizer width N) (publicOutputRealizer positive F)
    (Algorithms.encodeCountingInput r c b epsilon delta)
    (CountingInputSymbols.counting_nonzero r c b epsilon delta)
    (fun bs a ha => (publicOutput_symbols positive _ a ha).2)
    (sourceValue positive width _) (sourceValue_output positive width _)
    (fun q => 0 ≤ q) (sourceValue_nonnegative positive width _) t ht
  intro bits
  obtain ⟨q,hq,hp⟩ := hh bits
  exact ⟨q,hp,hq⟩

lemma sourceValue_zero (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ)
    (hz : Algorithms.count r c b=0)
    (bits : Bits (publicBudget width (Algorithms.encodeCountingInput r c b epsilon delta))) :
    sourceValue positive width (Algorithms.encodeCountingInput r c b epsilon delta) bits=0 := by
  have hf := (count_zero_iff_rejected hEK r c b epsilon delta).mp hz
  unfold sourceValue
  rw [parsedInput_public,output_rejected positive _ hf]
  norm_num [TreeFraction.val]

/-- Exact zero output follows from the executed feasibility test. -/
theorem outputs_zero (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ)
    (hz : Algorithms.count r c b=0) (t : ℕ)
    (ht : machineTime positive F width N (Algorithms.encodeCountingInput r c b epsilon delta) ≤ t) :
    ∀ bits : Bits t,
      Outputs (machine positive F width N) (Algorithms.encodeCountingInput r c b epsilon delta) bits 0 := by
  have hh := FiniteWordExecution.machine_rational_all
    (publicBudgetRealizer width N) (publicOutputRealizer positive F)
    (Algorithms.encodeCountingInput r c b epsilon delta)
    (CountingInputSymbols.counting_nonzero r c b epsilon delta)
    (fun bs a ha => (publicOutput_symbols positive _ a ha).2)
    (sourceValue positive width _) (sourceValue_output positive width _)
    (fun q => q=0) (sourceValue_zero positive width hEK r c b epsilon delta hz) t ht
  intro bits
  obtain ⟨q,hq,rfl⟩ := hh bits
  exact hq

end
end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law of the executed direct counting estimator -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open CommonBasesFPRAS FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

attribute [local irreducible] modelContext modelWidth modelValue
attribute [local irreducible] ComputedCountingParameters.data ComputedCountingParameters.coefficient
attribute [local irreducible] ComputedCountingParameters.phases ComputedCountingParameters.binCount
attribute [local irreducible] ComputedCountingZero.zeroEstimate ComputedCountingZero.zeroBits

lemma modelWidth_eq (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) (delta : ℚ) :
    modelWidth hEK r c b hne epsilon he delta=ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta := by
  unfold modelWidth modelContext RootedEstimatorMedianProgram.context
  rw [RootedEstimatorWordProgram.scheduledWordWidth]
  unfold ComputedCountingZero.zeroBits medianEstimatorBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]

attribute [local irreducible] referenceBits reference

lemma native_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    SameLaw (fun bits : Fin (modelWidth hEK r c b hne epsilon he delta)→Bool =>
      modelValue hEK r c b hne epsilon he delta (List.ofFn bits))
      (reference hEK r c b hne epsilon he delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let C := ComputedCountingParameters.coefficient r c b epsilon
  let K := ComputedCountingParameters.binCount r c b epsilon
  let H := ComputedCountingParameters.phases r c b epsilon
  have hs := RootedEstimatorMedianProgram.sameLaw A C K H
    (ComputedCountingParameters.coefficient_pos r c b epsilon he)
    (ComputedCountingParameters.phases_height hEK r c b hne epsilon he).le
    (ComputedCountingParameters.binCount_pos r c b epsilon he)
    (ComputedCountingParameters.cutoff_eq hEK r c b hne epsilon he).ge
    (ComputedCountingParameters.binCount_cast hEK r c b hne epsilon he)
    ((epsilon/2)/2) delta (by positivity) (fun _ => 0) (fun _ => Nat.zero_le _)
    (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))
    (List.replicate (degree r c b epsilon) false) (List.replicate (depth r c b epsilon) false)
    (by rw [List.length_replicate]; rfl) (by rw [List.length_replicate]; rfl)
  dsimp only [A,C,K,H] at hs
  rw [CountingPreparedState.start_transport hEK r c b hne epsilon he] at hs
  unfold RootedEstimatorMedianProgram.value at hs
  unfold modelWidth modelValue modelContext reference referenceBits ComputedCountingWords.root
  exact hs

lemma reference_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    SameLaw (reference hEK r c b hne epsilon he delta)
      (ComputedCountingZero.zeroEstimate hEK r c b hne epsilon he delta) := by
  unfold reference referenceBits ComputedCountingZero.zeroEstimate ComputedCountingZero.zeroBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]
  intro phi
  rfl

lemma model_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    SameLaw (fun bits : Fin (modelWidth hEK r c b hne epsilon he delta)→Bool =>
      modelValue hEK r c b hne epsilon he delta (List.ofFn bits))
      (ComputedCountingZero.zeroEstimate hEK r c b hne epsilon he delta) := by
  intro phi
  exact (native_sameLaw hEK r c b hne epsilon delta he phi).trans
    (reference_sameLaw hEK r c b hne epsilon delta he phi)

lemma output_model (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) (N : ℕ)
    (hwidth : modelWidth hEK r c b hne epsilon he delta ≤ N)
    (hdegree : degree r c b epsilon ≤ N) (hdepth : depth r c b epsilon ≤ N)
    (bits : Fin N→Bool) :
    TreeFraction.val (output (request r c b epsilon delta,List.ofFn bits))=
      modelValue hEK r c b hne epsilon he delta
        (List.ofFn (FirstSuccess.prefixWord hwidth bits)) := by
  have hw : wordWidth (request r c b epsilon delta,List.ofFn bits)=modelWidth hEK r c b hne epsilon he delta :=
    (wordWidth_data hEK r c b hne epsilon delta he hd _).trans (modelWidth_eq hEK r c b hne epsilon he delta).symm
  have hc : context (request r c b epsilon delta,List.ofFn bits)=modelContext hEK r c b hne epsilon he :=
    by
      unfold modelContext
      exact context_data hEK r c b hne epsilon delta he _
  have hr : repeats (request r c b epsilon delta,List.ofFn bits)=repetitionCount delta := by
    change FractionRepetitionProgram.count (TreeFraction.repr delta)=_
    rw [FractionRepetitionProgram.count_val,TreeFraction.val_repr hd.le]
  have hm := markers_data hEK r c b hne epsilon delta he N hdegree hdepth bits
  unfold output medianInput config sampleBits
  rw [hc,hr,hm,hw,BinVectorProgram.take_ofFn_prefix hwidth]
  unfold modelValue
  rfl

lemma sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    SameLaw (fun bits : Fin (budget (request r c b epsilon delta))→Bool =>
      TreeFraction.val (output (request r c b epsilon delta,List.ofFn bits)))
      (ComputedCountingZero.zeroEstimate hEK r c b hne epsilon he delta) := by
  have hbudget := budget_data hEK r c b hne epsilon delta he hd
  have hwidth : modelWidth hEK r c b hne epsilon he delta ≤ budget (request r c b epsilon delta) := by
    rw [modelWidth_eq,hbudget]
    omega
  have hdegree : degree r c b epsilon ≤ budget (request r c b epsilon delta) := by omega
  have hdepth : depth r c b epsilon ≤ budget (request r c b epsilon delta) := by omega
  intro phi
  simp_rw [output_model hEK r c b hne epsilon delta he hd _ hwidth hdegree hdepth]
  exact (FairBits.padded_equiv_average hwidth (Equiv.refl _) (fun bits =>
    phi (modelValue hEK r c b hne epsilon he delta (List.ofFn bits)))).trans
    (model_sameLaw hEK r c b hne epsilon delta he phi)

end
end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectSuccess
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the executed direct counting branch -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication GridBoundary CommonBasesFPRAS
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (hzero : Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he))=0) :
    1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Fin (budget (request r c b epsilon delta))→Bool =>
        if (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ) ≤
            (TreeFraction.val (output (request r c b epsilon delta,List.ofFn bits)):ℝ) ∧
          (TreeFraction.val (output (request r c b epsilon delta,List.ofFn bits)):ℝ) ≤
            (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
        then (1:ℝ) else 0) := by
  let event := fun q : ℚ => if
    (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ) ≤ (q:ℝ) ∧
      (q:ℝ) ≤ (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
    then (1:ℝ) else 0
  have hs := ComputedCountingZero.zero_success hEK hPL hCheeger r c b hne
    epsilon delta he he1 hd hzero
  exact hs.trans_eq (sameLaw hEK r c b hne epsilon delta he hd event).symm

end
end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the public dispatcher from its positive counting branch -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (positive : Input→TreeFraction.Fraction) (width : Request→ℕ)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hpositive : ∀ hne : ∃ X,TableTightening.Feasible r c b X,
      0<Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) →
      1-(delta:ℝ) ≤ uniformAverage
        (fun bits : Fin (width (CountingDirectProgram.request r c b epsilon delta))→Bool =>
          if Accurate r c b epsilon (TreeFraction.val (positive
            (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0)) :
    1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Fin (budget width (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        if Accurate r c b epsilon (TreeFraction.val (output positive
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0) := by
  let req := CountingDirectProgram.request r c b epsilon delta
  change 1-(delta:ℝ) ≤ uniformAverage
    (fun bits : Fin (budget width req)→Bool =>
      if Accurate r c b epsilon (TreeFraction.val (output positive (req,List.ofFn bits)))
        then (1:ℝ) else 0)
  by_cases hf : feasible req=true
  · have hne := (feasible_data hEK r c b epsilon delta).mp hf
    by_cases hz : direct req=true
    · rw [budget_direct width req hf hz]
      simp_rw [output_direct positive req hf hz]
      exact CountingDirectProgram.success hEK hPL hCheeger r c b hne epsilon delta he he1 hd
        ((direct_data hEK r c b hne epsilon delta he).mp hz)
    · have hz' := Bool.eq_false_iff.mpr hz
      rw [budget_positive width req hf hz']
      simp_rw [output_positive positive req hf hz']
      exact hpositive hne (Nat.pos_of_ne_zero (fun h => hz
        ((direct_data hEK r c b hne epsilon delta he).mpr h)))
  · have hf' := Bool.eq_false_iff.mpr hf
    have hzero := (count_zero_iff_rejected hEK r c b epsilon delta).mpr hf'
    have hz : Fintype.card (BoundedTable r c b)=0 := hzero
    simp_rw [output_rejected positive req hf',Accurate,hz,Nat.cast_zero,mul_zero]
    norm_num [TreeFraction.val,uniformAverage_const]
    exact_mod_cast hd.le

end
end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingExecutedMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One fixed counting machine with the computed adaptive program -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open scoped Classical
noncomputable section

variable {m n : ℕ}

theorem outputs_nonnegative (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (t : ℕ)
    (ht : machineTime (Algorithms.encodeCountingInput r c b epsilon delta)≤t) :
    ∀ bits : Bits t,∃ q : ℚ,0≤q ∧
      Outputs machine (Algorithms.encodeCountingInput r c b epsilon delta) bits q :=
  CountingBranchProgram.outputs_nonnegative positive positiveRealizer positiveWidth positiveWidthRealizer
    r c b epsilon delta t ht

theorem outputs_zero (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ)
    (hz : Algorithms.count r c b=0) (t : ℕ)
    (ht : machineTime (Algorithms.encodeCountingInput r c b epsilon delta)≤t) :
    ∀ bits : Bits t,Outputs machine (Algorithms.encodeCountingInput r c b epsilon delta) bits 0 :=
  CountingBranchProgram.outputs_zero positive positiveRealizer positiveWidth positiveWidthRealizer
    hEK r c b epsilon delta hz t ht

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingMachineMainEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite rational event in the main counting statement -/
namespace ContingencyTables.CountingMachineEvents
open MatchingFPRAS MatchingFPRAS.PhysicalStream CommonBasesFPRAS
open scoped Classical
noncomputable section
variable {wordCount : List Symbol→ℕ} {output : List Symbol×List Bool→List Symbol}
variable {m n : ℕ}

theorem goodTapes_success (N : TreeTyped.Realizer wordCount) (F : TreeTyped.Realizer output)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ)
    (hout : ∀ bs,∀ a∈output (Algorithms.encodeCountingInput r c b epsilon delta,bs),a≠6 ∧ a≠7)
    (draw : Bits (wordCount (Algorithms.encodeCountingInput r c b epsilon delta))→ℚ)
    (hf : ∀ bits,output (Algorithms.encodeCountingInput r c b epsilon delta,List.ofFn bits)=encodeRat (draw bits))
    (hs : 1-(delta:ℝ) ≤ uniformAverage (fun bits =>
      if (1-epsilon)*(Algorithms.count r c b:ℚ)≤draw bits ∧
        draw bits≤(1+epsilon)*(Algorithms.count r c b:ℚ) then (1:ℝ) else 0))
    (t : ℕ) (ht : FiniteWordExecution.machineTime N F
      (Algorithms.encodeCountingInput r c b epsilon delta)≤t) :
    1-delta ≤ ((Algorithms.goodCountingTapes (FiniteWordExecution.machine N F)
      r c b epsilon delta t).card:ℚ)/(2:ℚ)^t := by
  apply success N F (Algorithms.encodeCountingInput r c b epsilon delta)
    (CountingInputSymbols.counting_nonzero r c b epsilon delta) hout draw hf
    (fun q => (1-epsilon)*(Algorithms.count r c b:ℚ)≤q ∧
      q≤(1+epsilon)*(Algorithms.count r c b:ℚ)) delta ?_ t ht
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext bits
  split_ifs <;> rfl

end
end ContingencyTables.CountingMachineEvents

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting the concrete counting accuracy event to public machine tapes -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS MatchingFPRAS.PhysicalStream CommonBasesFPRAS CompanionFactorialApplication GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma accurate_iff (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon q : ℚ) :
    ((1-epsilon)*(Algorithms.count r c b:ℚ)≤q ∧
      q≤(1+epsilon)*(Algorithms.count r c b:ℚ)) ↔
      CountingBranchProgram.Accurate r c b epsilon q := by
  unfold CountingBranchProgram.Accurate Algorithms.count
  constructor <;> rintro ⟨hl,hu⟩ <;> constructor
  · exact_mod_cast hl
  · exact_mod_cast hu
  · exact_mod_cast hl
  · exact_mod_cast hu

attribute [local irreducible] CountingPositiveProgram.output CountingAmplifiedProgram.output
  CountingBranchProgram.output CountingBranchProgram.publicOutput CountingBranchProgram.machine
  CountingExecutedMachine.machine

theorem public_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hpositive : ∀ hne : ∃ X,TableTightening.Feasible r c b X,
      0<Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) →
      1-(delta:ℝ) ≤ uniformAverage
        (fun bits : Fin (positiveWidth (CountingDirectProgram.request r c b epsilon delta))→Bool =>
          if CountingBranchProgram.Accurate r c b epsilon (TreeFraction.val (positive
            (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0))
    (t : ℕ) (ht : machineTime (Algorithms.encodeCountingInput r c b epsilon delta)≤t) :
    1-delta ≤ ((Algorithms.goodCountingTapes machine r c b epsilon delta t).card:ℚ)/(2:ℚ)^t := by
  let P := fun q : ℚ => (1-epsilon)*(Algorithms.count r c b:ℚ)≤q ∧
    q≤(1+epsilon)*(Algorithms.count r c b:ℚ)
  have hraw := CountingBranchProgram.success hEK hPL hCheeger positive positiveWidth
    r c b epsilon delta he he1 hd hpositive
  have hs : 1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Bits (wordCount (Algorithms.encodeCountingInput r c b epsilon delta)) =>
        if P (sourceValue (Algorithms.encodeCountingInput r c b epsilon delta) bits) then (1:ℝ) else 0) := by
    simp only [P,accurate_iff,sourceValue,CountingBranchProgram.sourceValue,
      CountingBranchProgram.parsedInput_public]
    unfold wordCount CountingBranchProgram.publicBudget
    rw [CountingInputParser.public_spec]
    exact hraw
  rw [show machine=FiniteWordExecution.machine
    (CountingBranchProgram.publicBudgetRealizer positiveWidth positiveWidthRealizer)
    (CountingBranchProgram.publicOutputRealizer positive positiveRealizer) from by
      unfold machine CountingBranchProgram.machine; rfl]
  exact CountingMachineEvents.goodTapes_success
    (CountingBranchProgram.publicBudgetRealizer positiveWidth positiveWidthRealizer)
    (CountingBranchProgram.publicOutputRealizer positive positiveRealizer)
    r c b epsilon delta
    (fun bs a ha => (CountingBranchProgram.publicOutput_symbols positive _ a ha).2)
    (sourceValue (Algorithms.encodeCountingInput r c b epsilon delta))
    (CountingBranchProgram.sourceValue_output positive positiveWidth _)
    hs t ht

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingConditionalAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Assembly of the public counting specification from its executed history law -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section

theorem statement_of_single_law
    (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (hlaw : ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
      (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0<epsilon),
      SameLaw
        (fun bits : Fin (CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
          TreeFraction.val (CountingPositiveProgram.output
            (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
        (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
          (ComputedCountingWords.root hEK r c b hne epsilon he)
          (ComputedCountingParameters.settings hEK r c b hne epsilon he))) :
    Algorithms.CountingStatement := by
  obtain ⟨C,d,hC,ht⟩ := public_time hEK
  refine ⟨machine,C,d,hC,?_⟩
  intro m n _ _ r c b _ epsilon delta he he1 hd _
  have htime := ht m n r c b epsilon delta he hd
  refine ⟨outputs_nonnegative r c b epsilon delta _ htime,
    (fun hz => outputs_zero hEK r c b epsilon delta hz _ htime),?_⟩
  apply public_success hEK hPL hCheeger r c b epsilon delta he he1 hd
  · intro hne hp
    exact positive_success hEK hPL hCheeger r c b hne epsilon delta he he1 hd hp
      (hlaw m n r c b hne epsilon delta he)
  · exact htime

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingMainMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cell-bounded contingency-table FPRAS on one public fair-bit machine

The hypotheses are finite-box Prekopa-Leindler, finite-chain Cheeger
and Edmonds-Karp. They imply the guarantees for preprocessing, adaptive
phases, error amplification and fair-bit machine execution.
-/
namespace ContingencyTables.CountingExecutedMachine
open CompanionFactorialApplication GridBoundary

theorem counting_conditional
    (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k)) :
    Algorithms.CountingStatement :=
  statement_of_single_law hEK hPL hCheeger
    (fun _ _ r c b hne epsilon delta he =>
      CountingPositiveProgram.value_source_sameLaw hEK r c b hne epsilon delta he)

end ContingencyTables.CountingExecutedMachine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_CheegerCoarea
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted finite coarea for the published Cheeger input -/
namespace ContingencyTables.CheegerProof
open MeasureTheory CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

lemma level_eq (a : ℝ) :
    level a = Set.indicator (Set.Ico 0 a) (fun _ => (1:ℝ)) := by
  funext t
  simp [level,Set.indicator_apply,Set.mem_Ico]

lemma level_integrable (a : ℝ) : Integrable (level a) := by
  rw [level_eq]
  exact (integrableOn_const (isCompact_Icc.measure_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc 0 a)).mono_set
      Set.Ico_subset_Icc_self |>.integrable_indicator measurableSet_Ico

lemma level_integral {a : ℝ} (ha : 0 ≤ a) : ∫ t, level a t = a := by
  rw [level_eq,integral_indicator measurableSet_Ico]
  simp [ha]

lemma level_abs_sub (a b t : ℝ) :
    |level a t-level b t| = level a t+level b t-2*level (min a b) t := by
  simp only [level,lt_min_iff]
  by_cases h₀ : 0 ≤ t <;> by_cases ha : t < a <;> by_cases hb : t < b <;>
    norm_num [h₀,ha,hb]

lemma level_abs_integrable (a b : ℝ) : Integrable (fun t => |level a t-level b t|) :=
  ((level_integrable a).sub (level_integrable b)).abs

lemma level_abs_integral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ t, |level a t-level b t| = |a-b| := by
  simp_rw [level_abs_sub]
  rw [integral_sub (f := fun t => level a t+level b t)
      ((level_integrable a).add (level_integrable b))
      ((level_integrable (min a b)).const_mul 2),
    integral_add (level_integrable a) (level_integrable b),integral_const_mul,
    level_integral ha,level_integral hb,level_integral (le_min ha hb)]
  rcases le_total a b with h | h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring

variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma mass_mono {S T : Finset X} (h : S ⊆ T) : mass C S ≤ mass C T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => (C.positive x).le)

lemma mass_compl (S : Finset X) : mass C Sᶜ = 1-mass C S := by
  have h := Finset.sum_compl_add_sum S C.π
  rw [C.normalized] at h
  dsimp [mass]
  linarith

lemma cut_indicator (S : Finset X) :
    (∑ x, ∑ y, C.π x*C.P x y*
      |(if x ∈ S then (1:ℝ) else 0)-(if y ∈ S then (1:ℝ) else 0)|) = 2*cut C S := by
  have hs (x y : X) : C.π x*C.P x y*
      |(if x ∈ S then (1:ℝ) else 0)-(if y ∈ S then (1:ℝ) else 0)| =
      (if x ∈ S ∧ y ∉ S then C.π x*C.P x y else 0)+
      (if y ∈ S ∧ x ∉ S then C.π x*C.P x y else 0) := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx,hy]
  simp_rw [hs,Finset.sum_add_distrib]
  have hforward : (∑ x, ∑ y, if x ∈ S ∧ y ∉ S then C.π x*C.P x y else 0) = cut C S := by
    simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_filter]
    congr 1
    ext y
    simp
  have hback : (∑ x, ∑ y, if y ∈ S ∧ x ∉ S then C.π x*C.P x y else 0) = cut C S := by
    rw [Finset.sum_comm]
    simpa only [C.reversible] using hforward
  rw [hforward,hback]
  ring

/-- Coarea on a function supported on a set of stationary mass at most one half. -/
theorem coarea (κ : ℝ)
    (hcut : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hsmall : mass C (Finset.univ.filter fun x => 0 < g x) ≤ 1/2) :
    2*κ*(∑ x, C.π x*g x) ≤ ∑ x, ∑ y, C.π x*C.P x y*|g x-g y| := by
  let F : ℝ → ℝ := fun t => 2*κ*∑ x, C.π x*level (g x) t
  let J : ℝ → ℝ := fun t => ∑ x, ∑ y, C.π x*C.P x y*|level (g x) t-level (g y) t|
  have hF : Integrable F :=
    (integrable_finsetSum _ (fun x _ => (level_integrable (g x)).const_mul (C.π x))).const_mul _
  have hJ : Integrable J := integrable_finsetSum _ fun x _ =>
    integrable_finsetSum _ fun y _ => (level_abs_integrable (g x) (g y)).const_mul _
  have hle (t : ℝ) : F t ≤ J t := by
    let S := Finset.univ.filter fun x => 0 ≤ t ∧ t < g x
    have hi (x : X) : level (g x) t = if x ∈ S then 1 else 0 := by simp [level,S]
    have hm : mass C S ≤ 1/2 := (mass_mono C (by
      intro x hx
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx.1.trans_lt hx.2⟩)).trans hsmall
    have hc := hcut S
    rw [mass_compl,min_eq_left (by linarith : mass C S ≤ 1-mass C S)] at hc
    have hl : (∑ x, C.π x*level (g x) t) = mass C S := by
      simp only [hi,mul_ite,mul_one,mul_zero,mass]
      rw [← Finset.sum_filter]
      simp
    dsimp [F,J]
    rw [hl]
    simp only [hi,cut_indicator]
    linarith
  have H := integral_mono hF hJ hle
  dsimp [F,J] at H
  rw [integral_const_mul,integral_finsetSum _ (fun x _ => (level_integrable (g x)).const_mul _)] at H
  simp_rw [integral_const_mul,level_integral (hg _)] at H
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _
    (fun y _ => (level_abs_integrable (g x) (g y)).const_mul _))] at H
  simp_rw [integral_finsetSum _ (fun y _ => (level_abs_integrable _ _).const_mul _),
    integral_const_mul,level_abs_integral (hg _) (hg _)] at H
  exact H

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_CheegerMedian
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A stationary weighted median on a finite chain -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section
variable {X : Type*} [Fintype X] (C : FiniteChain X)

theorem exists_median (f : X → ℝ) : ∃ a : ℝ,
    mass C (Finset.univ.filter fun x => f x < a) ≤ 1/2 ∧
    mass C (Finset.univ.filter fun x => a < f x) ≤ 1/2 := by
  have hne : (Finset.univ : Finset X).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have h := C.normalized
    rw [hz,Finset.sum_empty] at h
    norm_num at h
  let M := Finset.univ.filter fun x =>
    1/2 ≤ mass C (Finset.univ.filter fun y => f y ≤ f x)
  have hM : M.Nonempty := by
    obtain ⟨x,hx,hm⟩ := Finset.exists_max_image Finset.univ f hne
    have he : (Finset.univ.filter fun y => f y ≤ f x) = Finset.univ := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact iff_true_intro (hm y (Finset.mem_univ _))
    refine ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩⟩
    rw [he]
    simp only [mass,C.normalized]
    norm_num
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image M f hM
  have hxM : 1/2 ≤ mass C (Finset.univ.filter fun y => f y ≤ f x) :=
    (Finset.mem_filter.mp hx).2
  refine ⟨f x,?_,?_⟩
  · let L := Finset.univ.filter fun y => f y < f x
    change mass C L ≤ 1/2
    by_contra hn
    have hL : 1/2 < mass C L := lt_of_not_ge hn
    have hLn : L.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he] at hL
      norm_num [mass] at hL
    obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image L f hLn
    have hyx : f y < f x := (Finset.mem_filter.mp hy).2
    have he : (Finset.univ.filter fun z => f z ≤ f y) = L := by
      ext z
      simp only [L,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun hz => hz.trans_lt hyx,fun hz => hymax z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)⟩
    have hyM : y ∈ M := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [he]
      exact hL.le
    exact (not_lt_of_ge (hmin y hyM)) hyx
  · have he : (Finset.univ.filter fun y => f y ≤ f x)ᶜ =
        Finset.univ.filter (fun y => f x < f y) := by
      ext y
      simp
    have h := mass_compl C (Finset.univ.filter fun y => f y ≤ f x)
    rw [he] at h
    linarith

theorem variance_le_centered (f : X → ℝ) (a : ℝ) :
    C.variance f ≤ ∑ x, C.π x*(f x-a)^2 := by
  have he : (∑ x, C.π x*(f x-a)^2) = C.inner f f-2*a*C.mean f+a^2 := by
    calc
      _ = (∑ x, C.π x*f x*f x)-2*a*(∑ x,C.π x*f x)+a^2*(∑ x,C.π x) := by
        simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [C.normalized,mul_one]; rfl
  rw [C.variance_formula,he]
  nlinarith [sq_nonneg (C.mean f-a)]

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_CheegerPositive
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cheeger energy bound for functions supported on half the mass -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

private lemma weighted_cauchy {ι : Type*} [Fintype ι]
    (w a b : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i*a i*b i)^2 ≤ (∑ i, w i*(a i)^2)*(∑ i, w i*(b i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)*a i) (fun i => Real.sqrt (w i)*b i)
  have hmul (i : ι) : (Real.sqrt (w i)*a i)*(Real.sqrt (w i)*b i) = w i*a i*b i := by
    calc
      _ = (Real.sqrt (w i))^2*a i*b i := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i)]
  have hsq (f : ι → ℝ) (i : ι) : (Real.sqrt (w i)*f i)^2 = w i*(f i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  simpa only [hmul,hsq] using h

variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma sum_pair_squares (g : X → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*((g x)^2+(g y)^2)) = 2*(∑ x, C.π x*(g x)^2) := by
  simp_rw [mul_add,Finset.sum_add_distrib]
  have hleft : (∑ x, ∑ y, C.π x*C.P x y*(g x)^2) = ∑ x, C.π x*(g x)^2 := by
    simp_rw [← Finset.sum_mul,← Finset.mul_sum,C.stochastic,mul_one]
  have hright : (∑ x, ∑ y, C.π x*C.P x y*(g y)^2) = ∑ y, C.π y*(g y)^2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,C.stationary]
  rw [hleft,hright]
  ring

lemma sum_pair_add_square_le (g : X → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*(g x+g y)^2) ≤ 4*(∑ x, C.π x*(g x)^2) := by
  calc
    _ ≤ ∑ x, ∑ y, 2*(C.π x*C.P x y*((g x)^2+(g y)^2)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hQ := mul_nonneg (C.positive x).le (C.nonnegative x y)
      have hsq : (g x+g y)^2 ≤ 2*((g x)^2+(g y)^2) := by nlinarith [sq_nonneg (g x-g y)]
      nlinarith [mul_le_mul_of_nonneg_left hsq hQ]
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [sum_pair_squares]; ring

theorem positive_energy (κ : ℝ) (hk : 0 < κ)
    (hcut : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hsmall : mass C (Finset.univ.filter fun x => 0 < g x) ≤ 1/2) :
    κ^2*(∑ x, C.π x*(g x)^2) ≤ 2*C.energy g := by
  let N := ∑ x, C.π x*(g x)^2
  let W := ∑ x, ∑ y, C.π x*C.P x y*|(g x)^2-(g y)^2|
  have hE : 0 ≤ C.energy g := C.energy_nonneg g
  have hN : 0 ≤ N := Finset.sum_nonneg fun x _ => mul_nonneg (C.positive x).le (sq_nonneg _)
  have hW : 0 ≤ W := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (C.positive x).le (C.nonnegative x y)) (abs_nonneg _)
  have hsquare : mass C (Finset.univ.filter fun x => 0 < (g x)^2) ≤ 1/2 := by
    apply le_trans (mass_mono C ?_) hsmall
    intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    nlinarith [hg x]
  have hc : 2*κ*N ≤ W := coarea C κ hcut (fun x => (g x)^2) (fun _ => sq_nonneg _) hsquare
  have hsqW : (2*κ*N)^2 ≤ W^2 := (sq_le_sq₀ (by positivity) hW).mpr hc
  have ha (x y : X) : |(g x)^2-(g y)^2| = |g x-g y| * (g x+g y) := by
    rw [show (g x)^2-(g y)^2 = (g x-g y)*(g x+g y) by ring,
      abs_mul,abs_of_nonneg (add_nonneg (hg x) (hg y))]
  have hcs := weighted_cauchy
    (fun z : X×X => C.π z.1*C.P z.1 z.2)
    (fun z => |g z.1-g z.2|) (fun z => g z.1+g z.2)
    (fun z => mul_nonneg (C.positive _).le (C.nonnegative _ _))
  simp only [Fintype.sum_prod_type,sq_abs] at hcs
  have he : (∑ x, ∑ y, C.π x*C.P x y*(g x-g y)^2) = 2*C.energy g := by
    rw [C.energy_eq]; ring
  have hW' : W = ∑ x, ∑ y, C.π x*C.P x y*|g x-g y| * (g x+g y) := by
    dsimp [W]
    simp_rw [ha,mul_assoc]
  rw [← hW',he] at hcs
  have hb := sum_pair_add_square_le C g
  have hall : (2*κ*N)^2 ≤ (2*C.energy g)*(4*N) :=
    (hsqW.trans hcs).trans (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*C.energy g))
  rcases hN.eq_or_lt with hz | hp
  · change κ^2*N ≤ _
    rw [← hz,mul_zero]
    positivity
  · change κ^2*N ≤ _
    have h : 4*N*(κ^2*N) ≤ 4*N*(2*C.energy g) := by nlinarith [hall]
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*N)).mp h

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.KLS_Convexity_PrekopaLeindler
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace AsymptoticStatistics

private theorem prekopaLeindler_1d_levelInclusion
    {f g h : ℝ → ℝ≥0∞}
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤) :
    t • {x | α < f x} + (1 - t) • {y | α < g y} ⊆ {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨_, hu, _, hv, rfl⟩ := hz
  rw [Set.mem_smul_set] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv

  simp only [smul_eq_mul, Set.mem_ofPred_eq] at hx hy ⊢

  have h_alpha_split : α = α ^ t * α ^ (1 - t) := by
    rw [← ENNReal.rpow_add t (1 - t) hα_pos.ne' hα_top]
    have ht_one : t + (1 - t) = (1 : ℝ) := by ring
    rw [ht_one, ENNReal.rpow_one]

  have h1 : α ^ t < f x ^ t := ENNReal.rpow_lt_rpow hx ht_pos
  have h2 : α ^ (1 - t) < g y ^ (1 - t) := ENNReal.rpow_lt_rpow hy h1t_pos

  have h3 : α ^ t * α ^ (1 - t) < f x ^ t * g y ^ (1 - t) := ENNReal.mul_lt_mul h1 h2

  calc α = α ^ t * α ^ (1 - t) := h_alpha_split
    _ < f x ^ t * g y ^ (1 - t) := h3
    _ ≤ h (t * x + (1 - t) * y) := h_le x y

private lemma oneDim_brunn_minkowski_compact_le
    {K_A K_B : Set ℝ}
    (hA_compact : IsCompact K_A) (hB_compact : IsCompact K_B)
    (hA_ne : K_A.Nonempty) (hB_ne : K_B.Nonempty) :
    volume K_A + volume K_B ≤ volume (K_A + K_B) := by

  set a := sSup K_A with ha_def
  set b := sInf K_B with hb_def
  have ha_mem : a ∈ K_A := hA_compact.sSup_mem hA_ne
  have hb_mem : b ∈ K_B := hB_compact.sInf_mem hB_ne
  have hA_le_a : ∀ x ∈ K_A, x ≤ a :=
    fun x hx => le_csSup hA_compact.bddAbove hx
  have hB_ge_b : ∀ y ∈ K_B, b ≤ y :=
    fun y hy => csInf_le hB_compact.bddBelow hy

  set U : Set ℝ := K_A + {b} with hU_def
  set V : Set ℝ := {a} + K_B with hV_def

  have hU_sub_AB : U ⊆ K_A + K_B := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    exact ⟨x, hx, b, hb_mem, rfl⟩
  have hV_sub_AB : V ⊆ K_A + K_B := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    exact ⟨a, ha_mem, y, hy, rfl⟩

  have hU_vol : volume U = volume K_A := by
    rw [hU_def, Set.add_singleton, Set.image_add_right]
    exact MeasureTheory.measure_preimage_add_right volume (-b) K_A

  have hV_vol : volume V = volume K_B := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact MeasureTheory.measure_preimage_add volume (-a) K_B

  have hU_sub_Iic : U ⊆ Set.Iic (a + b) := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    have := hA_le_a x hx
    simp only [Set.mem_Iic]
    linarith

  have hV_sub_Ici : V ⊆ Set.Ici (a + b) := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    have := hB_ge_b y hy
    simp only [Set.mem_Ici]
    linarith

  have h_inter_sub : U ∩ V ⊆ {a + b} := by
    rintro z ⟨hzU, hzV⟩
    have h1 := hU_sub_Iic hzU
    have h2 := hV_sub_Ici hzV
    simp only [Set.mem_Iic] at h1
    simp only [Set.mem_Ici] at h2
    simp only [Set.mem_singleton_iff]
    linarith

  have h_inter_zero : volume (U ∩ V) = 0 := by
    apply le_antisymm _ (by positivity)
    calc volume (U ∩ V)
        ≤ volume ({a + b} : Set ℝ) := MeasureTheory.measure_mono h_inter_sub
      _ = 0 := MeasureTheory.measure_singleton (a + b)

  have hV_meas : MeasurableSet V := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact (hB_compact.measurableSet).preimage (measurable_const_add (-a))
  have h_inc_excl : volume (U ∪ V) + volume (U ∩ V) = volume U + volume V :=
    MeasureTheory.measure_union_add_inter U hV_meas

  have h_union_sub : U ∪ V ⊆ K_A + K_B := Set.union_subset hU_sub_AB hV_sub_AB
  have h_union_le : volume (U ∪ V) ≤ volume (K_A + K_B) :=
    MeasureTheory.measure_mono h_union_sub

  calc volume K_A + volume K_B
      = volume U + volume V := by rw [hU_vol, hV_vol]
    _ = volume (U ∪ V) + volume (U ∩ V) := h_inc_excl.symm
    _ = volume (U ∪ V) + 0 := by rw [h_inter_zero]
    _ = volume (U ∪ V) := add_zero _
    _ ≤ volume (K_A + K_B) := h_union_le

private theorem oneDim_brunn_minkowski_le
    {A B C : Set ℝ}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (_hC_meas : MeasurableSet C)
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty)
    (hAB_sub : A + B ⊆ C) :
    volume A + volume B ≤ volume C := by

  by_cases hA_zero : volume A = 0
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    rw [hA_zero, zero_add]
    calc volume B = volume (({a₀} : Set ℝ) + B) := h_aB_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_aB_sub_C

  by_cases hB_zero : volume B = 0
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    rw [hB_zero, add_zero]
    calc volume A = volume (A + ({b₀} : Set ℝ)) := h_Ab_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_Ab_sub_C

  by_cases hA_top : volume A = ⊤
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hA_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume A = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hA_meas
    calc (⊤ : ℝ≥0∞)
        = volume A := hA_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_A => iSup_le fun hK_A_sub => iSup_le fun _ => ?_
          have h_KA_b0_sub : K_A + ({b₀} : Set ℝ) ⊆ C :=
            fun z ⟨x, hx, _, rfl, hxz⟩ => hAB_sub ⟨x, hK_A_sub hx, b₀, hb₀, hxz⟩
          have h_KA_b0_eq : volume (K_A + ({b₀} : Set ℝ)) = volume K_A := by
            rw [Set.add_singleton, Set.image_add_right]
            exact MeasureTheory.measure_preimage_add_right volume (-b₀) K_A
          calc volume K_A
              = volume (K_A + ({b₀} : Set ℝ)) := h_KA_b0_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_KA_b0_sub

  by_cases hB_top : volume B = ⊤
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hB_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume B = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hB_meas
    calc (⊤ : ℝ≥0∞)
        = volume B := hB_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_B => iSup_le fun hK_B_sub => iSup_le fun _ => ?_
          have h_a0_KB_sub : ({a₀} : Set ℝ) + K_B ⊆ C :=
            fun z ⟨_, rfl, y, hy, hyz⟩ => hAB_sub ⟨a₀, ha₀, y, hK_B_sub hy, hyz⟩
          have h_a0_KB_eq : volume (({a₀} : Set ℝ) + K_B) = volume K_B := by
            rw [Set.singleton_add, Set.image_add_left]
            exact MeasureTheory.measure_preimage_add volume (-a₀) K_B
          calc volume K_B
              = volume (({a₀} : Set ℝ) + K_B) := h_a0_KB_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_a0_KB_sub

  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hC_top

  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hδ_def
  have hδ_pos : (0 : ℝ≥0∞) < δ := by
    rw [hδ_def]
    refine ENNReal.div_pos ?_ (by norm_num)
    exact_mod_cast hε.ne'
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  have hδ_le : δ ≤ ε := by
    rw [hδ_def]; exact ENNReal.half_le_self

  obtain ⟨K_A, hK_A_sub, hK_A_compact, hK_A_lt⟩ :=
    hA_meas.exists_isCompact_lt_add hA_top hδ_ne
  obtain ⟨K_B, hK_B_sub, hK_B_compact, hK_B_lt⟩ :=
    hB_meas.exists_isCompact_lt_add hB_top hδ_ne

  rcases K_A.eq_empty_or_nonempty with hKA_empty | hKA_ne
  ·
    rw [hKA_empty, MeasureTheory.measure_empty, zero_add] at hK_A_lt

    have hA_le_ε : volume A ≤ (ε : ℝ≥0∞) := le_trans hK_A_lt.le hδ_le

    obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    have hB_le_C : volume B ≤ volume C := by
      rw [← h_aB_eq]; exact MeasureTheory.measure_mono h_aB_sub_C
    calc volume A + volume B ≤ (ε : ℝ≥0∞) + volume C := add_le_add hA_le_ε hB_le_C
      _ = volume C + (ε : ℝ≥0∞) := add_comm _ _
  rcases K_B.eq_empty_or_nonempty with hKB_empty | hKB_ne
  ·
    rw [hKB_empty, MeasureTheory.measure_empty, zero_add] at hK_B_lt
    have hB_le_ε : volume B ≤ (ε : ℝ≥0∞) := le_trans hK_B_lt.le hδ_le
    obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    have hA_le_C : volume A ≤ volume C := by
      rw [← h_Ab_eq]; exact MeasureTheory.measure_mono h_Ab_sub_C
    exact add_le_add hA_le_C hB_le_ε
  ·
    have hKAB_sub : K_A + K_B ⊆ C :=
      fun z ⟨x, hx, y, hy, hxyz⟩ =>
        hAB_sub ⟨x, hK_A_sub hx, y, hK_B_sub hy, hxyz⟩
    have h_compact_bm := oneDim_brunn_minkowski_compact_le
      hK_A_compact hK_B_compact hKA_ne hKB_ne
    have h_KAKB_le_C : volume (K_A + K_B) ≤ volume C :=
      MeasureTheory.measure_mono hKAB_sub

    have h_2δ_le_ε : (2 : ℝ≥0∞) * δ ≤ (ε : ℝ≥0∞) := by
      rw [hδ_def]; exact ENNReal.mul_div_le
    calc volume A + volume B
        ≤ (volume K_A + δ) + (volume K_B + δ) := by gcongr
      _ = (volume K_A + volume K_B) + (δ + δ) := by ring
      _ = (volume K_A + volume K_B) + 2 * δ := by ring
      _ ≤ volume C + 2 * δ := by
          gcongr
          exact le_trans h_compact_bm h_KAKB_le_C
      _ ≤ volume C + (ε : ℝ≥0∞) := by gcongr

private theorem prekopaLeindler_1d_levelMeasureBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤)
    (hA_ne : ({x | α < f x} : Set ℝ).Nonempty)
    (hB_ne : ({y | α < g y} : Set ℝ).Nonempty) :
    ENNReal.ofReal t * volume {x | α < f x}
      + ENNReal.ofReal (1 - t) * volume {y | α < g y}
      ≤ volume {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set A : Set ℝ := {x | α < f x} with hA_def
  set B : Set ℝ := {y | α < g y} with hB_def
  set C : Set ℝ := {z | α < h z} with hC_def

  have hA_meas : MeasurableSet A := hf_meas measurableSet_Ioi
  have hB_meas : MeasurableSet B := hg_meas measurableSet_Ioi
  have hC_meas : MeasurableSet C := hh_meas measurableSet_Ioi

  have h_incl : t • A + (1 - t) • B ⊆ C :=
    prekopaLeindler_1d_levelInclusion ht_pos ht_lt h_le hα_pos hα_top

  have htA_meas : MeasurableSet (t • A) :=
    hA_meas.const_smul_of_ne_zero ht_pos.ne'
  have h1tB_meas : MeasurableSet ((1 - t) • B) :=
    hB_meas.const_smul_of_ne_zero h1t_pos.ne'

  have htA_ne : (t • A).Nonempty := Set.smul_set_nonempty.mpr hA_ne
  have h1tB_ne : ((1 - t) • B).Nonempty := Set.smul_set_nonempty.mpr hB_ne

  have h_bm : volume (t • A) + volume ((1 - t) • B) ≤ volume C :=
    oneDim_brunn_minkowski_le htA_meas h1tB_meas hC_meas htA_ne h1tB_ne h_incl

  have h_finrank : Module.finrank ℝ ℝ = 1 := CommSemiring.finrank_self ℝ
  have h_smul_t : volume (t • A) = ENNReal.ofReal t * volume A := by
    rw [Measure.addHaar_smul_of_nonneg volume ht_pos.le A, h_finrank, pow_one]
  have h_smul_1t : volume ((1 - t) • B) = ENNReal.ofReal (1 - t) * volume B := by
    rw [Measure.addHaar_smul_of_nonneg volume h1t_pos.le B, h_finrank, pow_one]
  rw [← h_smul_t, ← h_smul_1t]
  exact h_bm

private theorem lintegral_eq_lintegral_meas_lt_ennreal
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x} := by

  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  have hfN_meas : ∀ n, Measurable (fN n) :=
    fun n => hf.inf measurable_const
  have hfN_lt_top : ∀ n x, fN n x ≠ ⊤ :=
    fun n x => ne_top_of_le_ne_top ENNReal.coe_ne_top inf_le_right
  have hfN_mono : Monotone fN := by
    intro m n hmn x
    exact inf_le_inf_left _ (by exact_mod_cast hmn)
  have hfN_iSup_eq : ∀ x, ⨆ n, fN n x = f x := fun x => by
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

  have hLHS : ∫⁻ x, f x = ⨆ n, ∫⁻ x, fN n x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas hfN_mono]
    exact MeasureTheory.lintegral_congr fun x => (hfN_iSup_eq x).symm

  have h_per_n : ∀ n, ∫⁻ x, fN n x =
      ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    intro n
    have h_eq : ∫⁻ x, fN n x = ∫⁻ x, ENNReal.ofReal ((fN n x).toReal) :=
      MeasureTheory.lintegral_congr fun x => (ENNReal.ofReal_toReal (hfN_lt_top n x)).symm
    rw [h_eq, MeasureTheory.lintegral_eq_lintegral_meas_lt volume
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        ((hfN_meas n).ennreal_toReal.aemeasurable)]

    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro α hα
    have hα_nn : (0 : ℝ) ≤ α := le_of_lt hα
    change volume {x | α < (fN n x).toReal}
        = volume {x | ENNReal.ofReal α < fN n x}
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mpr h
      rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)] at this
    · have h' : ENNReal.ofReal α < ENNReal.ofReal ((fN n x).toReal) := by
        rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mp h'

  have h_set_mono : ∀ α : ℝ,
      Monotone fun n : ℕ => {x | ENNReal.ofReal α < fN n x} := by
    intro α m n hmn x hx
    exact lt_of_lt_of_le hx (hfN_mono hmn x)
  have h_set_iUnion : ∀ α : ℝ,
      ⋃ n : ℕ, {x | ENNReal.ofReal α < fN n x}
        = {x | ENNReal.ofReal α < f x} := by
    intro α
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ => lt_of_lt_of_le hn (le_trans inf_le_left le_rfl), ?_⟩
    intro hx
    rw [← hfN_iSup_eq x] at hx
    exact lt_iSup_iff.mp hx

  have h_meas_vol : ∀ n,
      Measurable fun α : ℝ => volume {x | ENNReal.ofReal α < fN n x} := by
    intro n

    have h_set_meas : MeasurableSet
        {p : ℝ × ℝ | ENNReal.ofReal p.1 < fN n p.2} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((hfN_meas n).comp measurable_snd)

    exact measurable_measure_prodMk_left h_set_meas
  have hRHS : ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x}
        = ⨆ n, ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    rw [show (fun α => volume {x | ENNReal.ofReal α < f x})
          = fun α => ⨆ n, volume {x | ENNReal.ofReal α < fN n x} from
        funext fun α => by rw [← h_set_iUnion α,
          (h_set_mono α).measure_iUnion]]
    exact MeasureTheory.lintegral_iSup (fun n => h_meas_vol n)
      (fun m n hmn α => MeasureTheory.measure_mono (h_set_mono α hmn))
  rw [hLHS, hRHS]
  exact iSup_congr h_per_n

private theorem ennreal_geom_mean_le_arith_mean2_weighted
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (a b : ℝ≥0∞) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  by_cases ha : a = ⊤
  · subst ha
    have h_rhs : ENNReal.ofReal t * ⊤ + ENNReal.ofReal (1 - t) * b = ⊤ := by
      have : ENNReal.ofReal t ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top
  by_cases hb : b = ⊤
  · subst hb
    have h_rhs : ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * ⊤ = ⊤ := by
      have : ENNReal.ofReal (1 - t) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top

  set A : ℝ := a.toReal with hA_def
  set B : ℝ := b.toReal with hB_def
  have hA_nn : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB_nn : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hofa : ENNReal.ofReal A = a := ENNReal.ofReal_toReal ha
  have hofb : ENNReal.ofReal B = b := ENNReal.ofReal_toReal hb
  have h_real : A ^ t * B ^ (1 - t) ≤ t * A + (1 - t) * B :=
    Real.geom_mean_le_arith_mean2_weighted ht_pos.le h1t_pos.le hA_nn hB_nn
      (by linarith)
  have hAt_nn : (0 : ℝ) ≤ A ^ t := Real.rpow_nonneg hA_nn t
  have hBt_nn : (0 : ℝ) ≤ B ^ (1 - t) := Real.rpow_nonneg hB_nn (1 - t)
  calc a ^ t * b ^ (1 - t)
      = ENNReal.ofReal A ^ t * ENNReal.ofReal B ^ (1 - t) := by rw [hofa, hofb]
    _ = ENNReal.ofReal (A ^ t) * ENNReal.ofReal (B ^ (1 - t)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA_nn ht_pos.le,
            ENNReal.ofReal_rpow_of_nonneg hB_nn h1t_pos.le]
    _ = ENNReal.ofReal (A ^ t * B ^ (1 - t)) := by
        rw [← ENNReal.ofReal_mul hAt_nn]
    _ ≤ ENNReal.ofReal (t * A + (1 - t) * B) := ENNReal.ofReal_le_ofReal h_real
    _ = ENNReal.ofReal (t * A) + ENNReal.ofReal ((1 - t) * B) :=
        ENNReal.ofReal_add (mul_nonneg ht_pos.le hA_nn)
          (mul_nonneg h1t_pos.le hB_nn)
    _ = ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
        rw [ENNReal.ofReal_mul ht_pos.le, ENNReal.ofReal_mul h1t_pos.le,
            hofa, hofb]

private theorem prekopaLeindler_1d_arithBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (h_ess_eq : essSup f volume = essSup g volume) :
    ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ y, g y)
      ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set M : ℝ≥0∞ := essSup f volume with hM_def

  have h_pos_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, β < M → 0 < volume {x | β < φ x} := by
    intro φ hφ_ess β hβ
    by_contra h_neg
    rw [not_lt, nonpos_iff_eq_zero] at h_neg
    have h_ae : φ ≤ᵐ[volume] fun _ => β := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
      simpa using h_neg
    have : essSup φ volume ≤ β := essSup_le_of_ae_le β h_ae
    rw [hφ_ess] at this
    exact absurd this (not_le.mpr hβ)

  have h_null_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, M ≤ β → volume {x | β < φ x} = 0 := by
    intro φ hφ_ess β hβ
    have h_essSup_le : essSup φ volume ≤ β := hφ_ess.trans_le hβ

    have h_sub : {x | β < φ x} ⊆ {x | essSup φ volume < φ x} :=
      fun x hx => lt_of_le_of_lt h_essSup_le hx
    refine le_antisymm ?_ (by positivity)
    calc volume {x | β < φ x}
        ≤ volume {x | essSup φ volume < φ x} := MeasureTheory.measure_mono h_sub
      _ = 0 := meas_essSup_lt

  let volF : ℝ → ℝ≥0∞ := fun α => volume {x | ENNReal.ofReal α < f x}
  let volG : ℝ → ℝ≥0∞ := fun α => volume {y | ENNReal.ofReal α < g y}
  let volH : ℝ → ℝ≥0∞ := fun α => volume {z | ENNReal.ofReal α < h z}
  have hvolF_meas : Measurable volF :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hf_meas.comp measurable_snd))
  have hvolG_meas : Measurable volG :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hg_meas.comp measurable_snd))

  have h_pointwise : ∀ α : ℝ, 0 < α →
      ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α := by
    intro α hα
    have hα_pos_e : (0 : ℝ≥0∞) < ENNReal.ofReal α :=
      ENNReal.ofReal_pos.mpr hα
    have hα_top : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
    by_cases hαM : ENNReal.ofReal α < M
    ·
      have hA_pos : 0 < volume {x | ENNReal.ofReal α < f x} :=
        h_pos_meas hM_def.symm hαM
      have hB_pos : 0 < volume {y | ENNReal.ofReal α < g y} :=
        h_pos_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      have hA_ne : ({x | ENNReal.ofReal α < f x} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hA_pos.ne'
      have hB_ne : ({y | ENNReal.ofReal α < g y} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hB_pos.ne'
      exact prekopaLeindler_1d_levelMeasureBound hf_meas hg_meas hh_meas
        ht_pos ht_lt h_le hα_pos_e hα_top hA_ne hB_ne
    ·
      rw [not_lt] at hαM
      have hf_null : volF α = 0 := h_null_meas hM_def.symm hαM
      have hg_null : volG α = 0 := h_null_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      change ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α
      rw [hf_null, hg_null, mul_zero, mul_zero, zero_add]
      positivity

  rw [lintegral_eq_lintegral_meas_lt_ennreal hf_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hg_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hh_meas]

  change ENNReal.ofReal t * (∫⁻ α in Ioi (0:ℝ), volF α)
       + ENNReal.ofReal (1 - t) * (∫⁻ α in Ioi (0:ℝ), volG α)
       ≤ ∫⁻ α in Ioi (0:ℝ), volH α

  rw [← MeasureTheory.lintegral_const_mul _ hvolF_meas,
      ← MeasureTheory.lintegral_const_mul _ hvolG_meas]

  rw [← MeasureTheory.lintegral_add_left (hvolF_meas.const_mul _)]

  exact MeasureTheory.setLIntegral_mono'
    measurableSet_Ioi (fun α hα => h_pointwise α hα)

private theorem prekopaLeindler_1d_essBdd
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (hMf_top : essSup f volume ≠ ⊤) (hMg_top : essSup g volume ≠ ⊤) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set Mf := essSup f volume with hMf_def
  set Mg := essSup g volume with hMg_def

  by_cases hMf_zero : Mf = 0
  · have hf_int_zero : ∫⁻ x, f x = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hf_meas]
      filter_upwards [ENNReal.ae_le_essSup f] with x hx
      rw [← hMf_def, hMf_zero] at hx
      exact le_antisymm hx (by positivity)
    rw [hf_int_zero, ENNReal.zero_rpow_of_pos ht_pos, zero_mul]
    positivity

  by_cases hMg_zero : Mg = 0
  · have hg_int_zero : ∫⁻ y, g y = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hg_meas]
      filter_upwards [ENNReal.ae_le_essSup g] with y hy
      rw [← hMg_def, hMg_zero] at hy
      exact le_antisymm hy (by positivity)
    rw [hg_int_zero, ENNReal.zero_rpow_of_pos h1t_pos, mul_zero]
    positivity

  set c : ℝ≥0∞ := Mg / Mf with hc_def
  have hc_pos : (0 : ℝ≥0∞) < c := ENNReal.div_pos hMg_zero hMf_top
  have hc_top : c ≠ ⊤ := by
    rw [hc_def]
    exact (ENNReal.div_lt_top hMg_top hMf_zero).ne
  have hcMf_eq_Mg : c * Mf = Mg := by
    rw [hc_def, ENNReal.div_mul_cancel hMf_zero hMf_top]

  set f' : ℝ → ℝ≥0∞ := fun x => c * f x with hf'_def
  set h' : ℝ → ℝ≥0∞ := fun z => c ^ t * h z with hh'_def
  have hf'_meas : Measurable f' := hf_meas.const_mul c
  have hh'_meas : Measurable h' := hh_meas.const_mul (c ^ t)

  have hf'_essSup : essSup f' volume = Mg := by
    change essSup (fun x => c * f x) volume = Mg
    rw [ENNReal.essSup_const_mul, hcMf_eq_Mg]

  have h_le' : ∀ x y : ℝ,
      f' x ^ t * g y ^ (1 - t) ≤ h' (t * x + (1 - t) * y) := by
    intro x y
    change (c * f x) ^ t * g y ^ (1 - t) ≤ c ^ t * h (t * x + (1 - t) * y)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc]
    gcongr
    exact h_le x y

  have h_amgm := ennreal_geom_mean_le_arith_mean2_weighted ht_pos ht_lt
    (∫⁻ x, f' x) (∫⁻ y, g y)
  have h_arith := prekopaLeindler_1d_arithBound hf'_meas hg_meas hh'_meas
    ht_pos ht_lt h_le' (hf'_essSup.trans hMg_def.symm)
  have h_pl_rescaled :
      (∫⁻ x, f' x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h' z :=
    le_trans h_amgm h_arith

  rw [show ∫⁻ x, f' x = c * ∫⁻ x, f x from
        MeasureTheory.lintegral_const_mul c hf_meas,
      show ∫⁻ z, h' z = c ^ t * ∫⁻ z, h z from
        MeasureTheory.lintegral_const_mul (c ^ t) hh_meas,
      ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc] at h_pl_rescaled

  have hct_ne_zero : c ^ t ≠ 0 := (ENNReal.rpow_pos hc_pos hc_top).ne'
  have hct_ne_top : c ^ t ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ht_pos.le hc_top).ne

  rw [mul_comm (c ^ t) _, mul_comm (c ^ t) _] at h_pl_rescaled
  exact (ENNReal.mul_le_mul_iff_left hct_ne_zero hct_ne_top).mp h_pl_rescaled

theorem prekopaLeindler_1d
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt

  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  set gN : ℕ → ℝ → ℝ≥0∞ := fun n y => g y ⊓ (n : ℝ≥0∞) with hgN_def
  have hfN_meas : ∀ n, Measurable (fN n) := fun n => hf_meas.inf measurable_const
  have hgN_meas : ∀ n, Measurable (gN n) := fun n => hg_meas.inf measurable_const
  have hfN_essSup_top : ∀ n, essSup (fN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (fN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)
  have hgN_essSup_top : ∀ n, essSup (gN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (gN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)

  have h_le_N : ∀ n m, ∀ x y : ℝ,
      fN n x ^ t * gN m y ^ (1 - t) ≤ h (t * x + (1 - t) * y) := by
    intro n m x y
    calc fN n x ^ t * gN m y ^ (1 - t)
        ≤ f x ^ t * g y ^ (1 - t) := by
          gcongr <;> exact inf_le_left
      _ ≤ h (t * x + (1 - t) * y) := h_le x y

  have h_per_nm : ∀ n m,
      (∫⁻ x, fN n x) ^ t * (∫⁻ y, gN m y) ^ (1 - t) ≤ ∫⁻ z, h z := fun n m =>
    prekopaLeindler_1d_essBdd (hfN_meas n) (hgN_meas m) hh_meas ht_pos ht_lt
      (h_le_N n m) (hfN_essSup_top n) (hgN_essSup_top m)

  have hfN_mono : Monotone fun n => ∫⁻ x, fN n x := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro x; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hgN_mono : Monotone fun m => ∫⁻ y, gN m y := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro y; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hfN_iSup : ⨆ n, ∫⁻ x, fN n x = ∫⁻ x, f x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas (fun n m hnm x =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro x
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hgN_iSup : ⨆ m, ∫⁻ y, gN m y = ∫⁻ y, g y := by
    rw [← MeasureTheory.lintegral_iSup hgN_meas (fun n m hnm y =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro y
    simp only [gN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

  have h_rpow_iSup : ∀ (a : ℕ → ℝ≥0∞) (p : ℝ), 0 ≤ p → Monotone a →
      (⨆ n, a n) ^ p = ⨆ n, a n ^ p := by
    intro a p hp ha_mono
    have h_tendsto : Filter.Tendsto a Filter.atTop (𝓝 (⨆ n, a n)) :=
      tendsto_atTop_iSup ha_mono
    have h_tendsto_pow : Filter.Tendsto (fun n => a n ^ p) Filter.atTop
        (𝓝 ((⨆ n, a n) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h_tendsto
    have ha_pow_mono : Monotone (fun n => a n ^ p) := fun n m hnm =>
      ENNReal.rpow_le_rpow (ha_mono hnm) hp
    exact tendsto_nhds_unique h_tendsto_pow (tendsto_atTop_iSup ha_pow_mono)
  rw [← hfN_iSup, ← hgN_iSup]

  rw [h_rpow_iSup _ t ht_pos.le hfN_mono,
      h_rpow_iSup _ (1 - t) h1t_pos.le hgN_mono]

  rw [ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_

  exact h_per_nm n m

theorem prekopaLeindler.{u}
    {ι : Type u} [Fintype ι]
    {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ι → ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by

  suffices H : ∀ (κ : Type u) [Fintype κ] (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z by
    exact H ι f g h hf_meas hg_meas hh_meas ht_pos ht_lt h_le
  intro κ _Fκ
  refine Fintype.induction_empty_option
    (P := fun κ [Fintype κ] => ∀ (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z) ?_ ?_ ?_ κ
  ·

    intro α β _Fβ e IH f g h hf hg hh s hs hs1 hle
    let : Fintype α := Fintype.ofEquiv β e.symm
    set ψ : (β → ℝ) ≃ᵐ (α → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) e.symm with hψ_def

    have hψ_smul : ∀ x y : α → ℝ,
        ψ.symm (s • x + (1 - s) • y) = s • ψ.symm x + (1 - s) • ψ.symm y := fun _ _ => rfl

    have h_vol_fwd : (volume : Measure (β → ℝ)).map ψ = (volume : Measure (α → ℝ)) := by
      conv_lhs => rw [MeasureTheory.volume_pi]
      conv_rhs => rw [MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piCongrLeft e.symm (fun _ : α => volume)
    have h_vol : (volume : Measure (α → ℝ)).map ψ.symm = (volume : Measure (β → ℝ)) := by
      rw [← h_vol_fwd, MeasurableEquiv.map_symm_map]

    have hf' : Measurable (f ∘ ψ.symm) := hf.comp ψ.symm.measurable
    have hg' : Measurable (g ∘ ψ.symm) := hg.comp ψ.symm.measurable
    have hh' : Measurable (h ∘ ψ.symm) := hh.comp ψ.symm.measurable
    have hle' : ∀ x y : α → ℝ,
        (f ∘ ψ.symm) x ^ s * (g ∘ ψ.symm) y ^ (1 - s)
        ≤ (h ∘ ψ.symm) (s • x + (1 - s) • y) := by
      intro x y
      change f (ψ.symm x) ^ s * g (ψ.symm y) ^ (1 - s) ≤ h (ψ.symm (s • x + (1 - s) • y))
      rw [hψ_smul x y]
      exact hle (ψ.symm x) (ψ.symm y)

    have hf_int : ∫⁻ y, f y = ∫⁻ x, f (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hf ψ.symm.measurable
    have hg_int : ∫⁻ y, g y = ∫⁻ x, g (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hg ψ.symm.measurable
    have hh_int : ∫⁻ y, h y = ∫⁻ x, h (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hh ψ.symm.measurable
    rw [hf_int, hg_int, hh_int]
    exact IH (f ∘ ψ.symm) (g ∘ ψ.symm) (h ∘ ψ.symm) hf' hg' hh' hs hs1 hle'
  ·

    intro f g h hf_meas hg_meas hh_meas s hs_pos hs_lt h_le
    have h_volume : (volume : Measure (PEmpty → ℝ))
        = Measure.dirac (fun a : PEmpty => isEmptyElim a) :=
      Measure.volume_pi_eq_dirac _
    rw [h_volume, lintegral_dirac' _ hf_meas, lintegral_dirac' _ hg_meas,
        lintegral_dirac' _ hh_meas]
    have h_pl := h_le (fun a => isEmptyElim a) (fun a => isEmptyElim a)
    have h_smul : s • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                  + (1 - s) • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                = (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ) := by
      funext a; exact isEmptyElim a
    rwa [h_smul] at h_pl
  ·

    intro α _Fα IH f g h hf hg hh s hs hs1 hle
    let E : ((i : Option α) → ℝ) ≃ᵐ ((i : α) → ℝ) × ℝ :=
      MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)

    have hE_none : ∀ (x' : α → ℝ) (u : ℝ),
        E.symm (x', u) none = u := fun _ _ => rfl
    have hE_some : ∀ (x' : α → ℝ) (u : ℝ) (a : α),
        E.symm (x', u) (some a) = x' a := fun _ _ _ => rfl

    have hE_smul : ∀ (x' y' : α → ℝ) (u v : ℝ),
        s • E.symm (x', u) + (1 - s) • E.symm (y', v)
        = E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v) := by
      intro x' y' u v
      funext i
      cases i with
      | none =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * u + (1 - s) * v = s * u + (1 - s) * v
        rfl
      | some a =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * x' a + (1 - s) * y' a = s * x' a + (1 - s) * y' a
        rfl

    have h_vol : ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        = (volume : Measure (Option α → ℝ)) := by
      conv_rhs => rw [MeasureTheory.volume_pi]
      conv_lhs => rw [show (volume : Measure (α → ℝ))
          = MeasureTheory.Measure.pi (fun _ : α => volume) from MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piOptionEquivProd
        (fun _ : Option α => volume)

    set F : ℝ → ℝ≥0∞ := fun u => ∫⁻ x' : α → ℝ, f (E.symm (x', u)) with hF_def
    set G : ℝ → ℝ≥0∞ := fun v => ∫⁻ y' : α → ℝ, g (E.symm (y', v)) with hG_def
    set H_marg : ℝ → ℝ≥0∞ := fun w => ∫⁻ z' : α → ℝ, h (E.symm (z', w)) with hH_def

    have hf_comp : Measurable (fun p : (α → ℝ) × ℝ => f (E.symm p)) :=
      hf.comp E.symm.measurable
    have hg_comp : Measurable (fun p : (α → ℝ) × ℝ => g (E.symm p)) :=
      hg.comp E.symm.measurable
    have hh_comp : Measurable (fun p : (α → ℝ) × ℝ => h (E.symm p)) :=
      hh.comp E.symm.measurable
    have hF_meas : Measurable F := Measurable.lintegral_prod_left' hf_comp
    have hG_meas : Measurable G := Measurable.lintegral_prod_left' hg_comp
    have hH_marg_meas : Measurable H_marg := Measurable.lintegral_prod_left' hh_comp

    have h_FGH_le : ∀ u v : ℝ,
        F u ^ s * G v ^ (1 - s) ≤ H_marg (s * u + (1 - s) * v) := by
      intro u v
      have hf_slice : Measurable (fun x' : α → ℝ => f (E.symm (x', u))) :=
        hf.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hg_slice : Measurable (fun y' : α → ℝ => g (E.symm (y', v))) :=
        hg.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hh_slice : Measurable (fun z' : α → ℝ =>
          h (E.symm (z', s * u + (1 - s) * v))) :=
        hh.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have h_slice_le : ∀ x' y' : α → ℝ,
          f (E.symm (x', u)) ^ s * g (E.symm (y', v)) ^ (1 - s)
          ≤ h (E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v)) := by
        intro x' y'
        have h_pl := hle (E.symm (x', u)) (E.symm (y', v))
        rw [hE_smul] at h_pl
        exact h_pl
      exact IH _ _ _ hf_slice hg_slice hh_slice hs hs1 h_slice_le

    have h_1d := prekopaLeindler_1d hF_meas hG_meas hH_marg_meas hs hs1 h_FGH_le

    have h_int_split : ∀ (k : (Option α → ℝ) → ℝ≥0∞), Measurable k →
        ∫⁻ z, k z = ∫⁻ u : ℝ, ∫⁻ x' : α → ℝ, k (E.symm (x', u)) := by
      intro k hk
      conv_lhs => rw [show (volume : Measure (Option α → ℝ))
          = ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        from h_vol.symm]
      rw [MeasureTheory.lintegral_map hk E.symm.measurable]
      exact MeasureTheory.lintegral_prod_symm' _ (hk.comp E.symm.measurable)
    rw [h_int_split f hf, h_int_split g hg, h_int_split h hh]
    exact h_1d

end AsymptoticStatistics

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_FiniteBoxPrekopa
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the finite-box Prékopa–Leindler input

The finite-function-space Prékopa–Leindler inequality applies to the nonnegative
indicators of the three box unions. Compact-box continuity supplies all
measurability and integrability obligations without assumptions outside
the common box.
-/
namespace ContingencyTables.PublishedInputs
open MeasureTheory Set
open scoped ENNReal
noncomputable section

private theorem integral_interpolation {q : ℕ} {f g h : Point q → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y, f x ^ t * g y ^ (1-t) ≤ h (t • x+(1-t) • y)) :
    (∫ x, f x)^t * (∫ y, g y)^(1-t) ≤ ∫ z, h z := by
  have hp := AsymptoticStatistics.prekopaLeindler hf.ennreal_ofReal hg.ennreal_ofReal
    hh.ennreal_ofReal ht ht1 (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht.le,
        ENNReal.ofReal_rpow_of_nonneg (hg0 y) (sub_pos.mpr ht1).le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
      exact ENNReal.ofReal_le_ofReal (hfg x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0)] at hp
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) ht.le,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) (sub_pos.mpr ht1).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) t)] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh0)).mp hp

private theorem box_indicator {q : ℕ} {lower upper : Point q} {S : Set (Point q)}
    {f : Point q → ℝ} (hS : IsFiniteBoxUnion S)
    (hbox : closure S ⊆ Icc lower upper) (hf : ContinuousOn f (Icc lower upper))
    (hp : ∀ x ∈ Icc lower upper, 0 < f x) :
    (∀ x, 0 ≤ S.indicator f x) ∧ Measurable (S.indicator f) ∧
      Integrable (S.indicator f) := by
  classical
  have hs := hS.isOpen.measurableSet
  have hsub : S ⊆ Icc lower upper := subset_closure.trans hbox
  refine ⟨?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ S
    · simpa only [indicator_of_mem hx] using (hp x (hsub hx)).le
    · simp only [indicator_of_notMem hx, le_refl]
  · change Measurable (S.piecewise f (fun _ => 0))
    exact (hf.mono hsub).measurable_piecewise continuousOn_const hs
  · exact (hf.integrableOn_Icc.mono_set hsub).integrable_indicator hs

/-- The exact published analytic hypothesis required by both manuscripts. -/
theorem finiteBoxPrekopaLeindler (q : ℕ) : FiniteBoxPrekopaLeindler q := by
  intro t ht ht1 lower upper S₀ S₁ S₂ f₀ f₁ f₂ hS₀ hS₁ hS₂
    hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hp₀ hp₁ hp₂ hcover hle
  obtain ⟨h₀,hm₀,hi₀⟩ := box_indicator hS₀ hb₀ hc₀ hp₀
  obtain ⟨h₁,hm₁,hi₁⟩ := box_indicator hS₁ hb₁ hc₁ hp₁
  obtain ⟨h₂,hm₂,hi₂⟩ := box_indicator hS₂ hb₂ hc₂ hp₂
  have ht' : 0 < 1-t := sub_pos.mpr ht1
  have ht1' : 1-t < 1 := by linarith
  have H := integral_interpolation h₁ h₂ h₀ hm₁ hm₂ hm₀ hi₁ hi₂ hi₀ ht' ht1'
    (fun x y => by
      rw [show 1-(1-t)=t by ring]
      by_cases hx : x ∈ S₁
      · by_cases hy : y ∈ S₂
        · have hz : (1-t) • x+t • y ∈ S₀ := hcover ⟨x,hx,y,hy,rfl⟩
          simpa only [indicator_of_mem hx,indicator_of_mem hy,indicator_of_mem hz]
            using hle x hx y hy
        · rw [indicator_of_notMem hy,Real.zero_rpow (ne_of_gt ht),mul_zero]
          exact h₀ _
      · rw [indicator_of_notMem hx,Real.zero_rpow (ne_of_gt ht'),zero_mul]
        exact h₀ _)
  simpa only [integral_indicator hS₀.isOpen.measurableSet,
    integral_indicator hS₁.isOpen.measurableSet,integral_indicator hS₂.isOpen.measurableSet,
    sub_sub_cancel] using H

end
end ContingencyTables.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_FiniteCheegerProof
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the finite-chain Cheeger input by coarea and a weighted median -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

private lemma split_square (u : ℝ) : (max u 0)^2+(max (-u) 0)^2 = u^2 := by
  by_cases hu : 0 ≤ u
  · rw [max_eq_left hu,max_eq_right (neg_nonpos.mpr hu)]
    ring
  · rw [max_eq_right (le_of_not_ge hu),max_eq_left (by linarith)]
    ring

private lemma split_difference (u v : ℝ) :
    (max u 0-max v 0)^2+(max (-u) 0-max (-v) 0)^2 ≤ (u-v)^2 := by
  by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v
  · rw [max_eq_left hu,max_eq_left hv,max_eq_right (neg_nonpos.mpr hu),
      max_eq_right (neg_nonpos.mpr hv)]
    simp
  · have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_left hu,max_eq_right hv',max_eq_right (neg_nonpos.mpr hu),
      max_eq_left (neg_nonneg.mpr hv')]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hu hv']
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [max_eq_right hu',max_eq_left hv,max_eq_left (neg_nonneg.mpr hu'),
      max_eq_right (neg_nonpos.mpr hv)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hu' hv]
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_right hu',max_eq_right hv',max_eq_left (neg_nonneg.mpr hu'),
      max_eq_left (neg_nonneg.mpr hv')]
    nlinarith

variable {X : Type*} [Fintype X]

/-- Levin–Peres Theorem 13.10 lower bound, in the exact finite Poincaré form used here. -/
theorem finiteCheeger : PublishedInputs.FiniteCheeger X := by
  intro C κ hk hcut f
  obtain ⟨a,hbelow,habove⟩ := exists_median C f
  let p : X → ℝ := fun x => max (f x-a) 0
  let n : X → ℝ := fun x => max (a-f x) 0
  have hp : mass C (Finset.univ.filter fun x => 0 < p x) ≤ 1/2 := by
    simpa only [p,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using habove
  have hn : mass C (Finset.univ.filter fun x => 0 < n x) ≤ 1/2 := by
    simpa only [n,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using hbelow
  have hcut' : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S := hcut
  have hpe := positive_energy C κ hk hcut' p (fun _ => le_max_right _ _) hp
  have hne := positive_energy C κ hk hcut' n (fun _ => le_max_right _ _) hn
  have hnorm : (∑ x, C.π x*(p x)^2)+(∑ x, C.π x*(n x)^2) =
      ∑ x, C.π x*(f x-a)^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [p,n]
    rw [← mul_add,show a-f x = -(f x-a) by ring,split_square]
  have he : C.energy p+C.energy n ≤ C.energy f := by
    rw [C.energy_eq,C.energy_eq,C.energy_eq,← add_div,
      ← Finset.sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (C.positive x).le (C.nonnegative x y))
    dsimp [p,n]
    convert split_difference (f x-a) (f y-a) using 1
    all_goals first | rfl | ring | (congr 2; ring_nf) | (simp only [neg_sub])
  have hv := mul_le_mul_of_nonneg_left (variance_le_centered C f a) (sq_nonneg κ)
  have hb : κ^2*C.variance f ≤ 2*C.energy f := by
    rw [← hnorm] at hv
    nlinarith [hpe,hne,he]
  have hk2 : 0 < κ^2 := sq_pos_of_pos hk
  calc
    C.variance f ≤ (2*C.energy f)/κ^2 := (le_div_iff₀ hk2).mpr (by nlinarith [hb])
    _ = (2/κ^2)*C.energy f := by ring

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EdmondsKarpDistance
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded shortest-path labels for Edmonds--Karp

An unreachable vertex has label n. Reachable vertices have their actual
shortest distance, at most n-1. These labels are obtained from the already
proved breadth-first search, independently of its deterministic tie rule.
-/
namespace ContingencyTables.EdmondsKarpDistance
open FiniteDirectedBFS PublishedEdmondsKarp
open scoped Classical
noncomputable section
variable {n : ℕ}

lemma distance_of_some {E : Fin n→Fin n→Bool} {s v : Fin n} {xs : List (Fin n)}
    (h : paths E s n v=some xs) : distance E s v=xs.length-1 := by
  simp only [distance,h,Option.map_some,Option.getD_some]

lemma distance_of_none {E : Fin n→Fin n→Bool} {s v : Fin n}
    (h : paths E s n v=none) : distance E s v=n := by
  simp only [distance,h,Option.map_none,Option.getD_none]

lemma distance_le (E : Fin n→Fin n→Bool) (s v : Fin n) : distance E s v ≤ n := by
  cases h : paths E s n v with
  | none => exact (distance_of_none h).le
  | some xs =>
    rw [distance_of_some h]
    have hl := paths_length_le h
    omega

lemma distance_source (E : Fin n→Fin n→Bool) (s : Fin n) : distance E s s=0 := by
  obtain ⟨xs,hxs⟩ := source_found E s
  rw [distance_of_some hxs]
  have hshort := paths_shortest hxs [s] Route.start
  simp only [List.length_singleton] at hshort
  omega

lemma distance_route {E : Fin n→Fin n→Bool} {s v : Fin n} {xs : List (Fin n)}
    (h : Route E s v xs) : distance E s v ≤ xs.length-1 := by
  obtain ⟨ys,hys⟩ := route_found h
  rw [distance_of_some hys]
  exact Nat.sub_le_sub_right (paths_shortest hys xs h) 1

lemma distance_edge {E : Fin n→Fin n→Bool} {s u v : Fin n}
    (he : E u v=true) : distance E s v ≤ distance E s u+1 := by
  cases h : paths E s n u with
  | none =>
    rw [distance_of_none h]
    exact (distance_le E s v).trans (Nat.le_succ n)
  | some xs =>
    have hr := (paths_sound h).1
    have hv := distance_route (hr.extend he)
    rw [distance_of_some h]
    simp only [List.length_append,List.length_singleton] at hv
    have hp := hr.length_pos
    omega

lemma route_potential {E : Fin n→Fin n→Bool} {s v : Fin n} {xs : List (Fin n)}
    (d : Fin n→ℕ) (hzero : d s=0)
    (hedge : ∀ u v,E u v=true → d v ≤ d u+1)
    (h : Route E s v xs) : d v ≤ xs.length-1 := by
  induction h with
  | start => simp only [hzero,List.length_singleton,Nat.sub_self,le_refl]
  | @extend u v xs hr huv ih =>
    have he := hedge u v huv
    have hp := hr.length_pos
    simp only [List.length_append,List.length_singleton]
    omega

/-- Every bounded potential increasing by at most one on each edge lies
below the shortest-path labels. This also covers unreachable vertices. -/
lemma potential_le_distance (E : Fin n→Fin n→Bool) (s : Fin n) (d : Fin n→ℕ)
    (hzero : d s=0) (hbound : ∀ v,d v ≤ n)
    (hedge : ∀ u v,E u v=true → d v ≤ d u+1) (v : Fin n) :
    d v ≤ distance E s v := by
  cases h : paths E s n v with
  | none => simpa only [distance_of_none h] using hbound v
  | some xs =>
    rw [distance_of_some h]
    exact route_potential d hzero hedge (paths_sound h).1

/-- A unit-Lipschitz sequence attaining its maximal endpoint slope has
unit slope at every intermediate index. -/
lemma tight_sequence {k : ℕ} (d : Fin (k+1)→ℕ) (hzero : d 0=0)
    (hlast : d (Fin.last k)=k)
    (hstep : ∀ i : Fin k,d i.succ ≤ d i.castSucc+1) :
    ∀ i : Fin (k+1),d i=i.val := by
  have hu : ∀ i : Fin (k+1),d i ≤ i.val := by
    intro i
    refine Fin.induction ?_ (fun j ih => ?_) i
    · simpa only [Fin.val_zero,hzero] using (Nat.le_refl 0)
    · have hs := hstep j
      simp only [Fin.val_succ,Fin.val_castSucc] at *
      omega
  have hl : ∀ i : Fin (k+1),k ≤ d i+(k-i.val) := by
    intro i
    refine Fin.reverseInduction ?_ (fun j ih => ?_) i
    · simp only [Fin.val_last,hlast,Nat.sub_self,Nat.add_zero,le_refl]
    · have hs := hstep j
      have hj := j.isLt
      simp only [Fin.val_succ,Fin.val_castSucc] at *
      omega
  intro i
  have hupper := hu i
  have hlower := hl i
  have hi := i.isLt
  omega

lemma label_le (c : Capacity n) (f : Flow n) (s v : Fin n) : label c f s v ≤ n :=
  distance_le _ _ _

lemma label_source (c : Capacity n) (f : Flow n) (s : Fin n) : label c f s s=0 :=
  distance_source _ _

lemma label_edge {c : Capacity n} {f : Flow n} {s u v : Fin n}
    (h : 0 < (c u v:ℤ)-f u v) : label c f s v ≤ label c f s u+1 :=
  distance_edge (by simpa only [ResidualSearch.edge,decide_eq_true_eq] using h)

lemma label_target {c : Capacity n} {f : Flow n} {s t : Fin n} {k : ℕ}
    {p : Fin (k+1)→Fin n} (hp : ResidualPath c f s t k p)
    (hshort : ∀ l q,ResidualPath c f s t l q → k ≤ l) : label c f s t=k := by
  have hr := ResidualSearch.route_of_residual c f s t k p hp
  obtain ⟨xs,hxs⟩ := route_found hr
  obtain ⟨l,q,hq,hres,_⟩ := ResidualSearch.search_shortest c f s t xs hxs
  have hkl := hshort l q hres
  have hlen : xs.length=l+1 := by rw [hq,List.length_ofFn]
  have hshorter := paths_shortest hxs (List.ofFn p) hr
  simp only [List.length_ofFn] at hshorter
  change distance (ResidualSearch.edge c f) s t=k
  rw [distance_of_some hxs]
  omega

/-- Every vertex of a shortest residual augmenting path has its path
index as shortest distance from the source. -/
theorem label_path {c : Capacity n} {f : Flow n} {s t : Fin n} {k : ℕ}
    {p : Fin (k+1)→Fin n} (hp : ResidualPath c f s t k p)
    (hshort : ∀ l q,ResidualPath c f s t l q → k ≤ l) (i : Fin (k+1)) :
    label c f s (p i)=i.val := by
  apply tight_sequence (fun j => label c f s (p j))
  · rw [hp.1,label_source]
  · rw [hp.2.1]
    exact label_target hp hshort
  · intro j
    exact label_edge (hp.2.2.2 j)

lemma label_path_lt {c : Capacity n} {f : Flow n} {s t : Fin n} {k : ℕ}
    {p : Fin (k+1)→Fin n} (hp : ResidualPath c f s t k p)
    (hshort : ∀ l q,ResidualPath c f s t l q → k ≤ l) (i : Fin (k+1)) :
    label c f s (p i) < n := by
  rw [label_path hp hshort]
  have hcard := Fintype.card_le_of_injective p hp.2.2.1
  simp only [Fintype.card_fin] at hcard
  have hi := i.isLt
  omega

end
end ContingencyTables.EdmondsKarpDistance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EdmondsKarpAugmentation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Label monotonicity and critical arcs of a shortest augmentation -/
namespace ContingencyTables.EdmondsKarpAugmentation
open PublishedEdmondsKarp PathAugmentation EdmondsKarpDistance
open scoped Classical
noncomputable section
variable {n k : ℕ}

lemma reverse_count_zero (p : Fin (k+1)→Fin n) (hp : Function.Injective p) (i : Fin k) :
    arcCount p (p i.succ) (p i.castSucc)=0 := by
  apply arcCount_eq_zero
  rintro ⟨j,hj,hi⟩
  have h1 := congrArg Fin.val (hp hj)
  have h2 := congrArg Fin.val (hp hi)
  simp only [Fin.val_castSucc,Fin.val_succ] at h1 h2
  omega

lemma update_decrease (f : Flow n) (p : Fin (k+1)→Fin n) (a : ℤ) (ha : 0 ≤ a)
    (u v : Fin n) (h : update f p a u v < f u v) :
    ∃ i : Fin k,p i.castSucc=v ∧ p i.succ=u := by
  by_contra hn
  have hz : arcCount p v u=0 := arcCount_eq_zero p v u hn
  have hc := arcCount_nonneg p u v
  have hprod := mul_nonneg ha hc
  simp only [update,hz,sub_zero] at h
  omega

lemma update_new_edge (c : Capacity n) (f : Flow n) (p : Fin (k+1)→Fin n)
    (a : ℤ) (ha : 0 ≤ a) (u v : Fin n)
    (h : 0 < (c u v:ℤ)-update f p a u v) :
    0 < (c u v:ℤ)-f u v ∨ ∃ i : Fin k,p i.castSucc=v ∧ p i.succ=u := by
  by_cases hold : 0 < (c u v:ℤ)-f u v
  · exact Or.inl hold
  · exact Or.inr (update_decrease f p a ha u v (by omega))

lemma update_saturates (c : Capacity n) (f : Flow n) (p : Fin (k+1)→Fin n)
    (hp : Function.Injective p) (a : ℤ) (i : Fin k)
    (ha : a=(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) :
    update f p a (p i.castSucc) (p i.succ)=c (p i.castSucc) (p i.succ) := by
  rw [update,arcCount_eq_one p hp i,reverse_count_zero p hp i]
  omega

/-- All old distance labels remain valid lower potentials for the new
residual graph, including arcs created by cancellation of flow. -/
theorem labels_monotone {c : Capacity n} {s t : Fin n} {f g : Flow n}
    (h : ShortestAugmentation c s t f g) (v : Fin n) : label c f s v ≤ label c g s v := by
  obtain ⟨k,p,a,hp,hshort,ha,_,_,hg⟩ := h
  have he : g=update f p a := funext (fun u => funext (hg u))
  apply potential_le_distance (ResidualSearch.edge c g) s (label c f s)
    (label_source c f s) (label_le c f s)
  intro u v huv
  have hres : 0 < (c u v:ℤ)-g u v := of_decide_eq_true huv
  rw [he] at hres
  rcases update_new_edge c f p a ha.le u v hres with hold|⟨i,hi,hj⟩
  · exact label_edge hold
  · have h1 := label_path hp hshort i.castSucc
    have h2 := label_path hp hshort i.succ
    rw [hi] at h1
    rw [hj] at h2
    simp only [Fin.val_castSucc,Fin.val_succ] at h1 h2
    omega

/-- A decrease of flow on (u,v) means the augmentation used (v,u).
Consequently u was one distance layer beyond v. -/
theorem decrease_labels {c : Capacity n} {s t : Fin n} {f g : Flow n}
    (h : ShortestAugmentation c s t f g) (u v : Fin n) (hdec : g u v < f u v) :
    label c f s u=label c f s v+1 := by
  obtain ⟨k,p,a,hp,hshort,ha,_,_,hg⟩ := h
  have he : g=update f p a := funext (fun u => funext (hg u))
  rw [he] at hdec
  obtain ⟨i,hi,hj⟩ := update_decrease f p a ha.le u v hdec
  have h1 := label_path hp hshort i.castSucc
  have h2 := label_path hp hshort i.succ
  rw [hi] at h1
  rw [hj] at h2
  simp only [Fin.val_castSucc,Fin.val_succ] at h1 h2
  omega

/-- Each augmentation has an arc which was residual, becomes saturated,
and points from one finite distance layer to the next. -/
theorem critical_arc {c : Capacity n} {s t : Fin n} {f g : Flow n}
    (h : ShortestAugmentation c s t f g) :
    ∃ u v : Fin n,f u v < (c u v:ℤ) ∧ g u v=(c u v:ℤ) ∧
      label c f s v=label c f s u+1 ∧ label c f s u < n := by
  obtain ⟨k,p,a,hp,hshort,ha,_,⟨i,hsat⟩,hg⟩ := h
  have he : g=update f p a := funext (fun u => funext (hg u))
  refine ⟨p i.castSucc,p i.succ,?_,?_,?_,?_⟩
  · have hr := hp.2.2.2 i
    omega
  · rw [he]
    exact update_saturates c f p hp.2.2.1 a i hsat
  · rw [label_path hp hshort i.castSucc,label_path hp hshort i.succ]
    rfl
  · exact label_path_lt hp hshort i.castSucc

end
end ContingencyTables.EdmondsKarpAugmentation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EdmondsKarpTrace
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated critical arcs strictly increase their distance label -/
namespace ContingencyTables.EdmondsKarpTrace
open PublishedEdmondsKarp EdmondsKarpDistance EdmondsKarpAugmentation
open scoped Classical
noncomputable section
variable {n K : ℕ}

lemma descent_between (a : Fin (K+1)→ℤ) (i j : Fin (K+1)) (hij : i ≤ j)
    (h : a j < a i) :
    ∃ k : Fin K,i ≤ k.castSucc ∧ k.succ ≤ j ∧ a k.succ < a k.castSucc := by
  by_contra hn
  have hstep (k : Fin K) (hik : i ≤ k.castSucc) (hkj : k.succ ≤ j) :
      a k.castSucc ≤ a k.succ :=
    le_of_not_gt (fun hlt => hn ⟨k,hik,hkj,hlt⟩)
  have hm : ∀ u : Fin (K+1),i ≤ u → u ≤ j → a i ≤ a u := by
    intro u
    refine Fin.induction ?_ (fun k ih => ?_) u
    · intro hi _
      change i.val ≤ 0 at hi
      have he : i=0 := by
        apply Fin.ext
        simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hi
      subst i
      exact le_rfl
    · intro hi hj'
      by_cases hik : i ≤ k.castSucc
      · exact (ih hik ((Fin.castSucc_le_succ k).trans hj')).trans (hstep k hik hj')
      · have he : i=k.succ := Fin.ext (by
          change i.val ≤ k.val+1 at hi
          change ¬i.val ≤ k.val at hik
          change i.val=k.val+1
          omega)
        rw [he]
  exact (not_le_of_gt h) (hm j hij le_rfl)

lemma labels_monotone {c : Capacity n} {s t : Fin n} {F : Fin (K+1)→Flow n}
    (h : ∀ i : Fin K,ShortestAugmentation c s t (F i.castSucc) (F i.succ)) (v : Fin n) :
    Monotone (fun i => label c (F i) s v) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  exact EdmondsKarpAugmentation.labels_monotone (h i) v

/-- Once (u,v) is saturated, using it again requires a reverse
augmentation and hence at least two more source-distance layers at u. -/
theorem repeated_critical {c : Capacity n} {s t : Fin n} {F : Fin (K+1)→Flow n}
    (h : ∀ i : Fin K,ShortestAugmentation c s t (F i.castSucc) (F i.succ))
    (i j : Fin K) (hij : i < j) (u v : Fin n)
    (hsat : F i.succ u v=(c u v:ℤ))
    (hlevel : label c (F i.castSucc) s v=label c (F i.castSucc) s u+1)
    (hres : F j.castSucc u v < (c u v:ℤ)) :
    label c (F i.castSucc) s u+2 ≤ label c (F j.castSucc) s u := by
  have hisj : i.succ ≤ j.castSucc := by
    change i.val+1 ≤ j.val
    exact hij
  obtain ⟨k,hik,hkj,hdec⟩ := descent_between (fun q => F q u v) i.succ j.castSucc hisj
    (by rw [hsat]; exact hres)
  have hreverse := decrease_labels (h k) u v hdec
  have hfirst := labels_monotone h v ((Fin.castSucc_le_succ i).trans hik)
  have hlast := labels_monotone h u ((Fin.castSucc_le_succ k).trans hkj)
  dsimp only at hfirst hlast
  omega

end
end ContingencyTables.EdmondsKarpTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EdmondsKarpBound
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The shortest-augmentation bound

Charge an augmentation to a critical directed arc and its previous tail
label. A repeated directed arc has strictly larger label, so the charge
is injective into n×n×n.
-/
namespace ContingencyTables.EdmondsKarpBound
open PublishedEdmondsKarp EdmondsKarpDistance EdmondsKarpAugmentation EdmondsKarpTrace
open scoped Classical
noncomputable section
variable {n K : ℕ}

theorem shortest_trace_bound (c : Capacity n) (s t : Fin n) (F : Fin (K+1)→Flow n)
    (h : ∀ i : Fin K,ShortestAugmentation c s t (F i.castSucc) (F i.succ)) : K ≤ n^3 := by
  choose u v hu using (fun i : Fin K => critical_arc (h i))
  let code : Fin K→Fin n×Fin n×Fin n := fun i =>
    (u i,v i,⟨label c (F i.castSucc) s (u i),(hu i).2.2.2⟩)
  have hordered (i j : Fin K) (hij : i < j) (huv : u i=u j) (hvv : v i=v j) :
      label c (F i.castSucc) s (u i) < label c (F j.castSucc) s (u j) := by
    have hres : F j.castSucc (u i) (v i) < (c (u i) (v i):ℤ) := by
      simpa only [huv,hvv] using (hu j).1
    have hr := repeated_critical h i j hij (u i) (v i) (hu i).2.1 (hu i).2.2.1 hres
    rw [←huv]
    omega
  have hinj : Function.Injective code := by
    intro i j he
    have huij := congrArg Prod.fst he
    have hvij := congrArg (fun p : Fin n×Fin n×Fin n => p.2.1) he
    have hdij := congrArg (fun p : Fin n×Fin n×Fin n => p.2.2.val) he
    dsimp only [code] at huij hvij hdij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij|hji
    · exact (ne_of_lt (hordered i j hij huij hvij)) hdij
    · exact (ne_of_lt (hordered j i hji huij.symm hvij.symm)) hdij.symm
  have hc := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_fin,Fintype.card_prod,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hc

/-- Edmonds and Karp (1972), Theorem 1, in the exact integral-skew-flow
specialization for the sampling and counting algorithms. -/
theorem edmondsKarp1972Theorem1 : EdmondsKarp1972Theorem1 := by
  intro n c _ s t _ K F hF
  exact shortest_trace_bound c s t F hF.2.2

end
end ContingencyTables.EdmondsKarpBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_UnconditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampling and counting contingency tables with arbitrary margins

The finite-box Prékopa–Leindler inequality, finite Cheeger inequality
and Edmonds–Karp bound yield sampling and counting algorithms with
uniform polynomial bit-cost guarantees.
-/
namespace ContingencyTables

/-- Paper 200-02: the cell-bounded counting FPRAS with a public fair-bit machine. -/
theorem counting_oai : Algorithms.CountingStatement :=
  CountingExecutedMachine.counting_conditional EdmondsKarpBound.edmondsKarp1972Theorem1
    PublishedInputs.finiteBoxPrekopaLeindler (fun _ _ => CheegerProof.finiteCheeger)

end ContingencyTables

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.counting_oai := @OAI.ContingencyTables.counting_oai

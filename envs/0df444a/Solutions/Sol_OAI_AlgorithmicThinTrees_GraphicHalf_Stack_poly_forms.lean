-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_forms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:33.803491+00:00
-- url     : https://prove2.me/submissions/08c8c110-9587-4b49-a5a9-787e9073e07d

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT014

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_NaturalPolynomial
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23

namespace NaturalPolynomial

theorem eval_mono (p : NaturalPolynomial) : Monotone p.eval := by
  intro x y hxy
  induction p with
  | constant c => exact le_rfl
  | «variable» => exact hxy
  | add p q hp hq => exact Nat.add_le_add hp hq
  | mul p q hp hq => exact Nat.mul_le_mul hp hq
  | power p k hp => exact Nat.pow_le_pow_left hp k

end NaturalPolynomial
end KS.W23

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoutineLength
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.RoutineLength
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

lemma action_length (a : KS.W29.StackAction) (w : List Bool) :
    (a.apply w).length≤w.length+1 := by
  cases a <;> simp [KS.W29.StackAction.apply]; omega

lemma step_length (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (b : Bool)
    (j : Fin M.stackCount) : ((M.step s b).«stacks» j).length ≤ (s.«stacks» j).length+1 := by
  rcases s with ⟨control,tapes⟩
  cases control with
  | none => simp [KS.W01.FixedStack.Machine.step]
  | some c => exact action_length _ _

lemma run_length (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (bits : List Bool)
    (j : Fin M.stackCount) : ((M.run s bits).«stacks» j).length ≤ (s.«stacks» j).length+bits.length := by
  induction bits generalizing s with
  | nil => simp [KS.W01.FixedStack.Machine.run]
  | cons b bs ih =>
    have h := ih (M.step s b)
    have hs := step_length M s b j
    simp only [KS.W01.FixedStack.Machine.run,List.length_cons]
    omega

lemma output_length {k : ℕ} {P : Program k} {before after : Fin k → List Bool} {ticks : ℕ}
    (h : RunSpec P before after ticks) (j : Fin k) :
    (after j).length≤(before j).length+ticks := by
  have hr := run_length P.toMachine ⟨some P.initial,before⟩ (List.replicate ticks false) j
  rw [h _ (List.length_replicate ..)] at hr
  simpa using hr

end CurrentKS.RoutineLength

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word} {ed : δ → Word}
  {f : α → β} {g : β → γ}

lemma Realizes.output_length (r : Realizes ea eb f) (x : α) :
    (eb (f x)).length≤(ea x).length+r.cost x := by
  have h := RoutineLength.output_length (r.routine.spec x) 0
  simpa only [io_zero] using h

lemma prodCode_length (p : α×β) : (prodCode ea eb p).length=2*(ea p.1).length+1+(eb p.2).length := by
  simp only [prodCode,PairRoutine.pair,List.length_append,KS.W01.length_frame]
lemma le_prodCode_left (p : α×β) : (ea p.1).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega
lemma le_prodCode_right (p : α×β) : (eb p.2).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega

instance poly_first (ea : α → Word) (eb : β → Word) : PolyTime (first ea eb) := by
  refine ⟨⟨6*X+5,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  have h2 := le_prodCode_right (ea:=ea) (eb:=eb) p
  change 5*(ea p.1).length+(eb p.2).length+5≤6*(prodCode ea eb p).length+5
  omega
instance poly_second (ea : α → Word) (eb : β → Word) : PolyTime (second ea eb) := by
  refine ⟨⟨4*X+3,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  change 4*(ea p.1).length+3≤4*(prodCode ea eb p).length+3
  omega
instance poly_then (r : Realizes ea eb f) (s : Realizes eb ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.then s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q.comp (X+p),?_⟩⟩
  intro x
  have hl := r.output_length x
  have hs := (hq (f x)).trans (q.eval_mono (hl.trans (Nat.add_le_add_left (hp x) _)))
  have hh := Nat.add_le_add (hp x) hs
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_comp,NaturalPolynomial.eval_variable]
  exact hh
instance poly_both {g : α → γ} (r : Realizes ea eb f) (s : Realizes ea ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.both s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨16*X+13*p+q+15,?_⟩⟩
  intro x
  have hl := r.output_length x
  have h1 := hp x
  have h2 := hq x
  change PairRoutine.pairingTicks ea (fun x => eb (f x)) r.cost s.cost x≤
    16*(ea x).length+13*p.eval (ea x).length+q.eval (ea x).length+15
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ListRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ : Type*}

lemma fold_cons (xs ys : List α) : xs.foldl (fun acc x => x::acc) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLoops
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word}

lemma len_listCode (ea : α → Word) (xs : List α) :
    (listCode ea xs).length=(xs.map (fun x => 2*(ea x).length+1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length,List.map_cons,List.sum_cons,ih]
lemma sum_map_bound (xs : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x∈xs,f x≤B) :
    (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
lemma listCode_length_bound (xs : List α) (B : ℕ) (h : ∀ x∈xs,(ea x).length≤B) :
    (listCode ea xs).length≤xs.length*(2*B+1) := by
  rw [len_listCode]
  apply sum_map_bound
  intro x hx
  have := h x hx
  omega
lemma list_length_le_code (ea : α → Word) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length,List.length_cons];omega
lemma mem_length_le_code (xs : List α) {x : α} (hx : x∈xs) :
    (ea x).length≤(listCode ea xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rw [listCode_cons,prodCode_length]
      dsimp only
      rcases hx with rfl|hx
      · omega
      · have := ih hx;omega
lemma listCode_reverse_length (ea : α → Word) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  simp only [len_listCode,List.map_reverse,List.sum_reverse]

instance poly_map {f : α → β} (r : Realizes ea eb f) [PolyTime r] : PolyTime r.map := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let Q := X+p
  refine ⟨⟨2*X+X*(3*X+p+6*Q+8)+X*(2*Q+1)+4,?_⟩⟩
  intro xs
  let L := (listCode ea xs).length
  have hn : xs.length≤L := list_length_le_code ea xs
  have ho : ∀ x∈xs,(eb (f x)).length≤L+p.eval L := by
    intro x hx
    have hl : (ea x).length≤L := mem_length_le_code xs hx
    exact (r.output_length x).trans (Nat.add_le_add hl ((hp x).trans (p.eval_mono hl)))
  have hs := sum_map_bound xs (fun x => FramedMapRoutine.bodyTicks ea (fun x => eb (f x)) r.cost x+1)
    (3*L+p.eval L+6*(L+p.eval L)+8) (by
      intro x hx
      have hl : (ea x).length≤L := mem_length_le_code xs hx
      have hc := (hp x).trans (p.eval_mono hl)
      have hout := ho x hx
      simp only [FramedMapRoutine.bodyTicks,KS.W01.length_frame]
      omega)
  have ht := listCode_length_bound (ea:=fun x => eb (f x)) xs (L+p.eval L) ho
  have hs' := hs.trans (Nat.mul_le_mul_right _ hn)
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change FramedMapRoutine.ticks ea (fun x => eb (f x)) r.cost xs≤_
  simp only [FramedMapRoutine.ticks,FramedMapRoutine.scanTicks]
  change 2*L+2+((xs.map _).sum+1)+(listCode (fun x => eb (f x)) xs).length+1≤_
  change _≤2*L+L*(3*L+p.eval L+6*(L+p.eval L)+8)+L*(2*(L+p.eval L)+1)+4
  omega

lemma fold_scan_bound (F : α → β → α) (cost : α×β → ℕ) (s : α) (xs : List β) (S E C : ℕ)
    (hs : ∀ ys zs,xs=ys++zs → (ea (ys.foldl F s)).length≤S)
    (he : ∀ x∈xs,(eb x).length≤E)
    (hc : ∀ a x,(ea a).length≤S → (eb x).length≤E → cost (a,x)≤C) :
    FoldRoutine.scanTicks ea eb F cost s xs≤xs.length*(3*E+10*S+C+12)+1 := by
  induction xs generalizing s with
  | nil => simp [FoldRoutine.scanTicks]
  | cons x xs ih =>
      have h0 := hs [] (x::xs) rfl
      have h1 := hs [x] xs rfl
      have hx := he x (by simp)
      have hc0 := hc s x h0 hx
      have ht := ih (F s x) (by
        intro ys zs hz
        have h := hs (x::ys) zs (by simp only [List.cons_append];rw [hz])
        simpa only [List.foldl_cons] using h) (fun y hy => he y (by simp [hy]))
      simp only [FoldRoutine.scanTicks,FoldRoutine.bodyTicks,KS.W01.length_frame,List.length_cons,Nat.add_mul,Nat.one_mul]
      simp only [List.foldl_nil,List.foldl_cons] at h0 h1
      omega

instance poly_fold {f : α×β → α} (r : Realizes (prodCode ea eb) ea f) [PolyTime r] [FoldSize r] :
    PolyTime r.fold := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := FoldSize.bound (r:=r)
  refine ⟨⟨5*q+2*X+X*(3*X+10*q+p.comp (2*q+1+X)+12)+7,?_⟩⟩
  intro u
  let L := (prodCode ea (listCode eb) u).length
  let S := q.eval L
  have he : (listCode eb u.2).length≤L := le_prodCode_right u
  have hn := (list_length_le_code eb u.2).trans he
  have hs := hq u.1 u.2
  have h0 : (ea u.1).length≤S := hs [] u.2 rfl
  have hN : (ea (u.2.foldl (fun a b => f (a,b)) u.1)).length≤S := hs u.2 [] (by simp)
  have hc : ∀ a x,(ea a).length≤S → (eb x).length≤L → r.cost (a,x)≤p.eval (2*S+1+L) := by
    intro a x ha hx
    apply (hp (a,x)).trans (p.eval_mono ?_)
    rw [prodCode_length]
    dsimp only
    omega
  have hscan := fold_scan_bound (ea:=ea) (eb:=eb) (fun a b => f (a,b)) r.cost u.1 u.2 S L
    (p.eval (2*S+1+L)) hs (fun x hx => (mem_length_le_code u.2 hx).trans he) hc
  have hscan' := hscan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change FoldRoutine.ticks ea eb (fun a b => f (a,b)) r.cost u.1 u.2≤_
  simp only [FoldRoutine.ticks]
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change _≤5*S+2*L+L*(3*L+10*S+p.eval (2*S+1+L)+12)+7
  change _≤_ at hscan'
  change (FramedMapRoutine.tape eb u.2).length≤L at he
  omega

lemma iterate_ticks_bound {f : α → α} (r : Realizes ea ea f) (x : α) (n C : ℕ)
    (h : ∀ i,i<n → r.cost (f^[i] x)≤C) :
    IterateRoutine.loopTicks r.cost f n x≤n*(C+2)+1 := by
  induction n generalizing x with
  | zero => simp [IterateRoutine.loopTicks]
  | succ n ih =>
      have h0 := h 0 (by omega)
      have ht := ih (f x) (by
        intro i hi
        simpa only [←Function.iterate_succ_apply] using h (i+1) (by omega))
      simp only [Function.iterate_zero, id_eq] at h0
      simp only [IterateRoutine.loopTicks,Nat.add_mul,Nat.one_mul]
      omega
instance poly_iterate {f : α → α} (r : Realizes ea ea f) [PolyTime r] [IterateSize r] :
    PolyTime r.iterate := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := IterateSize.bound (r:=r)
  refine ⟨⟨3*X+X*(p.comp q+2)+3,?_⟩⟩
  intro u
  let L := (prodCode natCode ea u).length
  have hi : (ea u.2).length+u.1≤L := by simp only [L,prodCode_length,natCode,List.length_replicate];omega
  have hn : u.1≤L := by omega
  have ht := iterate_ticks_bound r u.2 u.1 (p.eval (q.eval L)) (by
    intro i hi'
    exact (hp _).trans (p.eval_mono ((hq u.2 i).trans (q.eval_mono (by omega)))))
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change 3*u.1+2+IterateRoutine.loopTicks r.cost f u.1 u.2≤3*L+L*(p.eval (q.eval L)+2)+3
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArrayRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α γ : Type*}

lemma fold_length (xs : List α) (n : ℕ) : xs.foldl (fun k _ => k+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLists
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma prefix_code_length (ea : α → Word) (xs ys zs : List α) (h : xs=ys++zs) :
    (listCode ea ys).length≤(listCode ea xs).length := by
  rw [h,listCode_append,List.length_append];omega
lemma prefix_length (xs ys zs : List α) (h : xs=ys++zs) : ys.length≤xs.length := by
  rw [h,List.length_append];omega

instance poly_appendList (ea : α → Word) : PolyTime (appendList ea) := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 (le_prodCode_left p)) 4
instance poly_reverseBody (ea : α → Word) : PolyTime (reverseBody ea) := by
  unfold reverseBody;infer_instance
instance size_reverseBody (ea : α → Word) : FoldSize (reverseBody ea) := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_cons,listCode_append,List.length_append,listCode_reverse_length]
  have hp := prefix_code_length ea xs ys zs h
  change _≤(prodCode (listCode ea) (listCode ea) (s,xs)).length
  rw [prodCode_length]
  try dsimp only
  omega
instance poly_reverseList (ea : α → Word) : PolyTime (reverseList ea) := by
  unfold reverseList;infer_instance

instance poly_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime (mapCtxBody ec ea eb r) := by
  dsimp only [mapCtxBody]
  apply poly_both
instance size_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    FoldSize (mapCtxBody ec ea eb r) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let U := 3*X+1+p.comp (3*X+1)
  refine ⟨⟨3*X+1+X*(2*U+1),?_⟩⟩
  intro s xs ys zs h
  rw [fold_mapCtx]
  let L := (prodCode (prodCode ec (listCode eb)) (listCode ea) (s,xs)).length
  have hc : (ec s.1).length≤L := (le_prodCode_left s).trans (le_prodCode_left (s,xs))
  have ha : (listCode eb s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have he : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have hn : ys.length≤L := (list_length_le_code ea ys).trans he
  have ho : ∀ x∈ys,(eb (f (s.1,x))).length≤3*L+1+p.eval (3*L+1) := by
    intro x hx
    have hl : (prodCode ec ea (s.1,x)).length≤3*L+1 := by
      have he' := (mem_length_le_code ys hx).trans he
      simp only [prodCode_length]
      try dsimp only
      omega
    exact (r.output_length (s.1,x)).trans (Nat.add_le_add hl ((hp _).trans (p.eval_mono hl)))
  have hm := listCode_length_bound (ea:=fun x => eb (f (s.1,x))) ys (3*L+1+p.eval (3*L+1)) ho
  have hm' := hm.trans (Nat.mul_le_mul_right _ hn)
  have heq : listCode eb (ys.map (fun x => f (s.1,x)))=listCode (fun x => eb (f (s.1,x))) ys := by
    simp only [listCode,FramedMapRoutine.tape,List.flatMap_map]
  rw [prodCode_length]
  dsimp only
  rw [listCode_append,List.length_append,listCode_reverse_length,heq]
  change 2*(ec s.1).length+1+((listCode (fun x => eb (f (s.1,x))) ys).length+(listCode eb s.2).length)≤_
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp,U]
  change _≤3*L+1+L*(2*(3*L+1+p.eval (3*L+1))+1)
  omega
instance poly_mapCtx {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime r.mapCtx := by
  unfold Realizes.mapCtx
  infer_instance

instance poly_natAdd : PolyTime natAdd := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  have h := le_prodCode_left (ea:=natCode) (eb:=natCode) p
  simp only [natCode,List.length_replicate] at h
  change 5*p.1+4≤5*(prodCode natCode natCode p).length+4
  omega

instance poly_rangeStep : PolyTime rangeStepRealizes := by dsimp only [rangeStepRealizes];apply poly_both
lemma range_iterate_size (s : ℕ×List ℕ) (k : ℕ) :
    (rangeStep^[k] s).1=s.1+k ∧
    (listCode natCode (rangeStep^[k] s).2).length≤(listCode natCode s.2).length+k*(2*(s.1+k)+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (rangeStep^[k] s).1+1=s.1+(k+1) ∧ _
      constructor
      · omega
      · change (listCode natCode ((rangeStep^[k] s).1::(rangeStep^[k] s).2)).length≤_
        rw [listCode_cons,prodCode_length]
        simp only [natCode,List.length_replicate]
        try dsimp only
        nlinarith [ih.2]
instance size_rangeStep : IterateSize rangeStepRealizes := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s k
  have h := range_iterate_size s k
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*(rangeStep^[k] s).1+1+(listCode natCode (rangeStep^[k] s).2).length≤10*(2*s.1+1+(listCode natCode s.2).length+k+1)^2
  rw [h.1]
  nlinarith [h.2]
instance poly_range : PolyTime range := by unfold range;infer_instance

instance poly_lengthBody (ea : α → Word) : PolyTime ((first natCode ea).then natSucc) := by infer_instance
instance size_lengthBody (ea : α → Word) : FoldSize ((first natCode ea).then natSucc) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  change (natCode (ys.foldl (fun k _ => k+1) s)).length≤_
  rw [fold_length]
  have hs := le_prodCode_left (ea:=natCode) (eb:=listCode ea) (s,xs)
  have hn := ((prefix_length xs ys zs h).trans (list_length_le_code ea xs)).trans (le_prodCode_right (ea:=natCode) (s,xs))
  simp only [natCode,List.length_replicate] at hs ⊢
  change s+ys.length≤2*(prodCode natCode (listCode ea) (s,xs)).length
  omega
instance poly_lengthList (ea : α → Word) : PolyTime (lengthList ea) := by unfold lengthList;infer_instance
instance poly_tabulate {f : γ×ℕ → α} (r : Realizes (prodCode ec natCode) ea f) [PolyTime r] :
    PolyTime r.tabulate := by unfold Realizes.tabulate;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialScalar
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

instance poly_ratOp (op : KS.W13.ExpressionMachine.BinaryOp) : PolyTime (ratOp op) := by
  refine ⟨⟨5*X+6000000*(X+1)^3+6,?_⟩⟩
  intro p
  have hl := RoutineLength.output_length (KS.W13.ExpressionMachine.binaryArithmetic_spec op p.1 p.2 [] []) 10
  have ht : (ratCode (op.eval p.1 p.2)).length≤KS.W13.ExpressionMachine.binaryBudget p.1 p.2 := by simpa [KS.W13.ExpressionMachine.registers] using hl
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 3
  have ha := le_prodCode_left (ea:=ratCode) (eb:=ratCode) p
  change ArithmeticRoutine.ticks op p.1 p.2≤5*(prodCode ratCode ratCode p).length+6000000*((prodCode ratCode ratCode p).length+1)^3+6
  simp only [ArithmeticRoutine.ticks,ArithmeticRoutine.encode,KS.W13.ExpressionMachine.binaryBudget,KS.W01.ratLength] at ht ⊢
  simp only [ratCode] at *
  omega

instance poly_ratLE : PolyTime ratLE := by
  refine ⟨⟨5*X+2048*(X+1)^2+8,?_⟩⟩
  intro p
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2
  have ha := le_prodCode_left (ea:=ratCode) (eb:=ratCode) p
  change CompareRoutine.ticks p.1 p.2≤5*(prodCode ratCode ratCode p).length+2048*((prodCode ratCode ratCode p).length+1)^2+8
  simp only [CompareRoutine.ticks,CompareRoutine.encode,KS.W29.polynomialFuel,List.length_append]
  simp only [ratCode] at *
  omega

instance poly_ratFloor : PolyTime ratFloor := by
  refine ⟨⟨192*(X+1)^2+2,?_⟩⟩
  intro q
  have hl := RoutineLength.output_length (KS.W20.FloorRationalMachine.polynomial_spec q) 5
  have ht : (ratCode (⌊q⌋ : ℚ)).length≤64*((ratCode q).length+1)^2 := by
    simpa [KS.W20.FloorRationalMachine.state,KS.W19.SignedFloorMachine.«stacks»,KS.W29.polynomialFuel] using hl
  change FloorCleanRoutine.ticks q≤192*((ratCode q).length+1)^2+2
  simp only [FloorCleanRoutine.ticks,KS.W29.polynomialFuel,FloorCleanRoutine.encode]
  simp only [ratCode] at *
  omega

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_conditional {f g : α → β} (r : Realizes ea eb f) (s : Realizes ea eb g)
    [PolyTime r] [PolyTime s] : PolyTime (conditional r s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q+6,?_⟩⟩
  intro x
  have hr := (hp x.2).trans (p.eval_mono (le_prodCode_right (ea:=boolCode) (eb:=ea) x))
  have hs := (hq x.2).trans (q.eval_mono (le_prodCode_right (ea:=boolCode) (eb:=ea) x))
  change 5+(if x.1 then r.cost x.2 else s.cost x.2)+1≤p.eval _+q.eval _+6
  split <;> omega
instance poly_ite {p : α → Bool} {f g : α → β} (b : Realizes ea boolCode p)
    (r : Realizes ea eb f) (s : Realizes ea eb g) [PolyTime b] [PolyTime r] [PolyTime s] : PolyTime (b.ite r s) := by unfold Realizes.ite; exact poly_then (b.both (identity ea)) (conditional r s)
instance poly_add {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.add s) := by unfold Realizes.add; exact poly_then (r.both s) (ratOp .add)
instance poly_sub {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.sub s) := by unfold Realizes.sub; exact poly_then (r.both s) (ratOp .sub)
instance poly_mul {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.mul s) := by unfold Realizes.mul; exact poly_then (r.both s) (ratOp .mul)
instance poly_div {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.div s) := by unfold Realizes.div; exact poly_then (r.both s) (ratOp .div)
instance poly_le {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.le s) := by unfold Realizes.le;infer_instance
instance poly_neg {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.neg := by unfold Realizes.neg;infer_instance
instance poly_abs {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.abs := by unfold Realizes.abs;infer_instance
instance poly_roundScalar : PolyTime roundScalar := by unfold roundScalar;infer_instance
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialArrays
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma fold_add_eq (xs : List ℚ) (q : ℚ) : xs.foldl (fun a b => a+b) q=q+xs.sum := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih => simp [ih,add_assoc]
lemma rat_sum_lengths_le (xs : List ℚ) :
    (xs.map KS.W01.ratLength).sum+xs.length≤(listCode ratCode xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,listCode_cons,prodCode_length]
      change KS.W01.ratLength x+_+_≤2*KS.W01.ratLength x+1+_
      omega
instance size_ratAdd : FoldSize (ratOp .add) := by
  refine ⟨⟨40*X+40,?_⟩⟩
  intro s xs ys zs h
  change (ratCode (ys.foldl (fun a b => a+b) s)).length≤_
  rw [fold_add_eq]
  have h1 := KS.W01.ratLength_sum_le ys
  have h2 := KS.W01.ratLength_add_le s ys.sum
  have hs := le_prodCode_left (ea:=ratCode) (eb:=listCode ratCode) (s,xs)
  have hy := (rat_sum_lengths_le ys).trans ((prefix_code_length ratCode xs ys zs h).trans
    (le_prodCode_right (ea:=ratCode) (s,xs)))
  change KS.W01.ratLength s≤_ at hs
  change KS.W01.ratLength (s+ys.sum)≤40*(prodCode ratCode (listCode ratCode) (s,xs)).length+40
  omega
instance poly_sumRationals : PolyTime sumRationals := by
  unfold sumRationals
  apply poly_congr
instance poly_l1Rationals : PolyTime l1Rationals := by unfold l1Rationals;apply poly_then

instance poly_lookupStep (ea : α → Word) : PolyTime (lookupStepRealizes ea) := by
  dsimp only [lookupStepRealizes]
  apply poly_congr
lemma lookup_fold_size (ea : α → Word) (s : ℕ×α) (xs : List α) (K B : ℕ)
    (hk : s.1≤K) (ha : (ea s.2).length≤B) (hx : ∀x∈xs,(ea x).length≤B) :
    (xs.foldl (fun s x => lookupStep (s,x)) s).1≤K ∧
    (ea (xs.foldl (fun s x => lookupStep (s,x)) s).2).length≤B := by
  induction xs generalizing s with
  | nil => exact ⟨hk,ha⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      · dsimp only [lookupStep]
        split_ifs <;> (try dsimp only) <;> omega
      · dsimp only [lookupStep]
        split_ifs <;> try dsimp only
        · exact ha
        · exact hx x (by simp)
        · exact ha
      · intro y hy;exact hx y (by simp [hy])
instance size_lookupStep (ea : α → Word) : FoldSize (lookupStepRealizes ea) := by
  refine ⟨⟨3*X+1,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode natCode ea) (listCode ea) (s,xs)).length
  have hk : s.1≤L := by
    have hl := (le_prodCode_left (ea:=natCode) (eb:=ea) s).trans (le_prodCode_left (eb:=listCode ea) (s,xs))
    simpa only [natCode,List.length_replicate] using hl
  have ha : (ea s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have ht := lookup_fold_size ea s ys L L hk ha (fun x hx => (mem_length_le_code ys hx).trans hy)
  change (prodCode natCode ea _).length≤3*L+1
  rw [prodCode_length]
  simp only [natCode,List.length_replicate]
  omega
instance poly_getD (ea : α → Word) (a : α) : PolyTime (getD ea a) := by unfold getD;infer_instance

instance poly_zipWith {f : α×β → γ} (r : Realizes (prodCode ea eb) ec f) (a : α) (b : β)
    [PolyTime r] : PolyTime (r.zipWith a b) := by unfold Realizes.zipWith;apply poly_then
instance poly_vectorAdd : PolyTime vectorAdd := by unfold vectorAdd;infer_instance
instance poly_vectorScaleBody : PolyTime vectorScaleBody := by unfold vectorScaleBody;exact poly_ratOp .mul
instance poly_vectorScale : PolyTime vectorScale := by unfold vectorScale;infer_instance
instance poly_matrixAdd : PolyTime matrixAdd := by unfold matrixAdd;infer_instance
instance poly_matrixScale : PolyTime matrixScale := by unfold matrixScale;infer_instance
instance poly_dot : PolyTime dot := by unfold dot;apply poly_then
instance poly_matVec : PolyTime matVec := by unfold matVec;apply poly_then
instance poly_quadratic : PolyTime quadratic := by unfold quadratic;apply poly_then

lemma ratLength_natCast (n : ℕ) : KS.W01.ratLength (n : ℚ)≤4*n+11 := by
  apply (KS.W01.ratLength_le_of_parts (n : ℚ) n n ?_ ?_).trans (by omega)
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n)))
  · simpa only [Rat.den_natCast] using (Nat.one_le_two_pow (n:=n))
instance size_ratSucc : IterateSize ((identity ratCode).add (constant ratCode ratCode 1)) := by
  refine ⟨⟨20*X+60,?_⟩⟩
  intro q n
  change (ratCode ((fun x : ℚ => x+1)^[n] q)).length≤_
  rw [iterate_ratSucc]
  have h := KS.W01.ratLength_add_le q (n : ℚ)
  have hn := ratLength_natCast n
  change KS.W01.ratLength (q+(n : ℚ))≤20*(KS.W01.ratLength q+n)+60
  omega
instance poly_natToRat : PolyTime natToRat := by unfold natToRat;infer_instance
instance size_natMulStep : IterateSize ((first natCode natCode).both natAdd) := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s n
  change (prodCode natCode natCode ((fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] s)).length≤_
  rcases s with ⟨k,z⟩
  rw [fold_natAdd]
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*k+1+(n*k+z)≤10*(2*k+1+z+n+1)^2
  nlinarith
instance poly_natMul : PolyTime natMul := by unfold natMul;infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratFloor _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {ι α β γ : Type*} {L f g : ι → ℕ}

lemma IsPoly.mono (hf : IsPoly L f) (h : ∀i,g i≤f i) : IsPoly L g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => (h i).trans (hp i)⟩
lemma IsPoly.add (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i+g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun i => Nat.add_le_add (hp i) (hq i)⟩
lemma IsPoly.mul (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i*g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun i => Nat.mul_le_mul (hp i) (hq i)⟩
lemma IsPoly.pow (hf : IsPoly L f) (k : ℕ) : IsPoly L (fun i => (f i)^k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k,fun i => Nat.pow_le_pow_left (hp i) k⟩
lemma isPoly_const (L : ι → ℕ) (c : ℕ) : IsPoly L (fun _ => c) := ⟨.constant c,fun _ => le_rfl⟩
lemma isPoly_self (L : ι → ℕ) : IsPoly L L := ⟨X,fun _ => le_rfl⟩
lemma IsPoly.eval (hf : IsPoly L f) (p : NaturalPolynomial) : IsPoly L (fun i => p.eval (f i)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,fun i => by simpa only [NaturalPolynomial.eval_comp] using p.eval_mono (hq i)⟩
lemma isPoly_pair {ea : α → Word} {eb : β → Word} {a : ι → α} {b : ι → β}
    (ha : IsPoly L (fun i => (ea (a i)).length)) (hb : IsPoly L (fun i => (eb (b i)).length)) :
    IsPoly L (fun i => (prodCode ea eb (a i,b i)).length) := by
  simpa only [prodCode_length] using (((isPoly_const L 2).mul ha).add (isPoly_const L 1)).add hb

variable {ea : α → Word} {eb : β → Word} {ec : γ → Word} {F : α → β} {G : β → γ}

lemma RunsPoly.of_poly (r : Realizes ea eb F) [PolyTime r] (a : ι → α)
    (h : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := by
  refine ⟨h,?_⟩
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  exact (h.eval p).mono (fun i => hp (a i))
lemma RunsPoly.output {r : Realizes ea eb F} {a : ι → α} (h : RunsPoly L r a) :
    IsPoly L (fun i => (eb (F (a i))).length) := (h.input.add h.cost).mono (fun i => r.output_length (a i))
lemma RunsPoly.then {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s (fun i => F (a i))) : RunsPoly L (r.then s) a :=
  ⟨hr.input,hr.cost.add hs.cost⟩
lemma RunsPoly.then_poly {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    (s : Realizes eb ec G) [PolyTime s] : RunsPoly L (r.then s) a :=
  hr.then (RunsPoly.of_poly s _ hr.output)
lemma RunsPoly.both {G : α → γ} {r : Realizes ea eb F} {s : Realizes ea ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.both s) a := by
  refine ⟨hr.input,?_⟩
  have h := (((((isPoly_const L 4).mul hr.input).add ((isPoly_const L 12).mul hr.output)).add hr.cost).add hs.cost).add (isPoly_const L 15)
  apply h.mono
  intro i
  change PairRoutine.pairingTicks ea (fun x => eb (F x)) r.cost s.cost (a i)≤_
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega
lemma RunsPoly.congr {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {F' : α → β} (h : ∀x,F x=F' x) : RunsPoly L (r.congr h) a := by
  have he : F=F' := funext h
  subst F'
  exact hr
lemma RunsPoly.changeOutput {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {δ : Type*} (ed : δ → Word) (g : α → δ) (h : ∀x,eb (F x)=ed (g x)) :
    RunsPoly L (r.changeOutput ed g h) a := ⟨hr.input,hr.cost⟩
lemma Realizes.congr_cost {r : Realizes ea eb F} {F' : α → β} (h : ∀x,F x=F' x) :
    (r.congr h).cost=r.cost := by
  have he : F=F' := funext h
  subst F'
  rfl
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialBranchFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_ratSucc _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}
lemma isPoly_dite {P : ι → Prop} [DecidablePred P] {f : (i : ι) → P i → ℕ}
    {g : (i : ι) → ¬P i → ℕ}
    (hf : IsPoly (fun i : {i // P i} => L i.val) (fun i => f i.val i.property))
    (hg : IsPoly (fun i : {i // ¬P i} => L i.val) (fun i => g i.val i.property)) :
    IsPoly L (fun i => if h : P i then f i h else g i h) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  refine ⟨p+q,?_⟩
  intro i
  by_cases h : P i
  · simp only [dite_eq_left h]
    exact (hp ⟨i,h⟩).trans (Nat.le_add_right _ _)
  · simp only [dite_eq_right h]
    exact (hq ⟨i,h⟩).trans (Nat.le_add_left _ _)

lemma RunsPoly.dite_on {P : α → Prop} [DecidablePred P]
    {F : {a // P a} → β} {G : {a // ¬P a} → β}
    {b : Realizes ea boolCode (fun a => decide (P a))}
    {r : Realizes (fun a : {a // P a} => ea a.val) eb F}
    {s : Realizes (fun a : {a // ¬P a} => ea a.val) eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hc : IsPoly L (fun i => if h : P (a i) then r.cost ⟨a i,h⟩ else s.cost ⟨a i,h⟩)) :
    RunsPoly L (b.dite r s) a := by
  unfold Realizes.dite
  have ht := (hb.both (RunsPoly.of_poly (identity ea) a hb.input)).changeOutput
    (fun x => prodCode boolCode ea (decide (P x),x)) id (fun _ => rfl)
  apply ht.then
  refine ⟨ht.output,?_⟩
  have h := ((isPoly_const L 5).add hc).add (isPoly_const L 1)
  simp only [Nat.add_assoc] at h ⊢
  exact h
lemma RunsPoly.dite_families {P : α → Prop} [DecidablePred P]
    {F : {a // P a} → β} {G : {a // ¬P a} → β}
    {b : Realizes ea boolCode (fun a => decide (P a))}
    {r : Realizes (fun a : {a // P a} => ea a.val) eb F}
    {s : Realizes (fun a : {a // ¬P a} => ea a.val) eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hr : RunsPoly (fun i : {i // P (a i)} => L i.val) r (fun i => ⟨a i.val,i.property⟩))
    (hs : RunsPoly (fun i : {i // ¬P (a i)} => L i.val) s (fun i => ⟨a i.val,i.property⟩)) :
    RunsPoly L (b.dite r s) a := hb.dite_on (isPoly_dite hr.cost hs.cost)
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCeiling
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratFloor _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_ratAdd _root_.OAI.CurrentKS.Realization.size_ratSucc _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

lemma ratNumToNat_cost : ∃ p : NaturalPolynomial,∀q,
    ratNumToNat.cost q≤p.eval (ratCode q).length+6*q.num.toNat := by
  have : PolyTime ratLE := by
    refine ⟨⟨5*X+2048*(X+1)^2+8,?_⟩⟩
    intro input
    have hinput : (ratCode input.1).length+(ratCode input.2).length ≤
        (prodCode ratCode ratCode input).length := by rw [prodCode_length];omega
    have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hinput 1) 2
    have hleft := le_prodCode_left (ea:=ratCode) (eb:=ratCode) input
    change CompareRoutine.ticks input.1 input.2≤5*(prodCode ratCode ratCode input).length+
      2048*((prodCode ratCode ratCode input).length+1)^2+8
    simp only [CompareRoutine.ticks,CompareRoutine.encode,KS.W29.polynomialFuel,List.length_append]
    simp only [ratCode] at *
    omega
  let cmp := ((constant ratCode ratCode 0).le (identity ratCode)).both (identity ratCode)
  have : PolyTime cmp := by dsimp [cmp,Realizes.le];infer_instance
  have : PolyTime wordTail := ⟨⟨1,fun _ => le_rfl⟩⟩
  have : PolyTime ratNumBinary := by unfold ratNumBinary ratFields;infer_instance
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=cmp)
  obtain ⟨r,hr⟩ := PolyTime.bound (r:=ratNumBinary)
  refine ⟨p+5*r+5*X+20,?_⟩
  intro q
  have hcost := hp q
  have hn := hr q
  have ho := ratNumBinary.output_length q
  have hz : (natCode 0).length=0 := rfl
  have hc : (conditional (ratNumBinary.then binaryToNat) (constant ratCode natCode 0)).cost
      (decide (0≤q),q) ≤ 5*r.eval (ratCode q).length+5*(ratCode q).length+20+6*q.num.toNat := by
    change 5+(if decide (0≤q) then ratNumBinary.cost q+(6*KS.W01.intPayload q.num+4*(binaryNatCode (KS.W01.intPayload q.num)).length+4)
      else (ratCode q).length+1+((natCode 0).length+1))+1≤_
    by_cases hq : 0≤q
    · have he : KS.W01.intPayload q.num=q.num.toNat := by
        have hnum := Rat.num_nonneg.mpr hq
        cases hh : q.num with
        | ofNat n => rfl
        | negSucc n => rw [hh] at hnum;omega
      simp only [hq,decide_true,↓reduceIte,he]
      change (binaryNatCode (KS.W01.intPayload q.num)).length≤_ at ho
      rw [he] at ho
      omega
    · simp only [hq,decide_false,Bool.false_eq_true,↓reduceIte,hz]
      omega
  unfold ratNumToNat
  rw [Realizes.congr_cost]
  change cmp.cost q+(conditional (ratNumBinary.then binaryToNat) (constant ratCode natCode 0)).cost (decide (0≤q),q)≤p.eval (ratCode q).length+5*r.eval (ratCode q).length+5*(ratCode q).length+20+6*q.num.toNat
  omega

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_ratNumToNat (a : ι → ℚ) (ha : IsPoly L (fun i => (ratCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).num.toNat)) : RunsPoly L ratNumToNat a := by
  obtain ⟨p,hp⟩ := ratNumToNat_cost
  exact ⟨ha,((ha.eval p).add ((isPoly_const L 6).mul hn)).mono (fun i => hp (a i))⟩
lemma runsPoly_ratCeil (a : ι → ℚ) (ha : IsPoly L (fun i => (ratCode (a i)).length))
    (hn : IsPoly L (fun i => ⌈a i⌉₊)) : RunsPoly L ratCeil a := by
  unfold ratCeil
  apply RunsPoly.congr
  have : PolyTime (ratOp .sub) := by
    refine ⟨⟨5*X+6000000*(X+1)^3+6,?_⟩⟩
    intro input
    have hlength := RoutineLength.output_length
      (KS.W13.ExpressionMachine.binaryArithmetic_spec .sub input.1 input.2 [] []) 10
    have houtput : (ratCode (KS.W13.ExpressionMachine.BinaryOp.sub.eval input.1 input.2)).length≤
        KS.W13.ExpressionMachine.binaryBudget input.1 input.2 := by
      simpa [KS.W13.ExpressionMachine.registers] using hlength
    have hinput : (ratCode input.1).length+(ratCode input.2).length ≤
        (prodCode ratCode ratCode input).length := by rw [prodCode_length];omega
    have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hinput 1) 3
    have hleft := le_prodCode_left (ea:=ratCode) (eb:=ratCode) input
    change ArithmeticRoutine.ticks .sub input.1 input.2≤5*(prodCode ratCode ratCode input).length+
      6000000*((prodCode ratCode ratCode input).length+1)^3+6
    simp only [ArithmeticRoutine.ticks,ArithmeticRoutine.encode,
      KS.W13.ExpressionMachine.binaryBudget,KS.W01.ratLength] at houtput ⊢
    simp only [ratCode] at *
    omega
  have : PolyTime ratFloor := by
    refine ⟨⟨192*(X+1)^2+2,?_⟩⟩
    intro input
    have hlength := RoutineLength.output_length (KS.W20.FloorRationalMachine.polynomial_spec input) 5
    have houtput : (ratCode (⌊input⌋ : ℚ)).length≤64*((ratCode input).length+1)^2 := by
      simpa [KS.W20.FloorRationalMachine.state,KS.W19.SignedFloorMachine.«stacks»,
        KS.W29.polynomialFuel] using hlength
    change FloorCleanRoutine.ticks input≤192*((ratCode input).length+1)^2+2
    simp only [FloorCleanRoutine.ticks,KS.W29.polynomialFuel,FloorCleanRoutine.encode]
    simp only [ratCode] at *
    omega
  let pre := ((identity ratCode).neg.then ratFloor).neg
  have : PolyTime pre := by
    dsimp only [pre, Realizes.neg, Realizes.sub]
    refine @poly_congr _ _ _ _ _ _ _ _ ?_
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · infer_instance
      · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
        · refine @poly_congr _ _ _ _ _ _ _ _ ?_
          refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
          · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_ <;> infer_instance
          · assumption
        · assumption
    · assumption
  have hp := RunsPoly.of_poly pre a ha
  apply hp.then
  apply runsPoly_ratNumToNat _ hp.output
  simpa only [id_eq,Int.floor_neg,Int.cast_neg,neg_neg,Rat.num_intCast,Int.ceil_toNat] using hn
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCoordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*} {ea : α → Word}
local instance coordinates_natLE : PolyTime natLE := by unfold natLE;infer_instance
local instance coordinates_natEq : PolyTime natEq := by unfold natEq;infer_instance
local instance coordinates_matrixEntry_r571236_1 : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
local instance coordinates_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
local instance coordinates_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
local instance coordinates_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then

local instance coordinates_fromBlocks_r571236_1 : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then
instance poly_natLT : PolyTime natLT := by unfold natLT;infer_instance
instance poly_scaleMatrix {f : α → ℚ} {g : α → MatrixData}
    (r : Realizes ea ratCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.scaleMatrix s) := by unfold Realizes.scaleMatrix;apply poly_then
instance poly_negateMatrix : PolyTime negateMatrix := by unfold negateMatrix;infer_instance
instance poly_zeroMatrix : PolyTime zeroMatrix := by unfold zeroMatrix;infer_instance
instance poly_squareTabulate {f : (MatrixData×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime (squareTabulate r) := by unfold squareTabulate;apply poly_then
instance poly_singletonList (ea : α → Word) : PolyTime (singletonList ea) := by unfold singletonList;apply poly_then
instance poly_replicateList (ea : α → Word) : PolyTime (replicateList ea) := by unfold replicateList;infer_instance
instance poly_blockScalar : PolyTime blockScalar := by unfold blockScalar;apply poly_then
instance poly_withLevel : PolyTime withLevel := by unfold withLevel;apply poly_both
instance poly_matrixSub : PolyTime matrixSub := by
  unfold matrixSub
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance poly_zeroRect : PolyTime zeroRect := by unfold zeroRect;apply poly_then
instance poly_basisVector : PolyTime basisVector := by unfold basisVector;apply poly_then
instance poly_pencilFromEval {f : α×List ℚ → MatrixData}
    (r : Realizes (prodCode ea vectorCode) matrixCode f) [PolyTime r] :
    PolyTime r.pencilFromEval := by
  unfold Realizes.pencilFromEval
  refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · refine @poly_tabulate _ _ _ _ _ _ ?_
      refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply poly_both
      · exact poly_matrixSub
instance poly_vdD : PolyTime vdD := by unfold vdD;infer_instance
instance poly_vdRest : PolyTime vdRest := by unfold vdRest;infer_instance
instance poly_vdAtoms : PolyTime vdAtoms := by unfold vdAtoms;infer_instance
instance poly_vdParams : PolyTime vdParams := by unfold vdParams;infer_instance
instance poly_vdX : PolyTime vdX := by unfold vdX;infer_instance
instance poly_vdTheta : PolyTime vdTheta := by unfold vdTheta;infer_instance
instance poly_vdEps : PolyTime vdEps := by unfold vdEps;infer_instance
instance poly_realDimension : PolyTime realDimension := by unfold realDimension;infer_instance
instance poly_valueDimension : PolyTime valueDimension := by unfold valueDimension;infer_instance
instance poly_coordinateIndexRealizes (b : Bool) : PolyTime (coordinateIndexRealizes b) := by unfold coordinateIndexRealizes;first | infer_instance | apply poly_then
instance poly_coordinateEntry (b : Bool) : PolyTime (coordinateEntry b) := by unfold coordinateEntry;infer_instance
instance poly_coordinates (b : Bool) : PolyTime (coordinates b) := by unfold coordinates;first | infer_instance | apply poly_then

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixFold
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

lemma QParts.mono {H K : ℕ} {q : ℚ} (h : QParts H q) (hk : H≤K) : QParts K q :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by decide) hk),h.2.trans (Nat.pow_le_pow_right (by decide) hk)⟩
lemma qparts_zero (H : ℕ) : QParts H 0 := by constructor <;> simp [Nat.one_le_two_pow]
lemma qparts_length (q : ℚ) : QParts (ratCode q).length q := KS.W01.rational_parts_le_two_pow_length q
lemma QParts.mul {H K : ℕ} {q r : ℚ} (hq : QParts H q) (hr : QParts K r) : QParts (H+K) (q*r) :=
  KS.W30.mul_parts_le_two_pow _ _ _ _ hq.1 hq.2 hr.1 hr.2
lemma QParts.add {H K : ℕ} {q r : ℚ} (hq : QParts H q) (hr : QParts K r) : QParts (H+K+1) (q+r) := by
  have ht := KS.W30.add_parts_le_two_pow _ _ _ _ hq.1 hq.2 hr.1 hr.2
  exact ⟨ht.1,ht.2.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
lemma QParts.length {H : ℕ} {q : ℚ} (hq : QParts H q) : (ratCode q).length≤4*H+7 := by
  have h := KS.W01.ratLength_le_of_parts q H H hq.1 hq.2
  change KS.W01.ratLength q≤4*H+7
  omega

lemma getD_property {α : Type*} (P : α → Prop) (xs : List α) (a : α) (i : ℕ)
    (ha : P a) (hx : ∀x∈xs,P x) : P (xs.getD i a) := by
  by_cases h : i<xs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hx _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ha
lemma zipDefault_property {α β γ : Type*} (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    (f : α×β → γ) (a : α) (b : β) (xs : List α) (ys : List β)
    (ha : P a) (hb : Q b) (hx : ∀x∈xs,P x) (hy : ∀y∈ys,Q y)
    (hf : ∀ x y,P x → Q y → R (f (x,y))) :
    ∀z∈zipDefault f a b (xs,ys),R z := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
  exact hf _ _ (getD_property P xs a i ha hx) (getD_property Q ys b i hb hy)

lemma matrixParts_length (M : MatrixData) : MatrixParts (matrixCode M).length M := by
  intro row hr q hq
  exact (qparts_length q).mono ((mem_length_le_code row hq).trans (mem_length_le_code M hr))
lemma MatrixParts.mono {H K : ℕ} {M : MatrixData} (h : MatrixParts H M) (hk : H≤K) : MatrixParts K M :=
  fun row hr q hq => (h row hr q hq).mono hk

lemma matrixShape_length (M : MatrixData) : MatrixShape (matrixCode M).length M := by
  refine ⟨list_length_le_code _ _,?_⟩
  intro row hr
  exact (list_length_le_code _ _).trans (mem_length_le_code M hr)
lemma MatrixShape.mono {L K : ℕ} {M : MatrixData} (h : MatrixShape L M) (hk : L≤K) : MatrixShape K M :=
  ⟨h.1.trans hk,fun row hr => (h.2 row hr).trans hk⟩
lemma matrix_length_bound {H L : ℕ} {M : MatrixData} (hh : MatrixParts H M) (hs : MatrixShape L M) :
    (matrixCode M).length≤L*(2*(L*(2*(4*H+7)+1))+1) := by
  apply (listCode_length_bound M _ (fun row hr => ?_)).trans (Nat.mul_le_mul_right _ hs.1)
  exact (listCode_length_bound row _ (fun q hq => (hh row hr q hq).length)).trans (Nat.mul_le_mul_right _ (hs.2 row hr))

lemma accumMatrix_shape {L : ℕ} (A : MatrixData) (p : ℚ×MatrixData)
    (h : MatrixShape L A) : MatrixShape L (accumMatrix (A,p)) := by
  constructor
  · simpa only [accumMatrix,zipDefault,List.length_map,List.length_range] using h.1
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simp only [zipDefault,List.length_map,List.length_range]
    exact getD_property (fun row : List ℚ => row.length≤L) A [] i (by simp) h.2
lemma accumMatrix_parts {H K : ℕ} (A : MatrixData) (p : ℚ×MatrixData)
    (ha : MatrixParts H A) (hq : QParts K p.1) (hb : MatrixParts K p.2) :
    MatrixParts (H+2*K+1) (accumMatrix (A,p)) := by
  have hs : MatrixParts (2*K) (p.2.map (fun row => row.map (fun x => p.1*x))) := by
    intro row hr0 q hq0
    obtain ⟨r,hr1,he⟩ := List.mem_map.mp hr0
    subst row
    obtain ⟨v,hv1,he'⟩ := List.mem_map.mp hq0
    subst q
    simpa [two_mul] using hq.mul (hb r hr1 v hv1)
  apply zipDefault_property
    (fun row => ∀q∈row,QParts H q) (fun row => ∀q∈row,QParts (2*K) q)
    (fun row => ∀q∈row,QParts (H+2*K+1) q) _ [] [] A _ (by simp) (by simp) ha hs
  intro x y hx hy
  exact zipDefault_property _ _ _ _ 0 0 x y (qparts_zero _) (qparts_zero _) hx hy (fun a b ha hb => ha.add hb)

lemma accumMatrix_fold {L H : ℕ} (A : MatrixData) (xs : List (ℚ×MatrixData))
    (shape : MatrixShape L A) (parts : MatrixParts H A)
    (hp : ∀p∈xs,QParts L p.1 ∧ MatrixParts L p.2) :
    MatrixShape L (xs.foldl (fun a p => accumMatrix (a,p)) A) ∧
      MatrixParts (H+xs.length*(2*L+1)) (xs.foldl (fun a p => accumMatrix (a,p)) A) := by
  induction xs generalizing A H with
  | nil => simpa using And.intro shape parts
  | cons x xs ih =>
    have h := ih (accumMatrix (A,x)) (accumMatrix_shape A x shape)
      (accumMatrix_parts A x parts (hp x (by simp)).1 (hp x (by simp)).2)
      (fun p hp' => hp p (by simp [hp']))
    simpa only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

instance poly_accumMatrix : PolyTime accumMatrixRealizes := by
  unfold accumMatrixRealizes
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance size_accumMatrix : FoldSize accumMatrixRealizes := by
  refine ⟨⟨1000*(X+1)^4,?_⟩⟩
  intro A xs ys zs h
  let L := (prodCode matrixCode (listCode (prodCode ratCode matrixCode)) (A,xs)).length
  have ha : (matrixCode A).length≤L := le_prodCode_left (A,xs)
  have hy : (listCode (prodCode ratCode matrixCode) ys).length≤L :=
    (prefix_code_length _ xs ys zs h).trans (le_prodCode_right (A,xs))
  have hn := (list_length_le_code _ _).trans hy
  have ht := accumMatrix_fold A ys ((matrixShape_length A).mono ha) ((matrixParts_length A).mono ha)
    (fun p hp => by
      have hl : (prodCode ratCode matrixCode p).length≤L := (mem_length_le_code ys hp).trans hy
      exact ⟨(qparts_length p.1).mono ((le_prodCode_left p).trans hl),
        (matrixParts_length p.2).mono ((le_prodCode_right p).trans hl)⟩)
  have he := matrix_length_bound ht.2 ht.1
  have he' : L+ys.length*(2*L+1)≤L+L*(2*L+1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) L
  apply he.trans
  change L*(2*(L*(2*(4*(L+ys.length*(2*L+1))+7)+1))+1)≤1000*(L+1)^4
  calc
    _≤ L*(2*(L*(2*(4*(L+L*(2*L+1))+7)+1))+1) := by gcongr
    _≤_ := by nlinarith [Nat.zero_le L, sq_nonneg (L:ℤ)]
instance poly_evalPencil : PolyTime evalPencil := by unfold evalPencil;apply poly_then
instance poly_normalPencil : PolyTime normalPencil := by unfold normalPencil;apply poly_then

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_QueryBits
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalBits

lemma Parts.abs_le {b : ℕ} {q : ℚ} (hq : Parts b q) : |q| ≤ (2:ℚ)^b := by
  have hnum : |(q.num:ℚ)| ≤ (2:ℚ)^b := by
    have hh : (q.num.natAbs:ℚ) ≤ (2:ℚ)^b := by exact_mod_cast hq.1
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  have hd : (1:ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  rw [←Rat.num_div_den q,abs_div,abs_of_pos (by positivity : (0:ℚ)<q.den)]
  apply (div_le_iff₀ (by positivity : (0:ℚ)<q.den)).mpr
  exact hnum.trans (le_mul_of_one_le_right (by positivity) hd)

end CurrentKS.RationalBits

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_RationalGridBits
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalGridSize

lemma Grid.mul_integer {D : ℕ} {q : ℚ} (hq : Grid D q) (k : ℤ) : Grid D (q*(k:ℚ)) := by
  apply (Rat.mul_den_dvd q (k:ℚ)).trans
  simpa only [Grid,Rat.den_intCast,mul_one] using hq

lemma Grid.den_le {D : ℕ} (hD : 0 < D) {q : ℚ} (hq : Grid D q) : q.den ≤ D :=
  Nat.le_of_dvd hD hq

open scoped BigOperators

end CurrentKS.RationalGridSize

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoots
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize

instance poly_ratNumBinary : PolyTime ratNumBinary := by unfold ratNumBinary;infer_instance
instance poly_unframeNat : PolyTime unframeNat := by unfold unframeNat;apply poly_reindex
instance poly_ratDenBinary : PolyTime ratDenBinary := by unfold ratDenBinary;apply poly_then
instance poly_ratDenSize : PolyTime ratDenSize := by unfold ratDenSize;infer_instance

lemma QParts.abs_le {H : ℕ} {q : ℚ} (h : QParts H q) : |q|≤(2:ℚ)^H :=
  RationalBits.Parts.abs_le h
lemma qparts_of_grid {D H K : ℕ} {q : ℚ} (hD : 0<D) (hg : Grid D q)
    (hd : D≤2^K) (hq : |q|≤(2:ℚ)^H) : QParts (H+K) q := by
  have hden := (hg.den_le hD).trans hd
  have he : |(q.num:ℚ)|=|q| * (q.den:ℚ) := by
    have h := congrArg abs (Rat.num_div_den q)
    rw [abs_div,abs_of_pos (by positivity : (0:ℚ)<q.den)] at h
    exact (div_eq_iff (by positivity : (q.den:ℚ)≠0)).mp h
  have hn : (q.num.natAbs:ℚ)≤(2:ℚ)^(H+K) := by
    rw [Nat.cast_natAbs,Int.cast_abs,he,pow_add]
    exact mul_le_mul hq (by exact_mod_cast hden) (by positivity) (by positivity)
  exact ⟨by exact_mod_cast hn,hden.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PSDCleanRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.PSDCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07 KS.W17 KS.W17.FixedPSD
open CleanRoutine

lemma output_length (a : Datum) : (output a).length ≤ controllerTicks a := by
  have h := RoutineLength.output_length
    (KS.W23.PSDControllerPolynomial.controller_polynomial_spec a.2) (23 : Fin 35)
  simp only [output,witnessState,matrixState,state,show (23 : Fin 35)≠32 by decide,
    show (23 : Fin 35)≠26 by decide,show (23 : Fin 35)≠31 by decide,
    show (23 : Fin 35)≠30 by decide,ite_false, if_false,ite_true, if_true,List.length_nil,zero_add] at h ⊢
  exact h

lemma ticks_le (a : Datum) : ticks a≤
    3*(Computability.encodeNat a.1).length+2*(KS.W08.denseMatrixTape a.2).length+
      3*controllerTicks a+6 := by
  have h := output_length a
  unfold ticks
  omega

end CurrentKS.PSDCleanRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStored
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma flatten_code_le (ea : α → Word) (xs : List (List α)) :
    (listCode ea xs.flatten).length≤(listCode (listCode ea) xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatten_cons,listCode_append,List.length_append,listCode_cons,prodCode_length]
      omega
instance size_appendList (ea : α → Word) : FoldSize (appendList ea) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_append_flatten,listCode_append,List.length_append]
  have hs := le_prodCode_left (ea:=listCode ea) (eb:=listCode (listCode ea)) (s,xs)
  have hy := (flatten_code_le ea ys).trans ((prefix_code_length (listCode ea) xs ys zs h).trans (le_prodCode_right (ea:=listCode ea) (s,xs)))
  change _≤2*(prodCode (listCode ea) (listCode (listCode ea)) (s,xs)).length
  dsimp only at hs hy
  omega
instance poly_flattenList (ea : α → Word) : PolyTime (flattenList ea) := by unfold flattenList;infer_instance
instance poly_joinList (ea : α → Word) : PolyTime (joinList ea) := by unfold joinList;infer_instance
instance poly_singleton (ea : α → Word) : PolyTime (singleton ea) := by unfold singleton;apply poly_then
instance poly_filterCtx {p : γ×α → Bool} (r : Realizes (prodCode ec ea) boolCode p) [PolyTime r] :
    PolyTime r.filterCtx := by unfold Realizes.filterCtx;infer_instance

instance poly_natToBinary : PolyTime natToBinary := by unfold natToBinary;infer_instance

lemma psd_raw_poly : ∃ p : NaturalPolynomial,∀a,PSDCleanRoutine.ticks a≤p.eval (PSDCleanRoutine.input a).length := by
  refine ⟨5*X+3*NaturalPolynomial.constant PSDControllerPolynomial.coefficient*(X+1)^58+6,?_⟩
  intro a
  have h := PSDCleanRoutine.ticks_le a
  have hd : (Computability.encodeNat a.1).length≤(PSDCleanRoutine.input a).length := by
    simp only [PSDCleanRoutine.input,List.length_append,KS.W01.length_frame];omega
  have hm : (KS.W08.denseMatrixTape a.2).length≤(PSDCleanRoutine.input a).length := by
    simp only [PSDCleanRoutine.input,List.length_append];omega
  unfold PSDCleanRoutine.controllerTicks KS.W29.polynomialFuel at h
  have hp := Nat.mul_le_mul_left PSDControllerPolynomial.coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 58)
  change _≤5*(PSDCleanRoutine.input a).length+3*PSDControllerPolynomial.coefficient*((PSDCleanRoutine.input a).length+1)^58+6
  rw [Nat.mul_assoc]
  omega
instance poly_psdStored : PolyTime psdStored := by
  unfold psdStored
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_changeOutput _ _ _ _ _ _ _ _ _ _ ?_
    refine @poly_reindex _ _ _ _ _ _ _ _ _ _ ?_
    refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · apply poly_then
    · apply poly_then
  · exact ⟨psd_raw_poly⟩

instance poly_natLE : PolyTime natLE := by unfold natLE;infer_instance
instance poly_natEq : PolyTime natEq := by unfold natEq;infer_instance
instance poly_matrixEntry : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
instance poly_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
instance poly_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
instance poly_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
instance poly_transposeMatrix : PolyTime transposeMatrix := by unfold transposeMatrix;apply poly_then
instance poly_matrixMul : PolyTime matrixMul := by unfold matrixMul;apply poly_then
instance poly_fromBlocks : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then
instance poly_tabulateFin {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] :
    PolyTime (r.tabulateFin rn) := by unfold Realizes.tabulateFin;infer_instance
instance poly_familyFirst {n : α → ℕ} : PolyTime (familyFirst (ea:=ea) (n:=n)) := by unfold familyFirst;apply poly_reindex
instance poly_familyIndex {n : α → ℕ} : PolyTime (familyIndex (ea:=ea) (n:=n)) := by unfold familyIndex;apply poly_reindex

instance poly_pow {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] (k : ℕ) : PolyTime (r.pow k) := by
  induction k with
  | zero => unfold Realizes.pow;infer_instance
  | succ k ih => unfold Realizes.pow;infer_instance
instance poly_min {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.min s) := by unfold Realizes.min;infer_instance
instance poly_max {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.max s) := by unfold Realizes.max;infer_instance
instance poly_inv {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.inv := by unfold Realizes.inv;infer_instance
instance poly_lt {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.lt s) := by unfold Realizes.lt;infer_instance
instance poly_eq {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.eq s) := by unfold Realizes.eq;infer_instance

instance poly_better (ea : α → Word) : PolyTime (better ea) := by unfold better;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCurvature
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_vectorNeg : PolyTime vectorNeg := by unfold vectorNeg;apply poly_map
instance poly_squareSum : PolyTime squareSum := by unfold squareSum;apply poly_then
instance poly_vectorDivide : PolyTime vectorDivide := by unfold vectorDivide;apply poly_mapCtx
instance poly_initialScale : PolyTime initialScale := by unfold initialScale;apply poly_then
instance poly_intCeil : PolyTime intCeil := by unfold intCeil;apply poly_congr
instance poly_nearest : PolyTime nearest := by unfold nearest;apply poly_congr
instance poly_nearestMesh : PolyTime nearestMesh := by unfold nearestMesh;apply poly_mul
instance poly_roundMesh : PolyTime roundMesh := by unfold roundMesh;apply poly_mapCtx
instance poly_cuN : PolyTime cuN := by unfold cuN;apply poly_then
instance poly_cuRest : PolyTime cuRest := by unfold cuRest;apply poly_then
instance poly_cuH : PolyTime cuH := by unfold cuH;apply poly_then
instance poly_cuScalars : PolyTime cuScalars := by unfold cuScalars;apply poly_then
instance poly_cuA : PolyTime cuA := by unfold cuA;apply poly_then
instance poly_cuMore : PolyTime cuMore := by unfold cuMore;apply poly_then
instance poly_cuM : PolyTime cuM := by unfold cuM;apply poly_then
instance poly_cuLast : PolyTime cuLast := by unfold cuLast;apply poly_then
instance poly_cuS : PolyTime cuS := by unfold cuS;apply poly_then
instance poly_cuRho : PolyTime cuRho := by unfold cuRho;apply poly_then
instance poly_cuShift : PolyTime cuShift := by unfold cuShift;apply poly_changeOutput
instance poly_updateVector : PolyTime updateVector := by unfold updateVector;apply poly_congr
instance poly_endpointEntry : PolyTime endpointEntry := by unfold endpointEntry;apply poly_then
instance poly_endpointCandidates : PolyTime endpointCandidates := by unfold endpointCandidates;apply poly_congr
instance poly_freezeScalar : PolyTime freezeScalar := by unfold freezeScalar;apply poly_congr
instance poly_freezeVector : PolyTime freezeVector := by unfold freezeVector;apply poly_mapCtx
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialExplicit
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
  {f : α → β} {g : β → γ}
lemma PolyTime.pow {f : α → ℚ} {r : Realizes ea ratCode f}
    (hr : PolyTime r) (n : ℕ) : PolyTime (r.pow n) := by
  let := hr;exact poly_pow r n
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFind
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_fromBlocks _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_identityEntry _root_.OAI.CurrentKS.Realization.poly_identityMatrix _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixEntry _root_.OAI.CurrentKS.Realization.poly_matrixMul _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_natEq _root_.OAI.CurrentKS.Realization.poly_natLE _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natToBinary _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_psdStored _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_transposeMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_ratAdd _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
lemma foldl_property {f : β → α → β} (P : β → Prop) (xs : List α) (s : β)
    (hs : P s) (hf : ∀ x∈xs,∀a,P a → P (f a x)) : P (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih => exact ih (f s x) (hf x (by simp) s hs) (fun y hy => hf y (by simp [hy]))
lemma find_fold_size {p : γ×α → Bool} {f : γ×α → β}
    (value : Realizes (prodCode ec ea) eb f) [PolyTime value]
    (r : Realizes (prodCode (prodCode ec eb) ea) (prodCode ec eb)
      (fun z => (z.1.1,if p (z.1.1,z.2) then f (z.1.1,z.2) else z.1.2))) : FoldSize r := by
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=value)
  let U := 3*X+1+q.comp (3*X+1)
  refine ⟨⟨3*X+1+U,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode ec eb) (listCode ea) (s,xs)).length
  have hc : (ec s.1).length≤L := (le_prodCode_left s).trans (le_prodCode_left (s,xs))
  have hb : (eb s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have hv : ∀x∈ys,(eb (f (s.1,x))).length≤U.eval L := by
    intro x hx
    have hl : (prodCode ec ea (s.1,x)).length≤3*L+1 := by
      have he := (mem_length_le_code ys hx).trans hy
      rw [prodCode_length];dsimp only;omega
    have h := (value.output_length (s.1,x)).trans
      (Nat.add_le_add hl ((hq _).trans (q.eval_mono hl)))
    simp only [U,NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
    exact h
  have hh := foldl_property (f:=fun a x => (a.1,if p (a.1,x) then f (a.1,x) else a.2))
    (fun a : γ×β => a.1=s.1 ∧ (eb a.2).length≤L+U.eval L) ys s
    ⟨rfl,hb.trans (Nat.le_add_right _ _)⟩ (by
      intro x hx a ha
      refine ⟨ha.1,?_⟩
      dsimp only
      split
      · rw [ha.1];exact (hv x hx).trans (Nat.le_add_left _ _)
      · exact ha.2)
  rw [prodCode_length,hh.1]
  change _≤3*L+1+U.eval L
  have hb' := hh.2
  dsimp only at *
  omega
instance poly_findValue {p : γ×α → Bool} {f : γ×α → β}
    (test : Realizes (prodCode ec ea) boolCode p) (value : Realizes (prodCode ec ea) eb f)
    [PolyTime test] [PolyTime value] : PolyTime (test.findValue value) := by
  let old := first (prodCode ec eb) ea
  let cx := (old.then (first ec eb)).both (second (prodCode ec eb) ea)
  let body := (old.then (first ec eb)).both ((cx.then test).ite (cx.then value) (old.then (second ec eb)))
  have : FoldSize body := find_fold_size value body
  dsimp only [Realizes.findValue]
  apply poly_congr
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSchedule
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_saD : PolyTime saD := by unfold saD;infer_instance
instance poly_saRest : PolyTime saRest := by unfold saRest;infer_instance
instance poly_saN : PolyTime saN := by unfold saN;apply poly_then
instance poly_saScalars : PolyTime saScalars := by unfold saScalars;apply poly_then
instance poly_saNu : PolyTime saNu := by unfold saNu;apply poly_then
instance poly_saLam : PolyTime saLam := by unfold saLam;apply poly_then
instance poly_saEpsilon : PolyTime saEpsilon := by unfold saEpsilon;apply poly_div
instance poly_saSigma : PolyTime saSigma := by unfold saSigma;apply poly_div
instance poly_movementBudget : PolyTime movementBudget := by unfold movementBudget;apply poly_max
instance poly_saThreshold : PolyTime saThreshold := by unfold saThreshold;apply poly_div
instance poly_saCoarse : PolyTime saCoarse := by unfold saCoarse;apply poly_add
instance poly_saCurve2 : PolyTime saCurve2 := by unfold saCurve2;apply poly_mul
instance poly_saCurve3 : PolyTime saCurve3 := by unfold saCurve3;apply poly_mul
instance poly_saBudget : PolyTime saBudget := by unfold saBudget;apply poly_add
instance poly_saStep : PolyTime saStep := by unfold saStep;apply poly_min
instance poly_saStencil : PolyTime saStencil := by unfold saStencil;apply poly_min
instance poly_saMesh : PolyTime saMesh := by unfold saMesh;apply poly_div
instance poly_parameters_singleton : PolyTime parameters.singletonRat := by unfold parameters.singletonRat;apply poly_then
instance poly_parameters : PolyTime parameters := by unfold parameters;apply poly_changeOutput
instance poly_parameterField (i : ℕ) : PolyTime (parameterField i) := by
  unfold parameterField
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_reindex
  · infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceBasics
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_activeIndices : PolyTime activeIndices := by unfold activeIndices;apply poly_then
instance poly_extendEntry : PolyTime extendEntry := by unfold extendEntry;apply poly_congr
instance poly_extendVector : PolyTime extendVector := by unfold extendVector;apply poly_then
instance poly_fD : PolyTime fD := by unfold fD;apply poly_then
instance poly_fRest : PolyTime fRest := by unfold fRest;apply poly_then
instance poly_fAtoms : PolyTime fAtoms := by unfold fAtoms;apply poly_then
instance poly_fArgs : PolyTime fArgs := by unfold fArgs;apply poly_then
instance poly_fBase : PolyTime fBase := by unfold fBase;apply poly_then
instance poly_fScalars : PolyTime fScalars := by unfold fScalars;apply poly_then
instance poly_fNu : PolyTime fNu := by unfold fNu;apply poly_then
instance poly_fLam : PolyTime fLam := by unfold fLam;apply poly_then
instance poly_fIndices : PolyTime fIndices := by unfold fIndices;apply poly_congr
instance poly_fN : PolyTime fN := by unfold fN;apply poly_congr
instance poly_fSchedule : PolyTime fSchedule := by unfold fSchedule;apply poly_then
instance poly_gather : PolyTime gather := by unfold gather;apply poly_mapCtx
instance poly_fState : PolyTime fState := by unfold fState;apply poly_congr
instance poly_fpP : PolyTime fpP := by unfold fpP;apply poly_then
instance poly_fpY : PolyTime fpY := by unfold fpY;apply poly_then
instance poly_fpExtend : PolyTime fpExtend := by unfold fpExtend;apply poly_congr
instance poly_fpPotential : PolyTime fpPotential := by unfold fpPotential;apply poly_changeOutput
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoundedStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize
open scoped BigOperators

local notation "X" => NaturalPolynomial.variable

instance poly_roundedUpdate : PolyTime roundedUpdate := by unfold roundedUpdate;apply poly_then
instance poly_statePencil : PolyTime statePencil := by unfold statePencil;apply poly_then
instance poly_stateParameters : PolyTime stateParameters := by unfold stateParameters;apply poly_then
instance poly_stateY : PolyTime stateY := by unfold stateY;apply poly_then
instance poly_stateWitness : PolyTime stateWitness := by unfold stateWitness;apply poly_then
instance poly_stateNextVector : PolyTime stateNextVector := by unfold stateNextVector;apply poly_congr
instance poly_pencilNext : PolyTime pencilNext := by unfold pencilNext;apply poly_changeOutput

lemma round_abs (ρ x : ℚ) : |RationalSDP.roundScalar ρ x|≤|x|+|ρ| := by
  by_cases hρ : ρ=0
  · simp [hρ,RationalSDP.roundScalar]
  have he : RationalSDP.roundScalar ρ x-x=ρ*((⌊x/ρ⌋:ℚ)-x/ρ) := by
    unfold RationalSDP.roundScalar
    rw [mul_sub, mul_div_cancel₀ _ hρ]
  have hf : |(⌊x/ρ⌋:ℚ)-x/ρ|≤1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le _))]
    linarith [Int.lt_floor_add_one (x/ρ)]
  have hd : |RationalSDP.roundScalar ρ x-x|≤|ρ| := by
    rw [he,abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (abs_nonneg ρ)
  have ht := abs_add_le (RationalSDP.roundScalar ρ x-x) x
  rw [sub_add_cancel] at ht
  linarith

lemma l1_coordinate {n : ℕ} (a : Fin n → ℚ) (i : Fin n) : |a i/RationalSDP.l1 a|≤1 := by
  have h0 : 0≤RationalSDP.l1 a := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hi : |a i|≤RationalSDP.l1 a := Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  by_cases h : RationalSDP.l1 a=0
  · simp [h]
  rw [abs_div,abs_of_nonneg h0]
  exact (div_le_one (lt_of_le_of_ne h0 (Ne.symm h))).mpr hi

lemma pencil_next_abs {n m : ℕ} (B : RationalSDP.Pencil n m) (step mesh : ℚ)
    (y : Fin n → ℚ) (i : Fin n) : |B.next step mesh y i|≤|y i|+|step|+|mesh| := by
  unfold RationalSDP.Pencil.next
  cases B.witness y with
  | none =>
    have h1 := abs_nonneg step;have h2 := abs_nonneg mesh;linarith
  | some v =>
    apply (round_abs mesh _).trans
    have hm : |step * B.normal v i / RationalSDP.l1 (B.normal v)|≤|step| := by
      rw [mul_div_assoc,abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (l1_coordinate (B.normal v) i) (abs_nonneg step)
    have ht := abs_sub (y i) (step*B.normal v i/RationalSDP.l1 (B.normal v))
    linarith

lemma pencil_next_grid {n m D : ℕ} (B : RationalSDP.Pencil n m) (step mesh : ℚ)
    (y : Fin n → ℚ) (i : Fin n) (hy : Grid D (y i)) (hm : Grid D mesh) :
    Grid D (B.next step mesh y i) := by
  unfold RationalSDP.Pencil.next
  cases hw : B.witness y with
  | none => exact hy
  | some v => exact hm.mul_integer _

lemma pencil_iterate_parts {n m L : ℕ} (B : RationalSDP.Pencil n m) (step mesh : ℚ)
    (y : Fin n → ℚ) (hs : QParts L step) (hm : QParts L mesh)
    (hy : ∀i,QParts L (y i)) (k : ℕ) (i : Fin n) :
    QParts (3*L+k+1) ((B.next step mesh)^[k] y i) := by
  have hg : ∀k,Grid ((y i).den*mesh.den) ((B.next step mesh)^[k] y i) := by
    intro k
    induction k with
    | zero => exact Nat.dvd_mul_right _ _
    | succ k ih => rw [Function.iterate_succ_apply'];exact pencil_next_grid B step mesh _ i ih (Nat.dvd_mul_left _ _)
  have ha : ∀k,|((B.next step mesh)^[k] y) i|≤(2:ℚ)^(L+k+1) := by
    intro k
    induction k with
    | zero =>
      exact (hy i).abs_le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    | succ k ih =>
      have ht := pencil_next_abs B step mesh ((B.next step mesh)^[k] y) i
      have hlow : (2:ℚ)^(L+1)≤2^(L+k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hp : (2:ℚ)^(L+(k+1)+1)=2*2^(L+k+1) := by rw [show L+(k+1)+1=(L+k+1)+1 by omega,pow_succ,mul_comm]
      rw [Function.iterate_succ_apply',hp]
      have hs' := hs.abs_le
      have hm' := hm.abs_le
      rw [pow_succ] at hlow
      linarith
  have hd : (y i).den*mesh.den≤2^(2*L) := by
    rw [show 2*L=L+L by omega,pow_add]
    exact Nat.mul_le_mul (hy i).2 hm.2
  have ht := qparts_of_grid (by positivity : 0<(y i).den*mesh.den) (hg k) hd (ha k)
  convert ht using 1 <;> first | (with_reducible_and_instances rfl) | (omega)

instance size_pencilNext : IterateSize pencilNext := by
  refine ⟨⟨100*(X+1)^2,?_⟩⟩
  intro s k
  let L := (pencilStateCode s).length
  have hb : (pencilCode (pencilData s.B)).length≤L := le_prodCode_left (pencilStateData s)
  have hp : (stepParametersCode (s.step,s.mesh)).length≤L := (le_prodCode_left (pencilStateData s).2).trans (le_prodCode_right (pencilStateData s))
  have hy : (vectorCode (List.ofFn s.y)).length≤L := (le_prodCode_right (pencilStateData s).2).trans (le_prodCode_right (pencilStateData s))
  have hs : QParts L s.step := (qparts_length s.step).mono ((le_prodCode_left (s.step,s.mesh)).trans hp)
  have hm : QParts L s.mesh := (qparts_length s.mesh).mono ((le_prodCode_right (s.step,s.mesh)).trans hp)
  have hy' : ∀i,QParts L (s.y i) := by
    intro i
    exact (qparts_length (s.y i)).mono ((mem_length_le_code (List.ofFn s.y) (List.mem_ofFn.mpr ⟨i,rfl⟩)).trans hy)
  have hn : s.n≤L := by simpa only [List.length_ofFn] using (list_length_le_code ratCode (List.ofFn s.y)).trans hy
  have ht := listCode_length_bound (List.ofFn ((s.B.next s.step s.mesh)^[k] s.y)) (4*(3*L+k+1)+7) (by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact (pencil_iterate_parts s.B s.step s.mesh s.y hs hm hy' k i).length)
  rw [List.length_ofFn] at ht
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change (pencilStateCode (PencilState.next^[k] s)).length≤100*(L+k+1)^2
  rw [pencilNext_iterate]
  simp only [pencilStateCode,pencilStateData,pencilStateDataCode,prodCode_length]
  simp only [pencilCode,prodCode_length] at hb
  simp only [stepParametersCode,prodCode_length] at hp
  change (vectorCode (List.ofFn ((s.B.next s.step s.mesh)^[k] s.y))).length≤_ at ht'
  nlinarith
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSearch
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_searchPencil : PolyTime searchPencil := by unfold searchPencil;apply poly_then
instance poly_searchParameters : PolyTime searchParameters := by unfold searchParameters;apply poly_then
instance poly_searchY : PolyTime searchY := by unfold searchY;apply poly_then
instance poly_searchDim : PolyTime searchDim := by unfold searchDim;infer_instance
instance poly_searchStep : PolyTime searchStepRealizes := by unfold searchStepRealizes;apply poly_div
instance poly_searchMesh : PolyTime searchMeshRealizes := by unfold searchMeshRealizes;apply poly_div
instance poly_searchInit : PolyTime searchInit := by unfold searchInit;apply poly_changeOutput

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_searchFuel (a : ι → SearchState)
    (ha : IsPoly L (fun i => (searchStateCode (a i)).length))
    (hn : IsPoly L (fun i => RationalSDP.searchFuel (a i).n (a i).r (a i).R)) :
    RunsPoly L searchFuelRealizes a := by
  unfold searchFuelRealizes
  apply RunsPoly.then_poly
  let expr := ((constant searchStateCode ratCode 4).mul
    ((searchParameters.then (second ratCode ratCode)).pow 2)).div (searchStepRealizes.pow 2)
  have hp := RunsPoly.of_poly expr a ha
  apply RunsPoly.then hp
  apply runsPoly_ratCeil
  · exact hp.output
  · apply hn.mono
    intro i
    change ⌈4*(a i).R^2/(RationalSDP.searchStep (a i).n (a i).r)^2⌉₊≤_
    exact Nat.le_succ _
lemma runsPoly_search (a : ι → SearchState)
    (ha : IsPoly L (fun i => (searchStateCode (a i)).length))
    (hn : IsPoly L (fun i => RationalSDP.searchFuel (a i).n (a i).r (a i).R)) :
    RunsPoly L search a := by
  unfold search
  apply RunsPoly.congr
  exact (((runsPoly_searchFuel a ha hn).both (RunsPoly.of_poly searchInit a ha)).then_poly
    pencilNext.iterate).then_poly stateY

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOptimize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_optB : PolyTime optB := by unfold optB;apply poly_then
instance poly_optF : PolyTime optF := by unfold optF;apply poly_then
instance poly_optScalars : PolyTime optScalars := by unfold optScalars;apply poly_then
instance poly_optDelta : PolyTime optDelta := by unfold optDelta;apply poly_then
instance poly_optRest : PolyTime optRest := by unfold optRest;apply poly_then
instance poly_optRadius : PolyTime optRadius := by unfold optRadius;apply poly_both
instance poly_optUpper : PolyTime optUpper := by unfold optUpper;apply poly_then
instance poly_optLevel : PolyTime optLevel := by unfold optLevel;apply poly_add
instance poly_optLevelPencil : PolyTime optLevelPencil := by unfold optLevelPencil;apply poly_congr
instance poly_osP : PolyTime osP := by unfold osP;apply poly_then
instance poly_osK : PolyTime osK := by unfold osK;apply poly_then
instance poly_osY : PolyTime osY := by unfold osY;apply poly_then
instance poly_isPSD : PolyTime isPSD := by unfold isPSD;apply poly_congr
instance poly_witnessEvaluation : PolyTime witnessEvaluation := by unfold witnessEvaluation;apply poly_changeOutput
instance poly_witnessNone : PolyTime witnessNone := by unfold witnessNone;apply poly_then
instance poly_osFeasible : PolyTime osFeasible := by
  unfold osFeasible
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_changeOutput
  · infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialValueQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_weightedSum : PolyTime weightedSum := by unfold weightedSum;apply poly_then
instance poly_veP : PolyTime veP := by unfold veP;infer_instance
instance poly_veY : PolyTime veY := by unfold veY;infer_instance
instance poly_veD : PolyTime veD := by unfold veD;apply poly_then
instance poly_veN : PolyTime veN := by unfold veN;apply poly_then
instance poly_veEye : PolyTime veEye := by unfold veEye;apply poly_then
instance poly_veEps : PolyTime veEps := by unfold veEps;apply poly_then
instance poly_veTime : PolyTime veTime := by unfold veTime;apply poly_then
instance poly_veSum : PolyTime veSum := by unfold veSum;apply poly_then
instance poly_sandwich : PolyTime sandwich := by unfold sandwich;apply poly_then
instance poly_eta : PolyTime eta := by unfold eta;apply poly_then
instance poly_tinyMatrix : PolyTime tinyMatrix := by unfold tinyMatrix;apply poly_then
instance poly_traceMatrix : PolyTime traceMatrix := by unfold traceMatrix;apply poly_then
instance poly_valueObjective : PolyTime valueObjective := by unfold valueObjective;apply poly_add
instance poly_valueCoeffs : PolyTime valueCoeffs := by unfold valueCoeffs;apply poly_then
instance poly_vqData : PolyTime vqData := by unfold vqData;apply poly_then
instance poly_vqDelta : PolyTime vqDelta := by unfold vqDelta;apply poly_then
instance poly_valueLipschitz : PolyTime valueLipschitz := by unfold valueLipschitz;apply poly_mul
instance poly_valueOuterRadius : PolyTime valueOuterRadius := by unfold valueOuterRadius;apply poly_mul
instance poly_valueInnerRadius : PolyTime valueInnerRadius := by unfold valueInnerRadius;apply poly_div
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialPotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_ppD : PolyTime ppD := by unfold ppD;apply poly_then
instance poly_ppRest : PolyTime ppRest := by unfold ppRest;apply poly_then
instance poly_ppAtoms : PolyTime ppAtoms := by unfold ppAtoms;apply poly_then
instance poly_ppArgs : PolyTime ppArgs := by unfold ppArgs;apply poly_then
instance poly_ppX : PolyTime ppX := by unfold ppX;apply poly_then
instance poly_ppScalars : PolyTime ppScalars := by unfold ppScalars;apply poly_then
instance poly_ppNu : PolyTime ppNu := by unfold ppNu;apply poly_then
instance poly_ppLam : PolyTime ppLam := by unfold ppLam;apply poly_then
instance poly_ppError : PolyTime ppError := by unfold ppError;apply poly_then
instance poly_ppN : PolyTime ppN := by unfold ppN;apply poly_congr
instance poly_ppRootTolerance : PolyTime ppRootTolerance := by unfold ppRootTolerance;apply poly_div
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ}
instance poly_fiP : PolyTime fiP := by unfold fiP;apply poly_familyFirst
instance poly_fiI : PolyTime fiI := by unfold fiI;apply poly_familyIndex
instance poly_fiBasis : PolyTime fiBasis := by unfold fiBasis;apply poly_congr
instance poly_fdS : PolyTime fdS := by unfold fdS;apply poly_familyFirst
instance poly_fdP : PolyTime fdP := by unfold fdP;apply poly_then
instance poly_fdI : PolyTime fdI := by unfold fdI;apply poly_then
instance poly_fdJ : PolyTime fdJ := by unfold fdJ;apply poly_familyIndex
instance poly_fdBasisI : PolyTime fdBasisI := by unfold fdBasisI;apply poly_then
instance poly_fdBasisJ : PolyTime fdBasisJ := by unfold fdBasisJ;apply poly_congr

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceChoice
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
instance poly_vectorSub : PolyTime vectorSub := by unfold vectorSub;apply poly_zipWith
instance poly_curvatureCandidates : PolyTime curvatureCandidates := by unfold curvatureCandidates;apply poly_congr
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceFuel
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
instance size_minDatum : FoldSize ((first ratCode ratCode).min (second ratCode ratCode)) := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs he
  let L := (prodCode ratCode vectorCode (s,xs)).length
  have hs : (ratCode s).length≤L := le_prodCode_left (s,xs)
  have hy : (vectorCode ys).length≤L := (prefix_code_length ratCode xs ys zs he).trans (le_prodCode_right (s,xs))
  exact foldl_property (fun a : ℚ => (ratCode a).length≤L) ys s hs (by
    intro x hx a ha
    change (ratCode (min a x)).length≤L
    rw [min_def]
    split
    · exact ha
    · exact (mem_length_le_code ys hx).trans hy)
instance poly_minList : PolyTime minList := by unfold minList;apply poly_congr
instance poly_fUniformDrop : PolyTime fUniformDrop := by unfold fUniformDrop;apply poly_congr
instance poly_packFace {α : Type*} {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a)))
    [PolyTime p] [PolyTime y] : PolyTime (packFace p y) := by
  unfold packFace;apply poly_changeOutput
instance poly_faceStart : PolyTime faceStart := by
  unfold faceStart
  refine @poly_packFace _ _ _ _ _ _ ?_ ?_
  · exact poly_identity _
  · apply poly_congr
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOriginalFields
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_isPSD _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_osFeasible _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilNext _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_stateNextVector _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateWitness _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_witnessEvaluation _root_.OAI.CurrentKS.Realization.poly_witnessNone _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_originalD : PolyTime originalD := by unfold originalD;apply poly_then
instance poly_originalRecords : PolyTime originalRecords := by unfold originalRecords;apply poly_then
instance poly_originalN : PolyTime originalN := by unfold originalN;apply poly_congr
instance poly_recordEntry (imag : Bool) : PolyTime (recordEntry imag) := by unfold recordEntry;apply poly_then
instance poly_recordCoordinate : PolyTime recordCoordinate := by unfold recordCoordinate;apply poly_congr
instance poly_recordCoordinates : PolyTime recordCoordinates := by unfold recordCoordinates;apply poly_then
instance poly_originalRecord : PolyTime originalRecord := by unfold originalRecord;apply poly_congr
instance poly_recordTrace : PolyTime recordTrace := by unfold recordTrace;apply poly_then
instance poly_originalTrace : PolyTime originalTrace := by unfold originalTrace;apply poly_congr
instance poly_originalTraces : PolyTime originalTraces := by unfold originalTraces;apply poly_tabulateFin
instance poly_originalScale : PolyTime originalScale := by unfold originalScale;apply poly_congr
instance poly_originalOrientation : PolyTime originalOrientation := by unfold originalOrientation;apply poly_congr
instance poly_nonzeroIndices : PolyTime nonzeroIndices := by unfold nonzeroIndices;apply poly_congr
instance poly_originalIndices : PolyTime originalIndices := by unfold originalIndices;apply poly_congr
instance poly_originalCountRealizes : PolyTime originalCountRealizes := by unfold originalCountRealizes;apply poly_congr
instance poly_originalIndex : PolyTime originalIndex := by unfold originalIndex;apply poly_changeOutput
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialVariance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_mgN : PolyTime mgN := by unfold mgN;apply poly_then
instance poly_mgRest : PolyTime mgRest := by unfold mgRest;apply poly_then
instance poly_mgM : PolyTime mgM := by unfold mgM;apply poly_then
instance poly_mgDen : PolyTime mgDen := by unfold mgDen;apply poly_then
instance poly_mgShift : PolyTime mgShift := by unfold mgShift;apply poly_changeOutput
instance poly_mgTest : PolyTime mgTest := by unfold mgTest;apply poly_congr
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {β : Type*}

instance poly_selectFlagged (eb : β → Word) : PolyTime (selectFlagged eb) := by
  unfold selectFlagged
  infer_instance

end CurrentKS.Realization

namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open Matrix
local notation "X" => NaturalPolynomial.variable

instance poly_numColumns : PolyTime numColumns := by
  unfold numColumns
  apply poly_congr

instance poly_outer : PolyTime outer := by
  unfold outer
  infer_instance
instance poly_gram : PolyTime gram := by
  unfold gram
  infer_instance

instance poly_column : PolyTime column := by unfold column; apply poly_congr
instance poly_scale : PolyTime scale := by unfold scale; infer_instance

instance poly_thresholdProgram : PolyTime thresholdProgram := by
  have hfactor : PolyTime factor := by
    unfold factor
    apply poly_then
  unfold thresholdProgram
  refine @poly_add _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_mul _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · refine @poly_sub _ _ _ _ _ _ ?_ ?_
      · infer_instance
      · exact hfactor.pow 2

instance poly_testProgram : PolyTime testProgram := by
  unfold testProgram
  infer_instance

instance poly_isHeavy : PolyTime isHeavy := by unfold isHeavy; infer_instance

instance poly_updated : PolyTime updated := by unfold updated; apply poly_congr

instance poly_newScales : PolyTime newScales := by unfold newScales; infer_instance

instance poly_step : PolyTime step := by unfold step; apply poly_changeOutput

lemma advance_iterate_parts (p : Params) (s : Fin p.m → ℚ) {b : ℕ}
    (ht : QParts b p.t) (hs : ∀i,QParts b (s i)) (k : ℕ) :
    ∀i,QParts (b+k*b) ((advance p.q p.t p.v)^[k] s i) := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    intro i
    rw [Function.iterate_succ_apply']
    rw [advance]
    cases hh : heavy p.q p.t p.v ((advance p.q p.t p.v)^[k] s) with
    | none =>
      exact (ih i).mono (show b+k*b ≤ b+(k+1)*b by simp only [Nat.add_mul,Nat.one_mul]; omega)
    | some j =>
      simp only [Option.elim_some]
      by_cases h : i=j
      · subst i
        simpa only [Function.update_self,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht.mul (ih j)
      · simpa only [Function.update_of_ne h] using
          (ih i).mono (show b+k*b ≤ b+(k+1)*b by simp only [Nat.add_mul,Nat.one_mul]; omega)

instance size_step : IterateSize step := by
  refine ⟨⟨100*(X+1)^3,?_⟩⟩
  intro s k
  let L := (stateCode s).length
  have hp : (paramsCode s.params).length≤L := le_prodCode_left (s.params,List.ofFn s.scales)
  have hy : (vectorCode (List.ofFn s.scales)).length≤L := le_prodCode_right (s.params,List.ofFn s.scales)
  have ht : QParts L s.params.t := (qparts_length _).mono
    (((le_prodCode_left (s.params.t,matrixData s.params.v)).trans
      (le_prodCode_right (s.params.q,(s.params.t,matrixData s.params.v)))).trans
        ((le_prodCode_right s.params.data).trans hp))
  have hs : ∀i,QParts L (s.scales i) := by
    intro i
    exact (qparts_length _).mono
      ((mem_length_le_code (List.ofFn s.scales) (List.mem_ofFn.mpr ⟨i,rfl⟩)).trans hy)
  have hm : s.params.m≤L := by
    simpa only [List.length_ofFn] using (list_length_le_code ratCode (List.ofFn s.scales)).trans hy
  have hlen := listCode_length_bound
    (List.ofFn ((advance s.params.q s.params.t s.params.v)^[k] s.scales)) (4*(L+k*L)+7) (by
      intro q hq
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact (advance_iterate_parts s.params s.scales ht hs k i).length)
  rw [List.length_ofFn] at hlen
  have hlen' := hlen.trans (Nat.mul_le_mul_right _ hm)
  change (stateCode (State.next^[k] s)).length≤100*(L+k+1)^3
  rw [next_iterate]
  change (prodCode paramsCode vectorCode
    (s.params,List.ofFn ((advance s.params.q s.params.t s.params.v)^[k] s.scales))).length≤_
  rw [prodCode_length]
  dsimp only
  change (vectorCode (List.ofFn ((advance s.params.q s.params.t s.params.v)^[k] s.scales))).length≤_ at hlen'
  have hL : L≤L+k+1 := by omega
  have hk : k≤L+k+1 := by omega
  have hLL := Nat.mul_le_mul hL hL
  have hkLL := Nat.mul_le_mul hk hLL
  nlinarith

instance poly_initial : PolyTime initial := by unfold initial; infer_instance

instance poly_run : PolyTime run := by unfold run; infer_instance

instance poly_unaryPow (k : ℕ) : PolyTime (unaryPow k) := by
  induction k with
  | zero => unfold unaryPow; apply poly_congr
  | succ k ih => unfold unaryPow; infer_instance

instance poly_multiplierProgram : PolyTime multiplierProgram := by
  unfold multiplierProgram; apply poly_sub

instance poly_fixedStep : PolyTime fixedStep := by unfold fixedStep; apply poly_changeOutput

instance poly_lengthProgram : PolyTime lengthProgram := by unfold lengthProgram; apply poly_then

instance poly_normalized : PolyTime normalized := by unfold normalized; apply poly_then

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_MatrixRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_column _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_fixedStep _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_gram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_initial _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_isHeavy _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_lengthProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_multiplierProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_newScales _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_normalized _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_numColumns _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_outer _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_run _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_scale _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_step _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_testProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_thresholdProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_unaryPow _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_updated _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_isPSD _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osFeasible _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_pencilNext _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_selectFlagged _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateNextVector _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateWitness _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessEvaluation _root_.OAI.CurrentKS.Realization.poly_witnessNone _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}

lemma matrixCode_parts_bound {n m b : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (h : ∀i j,QParts b (A i j)) :
    (matrixCode (matrixData A)).length≤n*(2*(m*(2*(4*b+7)+1))+1) := by
  apply (listCode_length_bound (matrixData A) (m*(2*(4*b+7)+1)) ?_).trans_eq
    (by rw [show (matrixData A).length=n from List.length_ofFn])
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  apply (listCode_length_bound (List.ofFn (A i)) (4*b+7) ?_).trans_eq
    (by rw [List.length_ofFn])
  intro q hq
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
  exact (h i j).length

instance poly_schurEntry : PolyTime schurEntry := by unfold schurEntry; apply poly_sub

instance poly_schur : PolyTime schur := by unfold schur; apply poly_changeOutput

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_SchurHistory
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schur history. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

instance poly_schurNext : PolyTime schurNext := by unfold schurNext; infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ArraySums
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array sums. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

instance poly_matrixSum : PolyTime matrixSum := by
  unfold matrixSum
  apply poly_then

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_sumFin {n : α → ℕ} {f : (a : α) → Fin (n a) → ℚ}
    (r : Realizes (finFamilyCode ea n) ratCode (fun a => f a.1 a.2))
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] : PolyTime (r.sumFin rn) := by
  unfold Realizes.sumFin;infer_instance
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BinaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_column _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_fixedStep _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_gram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_initial _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_isHeavy _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_lengthProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_multiplierProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_newScales _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_normalized _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_numColumns _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_outer _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_run _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_scale _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_step _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_testProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_thresholdProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_unaryPow _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_updated _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_isPSD _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osFeasible _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_pencilNext _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_schur _root_.OAI.CurrentKS.Realization.poly_schurEntry _root_.OAI.CurrentKS.Realization.poly_schurNext _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_selectFlagged _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateNextVector _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateWitness _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessEvaluation _root_.OAI.CurrentKS.Realization.poly_witnessNone _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance poly_binaryToRat : PolyTime binaryToRat := by unfold binaryToRat;infer_instance

instance poly_binaryDiv (d : ℕ) : PolyTime (binaryDiv d) := by unfold binaryDiv;infer_instance

instance poly_binaryMod (d : ℕ) : PolyTime (binaryMod d) := by unfold binaryMod;infer_instance

instance poly_binaryModUnary (d : ℕ) [hd : Fact (0<d)] : PolyTime (binaryModUnary d) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=binaryMod d)
  refine ⟨⟨5*p+4*X+NaturalPolynomial.constant (6*d+4),?_⟩⟩
  intro n
  have ho := (binaryMod d).output_length n
  have hn := Nat.mod_lt n hd.out
  have hh := hp n
  change (binaryMod d).cost n+(6*(n%d)+4*(binaryNatCode (n%d)).length+4)≤_
  change (binaryMod d).cost n+(6*(n%d)+4*(binaryNatCode (n%d)).length+4)≤
    5*p.eval (binaryNatCode n).length+4*(binaryNatCode n).length+(6*d+4)
  omega

instance poly_ratDenRat : PolyTime ratDenRat := by unfold ratDenRat;infer_instance

instance poly_scalarProductBinary : PolyTime scalarProductBinary := by
  unfold scalarProductBinary;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ScalarRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_column _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_fixedStep _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_gram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_initial _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_isHeavy _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_lengthProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_multiplierProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_newScales _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_normalized _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_numColumns _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_outer _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_run _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_scale _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_step _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_testProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_thresholdProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_unaryPow _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_updated _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_isPSD _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osFeasible _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilNext _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_schur _root_.OAI.CurrentKS.Realization.poly_schurEntry _root_.OAI.CurrentKS.Realization.poly_schurNext _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_selectFlagged _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_stateNextVector _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateWitness _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_witnessEvaluation _root_.OAI.CurrentKS.Realization.poly_witnessNone _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 AlgorithmicThinTrees.RationalGram
instance poly_squareScan : PolyTime squareScan := by
  let : Fact (0<4) := ⟨by decide⟩
  unfold squareScan
  apply poly_both

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_column _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_fixedStep _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_gram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_initial _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_isHeavy _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_lengthProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_multiplierProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_newScales _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_normalized _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_numColumns _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_outer _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_run _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_scale _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_step _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_testProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_thresholdProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_unaryPow _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_updated _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_isPSD _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osFeasible _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilNext _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_schur _root_.OAI.CurrentKS.Realization.poly_schurEntry _root_.OAI.CurrentKS.Realization.poly_schurNext _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_selectFlagged _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_stateNextVector _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateWitness _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_witnessEvaluation _root_.OAI.CurrentKS.Realization.poly_witnessNone _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance poly_natSub : PolyTime natSub := by unfold natSub;infer_instance

instance poly_natDivBinary : PolyTime natDivBinary := by unfold natDivBinary;infer_instance

instance poly_natDiv : PolyTime natDiv := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=natDivBinary)
  refine ⟨⟨5*p+10*X+4,?_⟩⟩
  intro a
  have hc := hp a
  have ho := natDivBinary.output_length a
  have hn := Nat.div_le_self a.1 a.2
  have hl := le_prodCode_left (ea:=natCode) (eb:=natCode) a
  simp only [natCode,List.length_replicate] at hl
  change natDivBinary.cost a+(6*(a.1/a.2)+4*(binaryNatCode (a.1/a.2)).length+4)≤
    5*p.eval (prodCode natCode natCode a).length+10*(prodCode natCode natCode a).length+4
  omega

instance poly_natMod : PolyTime natMod := by unfold natMod;infer_instance

variable {α : Type*} {ea : α → Word} {f g : α → ℕ}
instance instPolyTimeNatNadd {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nadd s) := by unfold Realizes.nadd;infer_instance
instance instPolyTimeNatNmul {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmul s) := by unfold Realizes.nmul;infer_instance
instance instPolyTimeNatNsub {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nsub s) := by unfold Realizes.nsub;infer_instance
instance instPolyTimeNatNdiv {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.ndiv s) := by unfold Realizes.ndiv;infer_instance
instance instPolyTimeNatNmod {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmod s) := by unfold Realizes.nmod;infer_instance
instance instPolyTimeBoolNeqOfNat {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.neq s) := by unfold Realizes.neq;infer_instance
instance instPolyTimeBoolNltOfNat {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nlt s) := by unfold Realizes.nlt;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryRoot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_schur _root_.OAI.CurrentKS.Realization.poly_schurEntry _root_.OAI.CurrentKS.Realization.poly_schurNext _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary root. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance poly_unaryRootStep (d : ℕ) : PolyTime (unaryRootStepProgram d) := by
  unfold unaryRootStepProgram
  apply poly_congr

instance size_unaryRootStep (d : ℕ) : IterateSize (unaryRootStepProgram d) := by
  refine ⟨⟨X,?_⟩⟩
  intro a k
  have h := unaryRootStep_iterate_bound d k a
  change (rootCode ((unaryRootStep d)^[k] a)).length≤(rootCode a).length+k
  simp only [rootCode,prodCode_length,natCode,List.length_replicate,h.1]
  omega

instance poly_unaryRoot (d : ℕ) (hd : d≠0) : PolyTime (unaryRoot d hd) := by
  unfold unaryRoot;infer_instance
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Feasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation feasibility. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma continuation_parameters (m : ℕ) :
    0 < continuationBaseline m ∧ continuationBaseline m ≤ 1 ∧
    continuationBaseline m*m < 1 ∧
    0 ≤ continuationStep m ∧ continuationStep m ≤ 1/32 ∧
    4*continuationStep m ≤ continuationBaseline m ∧ 4*continuationStep m*m ≤ 1 := by
  have hmp : (0:ℝ) < m+1 := by positivity
  have hκ : 0 < continuationBaseline m := one_div_pos.mpr hmp
  have hκeq : continuationBaseline m*((m:ℝ)+1)=1 := div_mul_cancel₀ 1 (ne_of_gt hmp)
  have hκm : 0 ≤ continuationBaseline m*m := mul_nonneg hκ.le (Nat.cast_nonneg m)
  have hκ1 : continuationBaseline m ≤ 1 := by nlinarith only [hκeq,hκm]
  have hκm1 : continuationBaseline m*m < 1 := by nlinarith only [hκeq,hκ]
  refine ⟨hκ,hκ1,hκm1,?_,?_,?_,?_⟩ <;> unfold continuationStep <;>
    nlinarith only [hκ,hκ1,hκm1,hκm]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation coordinates. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations

variable {n m : ℕ}

lemma dimension_bound (n m : ℕ) : dimension n m ≤ (n+m+2)^3 := by
  unfold dimension
  nlinarith [Nat.zero_le (n*n*m),Nat.zero_le (n*m*m),Nat.zero_le (m*m*m)]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Search
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation search. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations
open scoped BigOperators
variable {n m : ℕ}

lemma sizeQ_two (n m : ℕ) : 2  ≤  sizeQ n m := by
  unfold sizeQ
  linarith only [Nat.cast_nonneg (α:=ℚ) n,Nat.cast_nonneg (α:=ℚ) m]

lemma search_fuel_bound (n m : ℕ) :
    CurrentKS.RationalSDP.searchFuel (dimension n m) (radiusQ n m) (boundQ n m) ≤
      2304*(n+m+2)^114+1 := by
  let P : ℚ := sizeQ n m
  let D : ℚ := dimension n m+1
  have hP : 1 ≤ P := by linarith only [sizeQ_two n m]
  have hP0 : 0 < P := by linarith only [hP]
  have hD : 0 < D := by dsimp [D] <;> positivity
  have hd : D ≤ 2*P^3 := by
    have hh : (dimension n m:ℚ) ≤ P^3 := by
      dsimp [P, sizeQ]
      exact_mod_cast dimension_bound n m
    have hp : 1 ≤ P^3 := one_le_pow₀ hP
    dsimp only [D]
    linarith only [hh,hp]
  have he : 4*(boundQ n m)^2/(CurrentKS.RationalSDP.searchStep (dimension n m) (radiusQ n m))^2 =
      144*P^102*D^4 := by
    change 4*(6*P*D)^2/(P^(-50:ℤ)/D)^2=144*P^102*D^4
    rw [_root_.zpow_neg]
    field_simp
    ring
  have hpow := pow_le_pow_left₀ hD.le hd 4
  have hh : 4*(boundQ n m)^2/(CurrentKS.RationalSDP.searchStep (dimension n m) (radiusQ n m))^2 ≤
      (2304*(n+m+2)^114:ℕ) := by
    rw [he]
    have ht := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℚ) ≤ 144*P^102)
    have hr : 144*P^102*(2*P^3)^4=2304*P^114 := by ring
    rw [hr] at ht
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,P,sizeQ] using ht
  unfold CurrentKS.RationalSDP.searchFuel
  exact Nat.succ_le_succ ((Nat.ceil_le).mpr hh)

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GraphRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graph realization. -/

section

namespace AlgorithmicThinTrees.GraphStack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.MetricTests.RationalStep
open scoped BigOperators

instance poly_numEdges : PolyTime numEdges := by unfold numEdges;apply poly_congr

instance poly_edgeLeft : PolyTime edgeLeft := by unfold edgeLeft;apply poly_congr
instance poly_edgeRight : PolyTime edgeRight := by unfold edgeRight;apply poly_congr

instance poly_incidence : PolyTime incidence := by unfold incidence;infer_instance

instance poly_incidenceRows : PolyTime incidenceRows := by unfold incidenceRows;apply poly_tabulateFin

instance poly_laplacian : PolyTime laplacian := by unfold laplacian;apply poly_congr

instance poly_constantMatrix : PolyTime constantMatrix := by unfold constantMatrix;infer_instance

instance poly_projection : PolyTime projection := by unfold projection;infer_instance

instance poly_response : PolyTime response := by unfold response;infer_instance

end AlgorithmicThinTrees.GraphStack

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix
open scoped BigOperators

instance poly_dimensionProgram : PolyTime dimensionProgram := by
  unfold dimensionProgram Realizes.nadd
  apply poly_then

instance poly_rawEntry : PolyTime rawEntry := by unfold rawEntry;infer_instance

instance poly_raw : PolyTime raw := by unfold raw;infer_instance

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Loop
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation loop. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma stateAt_zero (H : MultiGraph n m) (r : ℕ) : stateAt H r 0=initial H r := rfl

lemma stateAt_succ (H : MultiGraph n m) (r i : ℕ) :
    stateAt H r (i+1)=advance H r (stateAt H r i) := Function.iterate_succ_apply' _ _ _

lemma advance_quality (H : MultiGraph n m) (r : ℕ) (a : State n m) :
    (a.quality:ℝ)-2*(gain r:ℝ)*r*continuationStep m ≤ ((advance H r a).quality:ℝ) ∧
    ((advance H r a).quality:ℝ) ≤ (a.quality:ℝ) := by
  have hg : 0 ≤ (gain r:ℝ) := by simp only [gain,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] <;> positivity
  have ht := (continuation_parameters m).2.2.2.1
  have hc : 0 ≤ 2*(gain r:ℝ)*r*continuationStep m := by positivity
  unfold advance
  split_ifs <;> (try simp only [update,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,cast_stepQ]) <;>
    constructor <;> linarith only [hc]

lemma stateAt_quality (H : MultiGraph n m) (r i : ℕ) :
    (r:ℝ)-(i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) ≤ ((stateAt H r i).quality:ℝ) ∧
    ((stateAt H r i).quality:ℝ) ≤ r := by
  induction i with
  | zero => simp [stateAt_zero,initial]
  | succ i ih =>
    rw [stateAt_succ]
    have hh := advance_quality H r (stateAt H r i)
    push_cast
    constructor <;> nlinarith only [ih.1,ih.2,hh.1,hh.2]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_FiniteFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_incidence _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_incidenceRows _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_laplacian _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_response _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite families. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_dite {α β : Type*} {ea : α → Word} {eb : β → Word}
    {P : α → Prop} [DecidablePred P]
    {f : {a // P a} → β} {g : {a // ¬P a} → β}
    (test : Realizes ea boolCode (fun a => decide (P a)))
    (r : Realizes (fun a : {a // P a} => ea a.val) eb f)
    (s : Realizes (fun a : {a // ¬P a} => ea a.val) eb g)
    [PolyTime test] [PolyTime r] [PolyTime s] : PolyTime (test.dite r s) := by
  refine ⟨?_⟩
  exact (RunsPoly.dite_families
    (RunsPoly.of_poly test id (isPoly_self (fun a => (ea a).length)))
    (RunsPoly.of_poly r id (isPoly_self (fun a : {a // P a} => (ea a.val).length)))
    (RunsPoly.of_poly s id (isPoly_self (fun a : {a // ¬P a} => (ea a.val).length)))).cost

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
variable {I J : α → Type*} {n m : α → ℕ}

instance poly_indexedFirst (e : (a : α) → I a ≃ Fin (n a)) :
    PolyTime (indexedFirst (ea:=ea) e) := by unfold indexedFirst;apply poly_reindex
instance poly_indexedIndex (e : (a : α) → I a ≃ Fin (n a)) :
    PolyTime (indexedIndex (ea:=ea) e) := by unfold indexedIndex;apply poly_reindex

instance poly_tabulateIndexed {e : (a : α) → I a ≃ Fin (n a)} {f : (Σ a,I a) → β}
    (r : Realizes (indexedCode ea e) eb f) (rn : Realizes ea natCode n)
    [PolyTime r] [PolyTime rn] : PolyTime (r.tabulateIndexed rn) := by
  unfold Realizes.tabulateIndexed
  refine @poly_tabulateFin _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_reindex
  · infer_instance

instance poly_indexedSumTest (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rn : Realizes ea natCode n) [PolyTime rn] :
    PolyTime (indexedSumTest e e' rn) := by unfold indexedSumTest;infer_instance

instance poly_indexedSumRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rn : Realizes ea natCode n) [PolyTime rn] :
    PolyTime (indexedSumRight e e' rn) := by unfold indexedSumRight;infer_instance

instance poly_sumCases {e : (a : α) → I a ≃ Fin (n a)}
    {e' : (a : α) → J a ≃ Fin (m a)} {f : (Σ a,I a) → β} {g : (Σ a,J a) → β}
    (r : Realizes (indexedCode ea e) eb f) (s : Realizes (indexedCode ea e') eb g)
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime s] [PolyTime rn] :
    PolyTime (r.sumCases s rn) := by unfold Realizes.sumCases;infer_instance

instance poly_splitProduct (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (splitProduct e e' rm) := by unfold splitProduct;infer_instance

instance poly_indexedProductLeft (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (indexedProductLeft e e' rm) := by unfold indexedProductLeft;infer_instance

instance poly_indexedProductRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (indexedProductRight e e' rm) := by unfold indexedProductRight;apply poly_changeOutput

instance poly_not {P : α → Prop} [DecidablePred P]
    (r : Realizes ea boolCode (fun a => decide (P a))) [PolyTime r] : PolyTime r.not := by
  unfold Realizes.not;infer_instance

instance poly_and {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) [PolyTime r] [PolyTime s] : PolyTime (r.and s) := by
  unfold Realizes.and;infer_instance

instance poly_finEq {n : α → ℕ} {f g : (a : α) → Fin (n a)}
    (r : Realizes ea natCode (fun a => (f a).val))
    (s : Realizes ea natCode (fun a => (g a).val)) [PolyTime r] [PolyTime s] :
    PolyTime (r.finEq s) := by unfold Realizes.finEq;infer_instance
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil parameters. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

private instance poly_paramsGraph : PolyTime paramsGraph := by
  unfold paramsGraph
  apply poly_then

private instance poly_paramsN : PolyTime paramsN := by
  unfold paramsN
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · unfold numVertices
    apply poly_then

private instance poly_paramsM : PolyTime paramsM := by
  unfold paramsM
  apply poly_then

instance poly_paramsField (k : ℕ) : PolyTime (paramsField k) := by unfold paramsField;apply poly_then
private instance poly_pointParams : PolyTime pointParams := by
  unfold pointParams
  apply poly_then

instance poly_pointParser : PolyTime pointParser := by
  have : PolyTime paramsDim := by unfold paramsDim; apply poly_then
  unfold pointParser
  apply poly_changeOutput

variable {α : Type*} {ea : α → Word} {p : α → Point}
instance poly_coordinate (rp : Realizes ea pointCode p)
    (i : (a : α) → Fin (dimension (p a).p.graph.n (p a).p.graph.m))
    (ri : Realizes ea natCode (fun a => (i a).val)) [PolyTime rp] [PolyTime ri] :
    PolyTime (coordinate rp i ri) := by unfold coordinate;apply poly_congr

instance poly_rawPoint : PolyTime rawPoint := by
  have : PolyTime pointN := by unfold pointN; apply poly_then
  have : PolyTime pointM := by unfold pointM; apply poly_then
  unfold rawPoint
  apply poly_changeOutput
instance poly_differenceVector {α : Type*} {ea : α → Word} {d : α → ℕ}
    (rn : Realizes ea natCode d) (i j : (a : α) → Fin (d a))
    (ri : Realizes ea natCode (fun a => (i a).val))
    (rj : Realizes ea natCode (fun a => (j a).val))
    [PolyTime rn] [PolyTime ri] [PolyTime rj] : PolyTime (differenceVector rn i j ri rj) := by
  unfold differenceVector;infer_instance
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_PointPrograms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine
variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_cons {f : α → β} {g : α → List β}
    (r : Realizes ea eb f) (s : Realizes ea (listCode eb) g) [PolyTime r] [PolyTime s] :
    PolyTime (r.cons s) := by unfold Realizes.cons;infer_instance

instance poly_select3 {i : α → Fin 3} (ri : Realizes ea natCode (fun a => (i a).val))
    {f g h : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g)
    (t : Realizes ea ratCode h) [PolyTime ri] [PolyTime r] [PolyTime s] [PolyTime t] :
    PolyTime (select3 ri r s t) := by unfold select3;apply poly_congr

instance poly_select7 {i : α → Fin 7} (ri : Realizes ea natCode (fun a => (i a).val))
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : α → ℚ}
    (r₀ : Realizes ea ratCode f₀) (r₁ : Realizes ea ratCode f₁) (r₂ : Realizes ea ratCode f₂)
    (r₃ : Realizes ea ratCode f₃) (r₄ : Realizes ea ratCode f₄) (r₅ : Realizes ea ratCode f₅)
    (r₆ : Realizes ea ratCode f₆) [PolyTime ri] [PolyTime r₀] [PolyTime r₁] [PolyTime r₂]
    [PolyTime r₃] [PolyTime r₄] [PolyTime r₅] [PolyTime r₆] :
    PolyTime (select7 ri r₀ r₁ r₂ r₃ r₄ r₅ r₆) := by unfold select7;apply poly_congr
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {a : α → Point}

private theorem poly_nadd_explicit {f g : α → ℕ}
    {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.nadd s) := by
  have := hr
  have := hs
  infer_instance

private theorem poly_nmul_explicit {f g : α → ℕ}
    {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.nmul s) := by
  have := hr
  have := hs
  infer_instance

instance poly_edgeCoord (p : Fin 3) (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (edgeCoord p r e re) := by
  have hn : PolyTime (r.then pointN) := by infer_instance
  have hm : PolyTime (r.then pointM) := by infer_instance
  unfold edgeCoord
  refine @poly_coordinate _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · exact poly_nadd_explicit (poly_nmul_explicit hn hn)
      (poly_nadd_explicit (poly_nmul_explicit hn (poly_nmul_explicit hn hn))
        (poly_nadd_explicit ‹PolyTime re›
          (poly_nmul_explicit hm (poly_constant ea natCode p.val))))

instance poly_flowCoord (p : Fin 2) (r : Realizes ea pointCode a)
    (v : (b : α) → Fin (a b).p.graph.n) (e : (b : α) → Fin (a b).p.graph.m)
    (rv : Realizes ea natCode (fun b => (v b).val)) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime rv] [PolyTime re] : PolyTime (flowCoord p r v e rv re) := by
  have hn : PolyTime (r.then pointN) := by infer_instance
  have hm : PolyTime (r.then pointM) := by infer_instance
  unfold flowCoord
  refine @poly_coordinate _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · exact poly_nadd_explicit (poly_nmul_explicit hn hn)
      (poly_nadd_explicit (poly_nmul_explicit hn (poly_nmul_explicit hn hn))
        (poly_nadd_explicit (poly_nmul_explicit (poly_constant ea natCode 3) hm)
          (poly_nadd_explicit (poly_nadd_explicit ‹PolyTime re› (poly_nmul_explicit hm ‹PolyTime rv›))
            (poly_nmul_explicit (poly_nmul_explicit hn hm) (poly_constant ea natCode p.val)))))

instance poly_storedU (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (storedU r e re) := by unfold storedU;apply poly_congr

instance poly_graphEdge (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (graphEdge r e re) := by unfold graphEdge;apply poly_changeOutput

instance poly_tripleCoordinate : PolyTime tripleCoordinate := by
  have hi : PolyTime tripleI := by infer_instance
  have hj : PolyTime tripleJ := by infer_instance
  have hk : PolyTime tripleK := by infer_instance
  have hn : PolyTime (triplePoint.then pointN) := by infer_instance
  unfold tripleCoordinate
  refine @poly_coordinate _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · exact poly_nadd_explicit (poly_nmul_explicit hn hn)
      (poly_nadd_explicit (poly_nadd_explicit hk (poly_nmul_explicit hn hj))
        (poly_nmul_explicit (poly_nmul_explicit hn hn) hi))

instance poly_tripleDistinct : PolyTime tripleDistinct := by
  have : PolyTime tripleI := by infer_instance
  have : PolyTime tripleJ := by infer_instance
  have : PolyTime tripleK := by infer_instance
  unfold tripleDistinct
  refine @poly_and _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_and _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_not

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_BlockAssembly
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_incidence _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_incidenceRows _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_laplacian _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_response _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_coordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_differenceVector _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeCoord _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_flowCoord _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsField _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParser _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawPoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_storedU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleCoordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleDistinct _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_cons _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_select3 _root_.OAI.CurrentKS.Realization.poly_select7 _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsM _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsN _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block assembly. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix KS.W23

instance poly_stK : PolyTime stK := by unfold stK;infer_instance
instance poly_stCut : PolyTime stCut := by unfold stCut;infer_instance

instance poly_stitchedMatrixEntry : PolyTime stitchedMatrixEntry := by
  have : PolyTime stI := by infer_instance
  have : PolyTime stJ := by infer_instance
  have : PolyTime stMatrices := by infer_instance
  unfold stitchedMatrixEntry;infer_instance

instance poly_stitchProgramEntry : PolyTime stitchProgramEntry := by
  have : PolyTime stI := by infer_instance
  have : PolyTime stJ := by infer_instance
  have : PolyTime stScalars := by infer_instance
  unfold stitchProgramEntry;infer_instance

instance poly_stitchProgram : PolyTime stitchProgram := by
  unfold stitchProgram
  apply poly_then

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_MatrixConstraintRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_stCut _root_.OAI.CurrentKS.Realization.poly_stK _root_.OAI.CurrentKS.Realization.poly_stitchProgram _root_.OAI.CurrentKS.Realization.poly_stitchProgramEntry _root_.OAI.CurrentKS.Realization.poly_stitchedMatrixEntry _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix constraint realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {I : α → Type*} [∀a,Fintype (I a)]
instance poly_sumIndexedMatrices {n d : α → ℕ} {e : (a : α) → I a ≃ Fin (n a)}
    {A : (a : α) → I a → Matrix (Fin (d a)) (Fin (d a)) ℚ}
    (r : Realizes (indexedCode ea e) matrixCode (fun a => matrixData (A a.1 a.2)))
    (rn : Realizes ea natCode n) (rd : Realizes ea natCode d)
    [PolyTime r] [PolyTime rn] [PolyTime rd] : PolyTime (r.sumIndexedMatrices rn rd) := by
  unfold Realizes.sumIndexedMatrices;infer_instance
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

namespace Stack

instance poly_triangleMatrixProgram : PolyTime triangleMatrixProgram := by
  have hi : PolyTime tripleI := by infer_instance
  have hj : PolyTime tripleJ := by infer_instance
  have hk : PolyTime tripleK := by infer_instance
  have hn : PolyTime (triplePoint.then pointN) := by infer_instance
  have hij : PolyTime ((differenceVector (triplePoint.then pointN)
      (fun p => p.2.1) (fun p => p.2.2.1) tripleI tripleJ).then Normalization.Stack.outer) := by
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · exact @poly_differenceVector _ _ _ _ _ _ _ _ hn hi hj
    · infer_instance
  have hjk : PolyTime ((differenceVector (triplePoint.then pointN)
      (fun p => p.2.2.1) (fun p => p.2.2.2) tripleJ tripleK).then Normalization.Stack.outer) := by
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · exact @poly_differenceVector _ _ _ _ _ _ _ _ hn hj hk
    · infer_instance
  have hik : PolyTime ((differenceVector (triplePoint.then pointN)
      (fun p => p.2.1) (fun p => p.2.2.2) tripleI tripleK).then Normalization.Stack.outer) := by
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · exact @poly_differenceVector _ _ _ _ _ _ _ _ hn hi hk
    · infer_instance
  unfold triangleMatrixProgram
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  apply poly_then

instance poly_weightedTriangleProgram : PolyTime weightedTriangleProgram := by
  unfold weightedTriangleProgram;infer_instance

instance poly_triangleSum : PolyTime triangleSum := by unfold triangleSum;infer_instance

instance poly_lowerMatrix : PolyTime lowerMatrix := by unfold lowerMatrix;infer_instance

instance poly_upperMatrix : PolyTime upperMatrix := by unfold upperMatrix;infer_instance

instance poly_edgeMatrix : PolyTime edgeMatrix := by
  have hp : PolyTime (indexedFirst (ea:=pointCode) eEquiv) := by infer_instance
  have he : PolyTime (indexedIndex (ea:=pointCode) eEquiv) := by infer_instance
  unfold edgeMatrix
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  refine @poly_ite _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · refine @poly_lt _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · exact @poly_storedU _ _ _ _ _ _ hp he
  · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply poly_then
      · refine @poly_scaleMatrix _ _ _ _ _ _ ?_ ?_
        · refine @poly_mul _ _ _ _ _ _ ?_ ?_
          · refine @poly_mul _ _ _ _ _ _ ?_ ?_
            · infer_instance
            · refine @poly_then _ _ _ _ _ _ _ _ _ _ hp ?_
              unfold pointS paramsS
              refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
              · infer_instance
              · apply poly_paramsField
          · exact @poly_edgeCoord _ _ _ _ _ _ _ hp he
        · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
          · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
            · exact @poly_graphEdge _ _ _ _ _ _ hp he
            · infer_instance
          · infer_instance
    · infer_instance
  · infer_instance

instance poly_specialMatrix : PolyTime specialMatrix := by unfold specialMatrix;infer_instance

instance poly_matrixConstraints : PolyTime matrixConstraints := by unfold matrixConstraints;infer_instance
end Stack
end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_ScalarConstraintRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_lowerMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixConstraints _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_specialMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_triangleMatrixProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_triangleSum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_upperMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_weightedTriangleProgram _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_stCut _root_.OAI.CurrentKS.Realization.poly_stK _root_.OAI.CurrentKS.Realization.poly_stitchProgram _root_.OAI.CurrentKS.Realization.poly_stitchProgramEntry _root_.OAI.CurrentKS.Realization.poly_stitchedMatrixEntry _root_.OAI.CurrentKS.Realization.poly_sumIndexedMatrices _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar constraint realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

private theorem scalar_poly_pointField (k : ℕ) : PolyTime (pointParams.then (paramsField k)) := by
  apply poly_then

instance poly_scalarTriple : PolyTime scalarTriple := by unfold scalarTriple;infer_instance

private theorem poly_esE : PolyTime esE := by
  unfold esE
  apply poly_then

instance poly_esY : PolyTime esY := by
  unfold esY
  refine @poly_edgeCoord _ _ _ _ _ _ _ ?_ poly_esE
  infer_instance
instance poly_esZ : PolyTime esZ := by
  unfold esZ
  refine @poly_edgeCoord _ _ _ _ _ _ _ ?_ poly_esE
  infer_instance
instance poly_esX : PolyTime esX := by
  unfold esX
  refine @poly_edgeCoord _ _ _ _ _ _ _ ?_ poly_esE
  infer_instance
instance poly_esU : PolyTime esU := by
  unfold esU
  refine @poly_storedU _ _ _ _ _ _ ?_ poly_esE
  infer_instance
instance poly_esActive : PolyTime esActive := by unfold esActive;infer_instance

instance poly_esCapacityRate : PolyTime esCapacityRate := by
  have hk : PolyTime pointK := scalar_poly_pointField 1
  have : PolyTime esK := by unfold esK; apply poly_then
  have ht : PolyTime pointT := scalar_poly_pointField 2
  have : PolyTime esT := by unfold esT; apply poly_then
  unfold esCapacityRate;infer_instance

instance poly_esCapacity : PolyTime esCapacity := by
  have hk : PolyTime pointK := scalar_poly_pointField 1
  have : PolyTime esK := by unfold esK; apply poly_then
  unfold esCapacity
  apply poly_congr

instance poly_scalarEdge : PolyTime scalarEdge := by
  have : PolyTime esP := by infer_instance
  have hk : PolyTime pointK := scalar_poly_pointField 1
  have : PolyTime esK := by unfold esK; apply poly_then
  unfold scalarEdge;infer_instance

private theorem poly_reR : PolyTime reR := by
  unfold reR
  apply poly_then

private theorem poly_reE : PolyTime reE := by
  unfold reE
  apply poly_then

instance poly_reA : PolyTime reA := by
  unfold reA
  refine @poly_flowCoord _ _ _ _ _ _ _ _ _ ?_ poly_reR poly_reE
  infer_instance
instance poly_reB : PolyTime reB := by
  unfold reB
  refine @poly_flowCoord _ _ _ _ _ _ _ _ _ ?_ poly_reR poly_reE
  infer_instance
instance poly_reX : PolyTime reX := by
  unfold reX
  refine @poly_edgeCoord _ _ _ _ _ _ _ ?_ poly_reE
  infer_instance

instance poly_scalarFlow : PolyTime scalarFlow := by
  have : PolyTime fsP := by infer_instance
  have : PolyTime fsRE := by infer_instance
  unfold scalarFlow;infer_instance

instance poly_beA : PolyTime beA := by
  have hr : PolyTime beR := by infer_instance
  unfold beA
  refine @poly_flowCoord _ _ _ _ _ _ _ _ _ ?_ hr ?_
  all_goals infer_instance
instance poly_beB : PolyTime beB := by
  have hr : PolyTime beR := by infer_instance
  unfold beB
  refine @poly_flowCoord _ _ _ _ _ _ _ _ _ ?_ hr ?_
  all_goals infer_instance

instance poly_budgetEdge : PolyTime budgetEdge := by
  have : PolyTime beGraphEdge := by infer_instance
  have : PolyTime beV := by infer_instance
  unfold budgetEdge;infer_instance

instance poly_budgetIncoming : PolyTime budgetIncoming := by unfold budgetIncoming;infer_instance

instance poly_scalarBudget : PolyTime scalarBudget := by
  have : PolyTime bsV := by infer_instance
  have : PolyTime bsR := by infer_instance
  have hq : PolyTime pointQ := scalar_poly_pointField 3
  have he : PolyTime pointE := scalar_poly_pointField 4
  unfold scalarBudget
  apply poly_congr

instance poly_edgeTotal : PolyTime edgeTotal := by unfold edgeTotal;infer_instance

instance poly_scalarTotalBase : PolyTime scalarTotalBase := by
  have hq : PolyTime pointQ := scalar_poly_pointField 3
  have he : PolyTime pointE := scalar_poly_pointField 4
  unfold scalarTotalBase
  apply poly_congr

instance poly_scalarTotal : PolyTime scalarTotal := by unfold scalarTotal; apply poly_congr

instance poly_scalarConstraints : PolyTime scalarConstraints := by unfold scalarConstraints;infer_instance

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack

instance poly_matrixCount : PolyTime matrixCount := by unfold matrixCount;infer_instance
instance poly_scalarCount : PolyTime scalarCount := by unfold scalarCount;infer_instance

instance poly_affinePoint : PolyTime affinePoint := by
  have : PolyTime pointN := by infer_instance
  unfold affinePoint;infer_instance

instance poly_pencilEval : PolyTime pencilEval := by unfold pencilEval;infer_instance

instance poly_buildPencil : PolyTime buildPencil := by unfold buildPencil;infer_instance
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Search realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

instance poly_graphRadius : PolyTime graphRadius := by unfold graphRadius;infer_instance

instance poly_graphBound : PolyTime graphBound := by
  unfold graphBound
  refine @poly_mul _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_add _ _ _ _ _ _ ?_ ?_
    · apply poly_then
    · infer_instance

instance poly_graphZeros : PolyTime graphZeros := by unfold graphZeros;infer_instance

instance poly_initializeSearch : PolyTime initializeSearch := by unfold initializeSearch; apply poly_changeOutput

lemma isPoly_graph_n : IsPoly (fun G => (graphCode G).length) Graph.n := by
  have h := (RunsPoly.of_poly numVertices id (isPoly_self (fun G => (graphCode G).length))).output
  simpa only [id_eq,natCode,List.length_replicate,Graph.data] using h
lemma isPoly_graph_m : IsPoly (fun G => (graphCode G).length) Graph.m := by
  have h := (RunsPoly.of_poly numEdges id (isPoly_self (fun G => (graphCode G).length))).output
  simpa only [id_eq,natCode,List.length_replicate,Graph.data] using h
lemma isPoly_graph_fuel : IsPoly (fun G => (graphCode G).length)
    (fun G => CurrentKS.RationalSDP.searchFuel (dimension G.n G.m) (radiusQ G.n G.m) (boundQ G.n G.m)) := by
  have hP := (isPoly_graph_n.add isPoly_graph_m).add (isPoly_const _ 2)
  exact (((isPoly_const _ 2304).mul (hP.pow 114)).add (isPoly_const _ 1)).mono
    (fun G => search_fuel_bound G.n G.m)

instance poly_solvePencil : PolyTime solvePencil := by
  let L := fun p => (paramsCode p).length
  have hi := RunsPoly.of_poly initializeSearch id (isPoly_self L)
  have hg := RunsPoly.of_poly paramsGraph id (isPoly_self L)
  obtain ⟨q,hq⟩ := isPoly_graph_fuel
  have hf := (hg.output.eval q).mono (fun p => hq p.graph)
  exact ⟨(hi.then (runsPoly_search Params.searchState hi.output hf)).cost⟩

instance poly_gridStep : PolyTime gridStep := by unfold gridStep;infer_instance

instance poly_gridMesh : PolyTime gridMesh := by unfold gridMesh;infer_instance

lemma search_parts_bound : ∃q : NaturalPolynomial, ∀p : Params, ∀i,
    QParts (q.eval (graphCode p.graph).length)
      (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0 i) := by
  have hc := (RunsPoly.of_poly (gridStep.both gridMesh) id
    (isPoly_self (fun G => (graphCode G).length))).output
  obtain ⟨b,hb⟩ := hc
  obtain ⟨f,hf⟩ := isPoly_graph_fuel
  refine ⟨3*b+f+1,?_⟩
  intro p i
  let H := b.eval (graphCode p.graph).length
  have hstep : QParts H (CurrentKS.RationalSDP.searchStep (dimension p.graph.n p.graph.m) (radiusQ p.graph.n p.graph.m)) :=
    (qparts_length _).mono ((le_prodCode_left _).trans (hb p.graph))
  have hmesh : QParts H (CurrentKS.RationalSDP.searchMesh (dimension p.graph.n p.graph.m) (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m)) :=
    (qparts_length _).mono ((le_prodCode_right _).trans (hb p.graph))
  apply (pencil_iterate_parts p.pencil _ _ 0 hstep hmesh (fun _ => qparts_zero H) _ i).mono
  change 3*H+_+1 ≤ 3*H+f.eval _+1
  exact Nat.add_le_add_right (Nat.add_le_add_left (hf p.graph) _) _

lemma search_output_bound : ∃q : NaturalPolynomial, ∀p : Params,
    (vectorCode (List.ofFn (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0))).length ≤
      q.eval (graphCode p.graph).length := by
  obtain ⟨b,hb⟩ := search_parts_bound
  obtain ⟨d,hd⟩ := (RunsPoly.of_poly graphDim id
    (isPoly_self (fun G => (graphCode G).length))).output
  refine ⟨d*(2*(4*b+7)+1),?_⟩
  intro p
  have h := listCode_length_bound (List.ofFn
    (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0))
      (4*b.eval (graphCode p.graph).length+7) (by
        intro q hq; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq;exact (hb p i).length)
  rw [List.length_ofFn] at h
  exact h.trans (Nat.mul_le_mul_right _ (by simpa only [id_eq,natCode,List.length_replicate,Graph.data] using hd p.graph))
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

private instance poly_graphBaseline : PolyTime graphBaseline := by
  unfold graphBaseline
  apply poly_div

private instance poly_graphStep : PolyTime graphStep := by
  unfold graphStep
  apply poly_div

instance poly_graphError : PolyTime graphError := by unfold graphError;infer_instance

instance poly_gainProgram : PolyTime gainProgram := by unfold gainProgram; apply poly_div

instance poly_clockProgram : PolyTime clockProgram := by
  unfold clockProgram Realizes.nmul
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_then
  · infer_instance

private instance poly_loopGraph : PolyTime loopGraph := by
  unfold loopGraph
  apply poly_then

private instance poly_loopCount : PolyTime loopCount := by
  unfold loopCount
  apply poly_then

private instance poly_loopScale : PolyTime loopScale := by
  unfold loopScale
  apply poly_then

private instance poly_loopQuality : PolyTime loopQuality := by
  unfold loopQuality
  apply poly_then

private instance poly_loopTarget : PolyTime loopTarget := by
  unfold loopTarget
  apply poly_sub

instance poly_loopParams : PolyTime loopParams := by unfold loopParams; apply poly_changeOutput

instance poly_found : PolyTime found := by unfold found; apply poly_congr

instance poly_updatedMatrix : PolyTime updatedMatrix := by unfold updatedMatrix; apply poly_congr

instance poly_updatedCapacity : PolyTime updatedCapacity := by
  have hf : PolyTime (edgeLoop.then found) := by apply poly_then
  have he : PolyTime edgeNumber := by infer_instance
  unfold updatedCapacity
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  refine @poly_ite _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · refine @poly_lt _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · exact @poly_storedU _ _ _ _ _ _ hf he
  · refine @poly_max _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · refine @poly_sub _ _ _ _ _ _ ?_ ?_
      · exact @poly_edgeCoord _ _ _ _ _ _ _ hf he
      · infer_instance
  · infer_instance

instance poly_updateProgram : PolyTime updateProgram := by unfold updateProgram; apply poly_changeOutput

instance poly_next : PolyTime next := by unfold next; apply poly_congr

instance poly_initializeLoop : PolyTime initializeLoop := by unfold initializeLoop;infer_instance

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_BitBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation bit bound. -/

section

namespace CurrentKS.Realization
open CleanRoutine
lemma QParts.neg {b : ℕ} {q : ℚ} (h : QParts b q) : QParts b (-q) := by
  simpa only [QParts,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using h
lemma QParts.sub {b c : ℕ} {q v : ℚ} (h : QParts b q) (hv : QParts c v) :
    QParts (b+c+1) (q-v) := by simpa only [sub_eq_add_neg] using h.add hv.neg
lemma QParts.max {b : ℕ} {q v : ℚ} (h : QParts b q) (hv : QParts b v) :
    QParts b (max q v) := by
  rcases le_total q v with hl|hl
  · simpa only [max_eq_right hl] using hv
  · simpa only [max_eq_left hl] using h
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

instance poly_meshRaw : PolyTime meshRaw := by
  have hg : PolyTime meshGraph := by unfold meshGraph; apply poly_then
  have hv : PolyTime meshVector := by unfold meshVector; apply poly_then
  unfold meshRaw
  apply poly_changeOutput

lemma response_parts_bound : ∃b : NaturalPolynomial,∀p : Params,∀i j,
    QParts (b.eval (graphCode p.graph).length)
      (qresponse (rawMatrix (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0)) i j) := by
  let a := fun p : Params => MeshPoint.mk p.graph
    (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0)
  have hin := isPoly_pair (isPoly_self (fun p : Params => (graphCode p.graph).length)) search_output_bound
  have hout := (RunsPoly.of_poly (meshRaw.then GraphStack.response) a hin).output
  obtain ⟨b,hb⟩ := hout
  refine ⟨b,?_⟩
  intro p i j
  have hh := matrixParts_length (matrixData (qresponse (rawMatrix (a p).v)))
  exact (hh _ (List.mem_ofFn.mpr ⟨i,rfl⟩) _ (List.mem_ofFn.mpr ⟨j,rfl⟩)).mono (hb p)

lemma coefficients_parts_bound : ∃b : NaturalPolynomial,∀G r,
    let B := b.eval (extractionInputCode (G,r)).length
    QParts B (1+stepQ G.m) ∧ QParts B (1-stepQ G.m) ∧
      QParts B (2*gain r*r*stepQ G.m) ∧ QParts B (stepQ G.m) ∧ QParts B (baselineQ G.m) := by
  obtain ⟨b,hb⟩ := (RunsPoly.of_poly coefficients id
    (isPoly_self (fun p => (extractionInputCode p).length))).output
  refine ⟨b,?_⟩
  intro G r
  have hh : ∀q∈[1+stepQ G.m,1-stepQ G.m,2*gain r*r*stepQ G.m,stepQ G.m,baselineQ G.m],
      QParts (b.eval (extractionInputCode (G,r)).length) q := by
    intro q hq
    exact (qparts_length q).mono ((mem_length_le_code _ hq).trans (hb (G,r)))
  exact ⟨hh _ (by simp),hh _ (by simp),hh _ (by simp),hh _ (by simp),hh _ (by simp)⟩

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open CurrentKS.Realization
open CurrentKS.CleanRoutine KS.W23
open Stack GraphStack

variable {n m : ℕ}
lemma State.Parts.mono {b c : ℕ} {a : State n m} (ha : a.Parts b) (h : b ≤ c) : a.Parts c :=
  ⟨ha.1.mono h,ha.2.1.mono h,fun i j => (ha.2.2.1 i j).mono h,fun e => (ha.2.2.2 e).mono h⟩

lemma update_parts_bound : ∃P : NaturalPolynomial,∀G : Graph,∀r a b,
    a.Parts b → (update G.G r (gain r) a).Parts
      (b+P.eval (extractionInputCode (G,r)).length) := by
  obtain ⟨c,hc⟩ := coefficients_parts_bound
  obtain ⟨v,hv⟩ := search_parts_bound
  obtain ⟨w,hw⟩ := response_parts_bound
  refine ⟨3*c+v+w+2,?_⟩
  intro G r a b ha
  let p : Params := ⟨G,a.scale,baselineQ G.m,stepQ G.m,
    target G.m r a.quality (gain r),errorQ G.n G.m,a.capacity⟩
  let L := (extractionInputCode (G,r)).length
  let C := c.eval L
  let V := v.eval L
  let W := w.eval L
  have hGl : (graphCode G).length≤L := le_prodCode_left (G,r)
  obtain ⟨hplus,hminus,hloss,ht,hbase⟩ := hc G r
  have hvec : ∀i,QParts V (search G.G a.scale (target G.m r a.quality (gain r)) a.capacity i) :=
    fun i => (hv p i).mono (v.eval_mono hGl)
  have hresp : ∀i j,QParts W (qresponse (rawMatrix (search G.G a.scale
      (target G.m r a.quality (gain r)) a.capacity)) i j) :=
    fun i j => (hw p i j).mono (w.eval_mono hGl)
  change (update G.G r (gain r) a).Parts (b+(3*C+V+W+2))
  refine ⟨(hplus.mul ha.1).mono (by dsimp [C,V,W,L];omega),(ha.2.1.sub hloss).mono (by dsimp [C,V,W,L];omega),?_,?_⟩
  · intro i j
    exact ((hminus.mul (ha.2.2.1 i j)).add (ht.mul (hresp i j))).mono (by dsimp [C,V,W,L];omega)
  · intro e
    change QParts _ (if 0<a.capacity e then max 0 (_-baselineQ G.m) else 0)
    split
    · exact ((qparts_zero (V+C+1)).max ((hvec (edgeIndex 1 e)).sub hbase)).mono (by dsimp [C,V,W,L];omega)
    · exact qparts_zero _

lemma advance_parts {P : NaturalPolynomial}
    (hP : ∀G : Graph,∀r a b, a.Parts b → (update G.G r (gain r) a).Parts
      (b+P.eval (extractionInputCode (G,r)).length))
    (G : Graph) (r : ℕ) {a : State G.n G.m} {b : ℕ} (ha : a.Parts b) :
    ∀k, ((advance G.G r)^[k] a).Parts (b+k*P.eval (extractionInputCode (G,r)).length) := by
  intro k
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [advance]
    split
    · simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hP G r _ _ ih
    · exact ih.mono (by simp only [Nat.add_mul,Nat.one_mul];omega)

end AlgorithmicThinTrees.MetricTests.RationalStep

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

lemma loop_parts (a : Loop) : a.state.Parts (loopCode a).length := by
  let L := (loopCode a).length
  have ht : (loopTailCode a.data.2.2).length≤L :=
    (le_prodCode_right a.data.2).trans (le_prodCode_right a.data)
  have hq := (le_prodCode_right a.data.2.2).trans ht
  have harr := (le_prodCode_right a.data.2.2.2).trans hq
  have hs := (le_prodCode_left a.data.2.2).trans ht
  have hQ := (le_prodCode_left a.data.2.2.2).trans hq
  have hmat := (le_prodCode_left a.data.2.2.2.2).trans harr
  have hcap := (le_prodCode_right a.data.2.2.2.2).trans harr
  refine ⟨(qparts_length _).mono hs,(qparts_length _).mono hQ,?_,?_⟩
  · intro i j
    exact ((matrixParts_length (matrixData a.state.matrix)) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
      _ (List.mem_ofFn.mpr ⟨j,rfl⟩)).mono hmat
  · intro e
    exact (qparts_length _).mono ((mem_length_le_code (List.ofFn a.state.capacity)
      (List.mem_ofFn.mpr ⟨e,rfl⟩)).trans hcap)

lemma loop_parts_length (a : Loop) {b : ℕ} (hb : a.state.Parts b) :
    (loopCode a).length ≤ 2*(graphCode a.graph).length+1+2*a.count+1+
      (4*(4*b+7)+3+2*(a.graph.n*(2*(a.graph.n*(2*(4*b+7)+1))+1))+
        a.graph.m*(2*(4*b+7)+1)) := by
  have hmat := matrixCode_parts_bound a.state.matrix hb.2.2.1
  have hvec := listCode_length_bound (List.ofFn a.state.capacity) (4*b+7)
    (by intro q hq;obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq;exact (hb.2.2.2 e).length)
  rw [List.length_ofFn] at hvec
  change (vectorCode (List.ofFn a.state.capacity)).length ≤ _ at hvec
  have hs := hb.1.length
  have hq := hb.2.1.length
  simp only [loopCode,loopDataCode,Loop.data,loopTailCode,prodCode_length,natCode,List.length_replicate]
  omega

instance size_next : IterateSize next := by
  obtain ⟨P,hP⟩ := update_parts_bound
  let L := fun u : Loop×ℕ => (loopCode u.1).length+u.2
  have ha : IsPoly L (fun u => (loopCode u.1).length) := (isPoly_self L).mono (fun u => Nat.le_add_right _ _)
  have hk : IsPoly L Prod.snd := (isPoly_self L).mono (fun u => Nat.le_add_left _ _)
  have hg := (RunsPoly.of_poly loopGraph Prod.fst ha).output
  have hr := (RunsPoly.of_poly loopCount Prod.fst ha).output
  have hr' : IsPoly L (fun u => u.1.count) := by simpa only [natCode,List.length_replicate] using hr
  have hpar := isPoly_pair hg hr
  have hn := ((RunsPoly.of_poly numVertices (fun u : Loop×ℕ => u.1.graph) hg).output)
  have hm := ((RunsPoly.of_poly numEdges (fun u : Loop×ℕ => u.1.graph) hg).output)
  have hn' : IsPoly L (fun u => u.1.graph.n) := by simpa only [natCode,List.length_replicate,Graph.data] using hn
  have hm' : IsPoly L (fun u => u.1.graph.m) := by simpa only [natCode,List.length_replicate,Graph.data] using hm
  have hb := ha.add (hk.mul (hpar.eval P))
  have hrat := ((isPoly_const L 4).mul hb).add (isPoly_const L 7)
  have helem := ((isPoly_const L 2).mul hrat).add (isPoly_const L 1)
  have hmat := hn'.mul (((isPoly_const L 2).mul (hn'.mul helem)).add (isPoly_const L 1))
  have hvec := hm'.mul helem
  have htotal := (((((isPoly_const L 2).mul hg).add (isPoly_const L 1)).add
    ((isPoly_const L 2).mul hr')).add (isPoly_const L 1)).add
      (((((isPoly_const L 4).mul hrat).add (isPoly_const L 3)).add
        ((isPoly_const L 2).mul hmat)).add hvec)
  obtain ⟨Q,hQ⟩ := htotal
  refine ⟨⟨Q,?_⟩⟩
  intro a k
  rw [next_iterate]
  apply (loop_parts_length ⟨a.graph,a.count,(advance a.graph.G a.count)^[k] a.state⟩
    (advance_parts hP a.graph a.count (loop_parts a) k)).trans
  exact hQ (a,k)

instance poly_extract : PolyTime extract := by unfold extract; apply poly_congr

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_InverseRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_incidence _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_incidenceRows _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_laplacian _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_response _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_affinePoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_beA _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_beB _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_budgetEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_budgetIncoming _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_buildPencil _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_clockProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_coordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_differenceVector _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeCoord _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeTotal _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esActive _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esCapacity _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esCapacityRate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esX _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esY _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esZ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_extract _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_flowCoord _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_found _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gainProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBound _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphError _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphRadius _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphZeros _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridMesh _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_initializeLoop _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_initializeSearch _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_lowerMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixConstraints _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshRaw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_next _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsField _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pencilEval _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParser _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawPoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reA _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reB _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reX _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarBudget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarConstraints _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarFlow _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTotal _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTotalBase _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTriple _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_solvePencil _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_specialMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_storedU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_triangleMatrixProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_triangleSum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleCoordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleDistinct _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updateProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updatedCapacity _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updatedMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_upperMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_weightedTriangleProgram _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_cons _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_dite _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_select3 _root_.OAI.CurrentKS.Realization.poly_select7 _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_stCut _root_.OAI.CurrentKS.Realization.poly_stK _root_.OAI.CurrentKS.Realization.poly_stitchProgram _root_.OAI.CurrentKS.Realization.poly_stitchProgramEntry _root_.OAI.CurrentKS.Realization.poly_stitchedMatrixEntry _root_.OAI.CurrentKS.Realization.poly_sumCases _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_sumIndexedMatrices _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBaseline _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopQuality _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopScale _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopTarget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsM _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsN _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

instance poly_solveRhs : PolyTime solveRhs := by unfold solveRhs;infer_instance

instance poly_solveTopRow : PolyTime solveTopRow := by unfold solveTopRow;infer_instance

instance poly_liftColumn : PolyTime liftColumn := by
  unfold liftColumn
  apply poly_then

instance poly_inverseLift : PolyTime inverseLift := by
  unfold inverseLift
  apply poly_then

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_affinePoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_beA _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_beB _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_budgetEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_budgetIncoming _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_buildPencil _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_clockProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeTotal _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esActive _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esCapacity _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esCapacityRate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esX _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esY _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esZ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_extract _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_found _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gainProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBound _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphError _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphRadius _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphZeros _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridMesh _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_initializeLoop _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_initializeSearch _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_lowerMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixConstraints _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshRaw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_next _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pencilEval _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reA _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reB _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reX _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarBudget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarConstraints _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarFlow _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTotal _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTotalBase _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTriple _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_solvePencil _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_specialMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_triangleMatrixProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_triangleSum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updateProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updatedCapacity _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updatedMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_upperMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_weightedTriangleProgram _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgTest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_stCut _root_.OAI.CurrentKS.Realization.poly_stK _root_.OAI.CurrentKS.Realization.poly_stitchProgram _root_.OAI.CurrentKS.Realization.poly_stitchProgramEntry _root_.OAI.CurrentKS.Realization.poly_stitchedMatrixEntry _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_sumIndexedMatrices _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBaseline _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopQuality _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopScale _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopTarget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix AlgorithmicThinTrees

instance poly_firstColumn : PolyTime firstColumn := by unfold firstColumn;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_affinePoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_beA _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_beB _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_budgetEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_budgetIncoming _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_buildPencil _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_clockProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_edgeTotal _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esActive _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esCapacity _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esCapacityRate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esX _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esY _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_esZ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_extract _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_found _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gainProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBound _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphError _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphRadius _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphZeros _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridMesh _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_gridStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_initializeLoop _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_initializeSearch _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_lowerMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixConstraints _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_matrixCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshRaw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_next _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pencilEval _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reA _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reB _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_reX _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarBudget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarConstraints _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarFlow _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTotal _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTotalBase _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_scalarTriple _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_solvePencil _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_specialMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_triangleMatrixProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_triangleSum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updateProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updatedCapacity _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_updatedMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_upperMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_weightedTriangleProgram _root_.OAI.CurrentKS.Realization.poly_matrixSum _root_.OAI.CurrentKS.Realization.poly_stCut _root_.OAI.CurrentKS.Realization.poly_stK _root_.OAI.CurrentKS.Realization.poly_stitchProgram _root_.OAI.CurrentKS.Realization.poly_stitchProgramEntry _root_.OAI.CurrentKS.Realization.poly_stitchedMatrixEntry _root_.OAI.CurrentKS.Realization.poly_sumFin _root_.OAI.CurrentKS.Realization.poly_sumIndexedMatrices _root_.OAI.CurrentKS.Realization.poly_unaryRoot _root_.OAI.CurrentKS.Realization.poly_unaryRootStep _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphBaseline _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphStep _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopCount _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopQuality _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopScale _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopTarget _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

private instance poly_frameDim : PolyTime frameDim := by
  unfold frameDim
  apply poly_then

private instance poly_frameRows : PolyTime frameRows := by
  unfold frameRows
  apply poly_then

instance poly_complexField : PolyTime complexField := by unfold complexField;infer_instance

instance poly_outerFields : PolyTime outerFields := by unfold outerFields;infer_instance

instance poly_signerInput : PolyTime signerInput := by
  unfold signerInput
  apply poly_changeOutput

instance poly_stack : PolyTime stack := by
  have : PolyTime pairLeft := by unfold pairLeft; apply poly_then
  have : PolyTime pairRight := by unfold pairRight; apply poly_then
  unfold stack
  apply poly_changeOutput

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparsification realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_ratNatFloorBinary : PolyTime ratNatFloorBinary := by
  unfold ratNatFloorBinary;infer_instance

lemma runsPoly_binaryToNat {ι : Type*} {L : ι → ℕ} (a : ι → ℕ)
    (ha : IsPoly L (fun i => (binaryNatCode (a i)).length)) (hn : IsPoly L a) :
    RunsPoly L binaryToNat a := by
  refine ⟨ha,?_⟩
  exact (((isPoly_const L 6).mul hn).add ((isPoly_const L 4).mul ha)).add (isPoly_const L 4)

end CurrentKS.Realization

namespace AlgorithmicThinTrees.GraphicHalf.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree Finset
open MetricTests MetricTests.RationalStep Normalization GraphStack
open MetricTests.RationalStep.Stack

private theorem poly_problemM : PolyTime problemM := by
  unfold problemM
  apply poly_then

instance poly_problemD : PolyTime problemD := by unfold problemD; apply poly_congr

instance poly_extraction : PolyTime extraction := by unfold extraction; apply poly_then

lemma packingTarget_le (p : Problem) : p.q ≤ p.r := by
  have h := (stateAt_quality p.G p.r (scheduleLength p.m p.r)).2
  have hq : p.state.quality ≤ (p.r:ℚ) := by exact_mod_cast h
  exact (Nat.floor_mono (show p.state.quality-1 ≤ (p.r:ℚ) by linarith)).trans_eq (Nat.floor_natCast _)

instance poly_targetBinary : PolyTime targetBinary := by unfold targetBinary; apply poly_then

instance poly_targetCount : PolyTime targetCount := by
  apply PolyTime.mk
  have ht := RunsPoly.of_poly targetBinary id (isPoly_self (fun p => (problemCode p).length))
  have hn : IsPoly (fun p => (problemCode p).length) Problem.r :=
    ((RunsPoly.of_poly problemCount id (isPoly_self (fun p => (problemCode p).length))).output).mono
      (fun p => by simp only [natCode,List.length_replicate];rfl)
  exact (ht.then (runsPoly_binaryToNat _ ht.output (hn.mono packingTarget_le))).cost

instance poly_edgeGraphInput : PolyTime edgeGraphInput := by unfold edgeGraphInput; apply poly_changeOutput

instance poly_edgeActive : PolyTime edgeActive := by unfold edgeActive;infer_instance

instance poly_fullColumn : PolyTime fullColumn := by unfold fullColumn; apply poly_congr

instance poly_fullRows : PolyTime fullRows := by
  unfold fullRows
  exact @poly_tabulateFin _ _ _ _ _ _ _ _ poly_fullColumn poly_problemM

instance poly_reducedEntry : PolyTime reducedEntry := by unfold reducedEntry;infer_instance

instance poly_reducedColumn : PolyTime reducedColumn := by unfold reducedColumn;infer_instance

instance poly_reducedRows : PolyTime reducedRows := by
  unfold reducedRows
  exact @poly_tabulateFin _ _ _ _ _ _ _ _ poly_reducedColumn poly_problemM

instance poly_normalizationParams : PolyTime normalizationParams := by unfold normalizationParams; apply poly_changeOutput

instance poly_scales : PolyTime scales := by unfold scales; apply poly_then

instance poly_positiveMatrix : PolyTime positiveMatrix := by unfold positiveMatrix; apply poly_congr

instance poly_secondMatrix : PolyTime secondMatrix := by
  unfold secondMatrix
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_changeOutput
  · infer_instance

instance poly_scaledRows : PolyTime scaledRows := by unfold scaledRows;infer_instance

@[instance] theorem poly_forms_oai : PolyTime forms := by unfold forms; apply poly_changeOutput

instance poly_maskEdgeInput : PolyTime maskEdgeInput := by unfold maskEdgeInput; apply poly_changeOutput

instance poly_maskBit : PolyTime maskBit := by unfold maskBit;infer_instance

instance poly_mask : PolyTime mask := by
  have hm : PolyTime (maskProblem.then problemM) := by
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ poly_problemM
    infer_instance
  unfold mask
  exact @poly_tabulateFin _ _ _ _ _ _ _ _ poly_maskBit hm

end AlgorithmicThinTrees.GraphicHalf.Stack
end

end OAI
end

theorem solution : type_of% @OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_forms_oai := @OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_forms_oai

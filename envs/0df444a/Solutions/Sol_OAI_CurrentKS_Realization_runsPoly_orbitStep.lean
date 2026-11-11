-- Prove2me | solution 1 for OAI.CurrentKS.Realization.runsPoly_orbitStep
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:17:22.362478+00:00
-- url     : https://prove2.me/submissions/1a270b39-bdbc-43cb-9032-99fabdd5c604

import Mathlib
import Definitions.Def_OAIQ241TT014
import Theorems.Thm_OAI_CurrentKS_Realization_isPoly_face_orbit
import Theorems.Thm_OAI_CurrentKS_Realization_isPoly_orbitScore
import Theorems.Thm_OAI_CurrentKS_Realization_isPoly_orbitStencil

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
lemma isPoly_const (L : ι → ℕ) (c : ℕ) : IsPoly L (fun _ => c) := ⟨.constant c,fun _ => le_rfl⟩
lemma isPoly_self (L : ι → ℕ) : IsPoly L L := ⟨X,fun _ => le_rfl⟩
lemma IsPoly.eval (hf : IsPoly L f) (p : NaturalPolynomial) : IsPoly L (fun i => p.eval (f i)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,fun i => by simpa only [NaturalPolynomial.eval_comp] using p.eval_mono (hq i)⟩
lemma IsPoly.reindex {κ : Type*} (hf : IsPoly L f) (a : κ → ι) : IsPoly (L ∘ a) (f ∘ a) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => hp (a i)⟩
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
lemma RunsPoly.reindex {r : Realizes ea eb F} {δ : Type*} (ed : δ → Word) (g : δ → α)
    (h : ∀x,ed x=ea (g x)) {a : ι → δ} (hr : RunsPoly L r (fun i => g (a i))) :
    RunsPoly L (r.reindex ed g h) a := by
  refine ⟨?_,hr.cost⟩
  simpa only [h] using hr.input
lemma Realizes.congr_cost {r : Realizes ea eb F} {F' : α → β} (h : ∀x,F x=F' x) :
    (r.congr h).cost=r.cost := by
  have he : F=F' := funext h
  subst F'
  rfl
lemma RunsPoly.ite {P : α → Bool} {G : α → β} {b : Realizes ea boolCode P}
    {r : Realizes ea eb F} {s : Realizes ea eb G} {a : ι → α}
    (hb : RunsPoly L b a) (hr : RunsPoly L r a) (hs : RunsPoly L s a) :
    RunsPoly L (b.ite r s) a := by
  unfold Realizes.ite
  have ht := hb.both (RunsPoly.of_poly (identity ea) a hb.input)
  apply ht.then
  refine ⟨ht.output,?_⟩
  apply ((hr.cost.add hs.cost).add (isPoly_const L 6)).mono
  intro i
  change 5+(if P (a i) then r.cost (a i) else s.cost (a i))+1 ≤ r.cost (a i)+s.cost (a i)+6
  split <;> omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialArithmeticFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ} {ea : α → Word} {a : ι → α}

lemma RunsPoly.ratOp (operation : KS.W13.ExpressionMachine.BinaryOp) {input : ι → ℚ × ℚ}
    (hinput : IsPoly L (fun index => (prodCode ratCode ratCode (input index)).length)) :
    RunsPoly L (ratOp operation) input := by
  refine ⟨hinput, ?_⟩
  apply (hinput.eval (5 * NaturalPolynomial.variable +
    6000000 * (NaturalPolynomial.variable + 1) ^ 3 + 6)).mono
  intro index
  have hlength := RoutineLength.output_length
    (KS.W13.ExpressionMachine.binaryArithmetic_spec operation (input index).1 (input index).2 [] []) 10
  have houtput : (ratCode (operation.eval (input index).1 (input index).2)).length ≤
      KS.W13.ExpressionMachine.binaryBudget (input index).1 (input index).2 := by
    simpa [KS.W13.ExpressionMachine.registers] using hlength
  have hpair : (ratCode (input index).1).length + (ratCode (input index).2).length ≤
      (prodCode ratCode ratCode (input index)).length := by
    rw [prodCode_length]
    omega
  have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hpair 1) 3
  have hleft := le_prodCode_left (ea := ratCode) (eb := ratCode) (input index)
  change ArithmeticRoutine.ticks operation (input index).1 (input index).2 ≤
    5 * (prodCode ratCode ratCode (input index)).length +
      6000000 * ((prodCode ratCode ratCode (input index)).length + 1) ^ 3 + 6
  simp only [ArithmeticRoutine.ticks, ArithmeticRoutine.encode,
    KS.W13.ExpressionMachine.binaryBudget, KS.W01.ratLength] at houtput ⊢
  simp only [ratCode] at *
  omega

variable {f g : α → ℚ} {r : Realizes ea ratCode f} {s : Realizes ea ratCode g}
lemma RunsPoly.add (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.add s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
lemma RunsPoly.sub (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.sub s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
lemma RunsPoly.mul (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.mul s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
lemma RunsPoly.div (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.div s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
end CurrentKS.Realization

end

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
local instance coordinates_matrixEntry : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
local instance coordinates_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
local instance coordinates_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
local instance coordinates_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
local instance coordinates_fromBlocks : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then

instance poly_natLT : PolyTime natLT := by unfold natLT;infer_instance
instance poly_scaleMatrix {f : α → ℚ} {g : α → MatrixData}
    (r : Realizes ea ratCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.scaleMatrix s) := by unfold Realizes.scaleMatrix;apply poly_then
instance poly_negateMatrix : PolyTime negateMatrix := by unfold negateMatrix;infer_instance
instance poly_zeroMatrix : PolyTime zeroMatrix := by unfold zeroMatrix;infer_instance
instance poly_reEntry : PolyTime reEntry := by unfold reEntry;infer_instance
instance poly_imEntry : PolyTime imEntry := by unfold imEntry;infer_instance
instance poly_squareTabulate {f : (MatrixData×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime (squareTabulate r) := by unfold squareTabulate;apply poly_then
instance poly_realDecode : PolyTime realDecode := by unfold realDecode;apply poly_then
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
instance poly_blockDiagonal : PolyTime blockDiagonal := by unfold blockDiagonal;apply poly_then
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
instance poly_matrixVariable (b : Bool) : PolyTime (matrixVariable b) := by unfold matrixVariable;first | infer_instance | apply poly_then

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixFold
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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

lemma Grid.add {D : ℕ} {q r : ℚ} (hq : Grid D q) (hr : Grid D r) : Grid D (q+r) :=
  (Rat.add_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)
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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize

local notation "X" => NaturalPolynomial.variable

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
lemma grid_mono {D E : ℕ} {q : ℚ} (hg : Grid D q) (hd : D∣E) : Grid E q := hg.trans hd
lemma grid_mid {D : ℕ} {a b : ℚ} (ha : Grid D a) (hb : Grid D b) :
    Grid (D*2) ((a+b)/2) := by
  change ((a+b)/2).den∣D*2
  have h := Rat.mul_den_dvd (a+b) (1/2:ℚ)
  norm_num only [show (1/2:ℚ).den=2 from by norm_num] at h
  simpa only [div_eq_mul_inv,one_div,one_mul] using h.trans (Nat.mul_dvd_mul (ha.add hb) (dvd_refl 2))
lemma abs_mid {a b M : ℚ} (ha : |a|≤M) (hb : |b|≤M) : |(a+b)/2|≤M := by
  rw [abs_div,abs_of_pos (by norm_num : (0:ℚ)<2)]
  have ht := (abs_add_le a b).trans (add_le_add ha hb)
  linarith

lemma root_iterate_invariant (pow : ℕ) (q a b : ℚ) (k : ℕ) (M : ℚ)
    (ha : |a|≤M) (hb : |b|≤M) :
    let z := (rootStep pow)^[k] (q,(a,b))
    z.1=q ∧ Grid (a.den*b.den*2^k) z.2.1 ∧ Grid (a.den*b.den*2^k) z.2.2 ∧
      |z.2.1|≤M ∧ |z.2.2|≤M := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero,id_eq,pow_zero,mul_one]
    exact ⟨True.intro,Nat.dvd_mul_right _ _,Nat.dvd_mul_left _ _,ha,hb⟩
  | succ k ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    let z := (rootStep pow)^[k] (q,(a,b))
    have hd : a.den*b.den*2^(k+1)=(a.den*b.den*2^k)*2 := by rw [pow_succ];ring
    have hg : a.den*b.den*2^k∣a.den*b.den*2^(k+1) := by rw [hd];exact Nat.dvd_mul_right _ _
    have hm := grid_mid ih.2.1 ih.2.2.1
    rw [←hd] at hm
    have ham := abs_mid ih.2.2.2.1 ih.2.2.2.2
    change (rootStep pow z).1=q ∧ _
    dsimp only [rootStep]
    split
    · exact ⟨ih.1,hm,grid_mono ih.2.2.1 hg,ham,ih.2.2.2.2⟩
    · exact ⟨ih.1,grid_mono ih.2.1 hg,hm,ih.2.2.2.1,ham⟩

local instance poly_roots_pow {α : Type*} {encoding : α → Word} {value : α → ℚ}
    (routine : Realizes encoding ratCode value) [PolyTime routine] (exponent : ℕ) :
    PolyTime (routine.pow exponent) := by
  induction exponent with
  | zero => unfold Realizes.pow; infer_instance
  | succ exponent hypothesis =>
      let := hypothesis
      unfold Realizes.pow
      infer_instance

instance poly_rootStep (pow : ℕ) : PolyTime (rootStepRealizes pow) := by
  unfold rootStepRealizes;apply poly_congr
instance size_rootStep (pow : ℕ) : IterateSize (rootStepRealizes pow) := by
  refine ⟨⟨100*X+100,?_⟩⟩
  intro p k
  let L := (rootStateCode p).length
  have hq : (ratCode p.1).length≤L := le_prodCode_left p
  have ha : (ratCode p.2.1).length≤L := (le_prodCode_left p.2).trans (le_prodCode_right p)
  have hb : (ratCode p.2.2).length≤L := (le_prodCode_right p.2).trans (le_prodCode_right p)
  have hpa := (qparts_length p.2.1).mono ha
  have hpb := (qparts_length p.2.2).mono hb
  have hi := root_iterate_invariant pow p.1 p.2.1 p.2.2 k ((2:ℚ)^L) hpa.abs_le hpb.abs_le
  dsimp only at hi
  have hd : p.2.1.den*p.2.2.den*2^k≤2^(2*L+k) := by
    rw [pow_add,show 2*L=L+L by omega,pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hpa.2 hpb.2)
  have hD : 0<p.2.1.den*p.2.2.den*2^k := by positivity
  have hla := (qparts_of_grid hD hi.2.1 hd hi.2.2.2.1).length
  have hlb := (qparts_of_grid hD hi.2.2.1 hd hi.2.2.2.2).length
  change (ratCode ((rootStep pow)^[k] p).2.1).length≤_ at hla
  change (ratCode ((rootStep pow)^[k] p).2.2).length≤_ at hlb
  change (rootStateCode ((rootStep pow)^[k] p)).length≤100*(L+k)+100
  simp only [rootStateCode,prodCode_length]
  rw [hi.1]
  omega
instance poly_rootRun (pow : ℕ) : PolyTime (rootRun pow) := by unfold rootRun;infer_instance
instance poly_upperSqrt : PolyTime upperSqrt := by unfold upperSqrt;apply poly_congr
instance poly_approxPsi : PolyTime approxPsi := by unfold approxPsi;apply poly_congr
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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_approxPsi _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_rootRun _root_.OAI.CurrentKS.Realization.poly_rootStep _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_upperSqrt _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
lemma fold_select_code (f : α×α → α) (h : ∀a b,f (a,b)=a ∨ f (a,b)=b)
    (s : α) (xs : List α) (L : ℕ) (hs : (ea s).length≤L) (hx : ∀x∈xs,(ea x).length≤L) :
    (ea (xs.foldl (fun a b => f (a,b)) s)).length≤L := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    apply ih
    · dsimp only
      rcases h s x with e|e <;> rw [e]
      · exact hs
      · exact hx x (by simp)
    · intro y hy;exact hx y (by simp [hy])
lemma size_selection {f : α×α → α} (r : Realizes (prodCode ea ea) ea f)
    (h : ∀a b,f (a,b)=a ∨ f (a,b)=b) : FoldSize r := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs he
  apply fold_select_code f h s ys _ (le_prodCode_left (s,xs))
  intro x hx
  exact (mem_length_le_code ys hx).trans ((prefix_code_length ea xs ys zs he).trans (le_prodCode_right (s,xs)))
instance size_better (ea : α → Word) : FoldSize (better ea) :=
  size_selection _ (fun _ _ => by unfold betterData;split_ifs <;> simp)
instance poly_selectScored (ea : α → Word) : PolyTime (selectScored ea) := by unfold selectScored;infer_instance
instance poly_chooseCoordinate : PolyTime chooseCoordinate := by unfold chooseCoordinate;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCurvature
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
instance poly_normalizeVector : PolyTime normalizeVector := by unfold normalizeVector;apply poly_then
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
instance poly_computedCurvature : PolyTime computedCurvature := by unfold computedCurvature;apply poly_congr
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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_approxPsi _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_rootRun _root_.OAI.CurrentKS.Realization.poly_rootStep _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperSqrt _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
lemma PolyTime.then {r : Realizes ea eb f} {s : Realizes eb ec g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.then s) := @poly_then _ _ _ _ _ _ _ _ _ _ hr hs
lemma PolyTime.both {g : α → γ} {r : Realizes ea eb f} {s : Realizes ea ec g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.both s) := @poly_both _ _ _ _ _ _ _ _ _ _ hr hs
lemma PolyTime.congr {g : α → β} {r : Realizes ea eb f} (hr : PolyTime r)
    (h : ∀x,f x=g x) : PolyTime (r.congr h) := @poly_congr _ _ _ _ _ _ _ _ hr
lemma PolyTime.changeOutput {ed : δ → Word} {r : Realizes ea eb f} (hr : PolyTime r)
    (g : α → δ) (h : ∀x,eb (f x)=ed (g x)) : PolyTime (r.changeOutput ed g h) := @poly_changeOutput _ _ _ _ _ _ _ _ _ _ hr
lemma runsPolyOf {ι : Type*} {L : ι → ℕ} {r : Realizes ea eb f} (h : PolyTime r) (a : ι → α)
    (ha : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := @RunsPoly.of_poly _ _ _ _ _ _ _ r h a ha
lemma PolyTime.mul {f g : α → ℚ} {r : Realizes ea ratCode f} {s : Realizes ea ratCode g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.mul s) := by
  let := hr;let := hs;exact poly_mul r s
lemma PolyTime.pow {f : α → ℚ} {r : Realizes ea ratCode f}
    (hr : PolyTime r) (n : ℕ) : PolyTime (r.pow n) := by
  let := hr;exact poly_pow r n
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFind
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_approxPsi _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_chooseCoordinate _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_fromBlocks _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_identityEntry _root_.OAI.CurrentKS.Realization.poly_identityMatrix _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixEntry _root_.OAI.CurrentKS.Realization.poly_matrixMul _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_natEq _root_.OAI.CurrentKS.Realization.poly_natLE _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natToBinary _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_psdStored _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_rootRun _root_.OAI.CurrentKS.Realization.poly_rootStep _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_selectScored _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_transposeMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperSqrt _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_better _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_ratAdd _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_approxPsi _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_rootRun _root_.OAI.CurrentKS.Realization.poly_rootStep _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperSqrt _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_approxPsi _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_evalPencil _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_rootRun _root_.OAI.CurrentKS.Realization.poly_rootStep _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperSqrt _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_accumMatrix _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMemberFamily
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_selectScored _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_better _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {ι α : Type*} {L : ι → ℕ} {ea : α → Word}
lemma isPoly_listMember (xs : ι → List α)
    (ha : IsPoly L (fun i => (listCode ea (xs i)).length)) :
    IsPoly (fun s : Σ i,{x // x∈xs i} => L s.1)
      (fun s => (ea s.2.val).length) :=
  (ha.reindex Sigma.fst).mono (fun s => mem_length_le_code (xs s.1) s.2.property)
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoundedStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

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

lemma RunsPoly.then_with {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
    {F : α → β} {G : β → γ} {ι : Type*} {L : ι → ℕ}
    {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a)
    (hs : IsPoly L (fun i => (eb (F (a i))).length) → RunsPoly L s (fun i => F (a i))) :
    RunsPoly L (r.then s) a := hr.then (hs hr.output)

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_optCandidate (a : ι → OptParams×ℕ)
    (ha : IsPoly L (fun i => (prodCode optCode natCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.searchCount)) : RunsPoly L optCandidate a := by
  unfold optCandidate
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hout
  apply runsPoly_search
  · exact hout
  · exact hn

lemma candidate_cost_bound : ∃q : NaturalPolynomial,∀p,optCandidate.cost p≤q.eval (candidateResource p) := by
  have hw : IsPoly candidateResource (fun p => (optCode p.1).length) :=
    (isPoly_self candidateResource).mono (fun _ => by unfold candidateResource;omega)
  have hk : IsPoly candidateResource (fun p => (natCode p.2).length) :=
    (isPoly_self candidateResource).mono (fun _ => by simp only [natCode,List.length_replicate];unfold candidateResource;omega)
  have hn : IsPoly candidateResource (fun p => p.1.searchCount) :=
    (isPoly_self candidateResource).mono (fun _ => by unfold candidateResource;omega)
  exact (runsPoly_optCandidate id (isPoly_pair hw hk) hn).cost
lemma candidate_length_bound : ∃q : NaturalPolynomial,∀p,
    (vectorCode (List.ofFn (p.1.B.levelCandidate p.1.f p.1.delta p.1.r p.1.R p.1.U p.2))).length≤q.eval (candidateResource p) := by
  obtain ⟨p,hp⟩ := candidate_cost_bound
  refine ⟨3*X+1+p,?_⟩
  intro a
  have h := optCandidate.output_length a
  have hc := hp a
  simp only [prodCode_length,natCode,List.length_replicate] at h
  change _≤3*candidateResource a+1+p.eval (candidateResource a)
  unfold candidateResource at *
  omega
lemma runsPoly_osNext (a : ι → OptState)
    (ha : IsPoly L (fun i => (optStateCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).p.searchCount)) : RunsPoly L osNext a := by
  unfold osNext
  apply RunsPoly.changeOutput
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.ite (RunsPoly.of_poly _ a ha) (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hout
  apply runsPoly_optCandidate
  · exact hout
  · exact hn

lemma osNext_cost_bound : ∃q : NaturalPolynomial,∀s,osNext.cost s≤q.eval (nextResource s) := by
  exact (runsPoly_osNext id ((isPoly_self nextResource).mono (fun _ => Nat.le_add_right _ _))
    ((isPoly_self nextResource).mono (fun _ => Nat.le_add_left _ _))).cost

lemma optimize_is_candidate (p : OptParams) (k : ℕ) : ∃j≤k,
    p.B.optimize p.f p.delta p.r p.R p.U k=p.B.levelCandidate p.f p.delta p.r p.R p.U j := by
  induction k with
  | zero => exact ⟨0,le_rfl,rfl⟩
  | succ k ih =>
      unfold RationalSDP.Pencil.optimize
      dsimp only
      split_ifs
      · obtain ⟨j,hj,he⟩ := ih
        exact ⟨j,by omega,he⟩
      · exact ⟨k+1,le_rfl,rfl⟩

lemma runsPoly_optInit (a : ι → OptParams)
    (ha : IsPoly L (fun i => (optCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).searchCount)) : RunsPoly L optInit a := by
  unfold optInit
  apply RunsPoly.changeOutput
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hout
  apply runsPoly_optCandidate
  · exact hout
  · exact hn

lemma opt_iterate_size_bound : ∃q : NaturalPolynomial,∀p k,
    (optStateCode (OptState.next^[k] p.init)).length≤q.eval ((optCode p).length+k+p.searchCount) := by
  obtain ⟨q,hq⟩ := candidate_length_bound
  refine ⟨4*X+2+q,?_⟩
  intro p k
  obtain ⟨j,hj,he⟩ := optimize_is_candidate p k
  have h : _≤q.eval ((optCode p).length+k+p.searchCount) := (hq (p,j)).trans (q.eval_mono (by change (optCode p).length+j+p.searchCount≤_;omega))
  dsimp only at h
  rw [opt_iterate]
  simp only [optStateCode,optStateData,optStateDataCode,prodCode_length,natCode,List.length_replicate]
  rw [he]
  change _≤4*((optCode p).length+k+p.searchCount)+2+q.eval ((optCode p).length+k+p.searchCount)
  omega

lemma optimize_loop_cost_bound : ∃q : NaturalPolynomial,∀p k,
    osNext.iterate.cost (k,p.init)≤q.eval ((optCode p).length+k+p.searchCount) := by
  obtain ⟨q,hq⟩ := opt_iterate_size_bound
  obtain ⟨r,hr⟩ := osNext_cost_bound
  refine ⟨3*X+X*(r.comp (q+X)+2)+3,?_⟩
  intro p k
  let T := (optCode p).length+k+p.searchCount
  have hk : k≤T := by unfold T;omega
  have ht := iterate_ticks_bound osNext p.init k (r.eval (q.eval T+T)) (by
    intro i hi
    apply (hr _).trans (r.eval_mono ?_)
    unfold nextResource
    have hs : _≤q.eval T := (hq p i).trans (q.eval_mono (by unfold T;omega))
    have hp : (OptState.next^[i] p.init).p=p := by rw [opt_iterate]
    rw [hp]
    have hn : p.searchCount≤T := by unfold T;omega
    omega)
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1)
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change 3*k+2+IterateRoutine.loopTicks osNext.cost OptState.next k p.init≤3*T+T*(r.eval (q.eval T+T)+2)+3
  omega

lemma runsPoly_optimize (a : ι → OptParams×ℕ)
    (ha : IsPoly L (fun i => (prodCode optCode natCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.searchCount)) : RunsPoly L optimize a := by
  have hp : IsPoly L (fun i => (optCode (a i).1).length) := ha.mono (fun i => le_prodCode_left (a i))
  have hk : IsPoly L (fun i => (a i).2) := ha.mono (fun i => by simpa only [natCode,List.length_replicate] using le_prodCode_right (ea:=optCode) (eb:=natCode) (a i))
  have hi := (RunsPoly.of_poly (first optCode natCode) a ha).then (runsPoly_optInit _ hp hn)
  have hin := (RunsPoly.of_poly (second optCode natCode) a ha).both hi
  obtain ⟨q,hq⟩ := optimize_loop_cost_bound
  have hlo : RunsPoly L osNext.iterate (fun i => ((a i).2,(a i).1.init)) :=
    ⟨hin.output,(((hp.add hk).add hn).eval q).mono (fun i => hq (a i).1 (a i).2)⟩
  unfold optimize
  apply RunsPoly.congr
  exact (hin.then hlo).then_poly osY
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialValueQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
instance poly_veVariable (b : Bool) : PolyTime (veVariable b) := by unfold veVariable;apply poly_then
instance poly_veSum : PolyTime veSum := by unfold veSum;apply poly_then
instance poly_sandwich : PolyTime sandwich := by unfold sandwich;apply poly_then
instance poly_eta : PolyTime eta := by unfold eta;apply poly_then
instance poly_schurEval (b : Bool) : PolyTime (schurEval b) := by unfold schurEval;apply poly_then
instance poly_lowerBox (b : Bool) : PolyTime (lowerBox b) := by unfold lowerBox;apply poly_then
instance poly_upperBox (b : Bool) : PolyTime (upperBox b) := by unfold upperBox;apply poly_then
instance poly_tinyMatrix : PolyTime tinyMatrix := by unfold tinyMatrix;apply poly_then
instance poly_blockWith {α : Type*} {ea : α → Word} {f g : α → MatrixData}
    (r : Realizes ea matrixCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.blockWith s) := by unfold Realizes.blockWith;infer_instance
instance poly_valueEval : PolyTime valueEval := by unfold valueEval;apply poly_blockWith
instance poly_traceMatrix : PolyTime traceMatrix := by unfold traceMatrix;apply poly_then
instance poly_valueObjective : PolyTime valueObjective := by unfold valueObjective;apply poly_add
instance poly_valueCoeffs : PolyTime valueCoeffs := by unfold valueCoeffs;apply poly_then
instance poly_valuePencil : PolyTime valuePencil := by unfold valuePencil;apply poly_then
instance poly_vqData : PolyTime vqData := by unfold vqData;apply poly_then
instance poly_vqDelta : PolyTime vqDelta := by unfold vqDelta;apply poly_then
instance poly_valueLipschitz : PolyTime valueLipschitz := by unfold valueLipschitz;apply poly_mul
instance poly_valueOuterRadius : PolyTime valueOuterRadius := by unfold valueOuterRadius;apply poly_mul
instance poly_valueInnerRadius : PolyTime valueInnerRadius := by unfold valueInnerRadius;apply poly_div
instance poly_vqOpt : PolyTime vqOpt := by unfold vqOpt;apply poly_changeOutput

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_vqFuel (a : ι → ValueQueryParams)
    (ha : IsPoly L (fun i => (valueQueryCode (a i)).length))
    (hn : IsPoly L (fun i => RationalSDP.optimizeFuel (a i).delta 100)) :
    RunsPoly L vqFuel a := by
  unfold vqFuel
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both
  · apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
    intro hw
    apply runsPoly_ratCeil _ hw
    apply hn.mono
    intro i
    change ⌈200/(a i).delta⌉₊≤⌈2*100/(a i).delta⌉₊+3
    norm_num
  · exact RunsPoly.of_poly _ a ha

lemma runsPoly_valueQueryPoint (a : ι → ValueQueryParams)
    (ha : IsPoly L (fun i => (valueQueryCode (a i)).length))
    (hk : IsPoly L (fun i => RationalSDP.optimizeFuel (a i).delta 100))
    (hn : IsPoly L (fun i => (a i).opt.searchCount)) : RunsPoly L valueQueryPoint a := by
  unfold valueQueryPoint
  apply RunsPoly.then_with ((RunsPoly.of_poly vqOpt a ha).both (runsPoly_vqFuel a ha hk))
  intro hw
  exact runsPoly_optimize _ hw hn
lemma runsPoly_valueQuery (a : ι → ValueQueryParams)
    (ha : IsPoly L (fun i => (valueQueryCode (a i)).length))
    (hk : IsPoly L (fun i => RationalSDP.optimizeFuel (a i).delta 100))
    (hn : IsPoly L (fun i => (a i).opt.searchCount)) : RunsPoly L valueQuery a := by
  unfold valueQuery
  apply RunsPoly.congr
  exact ((RunsPoly.of_poly vqData a ha).both (runsPoly_valueQueryPoint a ha hk hn)).then_poly valueObjective

lemma optFuel_le_scan (p : ValueQueryParams) : RationalSDP.optimizeFuel p.delta 100≤p.scanCount := by
  have hn : 1≤p.opt.searchCount := by unfold OptParams.searchCount RationalSDP.searchFuel;omega
  exact (Nat.le_succ _).trans (le_mul_of_one_le_right (Nat.zero_le _) hn)
lemma searchCount_le_scan (p : ValueQueryParams) : p.opt.searchCount≤p.scanCount :=
  le_mul_of_one_le_left (Nat.zero_le _) (by omega)
lemma runsPoly_valueQuery_scan (a : ι → ValueQueryParams)
    (ha : IsPoly L (fun i => (valueQueryCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).scanCount)) : RunsPoly L valueQuery a :=
  runsPoly_valueQuery a ha (hn.mono (fun i => optFuel_le_scan (a i)))
    (hn.mono (fun i => searchCount_le_scan (a i)))
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialPotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
instance poly_ppTheta : PolyTime ppTheta := by unfold ppTheta;apply poly_congr
instance poly_ppQuery : PolyTime ppQuery := by unfold ppQuery;apply poly_changeOutput

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_potentialQuery (a : ι → PotentialParams)
    (ha : IsPoly L (fun i => (potentialCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).scanCount)) : RunsPoly L potentialQuery a := by
  unfold potentialQuery Realizes.add
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both
  · apply RunsPoly.then_with (RunsPoly.of_poly ppQuery a ha)
    intro hw
    exact runsPoly_valueQuery_scan _ hw hn
  · exact RunsPoly.of_poly _ a ha
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

lemma potential_scanCount (p : PotentialParams) : p.scanCount=queryScanCount p.d p.nu p.error := by
  rfl

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_faceQuery (a : ι → FacePoint×ℚ)
    (ha : IsPoly L (fun i => (prodCode facePointCode ratCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.p.queryCount (a i).2)) : RunsPoly L faceQuery a := by
  unfold faceQuery
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_potentialQuery _ hw
  simpa only [potential_scanCount,FacePoint.potential,FaceParams.queryCount] using hn
lemma runsPoly_faceStencil (a : ι → FacePoint)
    (ha : IsPoly L (fun i => (facePointCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).p.stencilCount)) : RunsPoly L faceStencil a := by
  unfold faceStencil
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_faceQuery _ hw
  exact hn
lemma runsPoly_faceScore (a : ι → FacePoint)
    (ha : IsPoly L (fun i => (facePointCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).p.scoreCount)) : RunsPoly L faceScore a := by
  unfold faceScore
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_faceQuery _ hw
  exact hn
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMapFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_selectScored _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_better _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word} {f : α → β}
lemma runsPoly_map (r : Realizes ea eb f) (xs : ι → List α)
    (ha : IsPoly L (fun i => (listCode ea (xs i)).length))
    (hc : ∃ p : NaturalPolynomial,∀i x,x∈xs i → r.cost x≤p.eval (L i)) :
    RunsPoly L r.map xs := by
  obtain ⟨p,hp⟩ := hc
  obtain ⟨q,hq⟩ := ha
  refine ⟨⟨q,hq⟩,⟨2*q+q*(3*q+p+6*(q+p)+8)+q*(2*(q+p)+1)+4,?_⟩⟩
  intro i
  let A := q.eval (L i)
  let C := p.eval (L i)
  have hn : (xs i).length≤A := (list_length_le_code ea (xs i)).trans (hq i)
  have he : ∀x∈xs i,(ea x).length≤A := fun x hx => (mem_length_le_code (xs i) hx).trans (hq i)
  have ho : ∀x∈xs i,(eb (f x)).length≤A+C := fun x hx =>
    (r.output_length x).trans (Nat.add_le_add (he x hx) (hp i x hx))
  have hs := sum_map_bound (xs i) (fun x => FramedMapRoutine.bodyTicks ea (fun x => eb (f x)) r.cost x+1)
    (3*A+C+6*(A+C)+8) (by
      intro x hx
      have hl := he x hx
      have hc' := hp i x hx
      have hout := ho x hx
      simp only [FramedMapRoutine.bodyTicks,KS.W01.length_frame]
      omega)
  have ht := listCode_length_bound (ea:=fun x => eb (f x)) (xs i) (A+C) ho
  have hs' := hs.trans (Nat.mul_le_mul_right _ hn)
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change FramedMapRoutine.ticks ea (fun x => eb (f x)) r.cost (xs i)≤_
  simp only [FramedMapRoutine.ticks,FramedMapRoutine.scanTicks]
  change 2*(listCode ea (xs i)).length+2+((xs i).map _).sum+1+
    (listCode (fun x => eb (f x)) (xs i)).length+1≤_
  change _≤2*A+A*(3*A+C+6*(A+C)+8)+A*(2*(A+C)+1)+4
  have hl : (listCode ea (xs i)).length≤A := hq i
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFinFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppQuery _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppTheta _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_schurEval _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueEval _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_valuePencil _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqOpt _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}
lemma runsPoly_tabulateFin {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length))
    (hc : ∃p : NaturalPolynomial,∀i j,r.cost ⟨a i,j⟩≤p.eval (L i)) :
    RunsPoly L (r.tabulateFin rn) a := by
  unfold Realizes.tabulateFin
  apply RunsPoly.congr
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_map _ _ hw
  obtain ⟨p,hp⟩ := hc
  refine ⟨p,?_⟩
  intro i x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  exact hp i j
lemma runsPoly_tabulateFin_family {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length))
    (hc : RunsPoly (fun s : Σ i,Fin (n (a i)) => L s.1) r (fun s => ⟨a s.1,s.2⟩)) :
    RunsPoly L (r.tabulateFin rn) a := by
  apply runsPoly_tabulateFin r rn a ha
  obtain ⟨p,hp⟩ := hc.cost
  exact ⟨p,fun i j => hp ⟨i,j⟩⟩
lemma isPoly_finFamily {n : α → ℕ} (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length)) :
    IsPoly (fun s : Σ i,Fin (n (a i)) => L s.1)
      (fun s => (finFamilyCode ea n ⟨a s.1,s.2⟩).length) := by
  have hn := (RunsPoly.of_poly rn a ha).output
  have h := ((isPoly_const L 2).mul ha).add ((isPoly_const L 1).add hn)
  apply (h.reindex (fun s : Σ i,Fin (n (a i)) => s.1)).mono
  intro s
  simp only [finFamilyCode,prodCode_length,natCode,List.length_replicate,Function.comp_apply]
  have hj := s.2.isLt
  omega
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

lemma runsPoly_stencilAt {ea : α → Word} (p : α → FaceParams) (pr : Realizes ea faceCode p)
    [PolyTime pr] (v : (a : α) → Fin (p a).n → ℚ)
    (vr : Realizes ea vectorCode (fun a => List.ofFn (v a))) [PolyTime vr]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length))
    (hn : IsPoly L (fun i => (p (a i)).stencilCount)) :
    RunsPoly L (stencilAt p pr v vr) a := by
  unfold stencilAt
  apply RunsPoly.then_with
  · apply runsPolyOf ?_ a ha
    apply PolyTime.changeOutput
    apply PolyTime.both ‹PolyTime pr›
    apply PolyTime.then ?_ poly_vectorAdd
    apply PolyTime.both (PolyTime.then ‹PolyTime pr› poly_fState)
    exact ((((‹PolyTime pr›).then poly_fSchedule).then (poly_parameterField 5)).both ‹PolyTime vr›).then poly_vectorScale
  · intro hw
    exact runsPoly_faceStencil _ hw hn

lemma runsPoly_stencilGradientEntry (a : ι → FaceIndex)
    (ha : IsPoly L (fun i => (faceIndexCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.stencilCount)) :
    RunsPoly L stencilGradientEntry a := by
  unfold stencilGradientEntry
  apply RunsPoly.div
  · apply RunsPoly.sub
    · exact runsPoly_stencilAt _ _ _ _ a ha hn
    · exact runsPoly_stencilAt _ _ _ _ a ha hn
  · exact runsPolyOf ((poly_constant _ _ 2).mul ((poly_fiP.then poly_fSchedule).then (poly_parameterField 5))) a ha

lemma runsPoly_stencilGradient (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).stencilCount)) :
    RunsPoly L stencilGradient a := by
  unfold stencilGradient
  apply runsPoly_tabulateFin_family _ _ a ha
  exact runsPoly_stencilGradientEntry (fun s : Σ i,Fin (a i).n => ⟨a s.1,s.2⟩)
    (isPoly_finFamily fN a ha) (hn.reindex Sigma.fst)

lemma runsPoly_stencilHessianEntry (a : ι → FaceDouble)
    (ha : IsPoly L (fun i => (faceDoubleCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.1.stencilCount)) :
    RunsPoly L stencilHessianEntry a := by
  unfold stencilHessianEntry
  dsimp only
  apply RunsPoly.congr
  apply RunsPoly.ite (RunsPoly.of_poly _ a ha)
  · apply RunsPoly.div
    · apply RunsPoly.add
      · apply RunsPoly.sub
        · exact runsPoly_stencilAt _ _ _ _ a ha hn
        · apply RunsPoly.mul (RunsPoly.of_poly _ a ha)
          apply RunsPoly.then_with
          · apply runsPolyOf ?_ a ha
            apply PolyTime.changeOutput
            exact poly_fdP.both (poly_fdP.then poly_fState)
          · intro hw
            exact runsPoly_faceStencil _ hw hn
      · exact runsPoly_stencilAt _ _ _ _ a ha hn
    · exact runsPolyOf (((poly_fdP.then poly_fSchedule).then (poly_parameterField 5)).pow 2) a ha
  · apply RunsPoly.div
    · apply RunsPoly.add
      · apply RunsPoly.sub
        · apply RunsPoly.sub
          · exact @runsPoly_stencilAt _ _ _ _ _ _ poly_fdP _ _
              (((poly_fdBasisI.both poly_fdBasisJ).then poly_vectorAdd).congr
                (fun _ => vectorAdd_ofFn _ _)) a ha hn
          · exact @runsPoly_stencilAt _ _ _ _ _ _ poly_fdP _ _
              (((poly_fdBasisI.both ((poly_fdBasisJ.then poly_vectorNeg).congr
                (fun _ => vectorNeg_ofFn _))).then poly_vectorAdd).congr
                (fun _ => vectorAdd_ofFn _ _)) a ha hn
        · exact @runsPoly_stencilAt _ _ _ _ _ _ poly_fdP _ _
            (((((poly_fdBasisI.then poly_vectorNeg).congr (fun _ => vectorNeg_ofFn _)).both
              poly_fdBasisJ).then poly_vectorAdd).congr (fun _ => vectorAdd_ofFn _ _)) a ha hn
      · exact @runsPoly_stencilAt _ _ _ _ _ _ poly_fdP _ _
          (((((poly_fdBasisI.then poly_vectorNeg).congr (fun _ => vectorNeg_ofFn _)).both
            ((poly_fdBasisJ.then poly_vectorNeg).congr (fun _ => vectorNeg_ofFn _))).then
            poly_vectorAdd).congr (fun _ => vectorAdd_ofFn _ _)) a ha hn
    · exact runsPolyOf ((poly_constant _ _ 4).mul (((poly_fdP.then poly_fSchedule).then (poly_parameterField 5)).pow 2)) a ha
lemma runsPoly_stencilHessianRow (a : ι → FaceIndex)
    (ha : IsPoly L (fun i => (faceIndexCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.stencilCount)) :
    RunsPoly L stencilHessianRow a := by
  unfold stencilHessianRow
  apply runsPoly_tabulateFin_family _ _ a ha
  exact runsPoly_stencilHessianEntry (fun s : Σ i,Fin (a i).1.n => ⟨a s.1,s.2⟩)
    (isPoly_finFamily (fiP.then fN) a ha) (hn.reindex Sigma.fst)
lemma runsPoly_stencilHessian (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).stencilCount)) :
    RunsPoly L stencilHessian a := by
  unfold stencilHessian
  apply runsPoly_tabulateFin_family _ _ a ha
  exact runsPoly_stencilHessianRow (fun s : Σ i,Fin (a i).n => ⟨a s.1,s.2⟩)
    (isPoly_finFamily fN a ha) (hn.reindex Sigma.fst)
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
instance poly_gradientDirection : PolyTime gradientDirection := by unfold gradientDirection;apply poly_congr

lemma runsPoly_faceCurvatureParams (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).stencilCount)) : RunsPoly L faceCurvatureParams a := by
  unfold faceCurvatureParams
  apply RunsPoly.changeOutput
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  exact (runsPoly_stencilHessian a ha hn).both (RunsPoly.of_poly _ a ha)
lemma runsPoly_faceCurvature (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).stencilCount)) : RunsPoly L faceCurvature a :=
  (runsPoly_faceCurvatureParams a ha hn).then_poly _
lemma runsPoly_faGradientPoint (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount)) : RunsPoly L faGradientPoint a := by
  unfold faGradientPoint
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_poly
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  exact runsPoly_stencilGradient _ hw hn
lemma runsPoly_faCandidates (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount)) : RunsPoly L faCandidates a := by
  unfold faCandidates
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_poly
  apply RunsPoly.both (runsPoly_faGradientPoint a ha hn)
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  exact runsPoly_faceCurvature _ hw hn
lemma runsPoly_faCandidatePoints (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount)) : RunsPoly L faCandidatePoints a := by
  unfold faCandidatePoints
  apply RunsPoly.changeOutput
  exact ((RunsPoly.of_poly _ a ha).both (runsPoly_faCandidates a ha hn)).then_poly _
lemma runsPoly_scored (a : ι → FacePoint)
    (ha : IsPoly L (fun i => (facePointCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).p.scoreCount)) : RunsPoly L (fpY.both faceScore) a :=
  (RunsPoly.of_poly _ a ha).both (runsPoly_faceScore a ha hn)
lemma runsPoly_faScoredCandidates (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount))
    (hs : IsPoly L (fun i => (a i).val.scoreCount)) :
    RunsPoly L (faCandidatePoints.then (fpY.both faceScore).map) a := by
  apply RunsPoly.then_with (runsPoly_faCandidatePoints a ha hn)
  intro hw
  let xs (i : ι) := (a i).candidates.map (fun y => (⟨(a i).val,y⟩ : FacePoint))
  let b (s : Σ i,{x // x∈xs i}) : FacePoint := s.2.val
  have hb : IsPoly (fun s : Σ i,{x // x∈xs i} => L s.1) (fun s => (b s).p.scoreCount) := by
    apply (hs.reindex Sigma.fst).mono
    intro s
    obtain ⟨y,hy,he⟩ := List.mem_map.mp s.2.property
    change s.2.val.p.scoreCount≤(a s.1).val.scoreCount
    rw [←he]
  have hc := runsPoly_scored b (isPoly_listMember xs hw) hb
  apply runsPoly_map _ _ hw
  obtain ⟨p,hp⟩ := hc.cost
  exact ⟨p,fun i x hx => hp ⟨i,⟨x,hx⟩⟩⟩
lemma runsPoly_faChoice (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount))
    (hs : IsPoly L (fun i => (a i).val.scoreCount)) : RunsPoly L faChoice a := by
  unfold faChoice
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.then_poly
  apply RunsPoly.both
  · apply RunsPoly.then_with
    · apply runsPolyOf ?_ a ha
      apply PolyTime.changeOutput
      exact poly_faP.both (poly_faP.then poly_fState)
    · intro hw
      exact runsPoly_scored _ hw hs
  · exact runsPoly_faScoredCandidates a ha hn hs
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceFuel
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_gradientDirection _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppQuery _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppTheta _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_schurEval _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueEval _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_valuePencil _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqOpt _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceNext
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ}
lemma runsPoly_packFace {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a)))
    (a : ι → α) (hp : RunsPoly L p a) (hy : RunsPoly L y a) :
    RunsPoly L (packFace p y) a := by
  unfold packFace
  apply RunsPoly.changeOutput
  exact (hp.then_poly _).both ((hp.then_poly _).both (hy.both (hp.then_poly _)))
lemma runsPoly_faNextBase (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount))
    (hs : IsPoly L (fun i => (a i).val.scoreCount)) : RunsPoly L faNextBase a := by
  unfold faNextBase
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_poly
  apply RunsPoly.changeOutput
  exact (RunsPoly.of_poly _ a ha).both (runsPoly_faChoice a ha hn hs)
lemma runsPoly_faceNext (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly (fun i : {i // (a i).n≠0} => L i.val) (fun i => (a i.val).stencilCount))
    (hs : IsPoly (fun i : {i // (a i).n≠0} => L i.val) (fun i => (a i.val).scoreCount)) :
    RunsPoly L faceNext a := by
  unfold faceNext
  apply RunsPoly.congr
  apply RunsPoly.dite_families (RunsPoly.of_poly _ a ha)
  · apply RunsPoly.reindex
    exact RunsPoly.of_poly (identity faceCode) _ (ha.reindex Subtype.val)
  · apply runsPoly_packFace
    · exact RunsPoly.of_poly faP _ (ha.reindex Subtype.val)
    · exact runsPoly_faNextBase _ (ha.reindex Subtype.val) hn hs
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialVariance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_computedCurvature _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eta _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_fdBasisI _root_.OAI.CurrentKS.Realization.poly_fdBasisJ _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiBasis _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gradientDirection _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_normalizeVector _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppQuery _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppTheta _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_schurEval _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueEval _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_valuePencil _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veSum _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqOpt _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_weightedSum _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceRun
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_orbitStep_oai (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    RunsPoly (fun s : ι×ℕ => L s.1) faceNext (fun s => (a s.1).orbit s.2) :=
  runsPoly_faceNext _ (isPoly_face_orbit a ha hg) (isPoly_orbitStencil a ha hg) (isPoly_orbitScore a ha hg)

end CurrentKS.Realization

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentKS.Realization.runsPoly_orbitStep_oai.{u_1} := @OAI.CurrentKS.Realization.runsPoly_orbitStep_oai.{u_1}

-- Prove2me | solution 1 for OAI.ContingencyTables.ExactPublicLaw.halted_feasible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:57:09.322999+00:00
-- url     : https://prove2.me/submissions/10941990-d4bb-4609-ad44-f4840543ab62

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009
import Theorems.Thm_OAI_ContingencyTables_ExactPublicPrefix_prefix_correct
import Theorems.Thm_OAI_ContingencyTables_ExactTablePrefix_failure_bound

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

lemma average_add {n : ℕ} (f g : Bits n → ℚ) :
    average (fun b=>f b+g b)=average f+average g := by
  simp [average,sum_add_distrib,add_div]

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

lemma experiment_cost (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) :
    (experiment M n c).cost=n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [experiment,Experiment.cost,ih,max_self]; omega

lemma experiment_run (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Stream) :
    (experiment M n c).run b=(execute M n c b,n) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => simp only [experiment,Experiment.run,ih,execute]; congr 1; omega

theorem physical_law (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (f : Cfg Γ Q → ℚ) :
    average (fun b : Bits n=>f (execute M n c (extend b)))=(experiment M n c).mean f := by
  have h:=Experiment.average_run (experiment M n c) f n (by rw [experiment_cost])
  simpa only [experiment_run] using h

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

end Implements
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgramSeal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
end MatchingFPRAS.PhysicalPost.Program

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

lemma printMatrix_ofFn {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    printMatrix (List.ofFn (fun i => List.ofFn (X i)))=Algorithms.encodeMatrix X := by
  simp only [printMatrix,Algorithms.encodeMatrix,List.flatMap_def,List.ofFn_comp',List.map_map,
    Function.comp_def]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRetryTail
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical halting tails from finite rejection prefixes -/

namespace ContingencyTables.PhysicalRetryTail
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open scoped BigOperators Classical

variable {Γ Q B : Type} [Inhabited Γ]

lemma experiment_mean_add (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (n m : ℕ) (c : Cfg Γ Q) (g : Cfg Γ Q → ℚ) :
    (experiment M (n+m) c).mean g=
      (experiment M n c).mean (fun d => (experiment M m d).mean g) := by
  induction n generalizing c with
  | zero => simp only [Nat.zero_add,experiment,Experiment.mean]
  | succ n ih => simp only [Nat.succ_add,experiment,Experiment.mean,ih]

lemma halted_mean (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (h : c.state=none)
    (g : Cfg Γ Q → ℚ) : (experiment M n c).mean g=g c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht (b : Bool) : PhysicalPost.tick M c b=c := by simp [PhysicalPost.tick,h]
    simp only [experiment,Experiment.mean,ht,ih]
    ring

lemma padded_halted_result (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (out : B → Cfg Γ Q) (c : Cfg Γ Q)
    (p : Experiment B) (hp : Implements M out c p) (n : ℕ) (hn : p.cost≤n)
    (b : Stream) (hhalt : (out (p.run b).1).state=none) :
    execute M n c b=out (p.run b).1 := by
  have hb : (p.run b).2≤n := (Experiment.run_cost p b).trans hn
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hb
  rw [hk,execute_add,hp.execution b]
  have he : out (p.run b).1=⟨none,(out (p.run b).1).tape⟩ := by
    cases e:out (p.run b).1 with
    | mk state tape =>
      rw [e] at hhalt
      change state=none at hhalt
      subst state
      rfl
  rw [he,execute_halted]

end ContingencyTables.PhysicalRetryTail

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPartialSequence
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sequencing finite prefixes that can stop at a live configuration

A called prefix may have reached the continuation, or may still be inside
its first program. The construction stops exactly at that interface.
-/

namespace ContingencyTables.PhysicalPartialSequence
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing

variable {Γ Q R A : Type} [Inhabited Γ]

lemma mean_const (p : Experiment A) (v : ℚ) : p.mean (fun _ => v)=v := by
  induction p with
  | done => rfl
  | delay n p ih => exact ih
  | read p ih => simp only [Experiment.mean,ih]; ring

end ContingencyTables.PhysicalPartialSequence

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPublicPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed exact-sampling machine on the literal public binary tape -/

namespace ContingencyTables.ExactPublicPrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma word_eq (X : Table r c) : word r c X=Algorithms.encodeMatrix X.val :=
  GreedyFeasibleTable.printMatrix_ofFn X.val

lemma output_halted (X : Table r c) : (output r c (some X)).state=none := rfl

lemma output_tape (X : Table r c) :
    (output r c (some X)).tape.right₀=ListBlank.mk (Algorithms.encodeMatrix X.val) := by
  change (Tape.mk₁ (word r c X)).right₀=_
  rw [word_eq]
  simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]

end
end ContingencyTables.ExactPublicPrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalEventBounds
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal-event bounds from finite stopping prefixes -/

namespace ContingencyTables.PhysicalEventBounds
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open scoped BigOperators Classical
noncomputable section
variable {Γ Q A : Type} [Inhabited Γ]

lemma event_nonneg (P : Cfg Γ Q → Prop) (c : Cfg Γ Q) : 0≤event P c := by
  unfold event; split_ifs <;> norm_num
lemma event_le_one (P : Cfg Γ Q → Prop) (c : Cfg Γ Q) : event P c≤1 := by
  unfold event; split_ifs <;> norm_num

lemma mean_mono (p : Experiment A) (f g : A → ℚ) (h : ∀ a,f a≤g a) :
    p.mean f≤p.mean g := by
  induction p with
  | done a => exact h a
  | read p ih => simp only [Experiment.mean]; linarith [ih false,ih true]
  | delay n p ih => exact ih

lemma average_mono {n : ℕ} (f g : Bits n → ℚ) (h : ∀ b,f b≤g b) :
    average f≤average g := by
  unfold average
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun b _ => h b)) (by positivity)

/-- Only successful endpoints need be halted; the failure endpoint can be live. -/
theorem stopped_event_bounds (M : PhysicalPost.Table Γ Q) (out : Option A → Cfg Γ Q)
    (c : Cfg Γ Q) (p : Experiment (Option A)) (hp : Implements M out c p)
    (hhalt : ∀ a,(out (some a)).state=none) (P : Cfg Γ Q → Prop)
    (n : ℕ) (hn : p.cost≤n) :
    p.mean (fun o => o.elim 0 (fun a => event P (out (some a))))≤
        (experiment M n c).mean (event P) ∧
      (experiment M n c).mean (event P)≤
        p.mean (fun o => o.elim 0 (fun a => event P (out (some a))))+
          p.mean (fun o => if o=none then 1 else 0) := by
  have lower (b : Bits n) :
      ((p.run (extend b)).1.elim 0 (fun a => event P (out (some a))))≤
        event P (execute M n c (extend b)) := by
    cases he : (p.run (extend b)).1 with
    | none => exact event_nonneg P _
    | some a =>
      have hh : (out (p.run (extend b)).1).state=none := by rw [he]; exact hhalt a
      rw [PhysicalRetryTail.padded_halted_result M out c p hp n hn (extend b) hh,he]
      exact le_rfl
  have upper (b : Bits n) : event P (execute M n c (extend b))≤
      ((p.run (extend b)).1.elim 0 (fun a => event P (out (some a))))+
        (if (p.run (extend b)).1=none then 1 else 0) := by
    cases he : (p.run (extend b)).1 with
    | none => simpa only [Option.elim_none,ite_true, if_true,zero_add] using event_le_one P _
    | some a =>
      have hh : (out (p.run (extend b)).1).state=none := by rw [he]; exact hhalt a
      rw [PhysicalRetryTail.padded_halted_result M out c p hp n hn (extend b) hh,he]
      simp only [Option.elim_some,Option.some_ne_none,ite_false,add_zero,le_refl]
  have hl := average_mono _ _ lower
  have hu := average_mono _ _ upper
  rw [physical_law,Experiment.average_run p
    (fun o => o.elim 0 (fun a => event P (out (some a)))) n hn] at hl
  rw [physical_law,average_add,Experiment.average_run p
    (fun o => o.elim 0 (fun a => event P (out (some a)))) n hn,
    Experiment.average_run p (fun o => if o=none then 1 else 0) n hn] at hu
  exact ⟨hl,hu⟩

lemma terminal_event_monotone (M : PhysicalPost.Table Γ Q) (c : Cfg Γ Q)
    (P : Cfg Γ Q → Prop) (hP : ∀ d,P d → d.state=none) :
    Monotone (fun n => (experiment M n c).mean (event P)) := by
  intro n m hnm
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  change (experiment M n c).mean (event P)≤(experiment M (n+k) c).mean (event P)
  rw [PhysicalRetryTail.experiment_mean_add]
  apply mean_mono
  intro d
  by_cases hd : P d
  · rw [PhysicalRetryTail.halted_mean M k d (hP d hd)]
  · have h := (experiment M k d).mean_nonneg (event P)
      ((Experiment.all_true _).mono (fun d _ => event_nonneg P d))
    simpa only [event,ite_eq_right hd] using h

/-- A terminal event absent at every successful endpoint is bounded by
prefix failure even at times earlier than the stopping-prefix budget. -/
theorem absent_event_bound (M : PhysicalPost.Table Γ Q) (out : Option A → Cfg Γ Q)
    (c : Cfg Γ Q) (p : Experiment (Option A)) (hp : Implements M out c p)
    (hhalt : ∀ a,(out (some a)).state=none) (P : Cfg Γ Q → Prop)
    (hP : ∀ d,P d → d.state=none) (habsent : ∀ a,¬P (out (some a))) (n : ℕ) :
    (experiment M n c).mean (event P)≤p.mean (fun o => if o=none then 1 else 0) := by
  have hu := (stopped_event_bounds M out c p hp hhalt P (max n p.cost) (le_max_right _ _)).2
  have hz : p.mean (fun o => o.elim 0 (fun a => event P (out (some a))))=0 := by
    have he : (fun o : Option A => o.elim 0 (fun a => event P (out (some a))))=
        (fun _ => (0:ℚ)) := by
      funext o; cases o with
      | none => rfl
      | some a => simp only [Option.elim_some,event,ite_eq_right (habsent a)]
    rw [he,PhysicalPartialSequence.mean_const]
  rw [hz,zero_add] at hu
  exact (terminal_event_monotone M c P hP (le_max_left _ _)).trans hu

lemma run_halted_iff (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).state=none ↔
      (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=none := by
  let : Inhabited {q //q∈P.states} := ⟨⟨P.entry,P.entry_mem⟩⟩
  have he := congrArg Cfg.state (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))
  rw [Program.machine,restrictedMachine_run]
  change ((execute (restrict P.table P.states P.supported) n
    ⟨some default,Tape.mk₁ input⟩ (extend b)).state.map enumeration)=none ↔ _
  change (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=_ at he
  rw [he]
  simp only [liftCfg,Option.map_eq_none_iff]

end
end ContingencyTables.PhysicalEventBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPublicLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact public output law and almost-sure termination -/

namespace ContingencyTables.ExactPublicLaw
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalEventBounds PhysicalPublicLaw ExactPublicPrefix SmallGraphProfiles
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] ExactPublicPrefix.program ExactPublicPrefix.output
  ExactTablePrefix.experiment correctionPrecision
  PublishedInputs.FiniteBoxPrekopaLeindler PublishedInputs.FiniteCheeger
  CompletionCounts.dimensionAllowance

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)

lemma error_limit : Filter.Tendsto (prefixError r c) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).const_mul (1/(2:ℝ)^correctionPrecision r c)
  change Filter.Tendsto (fun N => (1/(2:ℝ)^(correctionPrecision r c))*(1/2:ℝ)^N) _ _
  simpa only [mul_zero] using h

section Conditional
variable
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin q) (4*k^8)))
    (htotal : (∑ i,r i)=∑ j,c j)
include hPL hCheeger htotal

lemma prefix_error (N : ℕ) :
    ((ExactTablePrefix.experiment r c N).mean (fun o => if o=none then 1 else 0):ℝ)≤prefixError r c N := by
  have h := ExactTablePrefix.failure_bound r c (hPL _) (hCheeger _ d) htotal N
  have hR := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [prefixError,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using hR

/-- Every finite halted public execution is feasible, including events of
arbitrarily small positive probability. -/
theorem halted_feasible_oai (t : ℕ) (bits : Bits t)
    (hh : (MatchingFPRAS.run machine (Algorithms.encodeMargins r c) bits).state=none) :
    ∃ X : Table r c,Algorithms.OutputsTable machine (Algorithms.encodeMargins r c) bits X.val := by
  let bad : Cfg Symbol program.State → Prop := fun cfg => cfg.state=none ∧
    ¬∃ X : Table r c,cfg.tape.right₀=ListBlank.mk (Algorithms.encodeMatrix X.val)
  have hb (N : ℕ) :
      ((experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean
        (event bad):ℝ)≤prefixError r c N := by
    obtain ⟨p,hp,hm⟩ := prefix_correct r c htotal N
    have h := absent_event_bound program.table (output r c) _ p hp (output_halted r c) bad
      (fun cfg hd => hd.1) (by intro X hX; exact hX.2 ⟨X,output_tape r c X⟩) t
    rw [hm] at h
    exact (show ((experiment program.table t (program.initial
      (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean (event bad):ℝ)≤
      ((ExactTablePrefix.experiment r c N).mean (fun o => if o=none then 1 else 0):ℝ) by
        exact_mod_cast h).trans (prefix_error r c hPL hCheeger htotal N)
  have hzR := ge_of_tendsto' (error_limit r c) hb
  have hz : (experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean
      (event bad)=0 := by
    have hnonneg := (experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean_nonneg
      (event bad) ((Experiment.all_true _).mono (fun cfg _ => event_nonneg bad cfg))
    exact le_antisymm (by exact_mod_cast hzR) hnonneg
  have hall : (experiment program.table t (program.initial
      (Tape.mk₁ (Algorithms.encodeMargins r c)))).All (fun cfg => ¬bad cfg) := by
    rw [Experiment.all_indicator]
    change (experiment program.table t (program.initial
      (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean (fun cfg => if ¬bad cfg then 0 else 1)=0
    have he : (fun cfg : Cfg Symbol program.State => if ¬bad cfg then (0:ℚ) else 1)=event bad := by
      funext cfg
      by_cases hb : bad cfg <;> simp [event,hb]
    rw [he]
    exact hz
  have hn := Experiment.all_run _ _ hall (extend bits)
  rw [experiment_run] at hn
  have hh' := (run_halted_iff program (Algorithms.encodeMargins r c) t bits).mp hh
  have hout : ∃ X : Table r c,(execute program.table t (program.initial
      (Tape.mk₁ (Algorithms.encodeMargins r c))) (extend bits)).tape.right₀=
      ListBlank.mk (Algorithms.encodeMatrix X.val) := by
    by_contra h
    exact hn ⟨hh',h⟩
  obtain ⟨X,hX⟩ := hout
  exact ⟨X,hh,(congrArg Tape.right₀ (Program.run_tape program _ t bits)).trans hX⟩

end Conditional
end
end ContingencyTables.ExactPublicLaw

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.ExactPublicLaw.halted_feasible_oai := @OAI.ContingencyTables.ExactPublicLaw.halted_feasible_oai

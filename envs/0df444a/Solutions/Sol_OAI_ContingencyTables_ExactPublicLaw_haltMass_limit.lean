-- Prove2me | solution 1 for OAI.ContingencyTables.ExactPublicLaw.haltMass_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:56:45.739307+00:00
-- url     : https://prove2.me/submissions/56ebe00a-1549-4db6-8a00-d08bdfd8738d

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRetryTail
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
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

private lemma mean_mono {A : Type} (p : Experiment A) (f g : A → ℚ) (h : ∀ a,f a≤g a) :
    p.mean f≤p.mean g := by
  induction p with
  | done a => exact h a
  | read p ih => simp only [Experiment.mean]; linarith [ih false,ih true]
  | delay n p ih => exact ih

private lemma mean_const {A : Type} (p : Experiment A) (c : ℚ) : p.mean (fun _ => c)=c := by
  induction p with
  | done => rfl
  | read p ih => simp only [Experiment.mean,ih]; ring
  | delay n p ih => exact ih

lemma live_nonnegative (c : Cfg Γ Q) : 0≤live c := by unfold live; split_ifs <;> norm_num
lemma live_le_one (c : Cfg Γ Q) : live c≤1 := by unfold live; split_ifs <;> norm_num

lemma tail_nonnegative (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (c : Cfg Γ Q) (n : ℕ) : 0≤tail M c n := by
  have hm:=mean_mono (experiment M n c) (fun _ => 0) live live_nonnegative
  rw [mean_const] at hm
  unfold tail
  exact_mod_cast hm

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

/-- All successful prefix executions have halted by the prefix cost.
This implication is enough even though the failed endpoint is still live. -/
theorem tail_le_failure (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (out : Option B → Cfg Γ Q) (c : Cfg Γ Q)
    (p : Experiment (Option B)) (hp : Implements M out c p)
    (hhalt : ∀ b,(out (some b)).state=none) (n : ℕ) (hn : p.cost≤n) :
    tail M c n≤(p.mean (fun b => if b=none then 1 else 0):ℚ) := by
  have hb : (experiment M n c).mean live≤p.mean (fun b => if b=none then 1 else 0) := by
    rw [←physical_law,←Experiment.average_run p _ n hn]
    unfold average
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro b _
    cases he:(p.run (extend b)).1 with
    | none => simp only [ite_true, if_true]; exact live_le_one _
    | some x =>
      have hh : (out (p.run (extend b)).1).state=none := by rw [he]; exact hhalt x
      rw [padded_halted_result M out c p hp n hn (extend b) hh]
      simp [he,live,hhalt]
  unfold tail
  exact_mod_cast hb

end ContingencyTables.PhysicalRetryTail

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

lemma output_halted (X : Table r c) : (output r c (some X)).state=none := rfl

end
end ContingencyTables.ExactPublicPrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalEventBounds
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
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

/-- Prefix accuracy transfers to physical time without assuming a
uniform bound on the number of steps in the prefix. -/
lemma tendsto_of_prefix_bounds (f a b : ℕ → ℝ) (L : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds L))
    (hb : Filter.Tendsto b Filter.atTop (nhds 0))
    (h : ∀ N,∃ S,∀ t,S≤t → a N≤f t ∧ f t≤a N+b N) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨Na,hNa⟩ := Metric.tendsto_atTop.1 ha (ε/2) (by linarith)
  obtain ⟨Nb,hNb⟩ := Metric.tendsto_atTop.1 hb (ε/2) (by linarith)
  obtain ⟨S,hS⟩ := h (max Na Nb)
  refine ⟨S,?_⟩
  intro t ht
  have h1 := hNa (max Na Nb) (le_max_left _ _)
  have h2 := hNb (max Na Nb) (le_max_right _ _)
  rw [Real.dist_eq] at h1 h2 ⊢
  have ha' := abs_lt.mp h1
  have hb' := abs_lt.mp h2
  have hh := hS t ht
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

lemma mean_one_sub (p : Experiment A) (f : A → ℚ) :
    p.mean (fun a => 1-f a)=1-p.mean f := by
  induction p with
  | done a => rfl
  | read p ih => simp only [Experiment.mean,ih]; ring
  | delay n p ih => exact ih

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPublicLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public probabilities and physical terminal events -/

namespace ContingencyTables.PhysicalPublicLaw
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalEventBounds
open scoped BigOperators Classical
noncomputable section

lemma haltMass_eq (P : Program) (input : List Symbol) (t : ℕ) :
    Algorithms.haltMass P.machine input t=
      ((experiment P.table t (P.initial (Tape.mk₁ input))).mean
        (event (fun d => d.state=none)):ℝ) := by
  have hm := physical_law P.table t (P.initial (Tape.mk₁ input))
    (event (fun d => d.state=none))
  have ha : average (fun b : Bits t => event (fun d => d.state=none)
      (execute P.table t (P.initial (Tape.mk₁ input)) (extend b)))=
      ((Finset.univ.filter fun b : Bits t => (MatchingFPRAS.run P.machine input b).state=none).card:ℚ)/
        (2:ℚ)^t := by
    simp only [average,event,←run_halted_iff,Finset.sum_boole]
  rw [ha] at hm
  have hc := congrArg (fun x : ℚ => (x:ℝ)) hm
  simpa only [Algorithms.haltMass,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using hc

lemma tail_eq (P : Program) (input : List Symbol) (t : ℕ) :
    1-Algorithms.haltMass P.machine input t=
      PhysicalRetryTail.tail P.table (P.initial (Tape.mk₁ input)) t := by
  rw [haltMass_eq]
  have he : event (fun d : Cfg Symbol P.State => d.state=none)=
      fun d => 1-PhysicalRetryTail.live d := by
    funext d
    unfold event PhysicalRetryTail.live
    split_ifs <;> norm_num
  rw [he,mean_one_sub]
  simp only [Rat.cast_sub,Rat.cast_one,PhysicalRetryTail.tail]
  ring

end
end ContingencyTables.PhysicalPublicLaw

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

theorem tail_limit :
    Filter.Tendsto (PhysicalRetryTail.tail program.table
      (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))) Filter.atTop (nhds 0) := by
  apply tendsto_of_prefix_bounds _ (fun _ => 0) (prefixError r c) 0 tendsto_const_nhds (error_limit r c)
  intro N
  obtain ⟨p,hp,hm⟩ := prefix_correct r c htotal N
  refine ⟨p.cost,?_⟩
  intro t ht
  have h := PhysicalRetryTail.tail_le_failure program.table (output r c) _ p hp
    (output_halted r c) t ht
  rw [hm] at h
  exact ⟨PhysicalRetryTail.tail_nonnegative _ _ _,
    (h.trans (prefix_error r c hPL hCheeger htotal N)).trans_eq (zero_add _).symm⟩

theorem haltMass_limit_oai :
    Filter.Tendsto (Algorithms.haltMass machine (Algorithms.encodeMargins r c))
      Filter.atTop (nhds 1) := by
  have h := (tail_limit r c hPL hCheeger htotal).const_sub 1
  have he : (fun t => 1-PhysicalRetryTail.tail program.table
      (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c))) t)=
      Algorithms.haltMass machine (Algorithms.encodeMargins r c) := by
    funext t
    rw [←tail_eq]
    change 1-(1-Algorithms.haltMass program.machine (Algorithms.encodeMargins r c) t)=
      Algorithms.haltMass program.machine (Algorithms.encodeMargins r c) t
    ring
  simpa only [he,sub_zero] using h

end Conditional
end
end ContingencyTables.ExactPublicLaw

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.ExactPublicLaw.haltMass_limit_oai := @OAI.ContingencyTables.ExactPublicLaw.haltMass_limit_oai

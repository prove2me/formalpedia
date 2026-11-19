-- Prove2me | solution 1 for KoanaKPaths.Main.graph_estimator_machine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:31:19.937511+00:00
-- url     : https://prove2.me/submissions/fd315855-aa27-4421-b6ed-4ad85694df41

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Main_Inputs
import Definitions.Def_KoanaKPaths_MedianOfMeans
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Input_readGraph_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_positiveRaw_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_wholeCost_budget
import Theorems.Thm_KoanaKPaths_Machine_finite_stack_compilation
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_exec_flat_sol_aux
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S P : ℕ}



































lemma nbits_eq_bits (n : ℕ) : nbits n = Nat.bits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nbits]
  | bit b n hn ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro hz
      cases b <;> simp_all [Nat.bit]
    rw [nbits,dif_neg hne,Nat.bit_mod_two,Nat.bit_div_two,ih,Nat.bits_append_bit n b hn]
    cases b <;> rfl

















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}














@[simp] lemma enc_work_stk (s : IState S) (i : Fin S) : (encI s).stk (ι i) = encL (s.G i) := by
  simp [encI,ι,i.isLt]













end KoanaKPaths.Machine

end

section

namespace KoanaKPaths.Machine.Raw
open NLogN
variable {S P : ℕ} {I : List Sym} {prog : Fin P→Stmt S P}
variable {p q : Stmt S P} {s s1 s2 : St S} {c d : ℕ}
lemma of_exec (h : Exec I prog p s s1 c) : Runs I prog p s s1 c := ⟨c,le_rfl,h⟩
lemma mono (h : Runs I prog p s s1 c) (hc : c≤d) : Runs I prog p s s1 d := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht.trans hc,h⟩
lemma seq (h1 : Runs I prog p s s1 c) (h2 : Runs I prog q s1 s2 d) :
    Runs I prog (.seq p q) s s2 (c+d) := by
  obtain ⟨t,ht,h1⟩ := h1
  obtain ⟨u,hu,h2⟩ := h2
  exact ⟨t+u,Nat.add_le_add ht hu,.seq h1 h2⟩
end KoanaKPaths.Machine.Raw

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main HypergraphUnreliability.FPRAS
attribute [local simp] Coins


lemma rawProg_correct (j : Fin 1) : rawProg j=compile (Wedge.prog j) := rfl









end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {P : ℕ}

lemma enc_nat (n : ℕ) : Item.enc (.int (n : ℤ))=hdPos::(Nat.bits n).map codeBit := by
  simp [Item.enc,hdOf,zbits,nbits_eq_bits]

lemma bits_pos_nonempty {n : ℕ} (hn : 0< n) : Nat.bits n≠[] := by
  intro he
  have hlen : (Nat.bits n).length=0 := by rw [he]; rfl
  rw [Nat.size_eq_bits_len] at hlen
  have hn0 : n=0 := Nat.size_eq_zero.mp hlen
  omega



lemma zeroFraction_exec (I : List Sym) (prog : Fin P→Stmt (128+4) P) (σ : St (128+4)) :
    Exec I prog zeroFraction σ (σ.setOut (σ.out++HypergraphUnreliability.FPRAS.fracCode ⟨0,1⟩)) 4 := by
  have h := Exec.seq (Exec.out (I := I) (prog := prog) σ false)
    (Exec.seq (Exec.out (σ.outB false) true)
      (Exec.seq (Exec.out ((σ.outB false).outB true) false) (Exec.out (((σ.outB false).outB true).outB false) true)))
  change Exec I prog zeroFraction σ _ 4 at h
  have he : (((σ.outB false).outB true).outB false).outB true=
      σ.setOut (σ.out++HypergraphUnreliability.FPRAS.fracCode ⟨0,1⟩) := by
    apply St.ext
    · rfl
    · rfl
    · simp [St.outB,St.setOut,HypergraphUnreliability.FPRAS.fracCode,HypergraphUnreliability.FPRAS.natCode,List.append_assoc]
  rw [he] at h
  exact h

lemma header_restores (s : IState 128) (n : ℕ) (hn : s.G 53=[.int (n : ℤ)]) :
    ((encI s).pop (ι (53 : Fin 128))).push (ι (53 : Fin 128)) hdPos=encI s := by
  apply St.ext
  · funext r
    by_cases hr : r=ι (53 : Fin 128)
    · subst r
      simp [St.push,St.pop,encI,encL,hn,enc_nat,ι]
    · simp [St.push,St.pop,hr]
  · rfl
  · rfl

lemma header_positive (s : IState 128) (n : ℕ) (hn : s.G 53=[.int (n : ℤ)]) (hpos : 0< n) :
    isBitT (((encI s).pop (ι (53 : Fin 128))).top (ι (53 : Fin 128)))=true := by
  have hnon := bits_pos_nonempty hpos
  cases he : Nat.bits n with
  | nil => exact False.elim (hnon he)
  | cons b bs =>
    cases b <;> simp [St.top,St.pop,encI,encL,hn,enc_nat,ι,he,isBitT,codeBit,bitOf]

lemma header_zero (s : IState 128) (hn : s.G 53=[.int (0 : ℤ)]) :
    isBitT (((encI s).pop (ι (53 : Fin 128))).top (ι (53 : Fin 128)))=false := by
  simp [St.top,St.pop,encI,encL,hn,Item.enc,hdOf,zbits,nbits_eq_bits,ι,isBitT,bitOf]

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine.Raw
variable {S P : ℕ} {I : List Sym} {prog : Fin P→Stmt S P}
variable {p q : Stmt S P} {s t : St S} {c : ℕ}
lemma iteT {i : Fin S} {f : Option Sym→Bool} (hf : f (s.top i)=true)
    (h : Runs I prog p s t c) : Runs I prog (.ite i f p q) s t (c+1) := by
  obtain ⟨u,hu,h⟩ := h
  exact ⟨u+1,by omega,.iteT hf h⟩
lemma iteF {i : Fin S} {f : Option Sym→Bool} (hf : f (s.top i)=false)
    (h : Runs I prog q s t c) : Runs I prog (.ite i f p q) s t (c+1) := by
  obtain ⟨u,hu,h⟩ := h
  exact ⟨u+1,by omega,.iteF hf h⟩
end KoanaKPaths.Machine.Raw

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main HypergraphUnreliability.FPRAS





lemma graphRoot_runs (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool)
    (hk : 1≤ k) (hTape : sampleBits n k a b≤ tape.length) :
    ∃ σ, Runs (logicalInput (graphInputControls n arcs k a b) tape) rawProg graphRoot (St.init (NS+4)) σ
      (rootCost n arcs k a b tape) ∧ σ.out=fracCode (tapeEstimate n arcs k a b tape) := by
  let I := logicalInput (graphInputControls n arcs k a b) tape
  let s := Input.parsedState n arcs k a b
  let σp := (encI s).pop (ι (53 : Fin NS))
  have hhead : s.G 53=[.int (n : ℤ)] := by
    simp [s,Input.parsedState,storeFields,Input.headerFields,Input.initial,IState.upd,Input.DB,
      Input.VertexField,Input.PathField,Input.AccuracyField,Input.ConfidenceField,Input.ArcCountField]
  have hfront : Runs I rawProg Input.readGraph (St.init (NS+4)) (encI s) (Input.graphReadCost n arcs k a b) :=
    Input.readGraph_runs rawProg Wedge.prog rawProg_correct n arcs k a b tape
  have hpop : Exec I rawProg (.pop (ι (53 : Fin NS))) (encI s) σp 1 := Exec.pop _ _
  by_cases hz : n=0
  · have hcond : isBitT (σp.top (ι (53 : Fin NS)))=false :=
      header_zero s (by simpa only [hz,Nat.cast_zero] using hhead)
    have hzero := zeroFraction_exec I rawProg σp
    have hb := Raw.iteF (p := .seq (.push (ι (53 : Fin NS)) hdPos) positiveRaw) hcond (Raw.of_exec hzero)
    have h := Raw.seq hfront (Raw.seq (Raw.of_exec hpop) hb)
    refine ⟨σp.setOut (σp.out++fracCode ⟨0,1⟩),?_,?_⟩
    · change Runs I rawProg graphRoot (St.init (NS+4)) _ _ at h
      exact Raw.mono h (by simp [rootCost,hz])
    · simp [St.setOut,σp,St.pop,s,Input.parsedState,storeFields,Input.headerFields,Input.initial,tapeEstimate,hz]
  · have hpos : 0< n := by omega
    obtain ⟨σ,hpositive,hout⟩ := positiveRaw_runs n arcs k a b tape hk hTape
    have hrest := header_restores s n hhead
    have hpush : Exec I rawProg (.push (ι (53 : Fin NS)) hdPos) σp (encI s) 1 := by
      simpa only [σp,hrest] using Exec.push (I := I) (prog := rawProg) σp (ι (53 : Fin NS)) hdPos
    have hcond : isBitT (σp.top (ι (53 : Fin NS)))=true := header_positive s n hhead hpos
    have hb := Raw.iteT (q := zeroFraction) hcond (Raw.seq (Raw.of_exec hpush) hpositive)
    have h := Raw.seq hfront (Raw.seq (Raw.of_exec hpop) hb)
    refine ⟨σ,?_,?_⟩
    · change Runs I rawProg graphRoot (St.init (NS+4)) σ _ at h
      exact Raw.mono h (by simp [rootCost,hz]; omega)
    · simpa only [tapeEstimate,if_neg hz] using hout

end KoanaKPaths.Machine.Trial

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}

lemma generic_stmt_size_pos (p : Stmt S P) : 0 < p.size := by
  induction p <;> simp only [Stmt.size] <;> omega

lemma generic_instrAt_placed (ent : Fin P → ℕ) (p : Stmt S P) (code : ℕ → Instr S) (a e : ℕ)
    (hcode : ∀ x, a ≤ x → x < a+p.size → code x = (p.instrAt ent a e x).getD .ret) :
    Placed code ent p a e := by
  induction p generalizing a e with
  | skip => simpa [Placed,Stmt.instrAt] using hcode a (by omega) (by simp [Stmt.size])
  | push i v => simpa [Placed,Stmt.instrAt] using hcode a (by omega) (by simp [Stmt.size])
  | pop i => simpa [Placed,Stmt.instrAt] using hcode a (by omega) (by simp [Stmt.size])
  | inRd i => simpa [Placed,Stmt.instrAt] using hcode a (by omega) (by simp [Stmt.size])
  | out v => simpa [Placed,Stmt.instrAt] using hcode a (by omega) (by simp [Stmt.size])
  | seq p q ihp ihq =>
    constructor
    · apply ihp
      intro x hx hx'
      have h := hcode x hx (by simp only [Stmt.size]; omega)
      simpa only [Stmt.instrAt,if_pos hx'] using h
    · apply ihq
      intro x hx hx'
      have h := hcode x (by omega) (by simp only [Stmt.size]; omega)
      simpa only [Stmt.instrAt,if_neg (by omega : ¬ x < a+p.size)] using h
  | ite i f p q ihp ihq =>
    refine ⟨?_,?_,?_⟩
    · simpa [Placed,Stmt.instrAt] using hcode a (by omega) (by simp only [Stmt.size]; omega)
    · apply ihp
      intro x hx hx'
      have h := hcode x (by omega) (by simp only [Stmt.size]; omega)
      simpa only [Stmt.instrAt,if_neg (by omega : x ≠ a),if_pos hx'] using h
    · apply ihq
      intro x hx hx'
      have h := hcode x (by omega) (by simp only [Stmt.size]; omega)
      simpa only [Stmt.instrAt,if_neg (by omega : x ≠ a),if_neg (by omega : ¬ x < a+1+p.size)] using h
  | loop i f p ih =>
    constructor
    · simpa [Placed,Stmt.instrAt] using hcode a (by omega) (by simp only [Stmt.size]; omega)
    · apply ih
      intro x hx hx'
      have h := hcode x (by omega) (by simp only [Stmt.size]; omega)
      simpa only [Stmt.instrAt,if_neg (by omega : x ≠ a)] using h
  | call j => simpa [Placed,Stmt.instrAt] using hcode a (by omega) (by simp [Stmt.size])

lemma generic_instrAt_none_ge (ent : Fin P → ℕ) (p : Stmt S P) (a e x : ℕ) (hx : a+p.size ≤ x) :
    p.instrAt ent a e x = none := by
  induction p generalizing a e x with
  | skip => simp [Stmt.instrAt,show x ≠ a by simp only [Stmt.size] at hx; omega]
  | push i v => simp [Stmt.instrAt,show x ≠ a by simp only [Stmt.size] at hx; omega]
  | pop i => simp [Stmt.instrAt,show x ≠ a by simp only [Stmt.size] at hx; omega]
  | inRd i => simp [Stmt.instrAt,show x ≠ a by simp only [Stmt.size] at hx; omega]
  | out v => simp [Stmt.instrAt,show x ≠ a by simp only [Stmt.size] at hx; omega]
  | seq p q ihp ihq =>
    simp only [Stmt.size] at hx
    rw [Stmt.instrAt,if_neg (by omega)]
    exact ihq _ _ _ (by omega)
  | ite i f p q ihp ihq =>
    simp only [Stmt.size] at hx
    rw [Stmt.instrAt,if_neg (by omega),if_neg (by omega)]
    exact ihq _ _ _ (by omega)
  | loop i f p ih =>
    simp only [Stmt.size] at hx
    rw [Stmt.instrAt,if_neg (by omega)]
    exact ih _ _ _ (by omega)
  | call j => simp [Stmt.instrAt,show x ≠ a by simp only [Stmt.size] at hx; omega]

lemma generic_instrAt_valid (ent : Fin P → ℕ) (L : ℕ) (hent : ∀ j, ent j < L) (p : Stmt S P) (a e : ℕ) (hs : a+p.size < L) (he : e < L) (x : ℕ) :
    Instr.Valid L ((p.instrAt ent a e x).getD .ret) := by
  induction p generalizing a e x with
  | skip => simp only [Stmt.instrAt]; split_ifs <;> simp_all [Instr.Valid]
  | push i v => simp only [Stmt.instrAt]; split_ifs <;> simp_all [Instr.Valid]
  | pop i => simp only [Stmt.instrAt]; split_ifs <;> simp_all [Instr.Valid]
  | inRd i => simp only [Stmt.instrAt]; split_ifs <;> simp_all [Instr.Valid]
  | out v => simp only [Stmt.instrAt]; split_ifs <;> simp_all [Instr.Valid]
  | seq p q ihp ihq =>
    have hq := generic_stmt_size_pos q
    simp only [Stmt.size] at hs
    rw [Stmt.instrAt]
    split_ifs
    · exact ihp a (a+p.size) (by omega) (by omega) x
    · exact ihq (a+p.size) e (by omega) he x
  | ite i f p q ihp ihq =>
    have hq := generic_stmt_size_pos q
    simp only [Stmt.size] at hs
    rw [Stmt.instrAt]
    split_ifs
    · simp only [Option.getD_some,Instr.Valid]
      constructor <;> omega
    · exact ihp (a+1) e (by omega) he x
    · exact ihq (a+1+p.size) e (by omega) he x
  | loop i f p ih =>
    simp only [Stmt.size] at hs
    rw [Stmt.instrAt]
    split_ifs
    · simp only [Option.getD_some,Instr.Valid]
      constructor <;> omega
    · exact ih (a+1) a (by omega) (by omega) x
  | call j => simp only [Stmt.instrAt]; split_ifs <;> simp_all [Instr.Valid]





lemma oneProcCode_progPlaced (proc root : Stmt S 1) :
    ProgPlaced (oneProcCode proc root) (fun _ => proc) (fun _ => 0) := by
  intro j
  constructor
  · apply generic_instrAt_placed
    intro x hx hx'
    simp only [zero_add] at hx'
    simp [oneProcCode,hx']
  · simp [oneProcCode]

lemma oneProcCode_rootPlaced (proc root : Stmt S 1) :
    Placed (oneProcCode proc root) (fun _ => 0) root (proc.size+1) (proc.size+1+root.size) := by
  apply generic_instrAt_placed
  intro x hx hx'
  simp [oneProcCode,show ¬ x<proc.size by omega,show x≠proc.size by omega]

lemma oneProcCode_ret (proc root : Stmt S 1) :
    oneProcCode proc root (proc.size+1+root.size) = .ret := by
  unfold oneProcCode
  rw [if_neg (by omega),if_neg (by have := generic_stmt_size_pos root; omega)]
  rw [generic_instrAt_none_ge (fun _ => 0) root _ _ _ (by omega)]
  rfl

lemma oneProcCode_valid (proc root : Stmt S 1) :
    ∀ x < proc.size+1+root.size+1,
      Instr.Valid (proc.size+1+root.size+1) (oneProcCode proc root x) := by
  intro x hx
  unfold oneProcCode
  split_ifs with hp he
  · exact generic_instrAt_valid (fun _ => 0) _ (by intro j; omega) proc 0 proc.size (by omega) (by omega) x
  · trivial
  · exact generic_instrAt_valid (fun _ => 0) _ (by intro j; omega) root (proc.size+1)
      (proc.size+1+root.size) (by omega) (by omega) x

lemma recursive_program_runsWithin (proc root : Stmt S 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ input tape σ t,
      Exec (logicalInput input tape) (fun _ => proc) root (St.init S) σ t →
      (flatMachine (proc.size+1+root.size) (proc.size+1) (oneProcCode proc root)).RunsWithin
        input tape (A*(t+σ.out.length+2)) σ.out := by
  obtain ⟨A,hA,hM⟩ := finite_stack_compilation S (proc.size+1+root.size) (proc.size+1)
    (oneProcCode proc root) (by have := generic_stmt_size_pos root; omega) (oneProcCode_valid proc root)
  refine ⟨A,hA,?_⟩
  intro input tape σ t ht
  have hs := NLogN.exec_flat_sol_aux (oneProcCode_progPlaced proc root) ht _ _
    (oneProcCode_rootPlaced proc root) []
  exact hM input tape ⟨proc.size+1+root.size,σ,[]⟩ t hs (oneProcCode_ret proc root) rfl

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine
open HypergraphUnreliability.FPRAS
variable {S : ℕ}
lemma recursive_program_machine (proc root : Stmt S 1) :
    ∃ (M : CoinMachine) (A : ℕ), 0< A ∧ ∀ input tape σ t,
      Exec (logicalInput input tape) (fun _ => proc) root (St.init S) σ t →
      M.RunsWithin input tape (A*(t+σ.out.length+2)) σ.out := by
  obtain ⟨A,hA,hM⟩ := recursive_program_runsWithin proc root
  exact ⟨_,A,hA,hM⟩
end KoanaKPaths.Machine

end

section

set_option autoImplicit false
namespace HypergraphUnreliability.FPRAS.CoinMachine
lemma RunsWithin.mono {M : CoinMachine} {input tape out : List Bool} {B C : ℕ}
    (h : M.RunsWithin input tape B out) (hBC : B≤ C) : M.RunsWithin input tape C out := by
  obtain ⟨s,c,hs,hcfg,hhalt,hout,hcoin⟩ := h
  exact ⟨s,c,hs.trans hBC,hcfg,hhalt,hout,fun s' hs' c' hcfg' =>
    (hcoin s' hs' c' hcfg').trans (Nat.add_le_add_left hBC _)⟩
end HypergraphUnreliability.FPRAS.CoinMachine

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main HypergraphUnreliability.FPRAS

lemma actual_machine_runs : ∃ (M : CoinMachine) (A : ℕ), 0< A ∧ ∀ (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool),
    1≤ k → sampleBits n k a b≤ tape.length →
    M.RunsWithin (graphInputControls n arcs k a b) tape
      (A*(rootCost n arcs k a b tape+(fracCode (tapeEstimate n arcs k a b tape)).length+2))
      (fracCode (tapeEstimate n arcs k a b tape)) := by
  obtain ⟨M,A,hA,hMachine⟩ := recursive_program_machine (compile Wedge.body) graphRoot
  refine ⟨M,A,hA,?_⟩
  intro n arcs k a b tape hk hTape
  obtain ⟨σ,hr,hout⟩ := graphRoot_runs n arcs k a b tape hk hTape
  obtain ⟨t,ht,hexec⟩ := hr
  have hM := hMachine (graphInputControls n arcs k a b) tape σ t hexec
  rw [hout] at hM
  apply CoinMachine.RunsWithin.mono hM
  exact Nat.mul_le_mul_left A (by omega)

end KoanaKPaths.Machine.Trial

end

section

namespace KoanaKPaths.Main

lemma trialBits_le (n k s : ℕ) : trialBits n k ≤ 3*(1+k+n+s)^4 := by
  let P := 1+k+n+s
  have hn : n ≤ P := by dsimp [P]; omega
  have hk : k ≤ P := by dsimp [P]; omega
  have hp : 1 ≤ P := by dsimp [P]; omega
  have hp2 : P^2 ≤ P^4 := Nat.pow_le_pow_right hp (by omega)
  have h1 : n*k ≤ P^4 := (Nat.mul_le_mul hn hk).trans (by simpa [pow_two] using hp2)
  have h2 : k*n ≤ P^4 := by simpa only [Nat.mul_comm] using h1
  have h3 : (k-1)*(k*(k*n)) ≤ P^4 := by
    calc
      _ ≤ P*(P*(P*P)) := Nat.mul_le_mul (le_trans (Nat.sub_le k 1) hk)
        (Nat.mul_le_mul hk (Nat.mul_le_mul hk hn))
      _ = P^4 := by ring
  unfold trialBits
  change n*k+(k*n+(k-1)*(k*(k*n))) ≤ 3*P^4
  omega

lemma sampleBits_le_budget (n k a b s : ℕ) :
    sampleBits n k a b ≤ timeBudget 6144 7 k (n+s) a b := by
  let P := 1+k+n+s
  have hk : k ≤ P := by dsimp [P]; omega
  have hpow : k^3 ≤ P^3 := Nat.pow_le_pow_left hk 3
  have ht : trialBits n k ≤ 3*P^4 := trialBits_le n k s
  have hq : 2*b+1 ≤ 2*(b+1) := by omega
  have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by omega)
  unfold sampleBits groupTrials timeBudget
  calc
    _ ≤ (2*(b+1))*(1024*P^3*4^a)*(3*P^4) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq (Nat.mul_le_mul_right (4^a)
        (Nat.mul_le_mul_left 1024 hpow))) ht
    _ = 6144*P^7*4^a*(b+1) := by ring
    _ ≤ 6144*2^k*P^7*4^a*(b+1) := by gcongr; omega
    _ = _ := by dsimp [P]; congr 4 <;> omega

end KoanaKPaths.Main

end

section

set_option autoImplicit false
namespace KoanaKPaths.Main
lemma timeBudget_mono {K K' c c' k size a b : ℕ} (hK : K≤ K') (hc : c≤ c') :
    timeBudget K c k size a b≤ timeBudget K' c' k size a b := by
  unfold timeBudget
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_right
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hK) (Nat.pow_le_pow_right (by omega) hc)
end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open HypergraphUnreliability.FPRAS KoanaKPaths.Main KoanaKPaths.Machine.Trial

theorem solution :
    ∃ (M : CoinMachine) (K c : ℕ), ∀ (n : ℕ) (arcs : List (Fin n × Fin n)), arcs.Nodup →
      (∀ p ∈ arcs, p.1 ≠ p.2) → ∀ k : ℕ, 1 ≤ k → ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      sampleBits n k a b ≤ timeBudget K c k (n + (graphCode n arcs).length) a b ∧
      ∀ tape : List Bool, timeBudget K c k (n + (graphCode n arcs).length) a b < tape.length →
        M.RunsWithin (graphInputControls n arcs k a b) tape
          (timeBudget K c k (n + (graphCode n arcs).length) a b)
          (fracCode (tapeEstimate n arcs k a b tape)) := by
  obtain ⟨M,A,hA,hMachine⟩ := actual_machine_runs
  let C : ℕ := 10000000000000000000000000000
  let K : ℕ := 6144+A*C
  refine ⟨M,K,20,?_⟩
  intro n arcs hNodup hLoops k hk a b ha hb
  have hK : 6144≤ K := by dsimp [K]; omega
  have hsample : sampleBits n k a b≤ timeBudget K 20 k (n+(graphCode n arcs).length) a b :=
    (sampleBits_le_budget n k a b (graphCode n arcs).length).trans
      (timeBudget_mono hK (by decide))
  refine ⟨hsample,?_⟩
  intro tape hTape
  have hS : sampleBits n k a b≤ tape.length := hsample.trans (Nat.le_of_lt hTape)
  have hM := hMachine n arcs k a b tape hk hS
  apply CoinMachine.RunsWithin.mono hM
  have hwhole := wholeCost_budget n arcs k a b tape hk
  have hscale := Nat.mul_le_mul_left A hwhole
  have heq : A*timeBudget C 20 k (n+(graphCode n arcs).length) a b=
      timeBudget (A*C) 20 k (n+(graphCode n arcs).length) a b := by simp only [timeBudget,Nat.mul_assoc]
  change _≤ A*timeBudget C 20 k (n+(graphCode n arcs).length) a b at hscale
  rw [heq] at hscale
  exact hscale.trans (timeBudget_mono (by dsimp [K]; omega) le_rfl)

end

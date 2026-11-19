-- Prove2me | solution 1 for KoanaKPaths.Machine.Native.invariant_loop
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.047676+00:00
-- url     : https://prove2.me/submissions/98a845bb-7a82-4e18-ad65-fa65c9d0aa3c

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.Machine.Native
open NLogN
variable {S P : ℕ} {I : List Sym} {iprog : Fin P→IStmt S P} {p q : IStmt S P} {s s1 s2 : IState S} {c d : ℕ}

lemma mono (h : IRuns I iprog p s s1 c) (hc : c ≤ d) : IRuns I iprog p s s1 d := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht.trans hc,h⟩
lemma of_exec (h : IExec I iprog p s s1 c) : IRuns I iprog p s s1 c := ⟨c,le_rfl,h⟩





lemma loopT {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = true)
    (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog (.loop i f p) s1 s2 d) :
    IRuns I iprog (.loop i f p) s s2 (c+d+30) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d'+30,by omega,.loopT hf h1 h2⟩
lemma loopF {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = false) :
    IRuns I iprog (.loop i f p) s s 30 := of_exec (.loopF hf)

end KoanaKPaths.Machine.Native

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Native
variable {S P : ℕ}

/-- A bounded loop rule charging every body execution and every branch test. -/
lemma invariant_loop (I : List Sym) (prog : Fin P→IStmt S P) (counter : Fin S)
    (body : IStmt S P) (Inv : ℕ→IState S→Prop) (L C : ℕ) (tail : List Item)
    (ht : cls tail.head?≠Cls.mark)
    (hcounter : ∀ i≤ L, ∀ s, Inv i s → s.G counter=List.replicate (L-i) .mark ++ tail)
    (hstep : ∀ i< L, ∀ s, Inv i s → ∃ s', IRuns I prog body s s' C ∧ Inv (i+1) s')
    (s : IState S) (hs : Inv 0 s) :
    ∃ s', IRuns I prog (.loop counter (fun c => decide (c=Cls.mark)) body) s s'
      ((C+30)*L+30) ∧ Inv L s' := by
  have haux : ∀ remaining i, remaining+i=L → ∀ s, Inv i s →
      ∃ s', IRuns I prog (.loop counter (fun c => decide (c=Cls.mark)) body) s s'
        ((C+30)*remaining+30) ∧ Inv L s' := by
    intro remaining
    induction remaining with
    | zero =>
      intro i hi s hs
      have he : i=L := by omega
      subst i
      have hc := hcounter L le_rfl s hs
      have hcl : decide (s.cl counter=Cls.mark)=false := by simp [IState.cl,hc,ht]
      exact ⟨s,loopF hcl,hs⟩
    | succ remaining ih =>
      intro i hi s hs
      have hiL : i< L := by omega
      obtain ⟨s1,hbody,hInv⟩ := hstep i hiL s hs
      obtain ⟨s2,htail,hend⟩ := ih (i+1) (by omega) s1 hInv
      have hc := hcounter i (by omega) s hs
      have hlen : L-i=remaining+1 := by omega
      have hcl : decide (s.cl counter=Cls.mark)=true := by
        simp [IState.cl,hc,hlen,List.replicate_succ,cls]
      refine ⟨s2,?_,hend⟩
      have h := loopT hcl hbody htail
      apply mono h
      ring_nf
      exact le_rfl
  exact haux L 0 (by omega) s hs

end KoanaKPaths.Machine.Native

end

theorem solution :
∀ {S P : Nat} (I : List.{0} NLogN.Sym) (prog : Fin P → NLogN.IStmt S P) (counter : Fin S) (body : NLogN.IStmt S P)
  (Inv : Nat → NLogN.IState S → Prop) (L C : Nat) (tail : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hcounter :
    ∀ (i : Nat),
      @LE.le.{0} Nat instLENat i L →
        ∀ (s : NLogN.IState S),
          Inv i s →
            @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s counter)
              (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                (@List.replicate.{0} NLogN.Item (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L i)
                  NLogN.Item.mark)
                tail))
  (hstep :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        ∀ (s : NLogN.IState S),
          Inv i s →
            @Exists.{1} (NLogN.IState S) fun (s' : NLogN.IState S) =>
              And (@NLogN.IRuns S P I prog body s s' C)
                (Inv
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  s'))
  (s : NLogN.IState S) (hs : Inv (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s),
  @Exists.{1} (NLogN.IState S) fun (s' : NLogN.IState S) =>
    And
      (@NLogN.IRuns S P I prog
        (@NLogN.IStmt.loop S P counter
          (fun (c : NLogN.Cls) =>
            @Decidable.decide (@Eq.{1} NLogN.Cls c NLogN.Cls.mark) (NLogN.instDecidableEqCls c NLogN.Cls.mark))
          body)
        s s'
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) C
              (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            L)
          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
      (Inv L s') := by
  exact @KoanaKPaths.Machine.Native.invariant_loop

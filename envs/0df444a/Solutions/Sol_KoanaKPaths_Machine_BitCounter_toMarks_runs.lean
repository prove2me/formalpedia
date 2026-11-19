-- Prove2me | solution 1 for KoanaKPaths.Machine.BitCounter.toMarks_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.440874+00:00
-- url     : https://prove2.me/submissions/d7f030df-195f-4bf5-b5b8-8a4d734fd5de

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_BitCounter_buildLoop_exec
import Theorems.Thm_KoanaKPaths_Machine_BitCounter_extractLoop_runs
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


lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩





end KoanaKPaths.Machine.Native

end

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

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]























end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.BitCounter







attribute [local simp] Source Ruler Rem Bits Count Tmp













lemma buildCost_bound (m : ℕ) (bs : List Bool) :
    buildCost m bs+97*m ≤ 97*bitValue m bs+120*bs.length+30 := by
  induction bs generalizing m with
  | nil => simp [buildCost,bitValue]; omega
  | cons b bs ih =>
    have h := ih (2*m+b.toNat)
    simp only [buildCost,bitValue,List.length_cons]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] at * <;> omega


lemma bitValue_append (m : ℕ) (xs ys : List Bool) :
    bitValue m (xs++ys)=bitValue (bitValue m xs) ys := by
  induction xs generalizing m with
  | nil => rfl
  | cons b xs ih => simpa only [List.cons_append,bitValue] using ih (2*m+b.toNat)

lemma bitValue_reverse_bits (n : ℕ) : bitValue 0 n.bits.reverse=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn,List.reverse_cons,bitValue_append,ih]
    cases b <;> simp [bitValue,Nat.bit]











lemma toMarks_runs (I : List Sym) (s : IState NS) (n : ℕ) (st : List Item)
    (hs : s.G Source=.int (n : ℤ)::st) (ht : cls (s.G Count).head? ≠ Cls.mark)
    (hx : s.G Tmp=[]) :
    IRuns I Fin.elim0 toMarks s
      ((s.upd Source st).upd Count (List.replicate n .mark ++ s.G Count)) (1000*(n+1)) := by
  let s0 := s.upd Bits (.mark::s.G Bits)
  let s1 := s0.upd Ruler (.int 2::s0.G Ruler)
  let s2 := (s1.upd Source (.int 0::st)).upd Bits
    (n.bits.reverse.map (fun b => Item.int (bitInt b)) ++ s1.G Bits)
  let s3 := s2.upd Source st
  let s4 := (s3.upd Bits (.mark::s.G Bits)).upd Count (List.replicate n .mark ++ s3.G Count)
  let s5 := s4.upd Bits (s.G Bits)
  let s6 := s5.upd Ruler (s.G Ruler)
  have hz0 : zsz (0 : ℤ)=0 := by simp [zsz,zbits,nbits_eq_bits]
  have hz2 : zsz (2 : ℤ)=2 := by
    have hh : (2 : ℕ).size=2 := by simpa using (Nat.size_pow (n := 1))
    simpa [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len] using hh
  have h0 : IExec I Fin.elim0 (.op (.mark Bits)) s s0 1 := .op (.mark)
  have h1 : IExec I Fin.elim0 (.op (.const Ruler 2)) s0 s1 4 := by
    simpa only [hz2] using (IExec.op (IOp.Step.const (s := s0) (i := Ruler) 2) : IExec I Fin.elim0 _ _ _ _)
  have h2 : IRuns I Fin.elim0 extractLoop s1 s2 (528*n.size+30) :=
    extractLoop_runs I n s1 st (s0.G Ruler) (by simp [s1,s0,hs]) (by simp [s1])
  have h3 : IExec I Fin.elim0 (.op (.drop Source)) s2 s3 2 := by
    simpa only [hz0] using
      (IExec.op (IOp.Step.drop (I := I) (s := s2) (i := Source) (a := 0) (L := st) (by simp [s2])) : IExec I Fin.elim0 _ _ _ _)
  have h4 : IExec I Fin.elim0 buildLoop s3 s4 (buildCost 0 n.bits.reverse) := by
    have hh := buildLoop_exec I s3 0 n.bits.reverse (s.G Bits) (s3.G Count)
      (by simpa [s3,s2,s1,s0] using ht) (by simp [s3,s2,s1,s0]) (by simp)
      (by simp [s3,s2,s1,s0,hx])
    simpa only [bitValue_reverse_bits] using hh
  have h5 : IExec I Fin.elim0 (.op (.unmark Bits)) s4 s5 1 := by
    exact .op (.unmark (by simp [s4]))
  have h6 : IExec I Fin.elim0 (.op (.drop Ruler)) s5 s6 6 := by
    simpa only [hz2] using
      (IExec.op (IOp.Step.drop (I := I) (s := s5) (i := Ruler)
        (show s5.G Ruler=.int 2::s.G Ruler by simp [s5,s4,s3,s2,s1,s0])) : IExec I Fin.elim0 _ _ _ _)
  have he : s6=(s.upd Source st).upd Count (List.replicate n .mark ++ s.G Count) := by
    cases s
    simp only [s6,s5,s4,s3,s2,s1,s0,IState.upd]
    congr 1
    funext i
    by_cases hS : i=Source
    · subst i; simp [Function.update_apply]
    by_cases hC : i=Count
    · subst i; simp [Function.update_apply]
    by_cases hB : i=Bits
    · subst i; simp [Function.update_apply]
    by_cases hR : i=Ruler
    · subst i; simp [Function.update_apply]
    simp [Function.update_apply,hS,hC,hB,hR]
  have hrun := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1) (Native.seq h2
    (Native.seq (Native.of_exec h3) (Native.seq (Native.of_exec h4)
      (Native.seq (Native.of_exec h5) (Native.of_exec h6))))))
  change IRuns I Fin.elim0 toMarks s _ _ at hrun
  rw [he] at hrun
  apply Native.mono hrun
  have hb := buildCost_bound 0 n.bits.reverse
  simp only [zero_mul,Nat.add_zero,List.length_reverse,Nat.size_eq_bits_len,bitValue_reverse_bits] at hb
  have hn : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

end KoanaKPaths.Machine.BitCounter

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.BitCounter.NS) (n : Nat) (st : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Source)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) st))
  (ht :
    @Ne.{1} NLogN.Cls
      (NLogN.cls
        (@List.head?.{0} NLogN.Item
          (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Count)))
      NLogN.Cls.mark)
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.BitCounter.toMarks s
    (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Source st)
      KoanaKPaths.Machine.BitCounter.Count
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item n NLogN.Item.mark)
        (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Count)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @KoanaKPaths.Machine.BitCounter.toMarks_runs

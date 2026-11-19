-- Prove2me | solution 1 for KoanaKPaths.Machine.BitCounter.extractLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:15.374406+00:00
-- url     : https://prove2.me/submissions/055230f6-6e81-4822-8c75-1f66fb1a0d2e

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

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]

@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]




















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.BitCounter







attribute [local simp] Source Ruler Rem Bits Count Tmp









lemma zsz_bitInt (b : Bool) : zsz (bitInt b)=b.toNat := by
  cases b <;> simp [bitInt,zsz,zbits,nbits_eq_bits]











/-- Split off one low bit while leaving the remaining integer in place. -/
lemma split_nat_bit (I : List Sym) (s : IState NS) (b : Bool) (n : ℕ)
    (st rt : List Item) (hs : s.G Source=.int (Nat.bit b n : ℤ)::st)
    (hr : s.G Ruler=.int 2::rt) :
    IExec I Fin.elim0 (.op (.split Source Ruler Rem)) s
      ((s.upd Source (.int (n : ℤ)::st)).upd Rem (.int (bitInt b)::s.G Rem)) 321 := by
  have hh : IExec I Fin.elim0 (.op (.split Source Ruler Rem)) s _ (splitCost 1+17) :=
    .op (.split (m := 1) (by decide) (by decide) (by decide) hs (by simpa using hr))
  have hq : sg (Nat.bit b n : ℤ) ((Nat.bit b n : ℤ).natAbs/2)=(n : ℤ) := by
    rw [sg,if_neg (by exact not_lt_of_ge (Int.natCast_nonneg _))]
    simp only [Int.natAbs_natCast,Nat.bit_div_two]
  have hm : sg (Nat.bit b n : ℤ) ((Nat.bit b n : ℤ).natAbs%2)=bitInt b := by
    rw [sg,if_neg (by exact not_lt_of_ge (Int.natCast_nonneg _))]
    simp only [Int.natAbs_natCast,Nat.bit_mod_two]
    cases b <;> rfl
  simpa only [show (2 : ℕ)^1=2 from by norm_num,hq,hm,show splitCost 1+17=321 from by norm_num [splitCost,moveCost,takeCost]] using hh



lemma extractLoop_runs (I : List Sym) (n : ℕ) : ∀ (s : IState NS) (st rt : List Item),
    s.G Source=.int (n : ℤ)::st → s.G Ruler=.int 2::rt →
    IRuns I Fin.elim0 extractLoop s
      ((s.upd Source (.int 0::st)).upd Bits
        (n.bits.reverse.map (fun b => Item.int (bitInt b)) ++ s.G Bits)) (528*n.size+30) := by
  induction n using Nat.binaryRec' with
  | zero =>
    intro s st rt hs hr
    have hS : s.upd Source (.int 0::st)=s := by
      rw [← show s.G Source=.int 0::st from hs]
      exact upd_same _ _
    have he : (s.upd Source (.int 0::st)).upd Bits
        ((0 : ℕ).bits.reverse.map (fun b => Item.int (bitInt b)) ++ s.G Bits)=s := by
      simp only [Nat.zero_bits,List.reverse_nil,List.map_nil,List.nil_append,hS,upd_same]
    rw [he]
    exact ⟨30,by simp,IExec.loopF (by simp [IState.cl,hs,cls])⟩
  | bit b n hn ih =>
    intro s st rt hs hr
    let s1 := (s.upd Source (.int (n : ℤ)::st)).upd Rem (.int (bitInt b)::s.G Rem)
    let s2 := (s1.upd Rem (s.G Rem)).upd Bits (.int (bitInt b)::s.G Bits)
    have h1 := split_nat_bit I s b n st rt hs hr
    have h2 : IExec I Fin.elim0 (.op (.mv Rem Bits)) s1 s2 (2*moveCost (zsz (bitInt b))+19) := by
      simpa only [s2,s1,upd_G_ne _ (show Bits≠Rem by decide),upd_G_ne _ (show Bits≠Source by decide)] using
        (IExec.op (IOp.Step.mv (I := I) (s := s1) (i := Rem) (j := Bits) (by decide)
          (by simp [s1])) : IExec I Fin.elim0 _ _ _ _)
    have htail := ih s2 st rt (by simp [s2,s1]) (by simp [s2,s1,hr])
    obtain ⟨c,hc,htail⟩ := htail
    have hne : Nat.bit b n≠0 := by intro he; cases b <;> simp_all [Nat.bit]
    have hcond : decide (s.cl Source=Cls.pos)=true := by
      simp [IState.cl,hs,cls,hne,Nat.pos_of_ne_zero hne]
    have hrun := IExec.loopT hcond (IExec.seq h1 h2) htail
    have he : (s2.upd Source (.int 0::st)).upd Bits
        (n.bits.reverse.map (fun b => Item.int (bitInt b)) ++ s2.G Bits) =
      (s.upd Source (.int 0::st)).upd Bits
        ((Nat.bit b n).bits.reverse.map (fun b => Item.int (bitInt b)) ++ s.G Bits) := by
      cases s
      simp only [s2,s1,IState.upd]
      congr 1
      funext i
      by_cases hS : i=Source <;> by_cases hB : i=Bits <;> by_cases hR : i=Rem <;>
        simp_all [Nat.bits_append_bit n b hn,List.reverse_cons,List.map_append,List.append_assoc]
    rw [he] at hrun
    change IExec I Fin.elim0 extractLoop s _ _ at hrun
    refine ⟨_,?_,hrun⟩
    rw [Nat.size_bit hne]
    cases b <;> simp only [zsz_bitInt,Bool.toNat_false,Bool.toNat_true,moveCost] <;> omega






end KoanaKPaths.Machine.BitCounter

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (n : Nat) (s : NLogN.IState KoanaKPaths.Machine.BitCounter.NS) (st rt : List.{0} NLogN.Item),
  @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Source)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) st) →
    @Eq.{1} (List.{0} NLogN.Item)
        (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Ruler)
        (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))) rt) →
      @NLogN.IRuns KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
        (@Fin.elim0.{1}
          (NLogN.IStmt KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        KoanaKPaths.Machine.BitCounter.extractLoop s
        (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Source
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) st))
          KoanaKPaths.Machine.BitCounter.Bits
          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
            (@List.map.{0, 0} Bool NLogN.Item
              (fun (b : Bool) => NLogN.Item.int (KoanaKPaths.Machine.BitCounter.bitInt b))
              (@List.reverse.{0} Bool (Nat.bits n)))
            (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Bits)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 528) (instOfNatNat (nat_lit 528))) (Nat.size n))
          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.BitCounter.extractLoop_runs

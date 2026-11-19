-- Prove2me | solution 1 for KoanaKPaths.Machine.Balanced.finishGroup_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:45:46.34882+00:00
-- url     : https://prove2.me/submissions/e16df228-3563-455d-885c-f3fab5f0adbb

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Balanced_foldPartials_exec
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
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
namespace KoanaKPaths.Machine
variable {S : ℕ}





lemma cls_int (z : ℤ) :
    cls (some (.int z)) = Cls.zero ∨ cls (some (.int z)) = Cls.pos ∨
      cls (some (.int z)) = Cls.neg := by
  by_cases hz : z=0
  · simp [cls,hz]
  · by_cases hn : z<0 <;> simp [cls,hz,hn]




































end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]

lemma zsz_add_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x+y)≤w+1 := by
  apply (zsz_le_iff _ _).mpr
  have hx' := (zsz_le_iff x w).mp hx
  have hy' := (zsz_le_iff y w).mp hy
  have ha := Int.natAbs_add_le x y
  rw [pow_succ]
  omega

































end KoanaKPaths.Machine.Wedge

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}








lemma itemState_ext {s t : IState S} (hG : ∀ i, s.G i=t.G i) (hip : s.ip=t.ip)
    (hout : s.out=t.out) : s=t := by
  cases s with
  | mk G ip o =>
    cases t with
    | mk H jp p =>
      have hh : G=H := funext hG
      cases hh
      cases hip
      cases hout
      rfl

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}









lemma clearInts_exec (I : List Sym) (src : Fin S) (s : IState S) (xs : List ℤ) (tail : List Item)
    (ht : ¬ (cls tail.head?=Cls.zero ∨ cls tail.head?=Cls.pos ∨ cls tail.head?=Cls.neg))
    (hs : s.G src=xs.map Item.int ++ tail) :
    IExec I Fin.elim0 (clearInts src) s (s.upd src tail) (clearIntsCost xs) := by
  induction xs generalizing s with
  | nil =>
    have he : s.upd src tail=s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    rw [he]
    exact IExec.loopF (by simpa [IState.cl,hs] using ht)
  | cons x xs ih =>
    let s1 := s.upd src (xs.map Item.int ++ tail)
    have h1 : IExec I Fin.elim0 (.op (.drop src)) s s1 (2*zsz x+2) := .op (.drop (by simpa using hs))
    have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg)=true := by
      simp only [IState.cl,hs,List.map_cons,List.cons_append,List.head?_cons,decide_eq_true_eq]
      exact cls_int x
    have hrun := IExec.loopT hh h1 (ih s1 (by simp [s1]))
    change IExec I Fin.elim0 (clearInts src) s _ _ at hrun
    simp only [s1,upd_upd] at hrun
    convert hrun using 1
    simp only [clearIntsCost,List.map_cons,List.sum_cons]
    omega









end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main















end KoanaKPaths.Main

namespace KoanaKPaths.Machine.Norm
lemma clearIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ x∈xs, zsz x≤ w) :
    clearIntsCost xs≤(2*w+32)*xs.length+30 := by
  unfold clearIntsCost
  have hh : (xs.map (fun x => 2*zsz x+32)).sum≤(2*w+32)*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  omega



end KoanaKPaths.Machine.Norm

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced















lemma carryInsert_sum (l : ℕ) (x : ℤ) (cs : List Chunk) :
    ((carryInsert l x cs).map Prod.snd).sum=x+(cs.map Prod.snd).sum := by
  induction cs generalizing l x with
  | nil => simp [carryInsert]
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    simp only [carryInsert]
    split_ifs
    · rw [ih]
      simp only [List.map_cons,List.sum_cons]
      ring
    · simp



lemma carryInsert_count (l : ℕ) (x : ℤ) (cs : List Chunk) :
    chunkCount (carryInsert l x cs)=2^l+chunkCount cs := by
  induction cs generalizing l x with
  | nil => simp [chunkCount,carryInsert]
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    simp only [carryInsert]
    split_ifs with h
    · subst j
      rw [ih]
      simp only [chunkCount,List.map_cons,List.sum_cons,pow_succ]
      omega
    · simp [chunkCount]







lemma accumulate_sum (cs : List Chunk) (xs : List ℤ) :
    ((accumulate cs xs).map Prod.snd).sum=(cs.map Prod.snd).sum+xs.sum := by
  induction xs generalizing cs with
  | nil => simp [accumulate]
  | cons x xs ih =>
    simp only [accumulate,ih,carryInsert_sum,List.sum_cons]
    ring

lemma accumulate_count (cs : List Chunk) (xs : List ℤ) :
    chunkCount (accumulate cs xs)=chunkCount cs+xs.length := by
  induction xs generalizing cs with
  | nil => simp [accumulate]
  | cons x xs ih => simp [accumulate,ih,carryInsert_count]; omega














end KoanaKPaths.Machine.Balanced

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced



lemma counterCode_digits (l : ℕ) (cs : List Chunk) :
    counterCode l cs=(counterDigits l cs).map Item.int ++ [.mark] := by
  induction cs generalizing l with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    simp [counterCode,counterDigits,ih,List.map_append,List.map_replicate,List.append_assoc]

lemma counterDigits_length (l : ℕ) (cs : List Chunk) :
    (counterDigits l cs).length≤chunkCount cs := by
  induction cs generalizing l with
  | nil => simp [counterDigits,chunkCount]
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    have ht := ih (j+1)
    have hp : j+1≤2^j := Nat.lt_two_pow_self
    simp only [counterDigits,List.length_append,List.length_replicate,List.length_cons,
      chunkCount,List.map_cons,List.sum_cons]
    change j-l+(List.length (counterDigits (j+1) cs)+1)≤2^j+chunkCount cs
    omega

lemma counterDigits_values (l : ℕ) (cs : List Chunk) :
    ∀ x∈counterDigits l cs, x=0 ∨ x=1 := by
  induction cs generalizing l with
  | nil => simp [counterDigits]
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    intro x hx
    simp only [counterDigits,List.mem_append,List.mem_cons] at hx
    rcases hx with hx|(rfl|hx)
    · exact Or.inl (List.eq_of_mem_replicate hx)
    · exact Or.inr rfl
    · exact ih (j+1) x hx

lemma counterDigits_clearCost (l : ℕ) (cs : List Chunk) :
    clearIntsCost (counterDigits l cs)≤34*chunkCount cs+30 := by
  have hw : ∀ x∈counterDigits l cs, zsz x≤1 := by
    intro x hx
    rcases counterDigits_values l cs x hx with rfl|rfl <;> simp [Wedge.zsz_eq_size]
  have h := Norm.clearIntsCost_bound (counterDigits l cs) 1 hw
  have hl := counterDigits_length l cs
  nlinarith

end KoanaKPaths.Machine.Balanced

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine.Wedge
lemma sum_word_width (xs : List ℤ) (w : ℕ) (hw : ∀ x∈xs, zsz x≤ w) : zsz xs.sum≤ w+xs.length := by
  induction xs with
  | nil => simp [zsz_eq_size]
  | cons x xs ih =>
    have hx := hw x (by simp)
    have ht := ih (fun y hy => hw y (by simp [hy]))
    have h := zsz_add_le x xs.sum (w+xs.length) (by omega) ht
    simpa only [List.sum_cons,List.length_cons,Nat.add_assoc] using h
end KoanaKPaths.Machine.Wedge

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Balanced

attribute [local simp] Partials Bits Sum Records



lemma finishGroup_runs (I : List Sym) (s : IState NS) (xs : List ℤ) (pt bt : List Item)
    (hp : s.G Partials=((accumulate [] xs).map Prod.snd).map Item.int ++ .mark::pt)
    (hb : s.G Bits=counterCode 0 (accumulate [] xs)++bt) (w : ℕ)
    (hw : ∀ x∈xs, zsz x≤ w) :
    IRuns I Fin.elim0 finishGroup s
      (((s.upd Partials pt).upd Bits bt).upd Records (.int xs.sum::s.G Records))
      (foldCharge 0 (accumulate [] xs)+34*xs.length+1000*(w+xs.length+1)) := by
  let cs := accumulate [] xs
  let s0 := s.upd Sum (.int 0::s.G Sum)
  let s1 := (s0.upd Partials (.mark::pt)).upd Sum (.int xs.sum::s.G Sum)
  let s2 := s1.upd Partials pt
  let s3 := s2.upd Bits (.mark::bt)
  let s4 := s3.upd Bits bt
  let s5 := (s4.upd Sum (s.G Sum)).upd Records (.int xs.sum::s.G Records)
  have h0 : IExec I Fin.elim0 (.op (.const Sum 0)) s s0 2 := by
    simpa [Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s) (i := Sum) 0))
  have hsum : (cs.map Prod.snd).sum=xs.sum := by simpa [cs] using accumulate_sum [] xs
  have h1 : IExec I Fin.elim0 foldPartials s0 s1 (foldCharge 0 cs) := by
    have h := foldPartials_exec I s0 0 cs (.mark::pt) (s.G Sum) (by simp [cls])
      (by simp [s0,cs,hp]) (by simp [s0])
    simpa [s1,hsum,s0] using h
  have h2 : IExec I Fin.elim0 (.op (.unmark Partials)) s1 s2 1 := .op (.unmark (by simp [s1]))
  have h3 : IExec I Fin.elim0 (clearInts Bits) s2 s3 (clearIntsCost (counterDigits 0 cs)) := by
    exact clearInts_exec I Bits s2 (counterDigits 0 cs) (.mark::bt) (by simp [cls])
      (by simpa [s2,s1,s0,cs,counterCode_digits,List.append_assoc] using hb)
  have h4 : IExec I Fin.elim0 (.op (.unmark Bits)) s3 s4 1 := .op (.unmark (by simp [s3]))
  have h5 : IExec I Fin.elim0 (.op (.mv Sum Records)) s4 s5 (2*moveCost (zsz xs.sum)+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s4) (i := Sum) (j := Records) (a := xs.sum) (L := s.G Sum)
        (by decide) (by simp [s4,s3,s2,s1]))
    simpa [s5,s4,s3,s2,s1,s0] using h
  have he : s5=((s.upd Partials pt).upd Bits bt).upd Records (.int xs.sum::s.G Records) := by
    apply itemState_ext
    · intro r
      by_cases h102 : r=102 <;> by_cases h103 : r=103 <;> by_cases h106 : r=106 <;> by_cases h107 : r=107 <;>
        simp [s5,s4,s3,s2,s1,s0,IState.upd,Function.update_apply,h102,h103,h106,h107]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq (Native.of_exec h3) (Native.seq (Native.of_exec h4) (Native.of_exec h5)))))
  rw [he] at h
  change IRuns I Fin.elim0 finishGroup s _ _ at h
  apply Native.mono h
  have hclear := counterDigits_clearCost 0 cs
  have hcount : chunkCount cs=xs.length := by simpa [cs,chunkCount] using accumulate_count [] xs
  rw [hcount] at hclear
  have hwidth := Wedge.sum_word_width xs w hw
  unfold moveCost
  nlinarith

end KoanaKPaths.Machine.Balanced

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Balanced.NS) (xs : List.{0} Int)
  (pt bt : List.{0} NLogN.Item)
  (hp :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0} (Prod.{0, 0} Nat Int) Int (@Prod.snd.{0, 0} Nat Int)
            (KoanaKPaths.Machine.Balanced.accumulate (@List.nil.{0} KoanaKPaths.Machine.Balanced.Chunk) xs)))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark pt)))
  (hb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Balanced.counterCode (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (KoanaKPaths.Machine.Balanced.accumulate (@List.nil.{0} KoanaKPaths.Machine.Balanced.Chunk) xs))
        bt))
  (w : Nat)
  (hw :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w),
  @NLogN.IRuns KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Balanced.finishGroup s
    (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials pt)
        KoanaKPaths.Machine.Balanced.Bits bt)
      KoanaKPaths.Machine.Balanced.Records
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@List.sum.{0} Int Int.instAdd
            (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) xs))
        (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Records)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (KoanaKPaths.Machine.Balanced.foldCharge (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (KoanaKPaths.Machine.Balanced.accumulate (@List.nil.{0} KoanaKPaths.Machine.Balanced.Chunk) xs))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))) (@List.length.{0} Int xs)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w (@List.length.{0} Int xs))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  exact @KoanaKPaths.Machine.Balanced.finishGroup_runs

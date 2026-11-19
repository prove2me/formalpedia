-- Prove2me | solution 1 for KoanaKPaths.Machine.Square.predCopy_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:35:39.293067+00:00
-- url     : https://prove2.me/submissions/477f47bc-3af2-4ca5-8564-8708f1a01ab5

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Square_binaryAdd_exec
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

lemma skip (s : IState S) : IRuns I iprog .skip s s 1 := of_exec (.skip s)
lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩
lemma iteT {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = true)
    (h : IRuns I iprog p s s1 c) : IRuns I iprog (.ite i f p q) s s1 (c+25) := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t+25,by omega,.iteT hf h⟩
lemma iteF {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = false)
    (h : IRuns I iprog q s s1 c) : IRuns I iprog (.ite i f p q) s s1 (c+25) := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t+25,by omega,.iteF hf h⟩



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
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]

















lemma addIntCost_formula (L : ℕ) : addIntCost L=297*L+393 := by
  simp only [addIntCost,addMagCost,subMagCost,zipCost,moveCost]
  ring

















end KoanaKPaths.Machine.Wedge

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square

attribute [local simp] Eval Value Arg X Y W Q R T






lemma binaryAdd_runs (I : List Sym) (s : IState NS) (x y : ℤ) (tail : List Item) (w : ℕ)
    (hs : s.G Eval=.int y::.int x::tail) (hx : zsz x≤ w) (hy : zsz y≤ w) :
    IRuns I Fin.elim0 binaryAdd s (s.upd Eval (.int (x+y)::tail)) (10000*(w+1)^2) := by
  apply Native.mono (Native.of_exec (binaryAdd_exec I s x y tail hs))
  rw [Wedge.addIntCost_formula]
  unfold moveCost
  nlinarith



end KoanaKPaths.Machine.Square

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square
attribute [local simp] Eval Value Arg



lemma predCopy_runs (I : List Sym) (src dst : Fin NS) (hs : src≠Eval) (hd : dst≠Eval)
    (s : IState NS) (n w : ℕ) (tail : List Item)
    (hn : s.G src=.int (n : ℤ)::tail) (hw : 1≤ w) (hb : zsz (n : ℤ)≤ w) :
    IRuns I Fin.elim0 (predCopy src dst) s
      (s.upd dst (.int ((n-1 : ℕ) : ℤ)::s.G dst)) (12000*(w+1)^2) := by
  let s1 := s.upd Eval (.int (n : ℤ)::s.G Eval)
  let s2 := s.upd Eval (.int ((n-1 : ℕ) : ℤ)::s.G Eval)
  let s3 := (s2.upd Eval (s.G Eval)).upd dst (.int ((n-1 : ℕ) : ℤ)::s.G dst)
  have h1 : IExec I Fin.elim0 (.op (.dup src Eval)) s s1 (dupCost (zsz (n : ℤ))+17) :=
    .op (IOp.Step.dup (L := tail) hs hn)
  have h2 : IRuns I Fin.elim0
      (.ite Eval (fun c => decide (c=Cls.zero)) .skip (.seq (.op (.const Eval (-1))) binaryAdd))
      s1 s2 (10000*(w+1)^2+28) := by
    by_cases hz : n=0
    · have he : s2=s1 := by simp [s2,s1,hz]
      rw [he]
      have hh : IRuns I Fin.elim0
          (.ite Eval (fun c => decide (c=Cls.zero)) .skip (.seq (.op (.const Eval (-1))) binaryAdd))
          s1 s1 26 := Native.iteT (by simp [IState.cl,s1,hz,cls]) (Native.skip s1)
      exact Native.mono hh (by omega)
    · let sa := s1.upd Eval (.int (-1)::s1.G Eval)
      have hconst : IExec I Fin.elim0 (.op (.const Eval (-1))) s1 sa 3 := by
        simpa [Wedge.zsz_eq_size] using
          (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s1) (i := Eval) (-1)))
      have hbin := binaryAdd_runs I sa (n : ℤ) (-1) (s.G Eval) w
        (by simp [sa,s1]) hb (by simpa [Wedge.zsz_eq_size] using hw)
      have hc : (n : ℤ)+ -1=((n-1 : ℕ) : ℤ) := by
        have h := congrArg (fun x : ℕ => (x : ℤ)) (Nat.sub_add_cancel (by omega : 1≤ n))
        push_cast at h
        omega
      have he : sa.upd Eval (.int ((n : ℤ)+ -1)::s.G Eval)=s2 := by simp [sa,s1,s2,hc]
      rw [he] at hbin
      have hcl : decide (s1.cl Eval=Cls.zero)=false := by
        simp [IState.cl,s1,cls,hz,show ¬(n : ℤ)<0 by omega]
      have h : IRuns I Fin.elim0
          (.ite Eval (fun c => decide (c=Cls.zero)) .skip (.seq (.op (.const Eval (-1))) binaryAdd))
          s1 s2 ((3+10000*(w+1)^2)+25) :=
        Native.iteF hcl (Native.seq (Native.of_exec hconst) hbin)
      exact Native.mono h (by omega)
  have h3 : IExec I Fin.elim0 (.op (.mv Eval dst)) s2 s3
      (2*moveCost (zsz ((n-1 : ℕ) : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s2) (i := Eval) (j := dst) (a := ((n-1 : ℕ) : ℤ))
        (L := s.G Eval) (Ne.symm hd) (by simp [s2]))
    simpa [s3,s2,hd] using h
  have he : s3=s.upd dst (.int ((n-1 : ℕ) : ℤ)::s.G dst) := by simp [s3,s2]
  have h := Native.seq (Native.of_exec h1) (Native.seq h2 (Native.of_exec h3))
  rw [he] at h
  change IRuns I Fin.elim0 (predCopy src dst) s _ _ at h
  apply Native.mono h
  have hpred : zsz ((n-1 : ℕ) : ℤ)≤ w := by
    apply (Wedge.zsz_le_iff _ _).mpr
    have h := (Wedge.zsz_le_iff (n : ℤ) w).mp hb
    simp only [Int.natAbs_natCast] at h ⊢
    omega
  unfold dupCost zipCost moveCost
  nlinarith

end KoanaKPaths.Machine.Square

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (src dst : Fin KoanaKPaths.Machine.Square.NS)
  (hs : @Ne.{1} (Fin KoanaKPaths.Machine.Square.NS) src KoanaKPaths.Machine.Square.Eval)
  (hd : @Ne.{1} (Fin KoanaKPaths.Machine.Square.NS) dst KoanaKPaths.Machine.Square.Eval)
  (s : NLogN.IState KoanaKPaths.Machine.Square.NS) (n w : Nat) (tail : List.{0} NLogN.Item)
  (hn :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s src)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) tail))
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (hb : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt n)) w),
  @NLogN.IRuns KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (KoanaKPaths.Machine.Square.predCopy src dst) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Square.NS s dst
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s dst)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 12000) (instOfNatNat (nat_lit 12000)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  exact @KoanaKPaths.Machine.Square.predCopy_runs

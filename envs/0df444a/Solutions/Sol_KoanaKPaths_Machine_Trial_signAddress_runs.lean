-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.signAddress_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:51.833842+00:00
-- url     : https://prove2.me/submissions/65ee1545-e907-4f28-b300-9b83a9b765de

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
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_compile_runs
import Theorems.Thm_KoanaKPaths_Machine_Square_predCopy_runs
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






































lemma zsz_neg (z : ℤ) : zsz (-z)=zsz z := by simp [zsz,zbits]



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

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}











lemma Expr.root_width (e : Expr v) (values : Fin v→ℕ) :
    zsz (e.eval values : ℤ)≤ e.width values := by
  cases e <;> exact le_max_left _ _



end KoanaKPaths.Machine.Arithmetic

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square
attribute [local simp] Eval Value Arg



lemma binarySub_exec (I : List Sym) (s : IState NS) (x y : ℤ) (tail : List Item)
    (hs : s.G Eval=.int y::.int x::tail) :
    IExec I Fin.elim0 binarySub s (s.upd Eval (.int (x-y)::tail))
      (2*moveCost (zsz y)+39+addIntCost (zsz x+zsz y)) := by
  let s1 := (s.upd Eval (.int x::tail)).upd Arg (.int y::s.G Arg)
  let s2 := s1.upd Arg (.int (-y)::s.G Arg)
  let sa := (s2.upd Eval tail).upd Arg (s.G Arg)
  let s3 := sa.upd Eval (.int (x-y)::tail)
  have h1 : IExec I Fin.elim0 (.op (.mv Eval Arg)) s s1 (2*moveCost (zsz y)+19) := .op (.mv (by decide) hs)
  have h2 : IExec I Fin.elim0 (.op (.neg Arg)) s1 s2 20 := .op (.neg (by simp [s1]))
  have h3 : IExec I Fin.elim0 (.op (.add Eval Arg Eval)) s2 s3 (addIntCost (zsz x+zsz y)) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.add (s := s2) (i := Eval) (j := Arg) (k := Eval)
        (a := x) (b := -y) (Li := tail) (Lj := s.G Arg) (by decide) (by simp [s2,s1]) (by simp [s2]))
    simpa [s3,sa,sub_eq_add_neg,zsz_neg] using h
  have he : s3=s.upd Eval (.int (x-y)::tail) := by
    apply itemState_ext
    · intro i
      by_cases hE : i=Eval
      · subst i; simp [s3,sa,s2,s1]
      by_cases hA : i=Arg
      · subst i; simp [s3,sa,s2,s1]
      simp [s3,sa,s2,s1,IState.upd,Function.update_apply,hE,hA]
    · rfl
    · rfl
  have h := IExec.seq h1 (IExec.seq h2 h3)
  rw [he] at h
  change IExec I Fin.elim0 binarySub s _ _ at h
  convert h using 1 <;> omega

lemma binarySub_runs (I : List Sym) (s : IState NS) (x y : ℤ) (tail : List Item) (w : ℕ)
    (hs : s.G Eval=.int y::.int x::tail) (hx : zsz x≤ w) (hy : zsz y≤ w) :
    IRuns I Fin.elim0 binarySub s (s.upd Eval (.int (x-y)::tail)) (10000*(w+1)^2) := by
  apply Native.mono (Native.of_exec (binarySub_exec I s x y tail hs))
  rw [Wedge.addIntCost_formula]
  unfold moveCost
  nlinarith

end KoanaKPaths.Machine.Square

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square


attribute [local simp] Total Base Square.Eval Square.Value BitCounter.Source
variable {v : ℕ}



lemma signAddress_runs (I : List Sym) (reg : Fin v→Fin NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (T w : ℕ) (hw : 1≤ w)
    (he : e.width values≤ w) (hT : zsz (T : ℤ)≤ w) (hj : e.eval values< T)
    (s : IState NS) (tt : List Item) (hTotal : s.G Total=.int (T : ℤ)::tt)
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail) :
    IRuns I Fin.elim0 (signAddress reg e) s
      (s.upd BitCounter.Source (.int ((T-1-e.eval values : ℕ) : ℤ)::s.G BitCounter.Source))
      (30000*(e.size+2)*(w+1)^2) := by
  let j := e.eval values
  let s0 := s.upd Base (.int ((T-1 : ℕ) : ℤ)::s.G Base)
  let s1 := (s0.upd Base (s.G Base)).upd Eval (.int ((T-1 : ℕ) : ℤ)::s.G Eval)
  let s2 := s1.upd Eval (.int (j : ℤ)::s1.G Eval)
  let s3 := s2.upd Eval (.int ((T-1-j : ℕ) : ℤ)::s.G Eval)
  let s4 := (s3.upd Eval (s.G Eval)).upd BitCounter.Source
    (.int ((T-1-j : ℕ) : ℤ)::s.G BitCounter.Source)
  have hpred : zsz ((T-1 : ℕ) : ℤ)≤ w := by
    apply (Wedge.zsz_le_iff _ _).mpr
    have h := (Wedge.zsz_le_iff (T : ℤ) w).mp hT
    simp only [Int.natAbs_natCast] at h ⊢
    omega
  have h0 : IRuns I Fin.elim0 (predCopy Total Base) s s0 (12000*(w+1)^2) :=
    predCopy_runs I Total Base (by decide) (by decide) s T w tt hTotal hw hT
  have h1 : IExec I Fin.elim0 (.op (.mv Base Eval)) s0 s1 (2*moveCost (zsz ((T-1 : ℕ) : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s0) (i := Base) (j := Eval) (a := ((T-1 : ℕ) : ℤ))
        (L := s.G Base) (by decide) (by simp [s0]))
    simpa [s1,s0] using h
  have hv1 : ∀ i, ∃ tail, s1.G (reg i)=.int (values i : ℤ)::tail := by
    intro i
    obtain ⟨tail,ht⟩ := hv i
    exact ⟨tail,by simp [s1,s0,hreg i,ht]⟩
  have h2 := e.compile_runs I reg hreg values w he s1 hv1
  have hsub : ((T-1 : ℕ) : ℤ)-(j : ℤ)=((T-1-j : ℕ) : ℤ) :=
    (Int.ofNat_sub (by dsimp [j]; omega : j≤ T-1)).symm
  have h3 : IRuns I Fin.elim0 binarySub s2 s3 (10000*(w+1)^2) := by
    have h := binarySub_runs I s2 ((T-1 : ℕ) : ℤ) (j : ℤ) (s.G Eval) w
      (by simp [s2,s1,s0]) hpred ((e.root_width values).trans he)
    simpa [s3,hsub] using h
  have h4 : IExec I Fin.elim0 (.op (.mv Eval BitCounter.Source)) s3 s4
      (2*moveCost (zsz ((T-1-j : ℕ) : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s3) (i := Eval) (j := BitCounter.Source) (a := ((T-1-j : ℕ) : ℤ))
        (L := s.G Eval) (by decide) (by simp [s3]))
    simpa [s4,s3,s2,s1,s0] using h
  have hidx : zsz ((T-1-j : ℕ) : ℤ)≤ w := by
    apply (Wedge.zsz_le_iff _ _).mpr
    have h := (Wedge.zsz_le_iff (T : ℤ) w).mp hT
    simp only [Int.natAbs_natCast] at h ⊢
    omega
  have hpost : s4=s.upd BitCounter.Source
      (.int ((T-1-e.eval values : ℕ) : ℤ)::s.G BitCounter.Source) := by
    apply itemState_ext
    · intro i
      by_cases hS : i=BitCounter.Source
      · subst i; simp [s4,s3,s2,s1,s0,j]
      by_cases hE : i=Eval
      · subst i; simp [s4,s3,s2,s1,s0]
      by_cases hB : i=Base
      · subst i; simp [s4,s3,s2,s1,s0]
      simp [s4,s3,s2,s1,s0,IState.upd,Function.update_apply,hS,hE,hB]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq (Native.of_exec h1)
    (Native.seq h2 (Native.seq h3 (Native.of_exec h4))))
  rw [hpost] at h
  change IRuns I Fin.elim0 (signAddress reg e) s _ _ at h
  apply Native.mono h
  unfold moveCost
  nlinarith [Nat.zero_le (e.size*w*w)]

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ {v : Nat} (I : List.{0} NLogN.Sym) (reg : Fin v → Fin KoanaKPaths.Machine.Trial.NS)
  (hreg : ∀ (i : Fin v), @Ne.{1} (Fin KoanaKPaths.Machine.Trial.NS) (reg i) KoanaKPaths.Machine.Square.Eval)
  (values : Fin v → Nat) (e : KoanaKPaths.Machine.Arithmetic.Expr v) (T w : Nat)
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (he : @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.width v values e) w)
  (hT : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt T)) w)
  (hj : @LT.lt.{0} Nat instLTNat (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e) T)
  (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (tt : List.{0} NLogN.Item)
  (hTotal :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt T)) tt))
  (hv :
    ∀ (i : Fin v),
      @Exists.{1} (List.{0} NLogN.Item) fun (tail : List.{0} NLogN.Item) =>
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s (reg i))
          (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (values i))) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.Trial.signAddress v reg e) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Source
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) T
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e))))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Source)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 30000) (instOfNatNat (nat_lit 30000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@KoanaKPaths.Machine.Arithmetic.Expr.size v e)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  exact @KoanaKPaths.Machine.Trial.signAddress_runs

-- Prove2me | solution 1 for KoanaKPaths.Machine.Square.increment_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:37:10.046174+00:00
-- url     : https://prove2.me/submissions/23b671e2-d2dd-4c9c-b237-50603edd0c72

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

lemma zsz_add_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x+y)≤w+1 := by
  apply (zsz_le_iff _ _).mpr
  have hx' := (zsz_le_iff x w).mp hx
  have hy' := (zsz_le_iff y w).mp hy
  have ha := Int.natAbs_add_le x y
  rw [pow_succ]
  omega















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
attribute [local simp] Eval Value



lemma increment_runs (I : List Sym) (i : Fin NS) (hi : i≠Eval) (s : IState NS)
    (n w : ℕ) (tail : List Item) (hs : s.G i=.int (n : ℤ)::tail)
    (hw : 1≤ w) (hn : zsz (n : ℤ)≤ w) :
    IRuns I Fin.elim0 (increment i) s (s.upd i (.int ((n+1 : ℕ) : ℤ)::tail))
      (13000*(w+1)^2) := by
  let s0 := s.upd Eval (.int (n : ℤ)::s.G Eval)
  let s1 := s0.upd Eval (.int 1::s0.G Eval)
  let s2 := s1.upd Eval (.int ((n+1 : ℕ) : ℤ)::s.G Eval)
  let s3 := s2.upd i tail
  let s4 := (s3.upd Eval (s.G Eval)).upd i (.int ((n+1 : ℕ) : ℤ)::tail)
  have h0 : IExec I Fin.elim0 (.op (.dup i Eval)) s s0 (dupCost (zsz (n : ℤ))+17) :=
    .op (IOp.Step.dup (L := tail) hi hs)
  have h1 : IExec I Fin.elim0 (.op (.const Eval 1)) s0 s1 3 := by
    simpa [Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s0) (i := Eval) 1))
  have h2 : IRuns I Fin.elim0 binaryAdd s1 s2 (10000*(w+1)^2) := by
    have h := binaryAdd_runs I s1 (n : ℤ) 1 (s.G Eval) w (by simp [s1,s0]) hn
      (by simpa [Wedge.zsz_eq_size] using hw)
    simpa [s2,Nat.cast_add] using h
  have h3 : IExec I Fin.elim0 (.op (.drop i)) s2 s3 (2*zsz (n : ℤ)+2) :=
    .op (IOp.Step.drop (L := tail) (by simp [s2,s1,s0,hi,hs]))
  have h4 : IExec I Fin.elim0 (.op (.mv Eval i)) s3 s4
      (2*moveCost (zsz ((n+1 : ℕ) : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s3) (i := Eval) (j := i) (a := ((n+1 : ℕ) : ℤ))
        (L := s.G Eval) (Ne.symm hi) (by simp [s3,s2,Ne.symm hi]))
    simpa [s4,s3] using h
  have he : s4=s.upd i (.int ((n+1 : ℕ) : ℤ)::tail) := by
    apply itemState_ext
    · intro r
      by_cases hr : r=i
      · subst r; simp [s4,s3,s2,s1,s0]
      by_cases hE : r=Eval
      · subst r; simp [s4,s3,s2,s1,s0,Ne.symm hi]
      simp [s4,s3,s2,s1,s0,IState.upd,Function.update_apply,hr,hE]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1)
    (Native.seq h2 (Native.seq (Native.of_exec h3) (Native.of_exec h4))))
  rw [he] at h
  change IRuns I Fin.elim0 (increment i) s _ _ at h
  apply Native.mono h
  have hnext : zsz ((n+1 : ℕ) : ℤ)≤ w+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using Wedge.zsz_add_le (n : ℤ) 1 w hn
      (by simpa [Wedge.zsz_eq_size] using hw)
  unfold dupCost zipCost moveCost
  nlinarith

end KoanaKPaths.Machine.Square

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (i : Fin KoanaKPaths.Machine.Square.NS)
  (hi : @Ne.{1} (Fin KoanaKPaths.Machine.Square.NS) i KoanaKPaths.Machine.Square.Eval)
  (s : NLogN.IState KoanaKPaths.Machine.Square.NS) (n w : Nat) (tail : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s i)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) tail))
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (hn : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt n)) w),
  @NLogN.IRuns KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (KoanaKPaths.Machine.Square.increment i) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Square.NS s i
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        tail))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 13000) (instOfNatNat (nat_lit 13000)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  exact @KoanaKPaths.Machine.Square.increment_runs

-- Prove2me | solution 1 for KoanaKPaths.Machine.Arithmetic.Expr.compile_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:13.133896+00:00
-- url     : https://prove2.me/submissions/e12bcf0c-d2e9-4d47-82e0-835b33677a1c

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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square









attribute [local simp] Value Arg X Y W Q R T

lemma zsz_mul_le (x y : ℤ) (u v : ℕ) (hx : zsz x≤u) (hy : zsz y≤v) : zsz (x*y)≤u+v := by
  apply (Wedge.zsz_le_iff _ _).mpr
  rw [Int.natAbs_mul]
  have hx' := (Wedge.zsz_le_iff x u).mp hx
  have hy' := (Wedge.zsz_le_iff y v).mp hy
  calc
    _ ≤ x.natAbs*2^v := Nat.mul_le_mul_left _ (Nat.le_of_lt hy')
    _ < 2^u*2^v := Nat.mul_lt_mul_of_pos_right hx' (by positivity)
    _ = _ := (pow_add _ _ _).symm





end KoanaKPaths.Machine.Square

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

lemma binaryMul_runs (I : List Sym) (s : IState NS) (x y : ℤ) (tail : List Item) (w : ℕ)
    (hs : s.G Eval=.int y::.int x::tail) (hx : zsz x≤ w) (hy : zsz y≤ w) :
    IRuns I Fin.elim0 binaryMul s (s.upd Eval (.int (x*y)::tail)) (10000*(w+1)^2) := by
  let s1 := (s.upd Eval (.int x::tail)).upd Arg (.int y::s.G Arg)
  let s2 := (s1.upd Eval tail).upd Arg (.int x::s1.G Arg)
  let s3 := s2.upd Arg (.int (x*y)::s.G Arg)
  let s4 := (s3.upd Arg (s.G Arg)).upd Eval (.int (x*y)::tail)
  have h1 : IExec I Fin.elim0 (.op (.mv Eval Arg)) s s1 (2*moveCost (zsz y)+19) :=
    .op (.mv (by decide) hs)
  have h2 : IExec I Fin.elim0 (.op (.mv Eval Arg)) s1 s2 (2*moveCost (zsz x)+19) :=
    .op (.mv (by decide) (by simp [s1]))
  have h3 : IRuns I Fin.elim0 (smul Arg X Y W Q R T) s2 s3 (smulCost (zsz x+zsz y)) := by
    exact NLogN.smul_runs (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (A := Arg) (X := X) (Y := Y) (W := W) (Q := Q) (R := R) (T := T)
      (by decide) s2 x y (s.G Arg) (by simp [s2,s1])
  have h4 : IExec I Fin.elim0 (.op (.mv Arg Eval)) s3 s4 (2*moveCost (zsz (x*y))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s3) (i := Arg) (j := Eval) (a := x*y) (L := s.G Arg)
        (by decide) (by simp [s3]))
    simpa [s4,s3,s2,s1] using h
  have he : s4=s.upd Eval (.int (x*y)::tail) := by
    apply itemState_ext
    · intro i
      by_cases hE : i=Eval
      · subst i; simp [s4,s3,s2,s1]
      by_cases hA : i=Arg
      · subst i; simp [s4,s3,s2,s1]
      simp [s4,s3,s2,s1,IState.upd,Function.update_apply,hE,hA]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq h3 (Native.of_exec h4)))
  change IRuns I Fin.elim0 binaryMul s _ _ at h
  rw [he] at h
  apply Native.mono h
  have hxy := zsz_mul_le x y w w hx hy
  have hsm : smulCost (zsz x+zsz y)≤8000*(w+1)^2 := by unfold smulCost; nlinarith
  unfold moveCost
  nlinarith

end KoanaKPaths.Machine.Square

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

lemma Expr.compile_runs (I : List Sym) (reg : Fin v→Fin Square.NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (w : ℕ) (hw : e.width values≤ w)
    (s : IState Square.NS) (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail) :
    IRuns I Fin.elim0 (e.compile reg) s
      (s.upd Eval (.int (e.eval values : ℤ)::s.G Eval)) (10000*e.size*(w+1)^2) := by
  induction e generalizing s with
  | constant n =>
    have hn : zsz (n : ℤ)≤ w := (le_max_left _ _).trans hw
    have h : IExec I Fin.elim0 (.op (.const Eval (n : ℤ))) s
        (s.upd Eval (.int (n : ℤ)::s.G Eval)) (zsz (n : ℤ)+2) := .op (.const n)
    apply Native.mono (Native.of_exec h)
    simp only [Expr.size,mul_one]
    nlinarith
  | input i =>
    obtain ⟨tail,ht⟩ := hv i
    have hn : zsz (values i : ℤ)≤ w := (le_max_left _ _).trans hw
    have h : IExec I Fin.elim0 (.op (.dup (reg i) Eval)) s
        (s.upd Eval (.int (values i : ℤ)::s.G Eval)) (dupCost (zsz (values i : ℤ))+17) :=
      .op (IOp.Step.dup (L := tail) (hreg i) ht)
    apply Native.mono (Native.of_exec h)
    simp only [Expr.size,mul_one]
    unfold dupCost zipCost moveCost
    nlinarith
  | add x y ihx ihy =>
    have hxy : x.width values≤ w ∧ y.width values≤ w :=
      max_le_iff.mp ((max_le_iff.mp hw).2)
    let s1 := s.upd Eval (.int (x.eval values : ℤ)::s.G Eval)
    let s2 := s1.upd Eval (.int (y.eval values : ℤ)::s1.G Eval)
    have h1 := ihx hxy.1 s hv
    have hv1 : ∀ i, ∃ tail, s1.G (reg i)=.int (values i : ℤ)::tail := by
      intro i
      obtain ⟨tail,ht⟩ := hv i
      exact ⟨tail,by simp [s1,hreg i,ht]⟩
    have h2 := ihy hxy.2 s1 hv1
    have h3 := binaryAdd_runs I s2 (x.eval values : ℤ) (y.eval values : ℤ) (s.G Eval) w
      (by simp [s2,s1]) ((x.root_width values).trans hxy.1) ((y.root_width values).trans hxy.2)
    have h := Native.seq h1 (Native.seq h2 h3)
    have he : s2.upd Eval (.int ((x.eval values : ℤ)+(y.eval values : ℤ))::s.G Eval)=
        s.upd Eval (.int ((Expr.add x y).eval values : ℤ)::s.G Eval) := by
      simp [s2,s1,Expr.eval,Nat.cast_add]
    rw [he] at h
    change IRuns I Fin.elim0 ((Expr.add x y).compile reg) s _ _ at h
    apply Native.mono h
    simp only [Expr.size]
    ring_nf
    exact le_rfl
  | mul x y ihx ihy =>
    have hxy : x.width values≤ w ∧ y.width values≤ w :=
      max_le_iff.mp ((max_le_iff.mp hw).2)
    let s1 := s.upd Eval (.int (x.eval values : ℤ)::s.G Eval)
    let s2 := s1.upd Eval (.int (y.eval values : ℤ)::s1.G Eval)
    have h1 := ihx hxy.1 s hv
    have hv1 : ∀ i, ∃ tail, s1.G (reg i)=.int (values i : ℤ)::tail := by
      intro i
      obtain ⟨tail,ht⟩ := hv i
      exact ⟨tail,by simp [s1,hreg i,ht]⟩
    have h2 := ihy hxy.2 s1 hv1
    have h3 := binaryMul_runs I s2 (x.eval values : ℤ) (y.eval values : ℤ) (s.G Eval) w
      (by simp [s2,s1]) ((x.root_width values).trans hxy.1) ((y.root_width values).trans hxy.2)
    have h := Native.seq h1 (Native.seq h2 h3)
    have he : s2.upd Eval (.int ((x.eval values : ℤ)*(y.eval values : ℤ))::s.G Eval)=
        s.upd Eval (.int ((Expr.mul x y).eval values : ℤ)::s.G Eval) := by
      simp [s2,s1,Expr.eval,Nat.cast_mul]
    rw [he] at h
    change IRuns I Fin.elim0 ((Expr.mul x y).compile reg) s _ _ at h
    apply Native.mono h
    simp only [Expr.size]
    ring_nf
    exact le_rfl

end KoanaKPaths.Machine.Arithmetic

end

theorem solution :
∀ {v : Nat} (I : List.{0} NLogN.Sym) (reg : Fin v → Fin KoanaKPaths.Machine.Square.NS)
  (hreg : ∀ (i : Fin v), @Ne.{1} (Fin KoanaKPaths.Machine.Square.NS) (reg i) KoanaKPaths.Machine.Square.Eval)
  (values : Fin v → Nat) (e : KoanaKPaths.Machine.Arithmetic.Expr v) (w : Nat)
  (hw : @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.width v values e) w)
  (s : NLogN.IState KoanaKPaths.Machine.Square.NS)
  (hv :
    ∀ (i : Fin v),
      @Exists.{1} (List.{0} NLogN.Item) fun (tail : List.{0} NLogN.Item) =>
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s (reg i))
          (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (values i))) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.Arithmetic.Expr.compile v reg e) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Square.NS s KoanaKPaths.Machine.Square.Eval
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e)))
        (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s KoanaKPaths.Machine.Square.Eval)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
        (@KoanaKPaths.Machine.Arithmetic.Expr.size v e))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  exact @KoanaKPaths.Machine.Arithmetic.Expr.compile_runs

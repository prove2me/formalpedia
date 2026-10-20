-- Prove2me | solution 2 for OAI.SingleFold.Counter.trace_system
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:28:25.626247+00:00
-- url     : https://prove2.me/submissions/03c8157a-bc5c-483a-99dc-06bd0ccbc4ea

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterBounds.lean:L258-L350
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.trace_system. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
import Theorems.Thm_OAI_SingleFold_Counter_value_bound
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit

-- ---- from OAI.NumberTheory.SingleFold.Packed ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed

lemma testBit_digit (w x t j : ℕ) :
    (digit (2^w) x t).testBit j=(decide (j < w) && x.testBit (w*t+j)) := by
  unfold digit
  rw [Nat.testBit_mod_two_pow,←pow_mul]
  congr 1
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.div_div_eq_div_mul,←pow_add]

lemma bits_blocks {w : ℕ} (hw : 0 < w) (x y : ℕ) :
    Bits x y ↔ ∀t, Bits (digit (2^w) x t) (digit (2^w) y t) := by
  simp only [bits_testBit,testBit_digit,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h t j hj
    exact ⟨hj.1,h _ hj.2⟩
  · intro h i hi
    have hh := h (i/w) (i%w) ⟨Nat.mod_lt i hw, by simpa [Nat.div_add_mod] using hi⟩
    simpa [Nat.div_add_mod] using hh.2

lemma digit_zero (B t : ℕ) : digit B 0 t=0 := by simp [digit]
lemma pack_succ (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=pack B k f+f k*B^k := by
  simp [pack,Finset.sum_range_succ]
lemma pack_cons (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=f 0+B*pack B k (fun t=>f (t+1)) := by
  simp only [pack,Finset.sum_range_succ',pow_zero,mul_one,Finset.mul_sum,pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intros; ring
lemma pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B 0 f=0 := by simp [pack]
lemma pack_add (B k : ℕ) (f g : ℕ → ℕ) :
    pack B k (fun t=>f t+g t)=pack B k f+pack B k g := by simp [pack,add_mul,Finset.sum_add_distrib]
lemma pack_mul (B k c : ℕ) (f : ℕ → ℕ) :
    pack B k (fun t=>c*f t)=c*pack B k f := by simp [pack,Finset.mul_sum,mul_assoc]
lemma pack_lt {B k : ℕ} (_hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) : pack B k f < B^k := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    rw [pack_succ,pow_succ]
    have hi := ih (fun t ht=>hf t (by omega))
    have hh := hf k (by omega)
    nlinarith only [hi,hh,pow_pos _hB k]

lemma digit_pack {B k : ℕ} (hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) (i : ℕ) :
    digit B (pack B k f) i=if i < k then f i else 0 := by
  induction k generalizing f i with
  | zero => simp [pack_zero,digit_zero]
  | succ k ih =>
    rw [pack_cons]
    cases i with
    | zero => simp [digit,Nat.mod_eq_of_lt (hf 0 (by omega))]
    | succ i =>
      rw [digit,pow_succ',←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (hf 0 (by omega)),zero_add]
      simpa only [digit, Nat.add_lt_add_iff_right] using ih (fun t ht=>hf (t+1) (by omega)) i

lemma bits_and (x y : ℕ) : Bits x y ↔ x&&&y=x := by
  rw [bits_testBit]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i  <;> simp [hx,h i]
  · intro h i hi
    have hh := congrArg (fun n=>Nat.testBit n i) h
    simpa [Nat.testBit_and,hi] using hh
lemma bits_le {x y : ℕ} (h : Bits x y) : x ≤ y := by
  rw [←(bits_and x y).mp h]
  exact Nat.and_le_right
lemma bits_refl (x : ℕ) : Bits x x := fun _=>le_rfl
lemma bits_zero_left (x : ℕ) : Bits 0 x := by intro i; simp
lemma bits_one (x : ℕ) : Bits x 1 ↔ x ≤ 1 := by
  constructor
  · exact bits_le
  · intro h
    interval_cases x
    · exact bits_zero_left 1
    · exact bits_refl 1
lemma bits_full (x h : ℕ) : Bits x (2^h-1) ↔ x < 2^h := by
  constructor
  · intro hh
    have := bits_le hh
    have := Nat.two_pow_pos h
    omega
  · intro hh
    rw [bits_and]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hh

lemma ones_mul (B k c : ℕ) : c*ones B k=pack B k (fun _=>c) := by
  simpa [ones] using (pack_mul B k c (fun _=>1)).symm
lemma geometric {B : ℕ} (hB : 1 < B) (k : ℕ) : (B-1)*ones B k=B^k-1 := by
  induction k with
  | zero => simp [ones,pack_zero]
  | succ k ih =>
    change (B-1)*pack B (k+1) (fun _=>1)=B^(k+1)-1
    rw [pack_succ,mul_add,one_mul,pow_succ]
    change (B-1)*ones B k+(B-1)*B^k=B^k*B-1
    rw [ih]
    have hp := pow_pos (by omega : 0 < B) k
    nlinarith only [hp, hB, Nat.sub_add_cancel (by omega : 1 ≤ B), Nat.sub_add_cancel (by omega : 1 ≤ B^k), Nat.sub_add_cancel (show 1 ≤ B^k*B by exact Nat.mul_pos hp (by omega))]
lemma pack_sum {ι : Type} [Fintype ι] (B k : ℕ) (f : ι → ℕ → ℕ) :
    pack B k (fun t=>∑i,f i t)=∑i,pack B k (f i) := by
  simp only [pack, Finset.sum_mul]
  rw [Finset.sum_comm]
lemma pack_congr {B k : ℕ} {f g : ℕ → ℕ} (h : ∀t < k,f t=g t) : pack B k f=pack B k g := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_range.mp ht)]
lemma pack_const_zero (B k : ℕ) : pack B k (fun _=>0)=0 := by simp [pack]
lemma pack_shift (B k : ℕ) (f : ℕ → ℕ) :
    pack B (k+1) (fun t=>if t=0 then 0 else f (t-1))=B*pack B k f := by
  rw [pack_cons]
  simp
lemma pack_init (B k a : ℕ) (f : ℕ → ℕ) :
    pack B (k+1) (fun t=>if t=0 then a else f (t-1))=a+B*pack B k f := by
  rw [pack_cons]
  simp
lemma pack_last {B T : ℕ} {f : ℕ → ℕ} (hf : f T=0) : pack B (T+1) f=pack B T f := by
  rw [pack_succ,hf,zero_mul,add_zero]

lemma update_identity {B T d : ℕ} (r a f : ℕ → ℕ) (h0 : r 0=d)
    (hstep : ∀t < T,r (t+1)+f t=r t+a t) :
    pack B (T+1) r+B*pack B T f=d+B*(pack B T r+pack B T a) := by
  rw [←pack_shift B T f,←pack_add,←pack_add,←pack_init B T d (fun t=>r t+a t)]
  apply pack_congr
  intro t ht
  by_cases he : t=0
  · simp [he,h0]
  · have hh := hstep (t-1) (by omega)
    simpa [he,show t-1+1=t by omega] using hh
end SingleFold.Packed

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter

section
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
omit [DecidableEq Q] in
lemma run_succ (M : Machine Q J) (d : J → ℕ) (t : ℕ) : run M d (t+1)=next M (run M d t) :=
  Function.iterate_succ_apply' _ _ _
variable [Fintype Q] [Fintype J]
end

open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
end

section
variable (h : System M d v)
include h
end

variable (h : System M d v)
include h
end System
end SingleFold.Counter

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace SingleFold.Packed
lemma bits_pack {B w k : ℕ} (hB : B=2^w) (hw : 0 < w) (f g : ℕ → ℕ)
    (hf : ∀t < k,f t < B) (hg : ∀t < k,g t < B) (hfg : ∀t < k,Bits (f t) (g t)) :
    Bits (pack B k f) (pack B k g) := by
  rw [hB,bits_blocks hw]
  intro t
  by_cases ht : t < k
  · simpa only [←hB,digit_pack (by rw [hB]; positivity) hf,
      digit_pack (by rw [hB]; positivity) hg,ite_eq_left ht] using hfg t ht
  · simp only [←hB,digit_pack (by rw [hB]; positivity) hf,
      digit_pack (by rw [hB]; positivity) hg,ite_eq_right ht]
    exact bits_refl 0
end SingleFold.Packed

namespace SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
omit [DecidableEq J] in
lemma stateAt_le (c : Cfg Q J) (q : Q) : stateAt c q ≤ 1 := by unfold stateAt; split_ifs <;> omega
omit [DecidableEq J] in
lemma zeroAt_le (M : Machine Q J) (c : Cfg Q J) (q : Q) : zeroAt M c q ≤ stateAt c q := by
  unfold zeroAt stateAt
  split <;> split_ifs <;> simp_all
omit [DecidableEq J] in
lemma decAt_le (M : Machine Q J) (c : Cfg Q J) (q : Q) : decAt M c q ≤ stateAt c q := by
  unfold decAt stateAt
  split <;> split_ifs <;> simp_all
omit [DecidableEq J] in
lemma arcAt_inactive (M : Machine Q J) (c : Cfg Q J) (q : Q) (b : Bool) (hq : q≠c.state) : arcAt M c q b=0 := by
  cases hi : M.instr q <;> cases b <;> simp [arcAt,stateAt,zeroAt,decAt,hi,hq]
omit [DecidableEq J] in
lemma arcAt_halt (M : Machine Q J) (c : Cfg Q J) (hc : c.state=M.halt) (q : Q) (b : Bool) : arcAt M c q b=0 := by
  by_cases hq : q=c.state
  · have hi : M.instr q=.halt := (M.halt_iff q).mpr (hq.trans hc)
    cases b <;> simp [arcAt,hi]
  · exact arcAt_inactive M c q b hq
omit [DecidableEq J] in
lemma testAt_partition (M : Machine Q J) (c : Cfg Q J) (q : Q) (j : J) (p0 pd : Q)
    (hi : M.instr q=.test j p0 pd) : zeroAt M c q+decAt M c q=stateAt c q := by
  simp only [zeroAt,decAt,hi,stateAt]
  by_cases hq : q=c.state <;> by_cases hz : c.value j=0 <;> simp [hq,hz]
variable [Fintype Q]
omit [DecidableEq J] in
lemma incomingAt_active (M : Machine Q J) (c : Cfg Q J) (p : Q) :
    incomingAt M c p=∑b : Bool,if dest M c.state b=some p then arcAt M c c.state b else 0 := by
  apply Finset.sum_eq_single c.state
  · intro q hq hqc
    apply Finset.sum_eq_zero
    intro b hb
    simp [arcAt_inactive M c q b hqc]
  · simp
lemma incAt_active (M : Machine Q J) (c : Cfg Q J) (j : J) :
    incAt M c j=match M.instr c.state with | .inc i _=>if i=j then 1 else 0 | _=>0 := by
  unfold incAt
  rw [Finset.sum_eq_single c.state]
  · simp [stateAt] <;> rfl
  · intro q hq hqc
    cases hi : M.instr q <;> simp [stateAt,hqc]
  · simp
lemma subAt_active (M : Machine Q J) (c : Cfg Q J) (j : J) :
    subAt M c j=match M.instr c.state with | .test i _ _=>if i=j ∧ c.value i≠0 then 1 else 0 | _=>0 := by
  unfold subAt
  rw [Finset.sum_eq_single c.state]
  · cases hi : M.instr c.state <;> simp [decAt,hi,ite_and]
  · intro q hq hqc
    cases hi : M.instr q <;> simp [decAt,hi,hqc]
  · simp
lemma incomingAt_next (M : Machine Q J) (c : Cfg Q J) (hc : c.state≠M.halt) (p : Q) :
    incomingAt M c p=stateAt (next M c) p := by
  rw [incomingAt_active]
  cases hi : M.instr c.state with
  | halt => exact False.elim (hc ((M.halt_iff _).mp hi))
  | inc j q => simp [dest,arcAt,hi,stateAt,next,eq_comm]
  | test j p0 pd =>
    by_cases hz : c.value j=0 <;> simp [dest,arcAt,hi,stateAt,next,zeroAt,decAt,hz,eq_comm]
lemma counterAt_next (M : Machine Q J) (c : Cfg Q J) (j : J) :
    (next M c).value j+subAt M c j=c.value j+incAt M c j := by
  rw [incAt_active,subAt_active]
  cases hi : M.instr c.state with
  | halt => simp [next,hi]
  | inc i p =>
    by_cases hij : i=j
    · subst i; simp [next,hi]
    · simp [next,hi,hij,Ne.symm hij,Function.update_of_ne]
  | test i p0 pd =>
    by_cases hz : c.value i=0
    · simp [next,hi,hz]
    · by_cases hij : i=j
      · subst i; simp [next,hi,hz]; omega
      · simp [next,hi,hz,hij,Ne.symm hij,Function.update_of_ne]
lemma incAt_halt (M : Machine Q J) (c : Cfg Q J) (hc : c.state=M.halt) (j : J) : incAt M c j=0 := by
  rw [incAt_active,(M.halt_iff _).mpr hc]
lemma subAt_halt (M : Machine Q J) (c : Cfg Q J) (hc : c.state=M.halt) (j : J) : subAt M c j=0 := by
  rw [subAt_active,(M.halt_iff _).mpr hc]
end SingleFold.Counter

namespace SingleFold.Packed
lemma pack_ite_const (B k : ℕ) (p : Prop) [Decidable p] (f g : ℕ → ℕ) :
    pack B k (fun t=>if p then f t else g t)=if p then pack B k f else pack B k g := by
  by_cases hp : p <;> simp [hp]
end SingleFold.Packed
namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
lemma trace_arc (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (q : Q) (a : Bool) :
    arc M (trace M d B w b T) q a=pack B (T+1) (fun t=>arcAt M (run M d t) q a) := by
  cases hi : M.instr q <;> cases a <;> simp [arc,arcAt,hi,trace,pack_const_zero]
lemma trace_incoming (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (q : Q) :
    incoming M (trace M d B w b T) q=pack B (T+1) (fun t=>incomingAt M (run M d t) q) := by
  simp only [incoming,incomingAt,pack_sum,pack_ite_const,pack_const_zero,trace_arc]
lemma trace_inc (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (j : J) :
    increments M (trace M d B w b T) j=pack B (T+1) (fun t=>incAt M (run M d t) j) := by
  simp only [increments,incAt,pack_sum]
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [trace,pack_const_zero,pack_ite_const]
lemma trace_sub (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (j : J) :
    decrements M (trace M d B w b T) j=pack B (T+1) (fun t=>subAt M (run M d t) j) := by
  simp only [decrements,subAt,pack_sum]
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [trace,pack_const_zero,pack_ite_const]
lemma trace_transition (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (hT : HaltsAt M d T) (q : Q) :
    (trace M d B w b T).state q=(if q=M.start then 1 else 0)+B*incoming M (trace M d B w b T) q := by
  rw [trace_incoming]
  have hlast : incomingAt M (run M d T) q=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro b hb
    simp [arcAt_halt M _ hT.1]
  rw [pack_last hlast]
  change pack B (T+1) (fun t=>stateAt (run M d t) q)=_
  rw [pack_cons]
  congr 1
  apply congrArg (B*·)
  apply pack_congr
  intro t ht
  rw [incomingAt_next M _ (hT.2 t ht),run_succ]
lemma trace_update (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (hT : HaltsAt M d T) (j : J) :
    (trace M d B w b T).counter (some j)+B*decrements M (trace M d B w b T) j=
      d j+B*((trace M d B w b T).rem (some j)+increments M (trace M d B w b T) j) := by
  rw [trace_inc,trace_sub]
  have hi := pack_last (B:=B) (T:=T) (f:=fun t=>incAt M (run M d t) j)
    (incAt_halt M _ hT.1 j)
  have hs := pack_last (B:=B) (T:=T) (f:=fun t=>subAt M (run M d t) j)
    (subAt_halt M _ hT.1 j)
  rw [hi,hs]
  exact update_identity _ _ _ rfl (fun t _=>by simpa only [valueAt,run_succ] using counterAt_next M (run M d t) j)
omit [DecidableEq Q] in
lemma valueAt_bound (M : Machine Q J) (d : J → ℕ) (j : Option J) (t T : ℕ) (ht : t ≤ T) :
    valueAt M d j t ≤ baseC Q d+T := by
  cases j with
  | none => dsimp [valueAt]; omega
  | some j =>
    have hi : d j ≤ ∑i,d i := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
    have hh := value_bound M d t j
    dsimp [valueAt,baseC]
    omega
end SingleFold.Counter

namespace SingleFold.Packed
lemma bits_of_le_one {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ 1) : Bits x y := by
  interval_cases y
  · have hx : x=0 := by omega
    simpa [hx] using bits_refl 0
  · exact (bits_one x).mpr hxy
end SingleFold.Packed

namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
lemma trace_clock (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) :
    (trace M d B w b T).counter none+B*(trace M d B w b T).last=
      baseC Q d+B*((trace M d B w b T).rem none+(trace M d B w b T).mask) := by
  have hh := update_identity (B:=B) (T:=T) (d:=baseC Q d)
    (fun t=>baseC Q d+t) (fun _=>1) (fun _=>0) (by omega) (by intros; omega)
  rw [pack_const_zero,mul_zero,add_zero] at hh
  change pack B (T+1) (fun t=>baseC Q d+t)+B*B^T=
    baseC Q d+B*(pack B T (fun t=>baseC Q d+t)+ones B (T+1))
  rw [hh,ones,pack_succ]
  ring

lemma trace_system (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ)
    (hT : HaltsAt M d T) (hB : B=2^w) (hw : 0 < w) (hb : 0 < b)
    (hbase : B=4*b) (hlarge : 2*(baseC Q d+T) < B) (hsmall : b ≤ baseC Q d+T) :
    System M d (trace M d B w b T) := by
  have hBpos : 0 < B := by omega
  have hBone : 1 < B := by omega
  have hhalf : 2*b=2^(w-1) := by
    have hh : 2^w=2^(w-1)*2 := by
      nth_rw 1 [show w=(w-1)+1 by omega]
      rw [pow_succ]
    omega
  have hv (j : Option J) (t : ℕ) (ht : t ≤ T) : valueAt M d j t < 2*b := by
    have := valueAt_bound M d j t T ht
    omega
  have hvl (j : Option J) (t : ℕ) (ht : t ≤ T) : valueAt M d j t < B := by
    have := hv j t ht
    omega
  have hs (t : ℕ) (q : Q) : stateAt (run M d t) q < B :=
    lt_of_le_of_lt (stateAt_le _ _) hBone
  refine ⟨hB,hbase,by dsimp [trace]; omega,by simp [trace],rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [trace]; rw [pow_succ,mul_comm]
  · exact geometric hBone (T+1)
  · intro q
    exact bits_pack hB hw _ _ (fun t _=>hs t q) (fun _ _=>hBone)
      (fun t _=>(bits_one _).mpr (stateAt_le _ _))
  · change (∑q,pack B (T+1) (fun t=>stateAt (run M d t) q))=ones B (T+1)
    rw [←pack_sum]
    apply pack_congr
    intro t ht
    simp [stateAt]
  · intro q
    cases hi : M.instr q with
    | halt => simp [trace,zeroAt,decAt,hi,pack_const_zero]
    | inc j p => simp [trace,zeroAt,decAt,hi,pack_const_zero]
    | test j p0 pd =>
      have hz (t : ℕ) : zeroAt M (run M d t) q ≤ 1 := le_trans (zeroAt_le _ _ _) (stateAt_le _ _)
      have hn (t : ℕ) : decAt M (run M d t) q ≤ 1 := le_trans (decAt_le _ _ _) (stateAt_le _ _)
      change Packed.Bits _ _ ∧ Packed.Bits _ _ ∧ _ ∧ _
      refine ⟨?_,?_,?_,?_⟩
      · exact bits_pack hB hw _ _ (fun t _=>lt_of_le_of_lt (hz t) hBone) (fun t _=>hs t q)
          (fun t _=>bits_of_le_one (zeroAt_le _ _ _) (stateAt_le _ _))
      · exact bits_pack hB hw _ _ (fun t _=>lt_of_le_of_lt (hn t) hBone) (fun t _=>hs t q)
          (fun t _=>bits_of_le_one (decAt_le _ _ _) (stateAt_le _ _))
      · change pack B (T+1) _+pack B (T+1) _=pack B (T+1) _
        rw [←pack_add]
        apply pack_congr
        intro t ht
        exact testAt_partition _ _ _ _ _ _ hi
      · change pack B (T+1) _+(match M.instr q with | .test _ _ _=>_ | _=>0)=ones B (T+1)
        rw [hi,←pack_add]
        apply pack_congr
        intro t ht
        exact Nat.add_sub_of_le (hz t)
  · exact trace_transition M d B w b T hT
  · intro j
    refine ⟨?_,?_,?_⟩
    · change Packed.Bits (pack B (T+1) (valueAt M d j)) ((2*b-1)*ones B (T+1))
      rw [ones_mul]
      apply bits_pack hB hw _ _ (fun t ht=>hvl j t (by omega)) (by intros; omega)
      intro t ht
      rw [hhalf]
      exact (bits_full _ _).mpr (by rw [←hhalf]; exact hv j t (by omega))
    · change pack B (T+1) _=valueAt M d j T*B^T+pack B T _
      rw [pack_succ,add_comm]
    · exact pack_lt hBpos (fun t ht=>hvl j t (by omega))
  · exact trace_update M d B w b T hT
  · intro q
    cases hi : M.instr q with
    | halt => trivial
    | inc j p => trivial
    | test j p0 pd =>
      change Packed.Bits (pack B (T+1) (valueAt M d (some j))) ((B-1)*_)
      simp only [trace,hi]
      rw [←pack_mul]
      apply bits_pack hB hw _ _ (fun t ht=>hvl (some j) t (by omega))
      · intro t ht
        have hh : zeroAt M (run M d t) q ≤ 1 := le_trans (zeroAt_le _ _ _) (stateAt_le _ _)
        interval_cases hz : zeroAt M (run M d t) q <;> simp <;> omega
      · intro t ht
        by_cases hz : zeroAt M (run M d t) q=0
        · simp only [hz,Nat.sub_zero,mul_one]
          rw [hB]
          exact (bits_full _ _).mpr (by rw [←hB]; exact hvl (some j) t (by omega))
        · have hj : (run M d t).value j=0 := by
            simp only [zeroAt,hi] at hz
            split_ifs at hz with hc
            · exact hc.2
            · contradiction
          simp only [valueAt,hj]
          exact bits_zero_left _
  · exact trace_clock M d B w b T
  · exact hsmall
  · exact hlarge

end SingleFold.Counter

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter
open Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.trace_system := @_root_.OAI.SingleFold.Counter.trace_system

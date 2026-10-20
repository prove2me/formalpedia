-- Prove2me | solution 2 for OAI.SingleFold.Counter.System.counter_update
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:16:05.815405+00:00
-- url     : https://prove2.me/submissions/f8aaa22d-fb84-4d31-81d6-0b1475f8f31b

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterRecords.lean:L60-L84
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.System.counter_update. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_Counter_System_counter_info
import Theorems.Thm_OAI_SingleFold_Counter_System_halt_mask
import Theorems.Thm_OAI_SingleFold_Counter_System_selected_bound
import Theorems.Thm_OAI_SingleFold_Counter_System_selected_digit
import Theorems.Thm_OAI_SingleFold_Packed_bits_mask
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit
import Theorems.Thm_OAI_SingleFold_Packed_pack_digits
import Theorems.Thm_OAI_SingleFold_Packed_update_coefficients

-- ---- from OAI.NumberTheory.SingleFold.Packed ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed

lemma digit_lt {B : ℕ} (hB : 0 < B) (x t : ℕ) : digit B x t < B := Nat.mod_lt _ hB
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
lemma bits_ones {w k x : ℕ} (hw : 0 < w) :
    Bits x (ones (2^w) k) ↔ x < (2^w)^k ∧ ∀t < k,digit (2^w) x t ≤ 1 := by
  simpa [bits_one] using bits_mask (x:=x) (k:=k) hw (Nat.one_lt_two_pow (by omega : w≠0))

lemma pack_sum {ι : Type} [Fintype ι] (B k : ℕ) (f : ι → ℕ → ℕ) :
    pack B k (fun t=>∑i,f i t)=∑i,pack B k (f i) := by
  simp only [pack, Finset.sum_mul]
  rw [Finset.sum_comm]
lemma digit_sum {ι : Type} [Fintype ι] {B k : ℕ} (hB : 0 < B) (x : ι → ℕ)
    (hx : ∀i,x i < B^k) (hc : ∀t < k,∑i,digit B (x i) t < B) (t : ℕ) :
    digit B (∑i,x i) t=if t < k then ∑i,digit B (x i) t else 0 := by
  have he : (∑i,x i)=pack B k (fun t=>∑i,digit B (x i) t) := by
    rw [pack_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (pack_digits hB (hx i)).symm
  rw [he,digit_pack hB hc]

lemma bits_trans {x y z : ℕ} (hxy : Bits x y) (hyz : Bits y z) : Bits x z :=
  fun i=>(hxy i).trans (hyz i)
lemma pack_last {B T : ℕ} {f : ℕ → ℕ} (hf : f T=0) : pack B (T+1) f=pack B T f := by
  rw [pack_succ,hf,zero_mul,add_zero]

lemma division_last {B T R ρ η : ℕ} (hB : 0 < B) (hR : R < B^(T+1))
    (he : R=ρ*B^T+η) (hη : η < B^T) :
    ρ=digit B R T ∧ η=pack B T (digit B R) := by
  have hp := pack_digits hB hR
  rw [pack_succ] at hp
  have hl : pack B T (digit B R) < B^T := pack_lt hB (fun t _=>digit_lt hB R t)
  have hq : R/B^T=ρ := by rw [he,Nat.add_comm,Nat.add_mul_div_right _ _ (pow_pos hB T),Nat.div_eq_of_lt hη,zero_add]
  have hq' : R/B^T=digit B R T := by nth_rw 1 [←hp]; rw [Nat.add_mul_div_right _ _ (pow_pos hB T),Nat.div_eq_of_lt hl,zero_add]
  have hr : ρ=digit B R T := hq.symm.trans hq'
  exact ⟨hr,by rw [hr] at he; omega⟩

end SingleFold.Packed

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

namespace SingleFold.Counter

section
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
variable [Fintype Q] [Fintype J]
end

open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
omit [DecidableEq Q] [DecidableEq J] h in
lemma Cpos : 0 < baseC Q d := by simp [baseC]
lemma Bpos : 0 < v.B := by have := h.bound; have := (System.Cpos (Q:=Q) (d:=d)); omega
lemma Bfour : 4 ≤ v.B := by have := h.base; have := h.Bpos; omega
lemma Bgt : 1 < v.B := by have := h.Bfour; omega
lemma width : 0 < v.w := by
  by_contra hh
  have hw : v.w=0 := by omega
  have := h.power
  rw [hw,pow_zero] at this
  have := h.Bfour
  omega
lemma states_bound : 2*Fintype.card Q < v.B := by
  have := h.bound
  dsimp [baseC] at this
  omega
lemma initial_bound (j : J) : d j < 2*v.b := by
  have hh : d j ≤ ∑i,d i := Finset.single_le_sum (fun i _=>Nat.zero_le _) (Finset.mem_univ j)
  have hb := h.bound
  have hbase := h.base
  dsimp [baseC] at hb
  omega
lemma last_eq : v.last=v.B^(v.k-1) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := h.last
  rw [h.full,hk,pow_succ'] at he
  exact Nat.eq_of_mul_eq_mul_left h.Bpos he
lemma mask_eq : v.mask=ones v.B v.k := by
  have he := h.mask
  rw [h.full,←geometric h.Bgt v.k] at he
  exact Nat.eq_of_mul_eq_mul_left (by have := h.Bgt; omega) he
lemma rem_eq (j : Option J) : v.rem j=pack v.B (v.k-1) (digit v.B (v.counter j)) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := (h.counter j).2.1
  rw [h.last_eq] at he
  have hr := (h.counter j).2.2
  rw [h.last_eq] at hr
  exact (division_last h.Bpos (by rw [←hk]; exact (h.counter_info j).1) he hr).2
end

section
variable (h : System M d v)
include h
lemma outgoing (q : Q) : v.state q=(if q=M.halt then v.state q else 0)+∑b : Bool,arc M v q b := by
  cases hi : M.instr q with
  | halt => have hq := (M.halt_iff q).mp hi; simp [hq,arc,(M.halt_iff M.halt).mpr rfl]
  | inc j p =>
    have hq : q≠M.halt := by intro hh; have := (M.halt_iff q).mpr hh; rw [hi] at this; contradiction
    simp [hq,arc,hi]
  | test j p0 pd =>
    have hq : q≠M.halt := by intro hh; have := (M.halt_iff q).mpr hh; rw [hi] at this; contradiction
    have hb := h.branch q
    rw [hi] at hb
    simpa [hq,arc,hi,add_comm] using hb.2.2.1.symm
lemma outgoing_sum : v.mask=v.state M.halt+∑q,∑b : Bool,arc M v q b := by
  rw [←h.partition]
  calc
    _ = ∑q,((if q=M.halt then v.state q else 0)+∑b : Bool,arc M v q b) :=
      Finset.sum_congr rfl (fun q _=>h.outgoing q)
    _ = _ := by rw [Finset.sum_add_distrib]; simp
lemma arc_bits (q : Q) (b : Bool) : Packed.Bits (arc M v q b) v.mask := by
  cases hi : M.instr q with
  | halt => cases b <;> simp [arc,hi,bits_zero_left]
  | inc j p => cases b <;> simp [arc,hi,bits_zero_left]; exact h.state_bits q
  | test j p0 pd =>
    have hb:=h.branch q
    rw [hi] at hb
    cases b
    · simpa only [arc,hi] using bits_trans hb.1 (h.state_bits q)
    · simpa only [arc,hi] using bits_trans hb.2.1 (h.state_bits q)
lemma arc_info (q : Q) (b : Bool) : arc M v q b < v.B^v.k ∧ ∀t < v.k,digit v.B (arc M v q b) t ≤ 1 := by
  have hh:=h.arc_bits q b
  rw [h.mask_eq,h.power] at hh
  rw [h.power]
  exact (bits_ones h.width).mp hh
end

variable (h : System M d v)
include h
lemma arcs_sum_eq : (∑q,∑b : Bool,arc M v q b)=ones v.B (v.k-1) := by
  have he:=h.outgoing_sum
  rw [h.mask_eq,h.halt_mask,h.last_eq] at he
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have hp : ones v.B v.k=ones v.B (v.k-1)+v.B^(v.k-1) := by
    nth_rw 1 [hk]
    simp only [ones,pack_succ,one_mul]
  rw [hp] at he
  omega
lemma arc_digit_cap (t : ℕ) (ht : t < v.k) : (∑q,∑b : Bool,digit v.B (arc M v q b) t) < v.B := by
  have hc : (∑q,∑b : Bool,digit v.B (arc M v q b) t) ≤ 2*Fintype.card Q := by
    calc _ ≤ ∑q : Q,∑b : Bool,1 := Finset.sum_le_sum (fun q _=>Finset.sum_le_sum (fun b _=>(h.arc_info q b).2 t ht))
         _ = _ := by simp; omega
  exact hc.trans_lt h.states_bound
lemma arc_digit_sum (t : ℕ) (ht : t < v.k) :
    (∑q,∑b : Bool,digit v.B (arc M v q b) t)=if t < v.k-1 then 1 else 0 := by
  have hc : ∀u < v.k,(∑a : Q×Bool,digit v.B (arc M v a.1 a.2) u) < v.B := by
    intro u hu
    simpa only [Fintype.sum_prod_type] using h.arc_digit_cap u hu
  have he:=digit_sum h.Bpos (fun a : Q×Bool=>arc M v a.1 a.2) (fun a=>(h.arc_info a.1 a.2).1) hc t
  simp only [Fintype.sum_prod_type,ite_eq_left ht,h.arcs_sum_eq] at he
  rw [ones,digit_pack h.Bpos (fun _ _=>h.Bgt)] at he
  exact he.symm

lemma selected_le_one (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) :
    digit v.B (selected (M:=M) (v:=v) P) t ≤ if t < v.k-1 then 1 else 0 := by
  rw [h.selected_digit P t ht,←h.arc_digit_sum t ht]
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro b hb
  split_ifs <;> simp
end System
end SingleFold.Counter

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterRecords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed
end SingleFold.Packed

namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System
variable (h : System M d v)
include h
lemma selected_pack (P : Q → Bool → Prop) [DecidableRel P] :
    selected (M:=M) (v:=v) P=pack v.B (v.k-1) (digit v.B (selected (M:=M) (v:=v) P)) := by
  have hp := pack_digits h.Bpos (h.selected_bound P)
  have hz : digit v.B (selected (M:=M) (v:=v) P) (v.k-1)=0 := by
    have hh:=h.selected_le_one P (v.k-1) (by have:=h.length; omega)
    simpa using hh
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  nth_rw 1 [hk] at hp
  rw [pack_last hz] at hp
  exact hp.symm
attribute [local instance] Classical.propDecidable
omit [Fintype J] [DecidableEq Q] h in
lemma inc_selected (j : J) : increments M v j=selected (M:=M) (v:=v)
    (fun q b=>match M.instr q with | .inc i _ => i=j ∧ b=false | _=>False) := by
  unfold increments selected
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [hi,arc]
omit [Fintype J] [DecidableEq Q] h in
lemma dec_selected (j : J) : decrements M v j=selected (M:=M) (v:=v)
    (fun q b=>match M.instr q with | .test i _ _ => i=j ∧ b=true | _=>False) := by
  unfold decrements selected
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [hi,arc]
lemma counter_update (j : J) :
    digit v.B (v.counter (some j)) 0=d j ∧ ∀t < v.k-1,
    digit v.B (v.counter (some j)) (t+1)+digit v.B (decrements M v j) t=
      digit v.B (v.counter (some j)) t+digit v.B (increments M v j) t := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have ha : ∀t < v.k-1,digit v.B (increments M v j) t ≤ 1 := by
    intro t ht
    rw [(System.inc_selected (M:=M) (v:=v))]
    have hh:=h.selected_le_one (fun q b=>match M.instr q with | .inc i _=>i=j ∧ b=false | _=>False) t (by omega)
    simpa [ht] using hh
  have hf : ∀t < v.k-1,digit v.B (decrements M v j) t ≤ 1 := by
    intro t ht
    rw [(System.dec_selected (M:=M) (v:=v))]
    have hh:=h.selected_le_one (fun q b=>match M.instr q with | .test i _ _=>i=j ∧ b=true | _=>False) t (by omega)
    simpa [ht] using hh
  apply update_coefficients (B:=v.B) (T:=v.k-1) (m:=2*v.b) (by have:=h.base; omega) (h.initial_bound j) _ _ _
    (by intro t ht; exact (h.counter_info (some j)).2 t (by omega)) ha hf
  have he:=h.update j
  rw [h.rem_eq] at he
  have hac := h.selected_pack (fun q b=>match M.instr q with | .inc i _=>i=j ∧ b=false | _=>False)
  have hfc := h.selected_pack (fun q b=>match M.instr q with | .test i _ _=>i=j ∧ b=true | _=>False)
  rw [←(System.inc_selected (M:=M) (v:=v))] at hac
  rw [←(System.dec_selected (M:=M) (v:=v))] at hfc
  rw [←hk,pack_digits h.Bpos (h.counter_info (some j)).1,←hac,←hfc]
  exact he
end System
end SingleFold.Counter

namespace SingleFold.Packed
end SingleFold.Packed
namespace SingleFold.Counter
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
attribute [local instance] Classical.propDecidable
end

variable (h : System M d v)
include h
end System

end SingleFold.Counter

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.System.counter_update := @_root_.OAI.SingleFold.Counter.System.counter_update

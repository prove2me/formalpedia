-- Prove2me | solution 2 for OAI.SingleFold.Counter.system_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:26:23.200576+00:00
-- url     : https://prove2.me/submissions/c52ebce8-0f0a-42d2-8c43-44498bb740fb

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterRecords.lean:L393-L459
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.system_unique. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_Counter_System_decode
import Theorems.Thm_OAI_SingleFold_Counter_System_haltsAt
import Theorems.Thm_OAI_SingleFold_Counter_System_test_choice
import Theorems.Thm_OAI_SingleFold_Packed_bits_mask
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit
import Theorems.Thm_OAI_SingleFold_Packed_pack_digits
import Theorems.Thm_OAI_SingleFold_Packed_unique_scale
import Theorems.Thm_OAI_SingleFold_Packed_update_coefficients

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

lemma digit_lt {B : ℕ} (hB : 0 < B) (x t : ℕ) : digit B x t < B := Nat.mod_lt _ hB
lemma pack_succ (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=pack B k f+f k*B^k := by
  simp [pack,Finset.sum_range_succ]
lemma pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B 0 f=0 := by simp [pack]
lemma pack_lt {B k : ℕ} (_hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) : pack B k f < B^k := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    rw [pack_succ,pow_succ]
    have hi := ih (fun t ht=>hf t (by omega))
    have hh := hf k (by omega)
    nlinarith only [hi,hh,pow_pos _hB k]

lemma digits_ext {B k x y : ℕ} (hB : 0 < B) (hx : x < B^k) (hy : y < B^k)
    (h : ∀t < k,digit B x t=digit B y t) : x=y := by
  rw [←pack_digits hB hx,←pack_digits hB hy]
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_range.mp ht)]

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

lemma bits_trans {x y z : ℕ} (hxy : Bits x y) (hyz : Bits y z) : Bits x z :=
  fun i=>(hxy i).trans (hyz i)
lemma pack_const_zero (B k : ℕ) : pack B k (fun _=>0)=0 := by simp [pack]
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
namespace OAI

namespace SingleFold.Counter

section
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
omit [DecidableEq Q] in
lemma haltsAt_unique {M : Machine Q J} {d : J → ℕ} {T U : ℕ}
    (hT : HaltsAt M d T) (hU : HaltsAt M d U) : T=U := by
  rcases lt_trichotomy T U with h|h|h
  · exact False.elim (hU.2 T h hT.1)
  · exact h
  · exact False.elim (hT.2 U h hU.1)
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
lemma clock_bound : baseC Q d < 2*v.b := by have := h.bound; have := h.base; omega
lemma last_eq : v.last=v.B^(v.k-1) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := h.last
  rw [h.full,hk,pow_succ'] at he
  exact Nat.eq_of_mul_eq_mul_left h.Bpos he
lemma mask_eq : v.mask=ones v.B v.k := by
  have he := h.mask
  rw [h.full,←geometric h.Bgt v.k] at he
  exact Nat.eq_of_mul_eq_mul_left (by have := h.Bgt; omega) he
lemma state_info (q : Q) : v.state q < v.B^v.k ∧ ∀t < v.k,digit v.B (v.state q) t ≤ 1 := by
  have hh := h.state_bits q
  change Packed.Bits (v.state q) v.mask at hh
  rw [h.mask_eq,h.power] at hh
  rw [h.power]
  exact (bits_ones h.width).mp hh
lemma rem_eq (j : Option J) : v.rem j=pack v.B (v.k-1) (digit v.B (v.counter j)) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := (h.counter j).2.1
  rw [h.last_eq] at he
  have hr := (h.counter j).2.2
  rw [h.last_eq] at hr
  exact (division_last h.Bpos (by rw [←hk]; exact (h.counter_info j).1) he hr).2
lemma final_eq (j : Option J) : v.final j=digit v.B (v.counter j) (v.k-1) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := (h.counter j).2.1
  rw [h.last_eq] at he
  have hr := (h.counter j).2.2
  rw [h.last_eq] at hr
  exact (division_last h.Bpos (by rw [←hk]; exact (h.counter_info j).1) he hr).1
end

section
variable (h : System M d v)
include h
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
end System
end SingleFold.Counter

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterRecords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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
attribute [local instance] Classical.propDecidable
lemma clock_update : digit v.B (v.counter none) 0=baseC Q d ∧ ∀t < v.k-1,
    digit v.B (v.counter none) (t+1)=digit v.B (v.counter none) t+1 := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have hmask : v.mask=v.last+ones v.B (v.k-1) := by
    rw [h.mask_eq,h.last_eq]
    nth_rw 1 [hk]
    rw [ones,pack_succ]
    simp only [one_mul]
    exact Nat.add_comm _ _
  have he : v.counter none=baseC Q d+v.B*(v.rem none+ones v.B (v.k-1)) := by
    have hh:=h.clock
    rw [hmask] at hh
    nlinarith only [hh]
  have hh := update_coefficients (B:=v.B) (T:=v.k-1) (m:=2*v.b) (d:=baseC Q d)
    (by have:=h.base; omega) h.clock_bound (digit v.B (v.counter none)) (fun _=>1) (fun _=>0)
    (by intro t ht; exact (h.counter_info none).2 t (by omega)) (by intros; omega) (by intros; omega)
  simp only [pack_const_zero,mul_zero,add_zero] at hh
  apply hh
  rw [←hk,pack_digits h.Bpos (h.counter_info none).1,←h.rem_eq]
  exact he
lemma clock_digits (t : ℕ) (ht : t < v.k) : digit v.B (v.counter none) t=baseC Q d+t := by
  induction t with
  | zero => simpa using h.clock_update.1
  | succ t ih => rw [h.clock_update.2 t (by omega),ih (by omega)]; omega
lemma clock_final : v.final none=baseC Q d+(v.k-1) := by
  rw [h.final_eq,h.clock_digits _ (by have:=h.length; omega)]
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
lemma arc_state_bits (q : Q) (b : Bool) : Packed.Bits (arc M v q b) (v.state q) := by
  cases hi : M.instr q with
  | halt => cases b <;> simp [arc,hi,bits_zero_left]
  | inc j p => cases b <;> simp [arc,hi,bits_zero_left,bits_refl]
  | test j p0 pd =>
    have hb:=h.branch q
    rw [hi] at hb
    cases b
    · simpa only [arc,hi,Bits,Packed.Bits] using hb.1
    · simpa only [arc,hi,Bits,Packed.Bits] using hb.2.1
lemma arc_digit_le (q : Q) (b : Bool) (t : ℕ) : digit v.B (arc M v q b) t ≤ digit v.B (v.state q) t := by
  have hh:=h.arc_state_bits q b
  rw [h.power] at *
  exact bits_le ((bits_blocks h.width _ _).mp hh t)
end

section
variable (h : System M d v)
include h
attribute [local instance] Classical.propDecidable
end

variable (h : System M d v)
include h
lemma branch_digits (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd)
    (t : ℕ) (ht : t < v.k) :
    digit v.B (v.zeroBranch q) t=(if q=(run M d t).state ∧ (run M d t).value j=0 then 1 else 0) ∧
    digit v.B (v.decBranch q) t=(if q=(run M d t).state ∧ (run M d t).value j≠0 then 1 else 0) := by
  by_cases hq : q=(run M d t).state
  · have hnh : q≠M.halt := by intro hh; have := (M.halt_iff q).mpr hh; rw [hi] at this; contradiction
    have hlt : t < v.k-1 := by
      have hh:=h.haltsAt.1
      by_contra hn
      have he : t=v.k-1 := by omega
      rw [he,hh] at hq
      exact hnh hq
    have hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0 := by
      intro p; rw [(h.decode t ht).1 p,hq]
    have hh:=h.test_choice t hlt q hs j p0 pd hi
    rw [(h.decode t ht).2 j] at hh
    by_cases hz : (run M d t).value j=0 <;> simpa [hq,hz] using hh
  · have hz:=h.arc_digit_le q false t
    have hn:=h.arc_digit_le q true t
    simp only [arc,hi] at hz hn
    rw [(h.decode t ht).1 q,ite_eq_right hq] at hz hn
    simp only [hq,false_and,ite_false]
    omega
end System

lemma system_unique {v u : Witness Q J} (hv : System M d v) (hu : System M d u) : v=u := by
  have hk : v.k=u.k := by
    have hh:=haltsAt_unique hv.haltsAt hu.haltsAt
    have := hv.length
    have := hu.length
    omega
  have hf : v.final none=u.final none := by rw [hv.clock_final,hu.clock_final,hk]
  have hw : v.w=u.w := by
    have hp : 0 < v.final none := by rw [hv.clock_final]; have:=(System.Cpos (Q:=Q) (d:=d)); omega
    obtain ⟨w,hw,huniq⟩:=unique_scale hp
    apply (huniq v.w _).trans (huniq u.w _).symm
    · have h₁:=hv.scale_lower; have h₂:=hv.scale_upper; have h₃:=hv.base
      rw [←hv.power]; omega
    · have h₁:=hu.scale_lower; have h₂:=hu.scale_upper; have h₃:=hu.base
      rw [←hu.power]; rw [hf]; omega
  have hB : v.B=u.B := by rw [hv.power,hu.power,hw]
  have hb : v.b=u.b := by have := hv.base; have := hu.base; omega
  have hH : v.H=u.H := by rw [hv.full,hu.full,hB,hk]
  have hl : v.last=u.last := by rw [hv.last_eq,hu.last_eq,hB,hk]
  have hm : v.mask=u.mask := by rw [hv.mask_eq,hu.mask_eq,hB,hk]
  have hs : v.state=u.state := by
    funext q
    apply digits_ext hv.Bpos (hv.state_info q).1 (by rw [hB,hk]; exact (hu.state_info q).1)
    intro t ht
    rw [(hv.decode t ht).1 q,hB,(hu.decode t (by omega)).1 q]
  have hc : v.counter=u.counter := by
    funext j
    apply digits_ext hv.Bpos (hv.counter_info j).1 (by rw [hB,hk]; exact (hu.counter_info j).1)
    intro t ht
    cases j with
    | none => rw [hv.clock_digits t ht,hB,hu.clock_digits t (by omega)]
    | some j => rw [(hv.decode t ht).2 j,hB,(hu.decode t (by omega)).2 j]
  have hz : v.zeroBranch=u.zeroBranch ∧ v.decBranch=u.decBranch ∧ v.complement=u.complement := by
    suffices ∀q,v.zeroBranch q=u.zeroBranch q ∧ v.decBranch q=u.decBranch q ∧ v.complement q=u.complement q from
      ⟨funext (fun q=>(this q).1),funext (fun q=>(this q).2.1),funext (fun q=>(this q).2.2)⟩
    intro q
    have hbv:=hv.branch q
    have hbu:=hu.branch q
    cases hi : M.instr q with
    | halt => rw [hi] at hbv hbu; omega
    | inc j p => rw [hi] at hbv hbu; omega
    | test j p0 pd =>
      rw [hi] at hbv hbu
      have hve:=hv.arc_info q false
      have hue:=hu.arc_info q false
      have hvn:=hv.arc_info q true
      have hun:=hu.arc_info q true
      simp only [arc,hi] at hve hue hvn hun
      have hze : v.zeroBranch q=u.zeroBranch q := by
        apply digits_ext hv.Bpos hve.1 (by rw [hB,hk]; exact hue.1)
        intro t ht
        rw [(hv.branch_digits q j p0 pd hi t ht).1,hB,(hu.branch_digits q j p0 pd hi t (by omega)).1]
      have hne : v.decBranch q=u.decBranch q := by
        apply digits_ext hv.Bpos hvn.1 (by rw [hB,hk]; exact hun.1)
        intro t ht
        rw [(hv.branch_digits q j p0 pd hi t ht).2,hB,(hu.branch_digits q j p0 pd hi t (by omega)).2]
      exact ⟨hze,hne,by omega⟩
  have hfinal : v.final=u.final := by
    funext j
    rw [hv.final_eq,hu.final_eq,hB,hk,hc]
  have hrem : v.rem=u.rem := by
    funext j
    rw [hv.rem_eq,hu.rem_eq,hB,hk,hc]
  rcases hz with ⟨hz,hn,hcpl⟩
  cases v
  cases u
  simp_all only
end SingleFold.Counter

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter
open Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.system_unique := @_root_.OAI.SingleFold.Counter.system_unique

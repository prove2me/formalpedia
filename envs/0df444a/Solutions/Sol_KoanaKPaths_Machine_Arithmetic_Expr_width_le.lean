-- Prove2me | solution 1 for KoanaKPaths.Machine.Arithmetic.Expr.width_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:37:10.000228+00:00
-- url     : https://prove2.me/submissions/9b7d91e9-26eb-4ea4-8d65-bcea869d1418

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
import Theorems.Thm_NLogN_smul_runs
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
namespace KoanaKPaths.Machine.Arithmetic
variable {v : ℕ}



lemma Expr.width_le (values : Fin v→ℕ) (e : Expr v) (U : ℕ) (hw : e.atomWidth values≤ U) :
    e.width values≤ e.size*(U+1) := by
  induction e with
  | constant n => simpa [Expr.width,Expr.eval,Expr.size,Expr.atomWidth] using Nat.le_trans hw (Nat.le_succ U)
  | input i => simpa [Expr.width,Expr.eval,Expr.size,Expr.atomWidth] using Nat.le_trans hw (Nat.le_succ U)
  | add x y ihx ihy =>
    have ha := max_le_iff.mp hw
    have hx := ihx ha.1
    have hy := ihy ha.2
    let B := (x.size+y.size)*(U+1)
    have hxl : x.width values≤ B := by dsimp [B]; nlinarith
    have hyl : y.width values≤ B := by dsimp [B]; nlinarith
    have hr := Wedge.zsz_add_le (x.eval values : ℤ) (y.eval values : ℤ) B
      ((x.root_width values).trans hxl) ((y.root_width values).trans hyl)
    have hb : B+1≤(x.size+y.size+1)*(U+1) := by dsimp [B]; nlinarith
    simp only [Expr.width,Expr.eval,Expr.size]
    apply max_le
    · apply le_trans ?_ hb
      simpa only [Nat.cast_add] using hr
    · exact (max_le hxl hyl).trans (Nat.le_trans (Nat.le_succ B) hb)
  | mul x y ihx ihy =>
    have ha := max_le_iff.mp hw
    have hx := ihx ha.1
    have hy := ihy ha.2
    let B := (x.size+y.size)*(U+1)
    have hxl : x.width values≤ B := by dsimp [B]; nlinarith
    have hyl : y.width values≤ B := by dsimp [B]; nlinarith
    have hr := Square.zsz_mul_le (x.eval values : ℤ) (y.eval values : ℤ)
      (x.size*(U+1)) (y.size*(U+1)) ((x.root_width values).trans hx) ((y.root_width values).trans hy)
    have hb : B≤(x.size+y.size+1)*(U+1) := by dsimp [B]; nlinarith
    simp only [Expr.width,Expr.eval,Expr.size]
    apply max_le
    · have he : x.size*(U+1)+y.size*(U+1)=B := by dsimp [B]; ring
      rw [he] at hr
      apply le_trans ?_ hb
      simpa only [Nat.cast_mul] using hr
    · exact (max_le hxl hyl).trans hb

end KoanaKPaths.Machine.Arithmetic

end

theorem solution :
∀ {v : Nat} (values : Fin v → Nat) (e : KoanaKPaths.Machine.Arithmetic.Expr v) (U : Nat)
  (hw : @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.atomWidth v values e) U),
  @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.width v values e)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@KoanaKPaths.Machine.Arithmetic.Expr.size v e)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) U
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @KoanaKPaths.Machine.Arithmetic.Expr.width_le

-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_final_cubic_grid_strip
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:30:57.663821+00:00
-- url     : https://prove2.me/submissions/d1a6ad28-320d-44b0-a7c9-194279d51c9a

import Definitions.Def_GrothendieckLB_Supplement_cqReplayRows
import Mathlib.Tactic.Eval
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate
set_option maxRecDepth 300000
set_option maxHeartbeats 180000000
set_option Elab.async false
namespace CubicStripEvidence

private def seg (f : ℕ → Bool) (l n : ℕ) := (List.range n).all fun i => f (l+i)
private theorem join {f : ℕ → Bool} {l n m : ℕ}
    (hn : seg f l n=true) (hm : seg f (l+n) m=true) : seg f l (n+m)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  have hx' := List.mem_range.mp hx
  by_cases h : x < n
  · exact List.all_eq_true.mp hn x (List.mem_range.mpr h)
  · have hh := List.all_eq_true.mp hm (x-n) (List.mem_range.mpr (by omega))
    change f (l+n+(x-n))=true at hh
    rwa [show l+n+(x-n)=l+x by omega] at hh
private theorem full {f : ℕ → Bool} {n : ℕ} (h : seg f 0 n=true) : (List.range n).all f=true := by
  simpa only [seg,Nat.zero_add] using h

private def Rinit : Packed := eval% (checkpoint 15).1
private def R0 : Packed := eval% (checkpoint 15).2
private def R1 : Packed := eval% entry default (makeStrip 240 2) 1
private def R2 : Packed := eval% entry default (makeStrip 240 3) 2
private def R3 : Packed := eval% entry default (makeStrip 240 4) 3
private def R4 : Packed := eval% entry default (makeStrip 240 5) 4
private def R5 : Packed := eval% entry default (makeStrip 240 6) 5
private def R6 : Packed := eval% entry default (makeStrip 240 7) 6
private def R7 : Packed := eval% entry default (makeStrip 240 8) 7
private def R8 : Packed := eval% entry default (makeStrip 240 9) 8
private def R9 : Packed := eval% entry default (makeStrip 240 10) 9
private def R10 : Packed := eval% entry default (makeStrip 240 11) 10
private def R11 : Packed := eval% (checkpoint 16).2
private def xs : Array Packed := #[R0,R1,R2,R3,R4,R5,R6,R7,R8,R9,R10]
private def rc0f : ℕ → Bool := rowTest 240 Rinit R0 R1
private theorem rc0_0_7 : seg rc0f 0 7=true := by decide +kernel
private theorem rc0_7_15 : seg rc0f 7 8=true := by decide +kernel
private theorem rc0_0_15 : seg rc0f 0 15=true := join (l:=0) (n:=7) (m:=8) rc0_0_7 rc0_7_15
private theorem rc0_15_23 : seg rc0f 15 8=true := by decide +kernel
private theorem rc0_23_31 : seg rc0f 23 8=true := by decide +kernel
private theorem rc0_15_31 : seg rc0f 15 16=true := join (l:=15) (n:=8) (m:=8) rc0_15_23 rc0_23_31
private theorem rc0_0_31 : seg rc0f 0 31=true := join (l:=0) (n:=15) (m:=16) rc0_0_15 rc0_15_31
private theorem rc0 : (List.range 31).all rc0f=true := full rc0_0_31
private def wc0f : ℕ → Bool := fun b => decide (weight 241 b=weightAt 240 b (getA R0 0 b))
private theorem wc0_0_5 : seg wc0f 0 5=true := by decide +kernel
private theorem wc0_5_11 : seg wc0f 5 6=true := by decide +kernel
private theorem wc0_0_11 : seg wc0f 0 11=true := join (l:=0) (n:=5) (m:=6) wc0_0_5 wc0_5_11
private theorem wc0 : (List.range 11).all wc0f=true := full wc0_0_11
private def rc1f : ℕ → Bool := rowTest 241 R0 R1 R2
private theorem rc1_0_7 : seg rc1f 0 7=true := by decide +kernel
private theorem rc1_7_14 : seg rc1f 7 7=true := by decide +kernel
private theorem rc1_0_14 : seg rc1f 0 14=true := join (l:=0) (n:=7) (m:=7) rc1_0_7 rc1_7_14
private theorem rc1_14_21 : seg rc1f 14 7=true := by decide +kernel
private theorem rc1_21_28 : seg rc1f 21 7=true := by decide +kernel
private theorem rc1_14_28 : seg rc1f 14 14=true := join (l:=14) (n:=7) (m:=7) rc1_14_21 rc1_21_28
private theorem rc1_0_28 : seg rc1f 0 28=true := join (l:=0) (n:=14) (m:=14) rc1_0_14 rc1_14_28
private theorem rc1 : (List.range 28).all rc1f=true := full rc1_0_28
private def wc1f : ℕ → Bool := fun b => decide (weight 242 b=weightAt 241 b (getA R1 1 b))
private theorem wc1_0_5 : seg wc1f 0 5=true := by decide +kernel
private theorem wc1_5_10 : seg wc1f 5 5=true := by decide +kernel
private theorem wc1_0_10 : seg wc1f 0 10=true := join (l:=0) (n:=5) (m:=5) wc1_0_5 wc1_5_10
private theorem wc1 : (List.range 10).all wc1f=true := full wc1_0_10
private def rc2f : ℕ → Bool := rowTest 242 R1 R2 R3
private theorem rc2_0_12 : seg rc2f 0 12=true := by decide +kernel
private theorem rc2_12_18 : seg rc2f 12 6=true := by decide +kernel
private theorem rc2_18_25 : seg rc2f 18 7=true := by decide +kernel
private theorem rc2_12_25 : seg rc2f 12 13=true := join (l:=12) (n:=6) (m:=7) rc2_12_18 rc2_18_25
private theorem rc2_0_25 : seg rc2f 0 25=true := join (l:=0) (n:=12) (m:=13) rc2_0_12 rc2_12_25
private theorem rc2 : (List.range 25).all rc2f=true := full rc2_0_25
private def wc2f : ℕ → Bool := fun b => decide (weight 243 b=weightAt 242 b (getA R2 0 b))
private theorem wc2_0_4 : seg wc2f 0 4=true := by decide +kernel
private theorem wc2_4_9 : seg wc2f 4 5=true := by decide +kernel
private theorem wc2_0_9 : seg wc2f 0 9=true := join (l:=0) (n:=4) (m:=5) wc2_0_4 wc2_4_9
private theorem wc2 : (List.range 9).all wc2f=true := full wc2_0_9
private def rc3f : ℕ → Bool := rowTest 243 R2 R3 R4
private theorem rc3_0_11 : seg rc3f 0 11=true := by decide +kernel
private theorem rc3_11_22 : seg rc3f 11 11=true := by decide +kernel
private theorem rc3_0_22 : seg rc3f 0 22=true := join (l:=0) (n:=11) (m:=11) rc3_0_11 rc3_11_22
private theorem rc3 : (List.range 22).all rc3f=true := full rc3_0_22
private def wc3f : ℕ → Bool := fun b => decide (weight 244 b=weightAt 243 b (getA R3 1 b))
private theorem wc3_0_8 : seg wc3f 0 8=true := by decide +kernel
private theorem wc3 : (List.range 8).all wc3f=true := full wc3_0_8
private def rc4f : ℕ → Bool := rowTest 244 R3 R4 R5
private theorem rc4_0_9 : seg rc4f 0 9=true := by decide +kernel
private theorem rc4_9_19 : seg rc4f 9 10=true := by decide +kernel
private theorem rc4_0_19 : seg rc4f 0 19=true := join (l:=0) (n:=9) (m:=10) rc4_0_9 rc4_9_19
private theorem rc4 : (List.range 19).all rc4f=true := full rc4_0_19
private def wc4f : ℕ → Bool := fun b => decide (weight 245 b=weightAt 244 b (getA R4 0 b))
private theorem wc4_0_7 : seg wc4f 0 7=true := by decide +kernel
private theorem wc4 : (List.range 7).all wc4f=true := full wc4_0_7
private def rc5f : ℕ → Bool := rowTest 245 R4 R5 R6
private theorem rc5_0_8 : seg rc5f 0 8=true := by decide +kernel
private theorem rc5_8_16 : seg rc5f 8 8=true := by decide +kernel
private theorem rc5_0_16 : seg rc5f 0 16=true := join (l:=0) (n:=8) (m:=8) rc5_0_8 rc5_8_16
private theorem rc5 : (List.range 16).all rc5f=true := full rc5_0_16
private def wc5f : ℕ → Bool := fun b => decide (weight 246 b=weightAt 245 b (getA R5 1 b))
private theorem wc5_0_6 : seg wc5f 0 6=true := by decide +kernel
private theorem wc5 : (List.range 6).all wc5f=true := full wc5_0_6
private def rc6f : ℕ → Bool := rowTest 246 R5 R6 R7
private theorem rc6_0_6 : seg rc6f 0 6=true := by decide +kernel
private theorem rc6_6_13 : seg rc6f 6 7=true := by decide +kernel
private theorem rc6_0_13 : seg rc6f 0 13=true := join (l:=0) (n:=6) (m:=7) rc6_0_6 rc6_6_13
private theorem rc6 : (List.range 13).all rc6f=true := full rc6_0_13
private def wc6f : ℕ → Bool := fun b => decide (weight 247 b=weightAt 246 b (getA R6 0 b))
private theorem wc6_0_5 : seg wc6f 0 5=true := by decide +kernel
private theorem wc6 : (List.range 5).all wc6f=true := full wc6_0_5
private def rc7f : ℕ → Bool := rowTest 247 R6 R7 R8
private theorem rc7_0_10 : seg rc7f 0 10=true := by decide +kernel
private theorem rc7 : (List.range 10).all rc7f=true := full rc7_0_10
private def wc7f : ℕ → Bool := fun b => decide (weight 248 b=weightAt 247 b (getA R7 1 b))
private theorem wc7_0_4 : seg wc7f 0 4=true := by decide +kernel
private theorem wc7 : (List.range 4).all wc7f=true := full wc7_0_4
private def rc8f : ℕ → Bool := rowTest 248 R7 R8 R9
private theorem rc8_0_7 : seg rc8f 0 7=true := by decide +kernel
private theorem rc8 : (List.range 7).all rc8f=true := full rc8_0_7
private def wc8f : ℕ → Bool := fun b => decide (weight 249 b=weightAt 248 b (getA R8 0 b))
private theorem wc8_0_3 : seg wc8f 0 3=true := by decide +kernel
private theorem wc8 : (List.range 3).all wc8f=true := full wc8_0_3
private def rc9f : ℕ → Bool := rowTest 249 R8 R9 R10
private theorem rc9_0_4 : seg rc9f 0 4=true := by decide +kernel
private theorem rc9 : (List.range 4).all rc9f=true := full rc9_0_4
private def wc9f : ℕ → Bool := fun b => decide (weight 250 b=weightAt 249 b (getA R9 1 b))
private theorem wc9_0_2 : seg wc9f 0 2=true := by decide +kernel
private theorem wc9 : (List.range 2).all wc9f=true := full wc9_0_2
private def rc10f : ℕ → Bool := rowTest 250 R9 R10 R11
private theorem rc10_0_1 : seg rc10f 0 1=true := by decide +kernel
private theorem rc10 : (List.range 1).all rc10f=true := full rc10_0_1
private def wc10f : ℕ → Bool := fun b => decide (weight 251 b=weightAt 250 b (getA R10 0 b))
private theorem wc10_0_1 : seg wc10f 0 1=true := by decide +kernel
private theorem wc10 : (List.range 1).all wc10f=true := full wc10_0_1
private def stepOK (c : ℕ) (xs : Array Packed) (k : ℕ) : Bool :=
    let p := 16*c+k
    let cur := inStrip c xs k
    ((List.range (rowLength (p+1))).all (rowTest p (beforeStrip c xs k) cur (inStrip c xs (k+1)))) &&
    (List.range (251-p)).all fun b => decide (weight (p+1) b=weightAt p b (getA cur (p%2) b))
private theorem step0 : stepOK 15 xs 0=true := Bool.and_eq_true_iff.mpr ⟨rc0,wc0⟩
private theorem step1 : stepOK 15 xs 1=true := Bool.and_eq_true_iff.mpr ⟨rc1,wc1⟩
private theorem step2 : stepOK 15 xs 2=true := Bool.and_eq_true_iff.mpr ⟨rc2,wc2⟩
private theorem step3 : stepOK 15 xs 3=true := Bool.and_eq_true_iff.mpr ⟨rc3,wc3⟩
private theorem step4 : stepOK 15 xs 4=true := Bool.and_eq_true_iff.mpr ⟨rc4,wc4⟩
private theorem step5 : stepOK 15 xs 5=true := Bool.and_eq_true_iff.mpr ⟨rc5,wc5⟩
private theorem step6 : stepOK 15 xs 6=true := Bool.and_eq_true_iff.mpr ⟨rc6,wc6⟩
private theorem step7 : stepOK 15 xs 7=true := Bool.and_eq_true_iff.mpr ⟨rc7,wc7⟩
private theorem step8 : stepOK 15 xs 8=true := Bool.and_eq_true_iff.mpr ⟨rc8,wc8⟩
private theorem step9 : stepOK 15 xs 9=true := Bool.and_eq_true_iff.mpr ⟨rc9,wc9⟩
private theorem step10 : stepOK 15 xs 10=true := Bool.and_eq_true_iff.mpr ⟨rc10,wc10⟩
private theorem certified : ∃ xs : Array Packed, stripChecks 15 xs=true := by
  refine ⟨xs,Bool.and_eq_true_iff.mpr ⟨by decide +kernel,?_⟩⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hn : k < 11 := List.mem_range.mp hk
  change stepOK 15 xs k=true
  rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
end CubicStripEvidence
open CubicStripEvidence in
theorem solution : ∃ xs : Array Packed, stripChecks 15 xs=true := certified

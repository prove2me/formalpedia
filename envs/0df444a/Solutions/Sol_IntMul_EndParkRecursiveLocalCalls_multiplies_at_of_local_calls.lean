-- Prove2me | solution 1 for IntMul.EndParkRecursiveLocalCalls.multiplies_at_of_local_calls
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T08:29:08.227976+00:00
-- url     : https://prove2.me/submissions/ee924ef9-7f9a-4a5a-afb1-a9b2d11371be

import Definitions.Def_IntMul_EndParkRecursiveLocalCalls
import Theorems.Thm_IntMul_EndParkRecursiveClockedCalls_native_clocked_calls_correct
import Mathlib.Tactic

namespace IntMul.EndParkRecursiveLocalCalls

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveClockedCalls
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem clocked_of_local_calls (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K) (childWidth : ℕ)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps calls work : ℕ)
    (certificate : HasLocalCalls M labels request resume childWidth extent c v w steps calls work)
    (τ : ℝ) (multiplies : MultipliesAt (machine M labels request resume) childWidth τ) :
    ∃ clocks : ℕ, (clocks : ℝ) ≤ (calls : ℝ)*τ ∧
      HasClockedCalls M labels request resume extent c v w steps clocks work := by
  induction certificate with
  | halt extent c v w halt out =>
    exact ⟨0,by simp,HasClockedCalls.halt extent c v w halt out⟩
  | step extent c v w steps calls work live ordinary rest ih =>
    obtain ⟨clocks,hclocks,hcert⟩ := ih
    exact ⟨clocks,hclocks,HasClockedCalls.step extent c v w steps clocks work live ordinary hcert⟩
  | call extent c v x y childWord w label childBudget parentSteps parentCalls parentWork live request_label packet hx hy child parent ih =>
    obtain ⟨H,hH,hhalt⟩ := multiplies x y hx hy
    obtain ⟨clocks,hclocks,hcert⟩ := ih
    refine ⟨H+clocks,?_,HasClockedCalls.call extent c v x y childWord w label childBudget H
      parentSteps clocks parentWork live request_label packet child hhalt.1 hcert⟩
    push_cast
    nlinarith

private theorem child_bound_nonnegative (M : MultitapeTM) (m : ℕ) (τ : ℝ)
    (multiplies : MultipliesAt M m τ) : 0 ≤ τ := by
  obtain ⟨H,hH,_⟩ := multiplies (List.replicate m false) (List.replicate m false) (by simp) (by simp)
  exact le_trans (Nat.cast_nonneg H) hH

/-- Uniform child multiplication bounds produce a real recurrence for the
same finite scheduler with coefficient exactly equal to the caller's call count. -/
private theorem multiplies_at_of_local_calls (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (n childWidth : ℕ) (A B τ : ℝ)
    (multiplies : MultipliesAt (machine M labels request resume) childWidth τ)
    (body : ∀ x y : List Bool, x.length=n → y.length=n →
      ∃ steps calls work,
        HasLocalCalls M labels request resume childWidth (initialExtent M x y) (M.initCfg x y)
          [] (bin (2*n) (val x*val y)) steps calls work ∧
        (calls : ℝ) ≤ A ∧
        (nativeOverhead M x y (bin (2*n) (val x*val y)) steps work : ℝ) ≤ B) :
    MultipliesAt (machine M labels request resume) n (A*τ+B) := by
  intro x y hx hy
  obtain ⟨steps,calls,work,hcert,hcalls,hoverhead⟩ := body x y hx hy
  obtain ⟨clocks,hclocks,hclocked⟩ := clocked_of_local_calls M labels request resume childWidth
    (initialExtent M x y) (M.initCfg x y) [] (bin (2*n) (val x*val y))
    steps calls work hcert τ multiplies
  obtain ⟨t,ht,hrun,hout⟩ := native_clocked_calls_correct M labels request resume x y
    (bin (2*n) (val x*val y)) steps clocks work hclocked
  have ht' : t ≤ clocks+nativeOverhead M x y (bin (2*n) (val x*val y)) steps work := by
    unfold nativeOverhead
    omega
  have hreal : (t : ℝ) ≤ (clocks : ℝ)+(nativeOverhead M x y (bin (2*n) (val x*val y)) steps work : ℝ) := by
    exact_mod_cast ht'
  have hτ := child_bound_nonnegative (machine M labels request resume) childWidth τ multiplies
  have hcallbound := mul_le_mul_of_nonneg_right hcalls hτ
  exact ⟨t,by linarith,hout⟩

end IntMul.EndParkRecursiveLocalCalls


open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveLocalCalls IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (n childWidth : ℕ) (A B τ : ℝ)
    (multiplies : MultipliesAt (machine M labels request resume) childWidth τ)
    (body : ∀ x y : List Bool, x.length=n → y.length=n →
      ∃ steps calls work,
        HasLocalCalls M labels request resume childWidth (initialExtent M x y) (M.initCfg x y)
          [] (bin (2*n) (val x*val y)) steps calls work ∧
        (calls : ℝ) ≤ A ∧
        (nativeOverhead M x y (bin (2*n) (val x*val y)) steps work : ℝ) ≤ B) :
    MultipliesAt (machine M labels request resume) n (A*τ+B) :=
  IntMul.EndParkRecursiveLocalCalls.multiplies_at_of_local_calls M labels request resume n childWidth A B τ multiplies body

#print axioms solution

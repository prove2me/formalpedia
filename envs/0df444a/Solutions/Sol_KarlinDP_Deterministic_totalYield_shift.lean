-- Prove2me | solution 1 for KarlinDP.Deterministic.totalYield_shift
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:21:22.881578+00:00
-- url     : https://prove2.me/submissions/a308a024-4c96-4583-b3de-08b08b169901

import Definitions.Def_KarlinDP_Deterministic_Model
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic
set_option autoImplicit false
open KarlinDP.Deterministic

private theorem trajectory_shift {Ω D : Type*} (T : D → Ω → Ω) (ω : Ω) (s : ℕ → D) (n : ℕ) :
    trajectory T ω s (n+1)=trajectory T (T (s 0) ω) (fun k => s (k+1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T (s (n+1)) (trajectory T ω s (n+1)) = T (s (n+1)) (trajectory T (T (s 0) ω) (fun k => s (k+1)) n)
    rw [ih]

private theorem weight_shift {D : Type*} (P : D → ℝ) (s : ℕ → D) (n : ℕ) :
    weight P s (n+1)=P (s 0)*weight P (fun k => s (k+1)) n := by
  simpa only [weight,mul_comm] using Finset.prod_range_succ' (fun i => P (s i)) n

private theorem yield_shift {Ω D : Type*} (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (ω : Ω) (s : ℕ → D)
    (hsum : Summable (fun n => L (trajectory T ω s n) (s n)*weight P s n)) :
    totalYield L T P ω s=L ω (s 0)+P (s 0)*totalYield L T P (T (s 0) ω) (fun k => s (k+1)) := by
  unfold totalYield
  rw [hsum.tsum_eq_zero_add]
  simp only [show trajectory T ω s 0=ω from rfl,show weight P s 0=1 by simp [weight],mul_one]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [trajectory_shift]
  rw [weight_shift]
  ring

theorem solution {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (ω : Ω) (s : ℕ → D)
    (hsum : Summable (fun n => L (trajectory T ω s n) (s n) * weight P s n)) :
    totalYield L T P ω s
      = L ω (s 0) + P (s 0) * totalYield L T P (T (s 0) ω) (fun k => s (k + 1)) := by
  exact yield_shift L T P ω s hsum

-- Prove2me | solution 1 for KarlinDP.Deterministic.solution_nstep_expansion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:22:55.060346+00:00
-- url     : https://prove2.me/submissions/32f039eb-fe10-41f5-a6fc-ca3a58a785e8

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

private theorem partial_shift {Ω D : Type*} (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (ω : Ω) (s : ℕ → D) (n : ℕ) :
    partialYield L T P ω s (n+1)=L ω (s 0)+P (s 0)*partialYield L T P (T (s 0) ω) (fun k => s (k+1)) n := by
  unfold partialYield
  rw [Finset.sum_range_succ']
  have hs : (∑ k ∈ Finset.range n, L (trajectory T ω s (k+1)) (s (k+1))*weight P s (k+1)) =
      P (s 0)*∑ k ∈ Finset.range n, L (trajectory T (T (s 0) ω) (fun j => s (j+1)) k) (s (k+1))*weight P (fun j => s (j+1)) k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [trajectory_shift,weight_shift]
    ring
  rw [hs]
  simp only [trajectory,weight,Finset.range_zero,Finset.prod_empty,mul_one]
  ring

private theorem finite_shift {Ω D : Type*} (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (M : Ω → ℝ) (ω : Ω) (s : ℕ → D) (n : ℕ) :
    partialYield L T P ω s (n+1)+M (trajectory T ω s (n+1))*weight P s (n+1) =
      L ω (s 0)+P (s 0)*(partialYield L T P (T (s 0) ω) (fun k => s (k+1)) n+
        M (trajectory T (T (s 0) ω) (fun k => s (k+1)) n)*weight P (fun k => s (k+1)) n) := by
  rw [partial_shift,trajectory_shift,weight_shift]
  ring

theorem solution {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (M : Ω → ℝ)
    (hM : ∀ ω, IsGreatest (Set.range fun δ => L ω δ + P δ * M (T δ ω)) (M ω)) :
    ∀ n ω, IsGreatest
      (Set.range fun s : ℕ → D => partialYield L T P ω s n + M (trajectory T ω s n) * weight P s n)
      (M ω) := by
  classical
  intro n
  induction n with
  | zero =>
    intro ω
    constructor
    · exact ⟨fun _ => Classical.arbitrary D,by simp [partialYield,trajectory,weight]⟩
    · rintro _ ⟨s,rfl⟩
      simp [partialYield,trajectory,weight]
  | succ n ih =>
    intro ω
    constructor
    · obtain ⟨δ,hδ⟩ := (hM ω).1
      obtain ⟨s,hs⟩ := (ih (T δ ω)).1
      refine ⟨(fun k => Nat.casesOn k δ s),?_⟩
      dsimp only at *
      rw [finite_shift]
      change L ω δ+P δ*(partialYield L T P (T δ ω) s n+M (trajectory T (T δ ω) s n)*weight P s n)=M ω
      rw [hs,hδ]
    · rintro _ ⟨s,rfl⟩
      dsimp only at *
      rw [finite_shift]
      have htail := (ih (T (s 0) ω)).2 ⟨(fun k => s (k+1)),rfl⟩
      have hhead := (hM ω).2 ⟨s 0,rfl⟩
      have hp := hP0 (s 0)
      nlinarith

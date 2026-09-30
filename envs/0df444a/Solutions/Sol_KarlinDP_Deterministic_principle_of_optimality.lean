-- Prove2me | solution 1 for KarlinDP.Deterministic.principle_of_optimality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:23:34.541752+00:00
-- url     : https://prove2.me/submissions/69ab93e2-f113-469f-8f4a-662c42556875

import Definitions.Def_KarlinDP_Deterministic_Model
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
set_option autoImplicit false
open KarlinDP.Deterministic

private theorem trajectory_cont {Ω D : Type*} [TopologicalSpace Ω] [TopologicalSpace D]
    (T : D → Ω → Ω) (hT : Continuous (fun p : D × Ω => T p.1 p.2)) (ω : Ω) (n : ℕ) :
    Continuous (fun s : ℕ → D => trajectory T ω s n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact hT.comp ((continuous_apply n).prodMk ih)

private theorem partial_cont {Ω D : Type*} [TopologicalSpace Ω] [TopologicalSpace D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2)) (hP : Continuous P) (ω : Ω) (n : ℕ) :
    Continuous (fun s : ℕ → D => partialYield L T P ω s n) := by
  apply continuous_finsetSum
  intro j hj
  apply Continuous.mul
  · exact hL.comp ((trajectory_cont T hT ω j).prodMk (continuous_apply j))
  · exact continuous_finsetProd _ (fun i _ => hP.comp (continuous_apply i))

private theorem exists_optimal {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (ω : Ω)
    (hunif : TendstoUniformly (fun k s => partialYield L T P ω s k) (totalYield L T P ω) Filter.atTop) :
    ∃ s₀ : ℕ → D, IsGreatest (Set.range (totalYield L T P ω)) (totalYield L T P ω s₀) := by
  have hc : Continuous (totalYield L T P ω) :=
    hunif.continuous (Filter.Frequently.of_forall (fun n => partial_cont L T P hL hT hP ω n))
  obtain ⟨s,hs,hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  refine ⟨s,⟨s,rfl⟩,?_⟩
  rintro y ⟨t,rfl⟩
  exact hmax (Set.mem_univ t)
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
    (hunif : ∀ ω, TendstoUniformly (fun k s => partialYield L T P ω s k) (totalYield L T P ω)
      Filter.atTop) :
    ∀ ω, IsGreatest (Set.range fun δ => L ω δ + P δ * optimalReturn L T P (T δ ω))
      (optimalReturn L T P ω) := by
  classical
  have hsum (ω : Ω) (s : ℕ → D) : Summable (fun n => L (trajectory T ω s n) (s n)*weight P s n) := by
    have hnonneg (n : ℕ) : 0 ≤ L (trajectory T ω s n) (s n)*weight P s n := by
      apply mul_nonneg (hL0 _ _)
      exact Finset.prod_nonneg (fun i _ => (hP0 (s i)).le)
    exact ((hasSum_iff_tendsto_nat_of_nonneg hnonneg (totalYield L T P ω s)).mpr ((hunif ω).tendsto_at s)).summable
  have hopt (ω : Ω) : IsGreatest (Set.range (totalYield L T P ω)) (optimalReturn L T P ω) := by
    obtain ⟨s,hs⟩ := exists_optimal L T P hL0 hL hT hP0 hP ω (hunif ω)
    have he : optimalReturn L T P ω=totalYield L T P ω s := hs.csSup_eq
    rw [he]
    exact hs
  intro ω
  have hupper (δ : D) : L ω δ+P δ*optimalReturn L T P (T δ ω) ≤ optimalReturn L T P ω := by
    obtain ⟨s,hs⟩ := (hopt (T δ ω)).1
    let v : ℕ → D := fun k => Nat.casesOn k δ s
    have hv := (hopt ω).2 ⟨v,rfl⟩
    rw [yield_shift L T P ω v (hsum ω v)] at hv
    change L ω δ+P δ*totalYield L T P (T δ ω) s ≤ optimalReturn L T P ω at hv
    rw [hs] at hv
    exact hv
  constructor
  · obtain ⟨s,hs⟩ := (hopt ω).1
    refine ⟨s 0,?_⟩
    have ht := (hopt (T (s 0) ω)).2 ⟨(fun k => s (k+1)),rfl⟩
    have hshift := yield_shift L T P ω s (hsum ω s)
    have hp := hP0 (s 0)
    have hu := hupper (s 0)
    dsimp only at *
    rw [hs] at hshift
    nlinarith
  · rintro _ ⟨δ,rfl⟩
    exact hupper δ

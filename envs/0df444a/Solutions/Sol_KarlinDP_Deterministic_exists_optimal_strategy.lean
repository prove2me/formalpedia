-- Prove2me | solution 1 for KarlinDP.Deterministic.exists_optimal_strategy
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:18:54.422982+00:00
-- url     : https://prove2.me/submissions/08d0e17c-e103-4189-86b3-3dcfbba18b28

import Definitions.Def_KarlinDP_Deterministic_Model
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
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

theorem solution {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
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

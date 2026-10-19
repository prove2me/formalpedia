-- Prove2me | solution 1 for MazurTransfer.DiscreteOrbitContinuityFromOpenStabilizer.continuous_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:19:21.287547+00:00
-- url     : https://prove2.me/submissions/68918ad9-85d6-402f-9932-432e4e1df376

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an orbit map into a discrete set is continuous if the
point stabilizer is open. Named downstream consumer: finite norm-fibre
orbits and actual continuous Kummer cocycles.
-/
import Mathlib

theorem solution {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MulAction G X] [TopologicalSpace X] [DiscreteTopology X] (x : X) (hx : IsOpen (MulAction.stabilizer G x : Set G)) :
    Continuous (fun g : G => g • x) := by
  rw [continuous_discrete_rng]
  intro y
  change IsOpen {g : G | g • x = y}
  by_cases hy : ∃ g : G, g • x = y
  · obtain ⟨g, hg⟩ := hy
    have hset : {h : G | h • x = y} =
        (fun h : G => g⁻¹ * h) ⁻¹' (MulAction.stabilizer G x : Set G) := by
      ext h
      change (h • x = y) ↔ (g⁻¹ * h) • x = x
      rw [mul_smul, inv_smul_eq_iff]
      rw [hg]
    rw [hset]
    exact hx.preimage (continuous_const.mul continuous_id)
  · have hempty : {g : G | g • x = y} = ∅ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hg => hy ⟨g, hg⟩
    rw [hempty]
    exact isOpen_empty

#print axioms solution

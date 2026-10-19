-- Prove2me | solution 1 for MazurTransfer.northcott_fiber_infimum_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T20:42:31.771266+00:00
-- url     : https://prove2.me/submissions/4e452d78-6f23-4444-a6ac-fcc9a3d58c50

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: quotient Northcott height by fiber infima. Named downstream
consumer: actual order-13 arithmetic Picard height. -/
import Mathlib
noncomputable section

theorem solution {X Y : Type*} (f : Y → X) (hf : Function.Surjective f)
    (h : Y → ℝ) (h0 : ∀ y, 0 ≤ h y) [Northcott h] :
    Northcott (fun x => sInf (h '' (f ⁻¹' {x}))) := by
  constructor
  intro B
  refine ((Northcott.finite_le (h := h) (B + 1)).image f).subset ?_
  intro x hx
  obtain ⟨y, hy⟩ := hf x
  have hne : (h '' (f ⁻¹' {x})).Nonempty := ⟨h y, y, hy, rfl⟩
  have hbb : BddBelow (h '' (f ⁻¹' {x})) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    exact h0 z
  have hlt : sInf (h '' (f ⁻¹' {x})) < B + 1 := lt_of_le_of_lt hx (lt_add_one B)
  obtain ⟨r, ⟨z, hz, rfl⟩, hr⟩ := (csInf_lt_iff hbb hne).mp hlt
  exact ⟨z, hr.le, hz⟩

#print axioms solution

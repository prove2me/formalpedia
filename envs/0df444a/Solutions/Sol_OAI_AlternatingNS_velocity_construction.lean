-- Prove2me | solution 1 for OAI.AlternatingNS.velocity_construction
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T03:50:53.743553+00:00
-- url     : https://prove2.me/submissions/eb8141b4-923f-44df-9297-510f16e25d99

/-
Proof of the platform statement `OAI.AlternatingNS.velocity_construction`.

The construction and all supporting results are imported from the platform definitions
`OAI_AlternatingFlow_Part01` ... `OAI_AlternatingFlow_Part11`, which are a port of OpenAI's formalization
(https://github.com/openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/MathematicalPhysics/AlternatingFlow/, Copyright OpenAI, Apache License 2.0). The final derivation
below follows the assembly in that repository's Main.lean, restricted to the velocity field.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part11

set_option autoImplicit false

-- ===== The platform statement OAI.AlternatingNS.velocity_construction =====
open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory OAI OAI.AlternatingNS

theorem solution :
    ∃ (U : Machine × List ℕ → Velocity) (compileVelocity : Machine × List ℕ → FieldProgram)
      (K : Set Space),
      Computable compileVelocity ∧ IsCompact K ∧
      ∀ (M : Machine) (w : List ℕ), M.WellFormed → M.ValidInput w →
        ProgramFor (compileVelocity (M, w)) (U (M, w)) ∧
        Smooth (U (M, w)) ∧ SupportedIn (U (M, w)) K ∧ Rapid (U (M, w)) ∧
        (∀ x, U (M, w) 0 x = 0) ∧
        (∀ t, 0 ≤ t → ∀ x, div (U (M, w)) t x = 0) ∧
        ∀ γ : ℝ → Space, IsTrajectory (U (M, w)) observedParticle γ →
          ((∃ t : ℝ, 0 ≤ t ∧ 0 < γ t 0) ↔ M.Halts w) := by
  obtain ⟨cu, hcu, hu⟩ := Effective.Certified.programs
    Effective.velocity_certified Effective.velocity_named
  refine ⟨fun z => Construction.velocity z.1 z.2, cu, Spatial.box, hcu, Spatial.box_compact, ?_⟩
  intro M w hM hw
  obtain ⟨_, hUs, _, hUk, hNS, X, hX, hXu, hhalt⟩ :=
    Construction.smooth_forced_simulation 1 M hM w hw
  refine ⟨hu (M, w), hUs, hUk, Bounds.velocity_rapid M w, hNS.2.1,
    fun t ht x => (hNS.2.2 t ht x).1, ?_⟩
  intro γ hγ
  have heq : ∀ t, 0 ≤ t → γ t = X observedParticle t := hXu _ _ hγ
  rw [← hhalt]
  constructor
  · rintro ⟨t, ht, hpos⟩; exact ⟨t, ht, by rw [← heq t ht]; exact hpos⟩
  · rintro ⟨t, ht, hpos⟩; exact ⟨t, ht, by rw [heq t ht]; exact hpos⟩

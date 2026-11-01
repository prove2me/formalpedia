-- Prove2me | solution 1 for Grunbaum2003.rayMachine_halt_unique_and_output_iso_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:17:23.896556+00:00
-- url     : https://prove2.me/submissions/a28c804e-c173-40a7-82ce-7b601f28a806

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem rayMachineStep_of_halt {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (c : RayConfiguration)
    (h : program[c.pc]? = some .halt) :
    rayMachineStep program oracle c = some c := by
  unfold rayMachineStep
  simp [h]

theorem rayMachineRun_of_halt {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (k : ℕ) (c : RayConfiguration)
    (h : program[c.pc]? = some .halt) :
    rayMachineRun program oracle k c = some c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [rayMachineRun, rayMachineStep_of_halt program oracle c h, ih]

theorem rayMachineRun_add {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t₁ t₂ : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (t₁ + t₂) c =
      (rayMachineRun program oracle t₁ c).bind (rayMachineRun program oracle t₂) := by
  induction t₁ generalizing c with
  | zero => simp [rayMachineRun]
  | succ t₁ ih =>
    rw [Nat.succ_add]
    change (rayMachineStep program oracle c).bind (rayMachineRun program oracle (t₁ + t₂)) =
      ((rayMachineStep program oracle c).bind (rayMachineRun program oracle t₁)).bind
        (rayMachineRun program oracle t₂)
    cases hstep : rayMachineStep program oracle c with
    | none => rfl
    | some c' => exact ih c'

/-- Grünbaum (2003), §3.6 (pp. 52b–52c): a ray machine has at most one halting
configuration from any initial state, and its face-lattice output predicate
`IsRayFaceLatticeOutput` is invariant under order isomorphism of face lattices
and uniquely determines the face lattice up to order isomorphism. -/
theorem rayMachine_halt_unique_and_output_iso_iff :
    (∀ {d : ℕ} (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ))
      (t₁ t₂ : ℕ) (c₀ c₁ c₂ : RayConfiguration),
      rayMachineRun program oracle t₁ c₀ = some c₁ →
      program[c₁.pc]? = some .halt →
      rayMachineRun program oracle t₂ c₀ = some c₂ →
      program[c₂.pc]? = some .halt →
      c₁ = c₂) ∧
    (∀ {d₁ d₂ : ℕ} (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
      (c : RayConfiguration),
      IsRayFaceLatticeOutput P c →
      (IsRayFaceLatticeOutput Q c ↔ Nonempty (PolytopeFace P ≃o PolytopeFace Q))) := by
  refine ⟨?_, ?_⟩
  · intro d program oracle t₁ t₂ c₀ c₁ c₂ hrun1 hhalt1 hrun2 hhalt2
    have h1 : rayMachineRun program oracle (t₁ + t₂) c₀ = some c₁ := by
      rw [rayMachineRun_add, hrun1]
      exact rayMachineRun_of_halt program oracle t₂ c₁ hhalt1
    have h2 : rayMachineRun program oracle (t₂ + t₁) c₀ = some c₂ := by
      rw [rayMachineRun_add, hrun2]
      exact rayMachineRun_of_halt program oracle t₁ c₂ hhalt2
    rw [Nat.add_comm] at h1
    exact Option.some.inj (h1.symm.trans h2)
  · intro d₁ d₂ P Q c ⟨n, h1, h0, eP, hbitP⟩
    constructor
    · rintro ⟨m, h1', h0', eQ, hbitQ⟩
      have hmn : m = n := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hones := h1 ⟨m, hlt⟩
          simp only at hones
          linarith [h0']
        · have hones := h1' ⟨n, hgt⟩
          simp only at hones
          linarith [h0]
      subst hmn
      refine ⟨{
        toEquiv := eP.symm.trans eQ
        map_rel_iff' := by
          intro F₁ F₂
          simp only [Equiv.trans_apply]
          rw [← (hbitQ (eP.symm F₁) (eP.symm F₂)).2,
            (hbitP (eP.symm F₁) (eP.symm F₂)).2,
            eP.apply_symm_apply, eP.apply_symm_apply]
      }⟩
    · rintro ⟨Φ⟩
      refine ⟨n, h1, h0, eP.trans Φ.toEquiv, ?_⟩
      intro i j
      refine ⟨(hbitP i j).1, ?_⟩
      rw [(hbitP i j).2]
      exact (Φ.map_rel_iff).symm

end Grunbaum2003

theorem solution :
    (∀ {d : ℕ} (program : List Grunbaum2003.RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ))
      (t₁ t₂ : ℕ) (c₀ c₁ c₂ : Grunbaum2003.RayConfiguration),
      Grunbaum2003.rayMachineRun program oracle t₁ c₀ = some c₁ →
      program[c₁.pc]? = some .halt →
      Grunbaum2003.rayMachineRun program oracle t₂ c₀ = some c₂ →
      program[c₂.pc]? = some .halt →
      c₁ = c₂) ∧
    (∀ {d₁ d₂ : ℕ} (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
      (c : Grunbaum2003.RayConfiguration),
      Grunbaum2003.IsRayFaceLatticeOutput P c →
      (Grunbaum2003.IsRayFaceLatticeOutput Q c ↔
        Nonempty (Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q))) :=
  Grunbaum2003.rayMachine_halt_unique_and_output_iso_iff

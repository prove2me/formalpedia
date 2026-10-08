-- Prove2me | solution 1 for Gomory69.Lifting.pushForward_path
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:20:15.070917+00:00
-- url     : https://prove2.me/submissions/1a297082-4547-4f96-90a1-aa2ef7dc10d4

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift



namespace Gomory69.Lifting

section A
variable {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem sumPush {M : Type*} [AddCommMonoid M] (ψ : G →+ H) (u : H → M) (hu : u 0 = 0)
    (w : Plus G → ℕ) :
    ∑ g : Plus G, w g • u (ψ (g : G)) = ∑ h : Plus H, pushForward ψ w h • u (h : H) := by
  have h1 : ∀ h : Plus H, pushForward ψ w h • u (h : H) =
      ∑ g : Plus G, if ψ (g : G) = (h : H) then w g • u (ψ (g : G)) else 0 := by
    intro h
    unfold pushForward
    rw [Finset.sum_smul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : ψ (g : G) = (h : H)
    · simp [hg]
    · simp [hg]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : ψ (g : G) = 0
  · simp [hg, hu]
  · rw [Finset.sum_eq_single ⟨ψ (g : G), hg⟩]
    · simp
    · intro b _ hb
      have : ψ (g : G) ≠ (b : H) := fun h => hb (Subtype.ext h.symm)
      simp [this]
    · simp

theorem pushForward_mem (ψ : G →+ H) (g₀ : G) (hg₀ : ψ g₀ ≠ 0) (t : Plus G → ℕ)
    (ht : t ∈ T G g₀) : pushForward ψ t ∈ T H (ψ g₀) := by
  obtain ⟨h1, h2⟩ := ht
  constructor
  · have := sumPush ψ (fun h : H => h) rfl t
    rw [← this, ← h1]
    simp [map_sum, map_nsmul]
  · intro h0
    apply hg₀
    have : ∑ h : Plus H, pushForward ψ t h • (h : H) = 0 := by simp [h0]
    rw [← this, ← sumPush ψ (fun h : H => h) rfl t, ← h1]
    simp [map_sum, map_nsmul]

theorem lift_dot (ψ : G →+ H) (π' : Plus H → ℝ) (t : Plus G → ℕ) :
    liftCoeff ψ π' ⬝ᵥ castVec t = π' ⬝ᵥ castVec (pushForward ψ t) := by
  have := sumPush ψ (ext π') (by simp [ext]) t
  simp only [dotProduct, liftCoeff, castVec]
  have e1 : ∀ g : Plus G, ext π' (ψ (g:G)) * (t g : ℝ) = t g • ext π' (ψ (g:G)) := by
    intro g; rw [nsmul_eq_mul, mul_comm]
  have e2 : ∀ h : Plus H, π' h * (pushForward ψ t h : ℝ) = pushForward ψ t h • ext π' (h:H) := by
    intro h; rw [nsmul_eq_mul, mul_comm]; simp [ext, h.2]
  simp_rw [e1, e2]
  exact this

theorem pushForward_path_core (ψ : G →+ H) (g₀ : G) (hg₀ : ψ g₀ ≠ 0) (π' : Plus H → ℝ) (π₀ : ℝ) :
    (∀ t ∈ T G g₀, pushForward ψ t ∈ T H (ψ g₀) ∧
        liftCoeff ψ π' ⬝ᵥ castVec t = π' ⬝ᵥ castVec (pushForward ψ t)) ∧
      ((∀ τ ∈ T H (ψ g₀), π₀ ≤ π' ⬝ᵥ castVec τ) →
        ∀ t ∈ T G g₀, π₀ ≤ liftCoeff ψ π' ⬝ᵥ castVec t) := by
  refine ⟨fun t ht => ⟨pushForward_mem ψ g₀ hg₀ t ht, lift_dot ψ π' t⟩, fun h t ht => ?_⟩
  rw [lift_dot]
  exact h _ (pushForward_mem ψ g₀ hg₀ t ht)

end A
end Gomory69.Lifting

open Gomory69.Lifting


theorem solution {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (g₀ : G) (hg₀ : ψ g₀ ≠ 0) (π' : Plus H → ℝ) (π₀ : ℝ) :
    (∀ t ∈ T G g₀, pushForward ψ t ∈ T H (ψ g₀) ∧
        liftCoeff ψ π' ⬝ᵥ castVec t = π' ⬝ᵥ castVec (pushForward ψ t)) ∧
      ((∀ τ ∈ T H (ψ g₀), π₀ ≤ π' ⬝ᵥ castVec τ) →
        ∀ t ∈ T G g₀, π₀ ≤ liftCoeff ψ π' ⬝ᵥ castVec t) := by
  exact pushForward_path_core ψ g₀ hg₀ π' π₀

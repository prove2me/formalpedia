-- Prove2me | solution 1 for Gomory69.Lifting.liftedPath_minimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:21:26.884184+00:00
-- url     : https://prove2.me/submissions/a4772ba4-65f3-4e46-aea8-08641492257a

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



theorem base_push (ψ : G →+ H) (φ : H → G) (hφ : ∀ h, ψ (φ h) = h) (k : G) (hk : ψ k = 0)
    (τ : Plus H → ℕ) : pushForward ψ (liftedPathBase ψ φ k τ) = τ := by
  funext h
  have hne : ψ (φ h + k) = (h : H) := by rw [map_add, hφ, hk, add_zero]
  have hne0 : φ (h:H) + k ≠ 0 := fun h0 => h.2 (by rw [← hne, h0, map_zero])
  unfold pushForward
  rw [Finset.sum_eq_single (⟨φ h + k, hne0⟩ : Plus G)]
  · have hh : ψ (φ (h:H) + k) ≠ 0 := by rw [hne]; exact h.2
    simp only [liftedPathBase]
    rw [dif_neg hh, if_pos (by simp [hne])]
    congr 1
    exact Subtype.ext hne
  · intro g hg hgne
    have hg' : ψ (g:G) = (h:H) := (Finset.mem_filter.mp hg).2
    have hh : ψ (g:G) ≠ 0 := by rw [hg']; exact h.2
    simp only [liftedPathBase]
    rw [dif_neg hh, if_neg]
    intro hc
    apply hgne
    apply Subtype.ext
    rw [hc, hg']
  · intro h'
    exfalso; apply h'
    simp [hne]

theorem liftedPath_minimal_core (ψ : G →+ H) (φ : H → G) (hφ : ∀ h, ψ (φ h) = h) (g₀ : G)
    (π' : Plus H → ℝ) (π₀ : ℝ) (τ : Plus H → ℕ) (hτ : τ ∈ T H (ψ g₀))
    (hτπ : π' ⬝ᵥ castVec τ = π₀) (k : G) (hk : ψ k = 0) :
    ψ (closingElement ψ φ g₀ k τ) = 0 ∧
      liftedPath ψ φ g₀ k τ ∈ T G g₀ ∧
        liftCoeff ψ π' ⬝ᵥ castVec (liftedPath ψ φ g₀ k τ) = π₀ := by
  have hB : ψ (∑ g : Plus G, liftedPathBase ψ φ k τ g • (g : G)) = ψ g₀ := by
    have := sumPush ψ (fun h : H => h) rfl (liftedPathBase ψ φ k τ)
    rw [base_push ψ φ hφ k hk τ] at this
    rw [map_sum]
    simpa [map_nsmul, hτ.1] using this.trans hτ.1
  have hc : ψ (closingElement ψ φ g₀ k τ) = 0 := by
    unfold closingElement
    rw [map_sub, hB, sub_self]
  have hsum : ∑ g : Plus G, (if (g : G) = closingElement ψ φ g₀ k τ then 1 else 0 : ℕ) • (g : G)
      = closingElement ψ φ g₀ k τ := by
    by_cases h0 : closingElement ψ φ g₀ k τ = 0
    · simp only [h0]
      exact Finset.sum_eq_zero (fun x _ => by simp [x.2])
    · rw [Finset.sum_eq_single (⟨_, h0⟩ : Plus G)]
      · simp
      · intro g _ hg
        have : (g : G) ≠ closingElement ψ φ g₀ k τ := fun h => hg (Subtype.ext h)
        simp [this]
      · simp
  have hpush : pushForward ψ (liftedPath ψ φ g₀ k τ) = τ := by
    funext h
    have : pushForward ψ (liftedPath ψ φ g₀ k τ) h =
        pushForward ψ (liftedPathBase ψ φ k τ) h := by
      unfold pushForward
      apply Finset.sum_congr rfl
      intro g hg
      have hg' : ψ (g:G) = (h:H) := (Finset.mem_filter.mp hg).2
      have : (g : G) ≠ closingElement ψ φ g₀ k τ := by
        intro e
        apply h.2
        rw [← hg', e, hc]
      simp [liftedPath, this]
    rw [this, base_push ψ φ hφ k hk τ]
  refine ⟨hc, ⟨?_, ?_⟩, ?_⟩
  · simp only [liftedPath, add_smul, Finset.sum_add_distrib, hsum]
    unfold closingElement; abel
  · intro h0
    obtain ⟨h, hh⟩ : ∃ h, τ h ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hτ.2 (funext hcon)
    have h1 : liftedPath ψ φ g₀ k τ = 0 := h0
    have := congrFun hpush h
    rw [h1] at this
    simp [pushForward] at this
    exact hh this.symm
  · rw [lift_dot, hpush, hτπ]

end A
end Gomory69.Lifting

open Gomory69.Lifting


theorem solution {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (φ : H → G) (hφ : ∀ h, ψ (φ h) = h) (g₀ : G)
    (π' : Plus H → ℝ) (π₀ : ℝ) (τ : Plus H → ℕ) (hτ : τ ∈ T H (ψ g₀))
    (hτπ : π' ⬝ᵥ castVec τ = π₀) (k : G) (hk : ψ k = 0) :
    ψ (closingElement ψ φ g₀ k τ) = 0 ∧
      liftedPath ψ φ g₀ k τ ∈ T G g₀ ∧
        liftCoeff ψ π' ⬝ᵥ castVec (liftedPath ψ φ g₀ k τ) = π₀ := by
  exact liftedPath_minimal_core ψ φ hφ g₀ π' π₀ τ hτ hτπ k hk

-- Prove2me | solution 1 for NumStochOpt.Stepsize.eq_18_18_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:59:20.069535+00:00
-- url     : https://prove2.me/submissions/2cf63299-7d67-4256-9c7a-58c941a386ec

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace

section ProjLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_le_of_min {S : Set E} (hcv : Convex ℝ S) {z p : E} (hp : p ∈ S)
    (hmin : ∀ w ∈ S, ‖z - p‖ ≤ ‖z - w‖) : ∀ w ∈ S, inner ℝ (z - p) (w - p) ≤ 0 := by
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have : ‖z - p‖ = ⨅ w : S, ‖z - (w : E)‖ := by
    have : Nonempty S := ⟨⟨p, hp⟩⟩
    apply le_antisymm
    · exact le_ciInf (fun w => hmin w w.2)
    · exact ciInf_le hb ⟨p, hp⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hcv hp).1 this

lemma min_of_inner_le {S : Set E} (hcv : Convex ℝ S) {z p : E} (hp : p ∈ S)
    (h : ∀ w ∈ S, inner ℝ (z - p) (w - p) ≤ 0) : ∀ w ∈ S, ‖z - p‖ ≤ ‖z - w‖ := by
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have := (norm_eq_iInf_iff_real_inner_le_zero hcv hp).2 h
  intro w hw
  rw [this]
  exact ciInf_le hb ⟨w, hw⟩

lemma proj_nonexp {S : Set E} (hcv : Convex ℝ S) {z z' y y' : E} (hy : y ∈ S) (hy' : y' ∈ S)
    (h1 : ∀ w ∈ S, ‖z - y‖ ≤ ‖z - w‖) (h2 : ∀ w ∈ S, ‖z' - y'‖ ≤ ‖z' - w‖) :
    ‖y - y'‖ ≤ ‖z - z'‖ := by
  have a1 := inner_le_of_min hcv hy h1 y' hy'
  have a2 := inner_le_of_min hcv hy' h2 y hy
  have key : ‖y - y'‖ ^ 2 ≤ inner ℝ (z - z') (y - y') := by
    have e1 : inner ℝ (z - y) (y' - y) = - inner ℝ (z - y) (y - y') := by
      rw [← inner_neg_right]; congr 1; abel
    have e2 : inner ℝ (z' - y') (y - y') = inner ℝ (z' - y') (y - y') := rfl
    have e3 : inner ℝ (z - z') (y - y') = inner ℝ (z - y) (y - y') - inner ℝ (z' - y') (y - y')
        + inner ℝ (y - y') (y - y') := by
      rw [← inner_sub_left, ← inner_add_left]; congr 1; abel
    rw [e3, real_inner_self_eq_norm_sq]
    linarith
  have key2 : inner ℝ (z - z') (y - y') ≤ ‖z - z'‖ * ‖y - y'‖ := real_inner_le_norm _ _
  by_cases h0 : ‖y - y'‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖y - y'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith
end ProjLib

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C₂ : ℝ)
    (hX_ne : X.Nonempty) (hX_closed : IsClosed X) (hX_conv : Convex ℝ X)
    (hx0 : x 0 ∈ X)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • ξ s))
    (hρ : ∀ s, 0 ≤ ρ s) (hξ : ∀ s, ‖ξ s‖ ≤ C₂) :
    ∀ s, ‖x (s + 1) - x s‖ ≤ ‖ρ s • ξ s‖ ∧ ‖ρ s • ξ s‖ ≤ ρ s * C₂ := by
  have hproj : ∀ y, NumStochOpt.QuasiFejer.projX X y ∈ X ∧
      ∀ z ∈ X, ‖y - NumStochOpt.QuasiFejer.projX X y‖ ≤ ‖y - z‖ := by
    intro y
    obtain ⟨v, hv, hvmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex hX_ne hX_closed.isComplete hX_conv y
    have hb : BddBelow (Set.range fun w : X => ‖y - (w : EuclideanSpace ℝ (Fin n))‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    have hex : ∃ x ∈ X, ∀ z ∈ X, ‖y - x‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
      refine ⟨v, hv, fun z hz => ?_⟩
      have : ‖y - v‖ ≤ ‖y - z‖ := by rw [hvmin]; exact ciInf_le hb ⟨z, hz⟩
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    unfold NumStochOpt.QuasiFejer.projX
    rw [dif_pos hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    refine ⟨h1, fun z hz => ?_⟩
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h2 z hz)
  intro s
  have hxs : ∀ s, x s ∈ X := by
    intro s
    induction s with
    | zero => exact hx0
    | succ k _ => rw [hrec k]; exact (hproj _).1
  have h1 : ‖x (s + 1) - x s‖ ≤ ‖(x s - ρ s • ξ s) - x s‖ := by
    rw [hrec s]
    apply proj_nonexp hX_conv (hproj _).1 (hxs s) (hproj _).2
    intro w _
    simp
  have h2 : ‖(x s - ρ s • ξ s) - x s‖ = ‖ρ s • ξ s‖ := by
    rw [sub_sub_cancel_left, norm_neg]
  refine ⟨h2 ▸ h1, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (hρ s)]
  exact mul_le_mul_of_nonneg_left (hξ s) (hρ s)

-- Prove2me | solution 1 for GlobalTheory.matrix_stableRange_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:56.918389+00:00
-- url     : https://prove2.me/submissions/35fbf929-50d3-4bf7-9f22-1ef062e10303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixFieldStableRangeOneDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ)
    (h : c * p + d * q = 1) : ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  classical
  set C := Matrix.toLin' c with hC
  set D := Matrix.toLin' d with hD
  obtain ⟨Wc, hW⟩ := Submodule.exists_isCompl (LinearMap.range D)
  let π := Submodule.linearProjOfIsCompl Wc (LinearMap.range D) hW.symm
  have hdec : ∀ w : Fin n → κ, C (p *ᵥ w) + D (q *ᵥ w) = w := by
    intro w
    simp only [hC, hD, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h,
      Matrix.one_mulVec]
  have hπD : ∀ v, π (D v) = 0 := by
    intro v
    exact Submodule.linearProjOfIsCompl_apply_right hW.symm ⟨D v, LinearMap.mem_range_self _ _⟩
  have hsurj : Function.Surjective (π ∘ₗ C) := by
    intro w
    refine ⟨p *ᵥ (w : Fin n → κ), ?_⟩
    have h2 : π (w : Fin n → κ) = w := Submodule.linearProjOfIsCompl_apply_left _ w
    have := congrArg π (hdec w)
    rw [map_add, hπD, add_zero, h2] at this
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (π ∘ₗ C)
    (LinearMap.range_eq_top.mpr hsurj)
  have hdim : Module.finrank κ (LinearMap.ker D) = Module.finrank κ Wc := by
    have h1 := LinearMap.finrank_range_add_finrank_ker D
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hdim
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker D)
  let projK := Submodule.linearProjOfIsCompl (LinearMap.ker D) K' hK
  let Y : (Fin n → κ) →ₗ[κ] (Fin n → κ) := g ∘ₗ (e : LinearMap.ker D →ₗ[κ] Wc) ∘ₗ projK
  refine ⟨LinearMap.toMatrix' Y, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hM : (c * LinearMap.toMatrix' Y + d) *ᵥ v = C (Y v) + D v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    rfl
  rw [hM] at hv
  have hp : π (C (Y v)) = e (projK v) := by
    have := LinearMap.congr_fun hg (e (projK v))
    simpa [Y] using this
  have h3 : e (projK v) = 0 := by
    have := congrArg π hv
    rwa [map_add, hπD, add_zero, hp, map_zero] at this
  have hk : projK v = 0 := (LinearEquiv.map_eq_zero_iff e).mp h3
  have hY : Y v = 0 := by simp [Y, hk]
  have hDv : D v = 0 := by rw [hY, map_zero, zero_add] at hv; exact hv
  have hvK : v ∈ LinearMap.ker D := hDv
  have h4 := Submodule.linearProjOfIsCompl_apply_left hK ⟨v, hvK⟩
  have : (⟨v, hvK⟩ : LinearMap.ker D) = 0 := by rw [← h4]; exact hk
  exact hv0 (congrArg Subtype.val this)
end GlobalTheory

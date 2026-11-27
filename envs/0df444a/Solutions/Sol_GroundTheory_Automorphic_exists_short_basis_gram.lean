-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_short_basis_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:16.02187+00:00
-- url     : https://prove2.me/submissions/a318e7e0-eb27-4dd9-b9d0-3f110a66e09c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_GramReduction
import Theorems.Thm_GroundTheory_Automorphic_exists_short_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix Submodule
open scoped RealInnerProductSpace
variable {J : Type*} [Fintype J]
namespace GroundTheory.Automorphic
theorem _root_.solution (G : Matrix J J ℝ) (hs : Gᵀ = G)
    (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) (L : AddSubgroup (J → ℝ)) (μ : ℝ)
    (hμ : 0 < μ) (hL : span ℝ (L : Set (J → ℝ)) = ⊤)
    (hD : span ℝ {y : J → ℝ | ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} = ⊤)
    (hmin : ∀ y : J → ℝ, (∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n) → y ≠ 0 →
      μ ^ 2 ≤ y ⬝ᵥ (G *ᵥ y)) :
    ∃ e : Fin (Fintype.card J) → (J → ℝ), LinearIndependent ℝ e ∧
      ∀ i, e i ∈ L ∧ e i ⬝ᵥ (G *ᵥ e i) ≤ shortBasisBound (Fintype.card J) μ ^ 2 := by
  let core := gramCore G hs hpos
  let _ : NormedAddCommGroup (GramSpace G) := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ (GramSpace G) := .ofCore _
  have hinner : ∀ x y : J → ℝ, ⟪toGram G x, toGram G y⟫ = x ⬝ᵥ (G *ᵥ y) := fun _ _ => rfl
  have hnorm : ∀ x : J → ℝ, ‖toGram G x‖ ^ 2 = x ⬝ᵥ (G *ᵥ x) := by
    intro x
    rw [← real_inner_self_eq_norm_sq, hinner]
  let L' : AddSubgroup (GramSpace G) := L.map (toGram G).toLinearMap.toAddMonoidHom
  have memL' : ∀ z, z ∈ L' ↔ (toGram G).symm z ∈ L := by
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨_, hz, by simp⟩
  have hdual : ∀ z, z ∈ latticeDual L' ↔ (toGram G).symm z ∈
      {y : J → ℝ | ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} := by
    intro z
    constructor
    · intro hz x hx
      have := hz (toGram G x) ((memL' _).2 (by simpa using hx))
      simpa [← hinner] using this
    · intro hz x hx
      have := hz _ ((memL' x).1 hx)
      rw [← hinner] at this
      simpa using this
  have hLspan : span ℝ (L' : Set (GramSpace G)) = ⊤ := by
    have : (L' : Set (GramSpace G)) = (toGram G) '' (L : Set (J → ℝ)) := by
      ext z
      rw [SetLike.mem_coe, memL', Set.mem_image]
      constructor
      · intro h; exact ⟨_, h, by simp⟩
      · rintro ⟨x, hx, rfl⟩; simpa using hx
    rw [this, ← LinearEquiv.coe_coe, span_image, hL, Submodule.map_top,
      LinearMap.range_eq_top.2 (toGram G).surjective]
  have hDspan : span ℝ (latticeDual L' : Set (GramSpace G)) = ⊤ := by
    have : (latticeDual L' : Set (GramSpace G)) =
        (toGram G) '' {y : J → ℝ | ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} := by
      ext z
      rw [SetLike.mem_coe, hdual, Set.mem_image]
      constructor
      · intro h; exact ⟨_, h, by simp⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [this, ← LinearEquiv.coe_coe, span_image, hD, Submodule.map_top,
      LinearMap.range_eq_top.2 (toGram G).surjective]
  have hmin' : ∀ z ∈ latticeDual L', z ≠ 0 → μ ≤ ‖z‖ := by
    intro z hz hz0
    have h1 := hmin ((toGram G).symm z) ((hdual z).1 hz) (by simpa using hz0)
    rw [← hnorm, LinearEquiv.apply_symm_apply] at h1
    exact le_of_sq_le_sq (by simpa using h1) (norm_nonneg _) |>.trans_eq' rfl
  obtain ⟨e, hli, he⟩ := exists_short_basis (Fintype.card J) (X := GramSpace G)
    (by rw [show finrank ℝ (GramSpace G) = finrank ℝ (J → ℝ) from rfl, finrank_fintype_fun_eq_card])
    L' μ hμ hLspan hDspan hmin'
  refine ⟨fun i => (toGram G).symm (e i), hli.map' (toGram G).symm.toLinearMap (by simp), fun i => ?_⟩
  refine ⟨(memL' _).1 (he i).1, ?_⟩
  rw [← hnorm, LinearEquiv.apply_symm_apply]
  have h0 := norm_nonneg (e i)
  exact pow_le_pow_left₀ h0 (he i).2 2
end GroundTheory.Automorphic

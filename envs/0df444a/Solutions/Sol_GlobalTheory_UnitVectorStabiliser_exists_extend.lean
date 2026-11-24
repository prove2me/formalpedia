-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.exists_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:48.024673+00:00
-- url     : https://prove2.me/submissions/05a45fb6-50c8-4b19-bb8f-cb30b9723e0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_hf_add_left
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_hf_smul_left
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_hf_herm
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_hf_single
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_exists_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabiliser
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (s : A →+* A) (J : Matrix n n A)
namespace GlobalTheory.UnitVectorStabiliser
theorem _root_.solution (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j)
    (hd : IsUnit J.det) (x : n → A) (hx : IsUnit (hform s J x x)) (P : Submodule A (n → A))
    (hP : ∀ y, y ∈ P ↔ hform s J x y = 0) (u : P →ₗ[A] P)
    (hu : ∀ y z : P, hform s J (u y) (u z) = hform s J y z) :
    ∃ g : GL n A, g ∈ UJ s J ∧ (g : Matrix n n A) *ᵥ x = x ∧
      ∀ y : P, (g : Matrix n n A) *ᵥ y = u y := by
  obtain ⟨c, p, h1, h2, h3⟩ := exists_proj s J x hx P hP
  let f : (n → A) →ₗ[A] (n → A) := c.smulRight x + P.subtype ∘ₗ u ∘ₗ p
  have hf : ∀ y, f y = c y • x + (u (p y) : n → A) := fun y => rfl
  have o1 : ∀ y : P, hform s J x y = 0 := fun y => (hP y).1 y.2
  have o2 : ∀ y : P, hform s J y x = 0 := fun y => by rw [← hf_herm s J hs hJ, o1, map_zero]
  have hiso : ∀ y z, hform s J (f y) (f z) = hform s J y z := by
    intro y z
    conv_rhs => rw [h1 y, h1 z]
    simp only [hf, hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, o1, o2, hu]
  have hg : cT s (LinearMap.toMatrix' f) * J * LinearMap.toMatrix' f = J := by
    ext i j
    rw [← hf_single s (cT s (LinearMap.toMatrix' f) * J * LinearMap.toMatrix' f) i j, ← hf_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hiso,
      hf_single]
  have hdet : IsUnit (LinearMap.toMatrix' f).det := by
    rw [← hg, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  obtain ⟨g, hg'⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  refine ⟨g, ?_, ?_, fun y => ?_⟩
  · show cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J
    rw [hg', hg]
  · have : p x = 0 := by
      have := h1 x
      rw [h2, one_smul] at this
      exact Subtype.ext (by simpa using this)
    rw [hg', LinearMap.toMatrix'_mulVec, hf, h2, this]
    simp
  · have : p y = y := by
      have := h1 y
      rw [h3, zero_smul, zero_add] at this
      exact Subtype.ext this.symm
    rw [hg', LinearMap.toMatrix'_mulVec, hf, h3, this]
    simp
end GlobalTheory.UnitVectorStabiliser

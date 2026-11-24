-- Prove2me | solution 1 for GlobalTheory.AffinePoints.isOpenEmbedding_comap_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:04.143451+00:00
-- url     : https://prove2.me/submissions/d941e97f-768b-47d0-89d5-4a66976feffd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Theorems.Thm_GlobalTheory_AffinePoints_isOpen_nonvanishing
import Theorems.Thm_GlobalTheory_AffinePoints_range_comap_away
import Theorems.Thm_GlobalTheory_AffinePoints_apply_eq_div_of_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set
variable {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] [Field K] [Algebra R K]
namespace GlobalTheory.AffinePoints
theorem _root_.solution (f : A) [IsLocalization.Away f B]
    [TopologicalSpace K] [T1Space K] [IsTopologicalDivisionRing K] :
    IsOpenEmbedding (comap (IsScalarTower.toAlgHom R A B) : (B →ₐ[R] K) → (A →ₐ[R] K)) := by
  have key : ∀ b : B, ∃ a s : A, IsUnit (algebraMap A B s) ∧
      b * algebraMap A B s = algebraMap A B a := fun b => by
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) b
    exact ⟨a, s, IsLocalization.map_units B s, h⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInducing_iff_nhds]
    intro p
    refine le_antisymm (continuous_comap _).continuousAt.le_comap ?_
    rw [← tendsto_id', tendsto_nhds_iff]
    intro b
    obtain ⟨a, s, hs, h⟩ := key b
    have H := tendsto_nhds_iff.1 (tendsto_comap
      (f := (comap (IsScalarTower.toAlgHom R A B) : (B →ₐ[R] K) → (A →ₐ[R] K)))
      (x := 𝓝 (comap (IsScalarTower.toAlgHom R A B) p)))
    simp only [id, fun q : B →ₐ[R] K => apply_eq_div_of_mul_eq q hs h]
    exact (H a).div (H s) (hs.map p).ne_zero
  · intro p q hpq
    ext b
    obtain ⟨a, s, hs, h⟩ := key b
    rw [apply_eq_div_of_mul_eq p hs h, apply_eq_div_of_mul_eq q hs h]
    exact congrArg₂ (· / ·) (DFunLike.congr_fun hpq a) (DFunLike.congr_fun hpq s)
  · rw [range_comap_away f]; exact isOpen_nonvanishing f
end GlobalTheory.AffinePoints

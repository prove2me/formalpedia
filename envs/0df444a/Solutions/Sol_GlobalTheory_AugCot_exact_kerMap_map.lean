-- Prove2me | solution 1 for GlobalTheory.AugCot.exact_kerMap_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:15.178955+00:00
-- url     : https://prove2.me/submissions/b3d1a025-27df-4c79-a7c4-d1f8dd13b499

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] {εA : A →ₐ[R] R} {εB : B →ₐ[R] R} {εC : C →ₐ[R] R}
namespace GlobalTheory.AugCot
theorem _root_.solution (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (hφ : Function.Surjective φ) :
    Function.Exact (kerMap φ h) (map φ h) := by
  intro x
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := (RingHom.ker εA).toCotangent_surjective x
    rw [map_toCotangent, Ideal.toCotangent_eq_zero] at hx
    have hI : RingHom.ker εB = (RingHom.ker εA).map φ := by
      rw [ker_eq_comap φ h, Ideal.map_comap_of_surjective _ hφ]
    have hx' : φ x ∈ (RingHom.ker εA ^ 2).map φ := by
      rw [Ideal.map_pow, ← hI]; exact hx
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ hφ).1 hx'
    refine ⟨⟨x - y, by simp [RingHom.mem_ker, hxy]⟩, ?_⟩
    have hy' : y ∈ RingHom.ker εA := Ideal.pow_le_self two_ne_zero hy
    have : d εA y = 0 := by rw [d_of_mem εA hy', Ideal.toCotangent_eq_zero]; exact hy
    simp [this]
  · rintro ⟨x, rfl⟩
    have : φ x = 0 := x.2
    simp [this]
end GlobalTheory.AugCot

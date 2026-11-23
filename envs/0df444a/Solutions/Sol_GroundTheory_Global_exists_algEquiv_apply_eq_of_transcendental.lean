-- Prove2me | solution 1 for GroundTheory.Global.exists_algEquiv_apply_eq_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.864947+00:00
-- url     : https://prove2.me/submissions/fefa01b3-5fc5-4499-afa0-fac5b2192978

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
import Theorems.Thm_GroundTheory_Global_exists_ringEquiv_extend_of_isTranscendenceBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]
namespace GroundTheory.Global
theorem _root_.solution {x y : Ω} (hx : Transcendental F x)
    (hy : Transcendental F y) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
  classical
  have ind : ∀ z : Ω, Transcendental F z → AlgebraicIndepOn F id ({z} : Set Ω) := fun z hz =>
    (algebraicIndependent_singleton_iff (⟨z, rfl⟩ : ({z} : Set Ω))).mpr hz
  obtain ⟨t₁, hxt, ht₁⟩ := exists_isTranscendenceBasis_superset (ind x hx)
  obtain ⟨t₂, hyt, ht₂⟩ := exists_isTranscendenceBasis_superset (ind y hy)
  have hx₁ : x ∈ t₁ := Set.singleton_subset_iff.mp hxt
  have hy₂ : y ∈ t₂ := Set.singleton_subset_iff.mp hyt
  obtain ⟨f⟩ := Cardinal.eq.1 (ht₁.cardinalMk_eq_trdeg.trans ht₂.cardinalMk_eq_trdeg.symm)
  let φ : t₁ ≃ t₂ := f.trans (Equiv.swap (f ⟨x, hx₁⟩) ⟨y, hy₂⟩)
  obtain ⟨σ, hσF, hσv⟩ :=
    exists_ringEquiv_extend_of_isTranscendenceBasis (RingEquiv.refl F) ht₁ ht₂ φ
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun a => hσF a, ?_⟩
  have := hσv ⟨x, hx₁⟩
  simp only [φ, Equiv.trans_apply, Equiv.swap_apply_left] at this
  exact this
end GroundTheory.Global

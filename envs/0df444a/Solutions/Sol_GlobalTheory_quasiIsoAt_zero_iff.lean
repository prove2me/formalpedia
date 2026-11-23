-- Prove2me | solution 1 for GlobalTheory.quasiIsoAt_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:04.341268+00:00
-- url     : https://prove2.me/submissions/4b17edc4-c6e8-4926-85a5-84ccfb830320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_shortComplex_quasiIso_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) :
    QuasiIsoAt φ 0 ↔
      (∀ y : C.X 0, (C.d 0 1).hom y = 0 → ∃ x : K.X 0, (K.d 0 1).hom x = 0 ∧ (φ.f 0).hom x = y) ∧
      (∀ x : K.X 0, (K.d 0 1).hom x = 0 → (φ.f 0).hom x = 0 → x = 0) := by
  rw [quasiIsoAt_iff' φ 0 0 1 (by simp) (by simp), shortComplex_quasiIso_iff]
  have hK : ∀ x, (K.d 0 0).hom x = 0 := fun x => by rw [K.shape 0 0 (by simp)]; rfl
  have hC : ∀ x, (C.d 0 0).hom x = 0 := fun x => by rw [C.shape 0 0 (by simp)]; rfl
  change (∀ y : C.X 0, (C.d 0 1).hom y = 0 → ∃ (x : K.X 0) (z : C.X 0), (K.d 0 1).hom x = 0 ∧
    (C.d 0 0).hom z + (φ.f 0).hom x = y) ∧ (∀ (x : K.X 0) (z : C.X 0), (K.d 0 1).hom x = 0 →
      (C.d 0 0).hom z = (φ.f 0).hom x → ∃ w : K.X 0, (K.d 0 0).hom w = x) ↔ _
  simp only [hK, hC, zero_add]
  refine and_congr (forall₂_congr fun y _ => ?_) ⟨fun h x h1 h2 => ?_, fun h x _ h1 h2 => ?_⟩
  · exact ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, 0, h⟩⟩
  · obtain ⟨_, hw⟩ := h x 0 h1 h2.symm
    exact hw.symm
  · exact ⟨0, (h x h1 h2.symm).symm⟩
end GlobalTheory

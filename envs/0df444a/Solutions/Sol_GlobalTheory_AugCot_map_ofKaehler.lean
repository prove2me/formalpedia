-- Prove2me | solution 1 for GlobalTheory.AugCot.map_ofKaehler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:42.063854+00:00
-- url     : https://prove2.me/submissions/75db12e7-ff7b-4918-ab34-95c0a5f50cd8

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
theorem _root_.solution [Algebra A B] [IsScalarTower R A B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) (m : Ω[A⁄R]) :
    map _ h (ofKaehler εA m) = ofKaehler εB (KaehlerDifferential.map R R A B m) := by
  have hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; simp [KaehlerDifferential.map_D]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, smul_eq, map_smul, hx, map_smul, ← algebraMap_smul B a, map_smul, smul_eq, ← h]
    rfl
end GlobalTheory.AugCot

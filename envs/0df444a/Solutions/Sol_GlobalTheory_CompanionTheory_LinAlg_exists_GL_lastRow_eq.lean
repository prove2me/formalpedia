-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LinAlg.exists_GL_lastRow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:34.01427+00:00
-- url     : https://prove2.me/submissions/cfa7f218-2da6-4f26-9b30-0ca3aa0c0ec4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGlLastRowEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LinAlg
namespace GlobalTheory.CompanionTheory.LinAlg
theorem _root_.solution : ∀ (K : Type) [Field K] (n : ℕ) (a : Fin (n + 1) → K), a ≠ 0 →
    ∃ m : GL (Fin (n + 1)) K, vecMul (Pi.single (Fin.last n) 1) (m : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = a := by
  intro K _ n a ha
  classical
  set e : Fin (n + 1) → K := Pi.single (Fin.last n) 1 with he_def
  have he : e ≠ 0 := by simp [e]
  let f : (K ∙ e) ≃ₗ[K] (K ∙ a) :=
    (LinearEquiv.toSpanNonzeroSingleton K _ e he).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton K _ a ha
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : (LinearEquiv.toSpanNonzeroSingleton K _ e he).symm
      ⟨e, Submodule.mem_span_singleton_self e⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  have hga : g e = a := by
    have hx := hg ⟨e, Submodule.mem_span_singleton_self e⟩
    rw [← hx]
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.toSpanNonzeroSingleton_one]
  have hdet : IsUnit (LinearMap.toMatrix' (g : (Fin (n + 1) → K) →ₗ[K] Fin (n + 1) → K))ᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' g
  refine ⟨hdet.unit, ?_⟩
  rw [IsUnit.unit_spec, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  simpa using hga
end GlobalTheory.CompanionTheory.LinAlg

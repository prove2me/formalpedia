-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:53:59.223817+00:00
-- url     : https://prove2.me/submissions/5578d834-df05-4f8d-a536-85b031844ce4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegerCoordinatesBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NumberFieldCoord
namespace GlobalTheory.CompanionTheory.NumberFieldCoord
theorem _root_.solution :
    ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)),
      Function.Surjective (fun i => InfinitePlace.mk (τ i)) →
      ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) →
        ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  intro E _ _ I _ τ hτ
  classical
  set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis E).equivFun.toLinearMap
    with hLc
  refine ⟨‖Lc‖ + 1, by positivity, fun e R hR k => ?_⟩
  have hR0 : 0 ≤ R := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    obtain ⟨i, -⟩ := hτ w
    exact (norm_nonneg _).trans (hR i)
  have hw : ∀ w : InfinitePlace E, w (e : E) ≤ R := by
    intro w
    obtain ⟨i, rfl⟩ := hτ w
    simpa only [InfinitePlace.apply] using hR i
  have hn : ‖mixedEmbedding E (e : E)‖ ≤ R := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_of_isReal w.2] at h
      simpa [mixedEmbedding] using h
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_eq] at h
      simpa [mixedEmbedding] using h
  have hval : Lc (mixedEmbedding E (e : E)) k = (((RingOfIntegers.basis E).repr e k : ℤ) : ℝ) := by
    change (mixedEmbedding.latticeBasis E).equivFun (mixedEmbedding E (e : E)) k = _
    rw [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]
    have := integralBasis_repr_apply E e k
    rw [show (e : E) = algebraMap (𝓞 E) E e from rfl, this]
    simp
  rw [← hval, ← Real.norm_eq_abs]
  calc ‖Lc (mixedEmbedding E (e : E)) k‖ ≤ ‖Lc (mixedEmbedding E (e : E))‖ := norm_le_pi_norm _ k
    _ ≤ ‖Lc‖ * ‖mixedEmbedding E (e : E)‖ := Lc.le_opNorm _
    _ ≤ ‖Lc‖ * R := by gcongr
    _ ≤ (‖Lc‖ + 1) * R := by nlinarith
end GlobalTheory.CompanionTheory.NumberFieldCoord

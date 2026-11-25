-- Prove2me | solution 1 for GlobalTheory.mvPowerSeries_eval_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:49.247416+00:00
-- url     : https://prove2.me/submissions/6ea41e5c-5102-4a24-b32d-b6e834313017

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
import Theorems.Thm_GlobalTheory_NilpotentEval_isHausdorff_of_pow_le
import Theorems.Thm_GlobalTheory_NilpotentEval_isPrecomplete_of_pow_le
import Theorems.Thm_GlobalTheory_NilpotentEval_exists_pow_sup_span_le
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvPowerSeries_algHom_ext_of_isHausdorff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mvEvalAdic_X



set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open NilpotentEval
namespace GlobalTheory
theorem _root_.solution : ∀ (A : Type) [CommRing A] (K : Ideal A) (σ : Type) [Finite σ] (a : σ → A), (∀ j, ∃ M : ℕ, a j ^ M ∈ K) → (IsAdicComplete K A → ∀ (R : Type) [CommRing R] [Algebra R A], ∃ ψ : MvPowerSeries σ R →ₐ[R] A, ∀ j, ψ (MvPowerSeries.X j) = a j) ∧ (IsHausdorff K A → ∀ (T : Type) [CommRing T] (ψ ψ' : MvPowerSeries σ T →+* A), (∀ t, ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)) → (∀ j, ψ (MvPowerSeries.X j) = a j) → (∀ j, ψ' (MvPowerSeries.X j) = a j) → ψ = ψ') := by
  intro A _ K σ _ a ha
  obtain ⟨N, hN⟩ := exists_pow_sup_span_le K a ha
  have hmem : ∀ j, a j ∈ K ⊔ Ideal.span (Set.range a) := fun j =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨fun hK R _ _ => ?_, fun hK T _ ψ ψ' hC hψ hψ' => ?_⟩
  · haveI : IsAdicComplete (K ⊔ Ideal.span (Set.range a)) A :=
      { toIsHausdorff := isHausdorff_of_pow_le hN
        toIsPrecomplete := isPrecomplete_of_pow_le hN le_sup_left }
    exact ⟨mvEvalAdic R _ a hmem, mvEvalAdic_X _ a hmem⟩
  · haveI := isHausdorff_of_pow_le hN
    letI : Algebra T A := (ψ.comp MvPowerSeries.C).toAlgebra
    let φ : MvPowerSeries σ T →ₐ[T] A := { ψ with commutes' := fun _ => rfl }
    let φ' : MvPowerSeries σ T →ₐ[T] A := { ψ' with commutes' := fun t => (hC t).symm }
    have : φ = φ' := mvPowerSeries_algHom_ext_of_isHausdorff (K ⊔ Ideal.span (Set.range a))
      (fun j => by change ψ _ ∈ _; rw [hψ]; exact hmem j)
      (fun j => (hψ j).trans (hψ' j).symm)
    exact RingHom.ext fun g => DFunLike.congr_fun this g
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LagFun.exists_param
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:40.772017+00:00
-- url     : https://prove2.me/submissions/41fe5c68-83c6-4bff-bfce-c3bf2aa8147b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LagFun
namespace GlobalTheory.CompanionTheory.LagFun
theorem _root_.solution {k : Type} [Field k] {κ : Type} [Fintype κ] (large₂ : Submodule k ((κ → k) × (κ → k))) :
    ∃ (n : ℕ) (j σ : (Fin n → k) →ₗ[k] (κ → k)) (p : (κ → k) →ₗ[k] (Fin n → k)),
      (∀ t, p (j t) = t) ∧ (∀ t, (j t, σ t) ∈ large₂) ∧ ∀ w ∈ large₂, ∃ t, j t = w.1 := by
  set f : large₂ →ₗ[k] (κ → k) := LinearMap.fst k _ _ ∘ₗ large₂.subtype with hf
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  set e := (Module.finBasis k (LinearMap.range f)).equivFun.symm
  set j := (LinearMap.range f).subtype ∘ₗ e.toLinearMap with hj
  have hinj : LinearMap.ker j = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp e.injective
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective hinj
  refine ⟨_, j, LinearMap.snd k _ _ ∘ₗ large₂.subtype ∘ₗ s ∘ₗ e.toLinearMap, p, fun t => LinearMap.congr_fun hp t,
    fun t => ?_, fun w hw => ⟨e.symm ⟨w.1, ⟨w, hw⟩, rfl⟩, by simp [hj]⟩⟩
  have h1 : (s (e t) : (κ → k) × (κ → k)).1 = j t := congrArg Subtype.val (LinearMap.congr_fun hs (e t))
  rw [← h1]
  exact (s (e t)).2
end GlobalTheory.CompanionTheory.LagFun

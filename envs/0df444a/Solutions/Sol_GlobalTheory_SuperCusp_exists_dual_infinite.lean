-- Prove2me | solution 1 for GlobalTheory.SuperCusp.exists_dual_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:06.813382+00:00
-- url     : https://prove2.me/submissions/2af0d94f-6526-43d7-a3a1-45a64b848f5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp
namespace GlobalTheory.SuperCusp
theorem _root_.solution {Q : Type} [AddCommGroup Q] [Module ℂ Q] (w : ℕ → Q) (hw : ∀ r, w r ≠ 0) :
    ∃ φ : Module.Dual ℂ Q, {r | φ (w r) ≠ 0}.Infinite := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range w)
  set B := Module.Basis.span hli
  have hmem : ∀ r, w r ∈ Submodule.span ℂ (Set.range (Subtype.val : s → Q)) := fun r => by
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span ⟨r, rfl⟩
  have hext : ∀ φ' : Submodule.span ℂ (Set.range (Subtype.val : s → Q)) →ₗ[ℂ] ℂ, ∃ φ : Module.Dual ℂ Q,
      ∀ r, φ (w r) = φ' ⟨w r, hmem r⟩ := by
    intro φ'
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend φ'
    exact ⟨φ, fun r => LinearMap.congr_fun hφ ⟨w r, hmem r⟩⟩
  by_cases hfin : s.Finite
  · haveI : Finite s := hfin.to_subtype
    have hne : ∀ r, ∃ i, B.repr ⟨w r, hmem r⟩ i ≠ 0 := by
      intro r
      by_contra hc
      push_neg at hc
      apply hw r
      have h0 : B.repr ⟨w r, hmem r⟩ = B.repr 0 := by rw [map_zero]; exact Finsupp.ext hc
      simpa using congrArg Subtype.val (B.repr.injective h0)
    choose f hf using hne
    obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber f
    obtain ⟨φ, hφ⟩ := hext (B.coord i)
    refine ⟨φ, (Set.infinite_coe_iff.1 hi).mono fun r hr => ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hr
    show φ (w r) ≠ 0
    rw [hφ, Module.Basis.coord_apply, ← hr]
    exact hf r
  · obtain ⟨φ, hφ⟩ := hext (B.constr ℂ fun _ => (1 : ℂ))
    refine ⟨φ, Set.Infinite.mono (s := w ⁻¹' s) (fun r hr => ?_) ?_⟩
    · show φ (w r) ≠ 0
      rw [hφ]
      have : (⟨w r, hmem r⟩ : Submodule.span ℂ (Set.range (Subtype.val : s → Q))) = B ⟨w r, hr⟩ := by
        ext; simp [B, Module.Basis.span_apply]
      rw [this, Module.Basis.constr_basis]
      exact one_ne_zero
    · refine Set.Infinite.of_image w ?_
      rwa [Set.image_preimage_eq_of_subset hs]
end GlobalTheory.SuperCusp

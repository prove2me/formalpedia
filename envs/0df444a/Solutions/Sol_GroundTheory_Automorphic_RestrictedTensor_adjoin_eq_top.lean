-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:44.711842+00:00
-- url     : https://prove2.me/submissions/6acace8a-f142-44e0-8d41-97e8e547e065

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable [FiniteDimensional ℂ M]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {T : Set (End ℂ M)} (h : IsSimpleUnder T) : Algebra.adjoin ℂ T = ⊤ := by
  have := h.1
  set A := Algebra.adjoin ℂ T
  have hsimple : IsSimpleModule A M := by
    have : Nontrivial (Submodule A M) := (Submodule.nontrivial_iff A).2 h.1
    refine { eq_bot_or_eq_top := fun p => ?_ }
    have hst : IsStable T (p.restrictScalars ℂ) := by
      intro t ht x hx
      have : (⟨t, Algebra.subset_adjoin ht⟩ : A) • x ∈ p := p.smul_mem _ hx
      exact this
    rcases h.2 _ hst with h0 | h0
    · left
      rw [← Submodule.restrictScalars_eq_bot_iff ℂ]
      exact h0
    · right
      rw [← Submodule.restrictScalars_eq_top_iff ℂ]
      exact h0
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ (A := A) (V := M)
  have : Module.Finite (End A M) M := Module.Finite.of_restrictScalars_finite ℂ (End A M) M
  have hsurj := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := M)
  refine eq_top_iff.2 fun φ _ => ?_
  have hφ : ∀ (f : End A M) (x : M), φ (f x) = f (φ x) := by
    intro f x
    obtain ⟨c, rfl⟩ := hb.2 f
    simp [Algebra.algebraMap_eq_smul_one]
  let ψ : End (End A M) M :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun f x => hφ f x }
  obtain ⟨a, ha⟩ := hsurj ψ
  have : (a : End ℂ M) = φ := by
    ext x
    have := congrArg (fun g : End (End A M) M => g x) ha
    exact this
  rw [← this]
  exact a.2
end GroundTheory.Automorphic.RestrictedTensor

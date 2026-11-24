-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.mem_span_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:50.279548+00:00
-- url     : https://prove2.me/submissions/f64baae6-0c35-4ac5-a0c9-a8f8d001b756

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero
namespace GlobalTheory.SS.DefectZero
theorem _root_.solution {A D k M I I' : Type} [CommRing A] [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] [CommRing k] [Algebra A D] [Algebra D k] [Algebra A k]
    [IsScalarTower A D k] [AddCommGroup M] [Module A M] [Module.Finite A M] (π : D)
    (hπ : π ∈ IsLocalRing.maximalIdeal D) (hs : Function.Surjective (algebraMap D k))
    (hk : ∀ d, algebraMap D k d = 0 → π ∣ d) (g : I → M) (a : I' → I)
    (hsat : ∀ v, π • v ∈ Submodule.span D (Set.range fun i => (1 : D) ⊗ₜ[A] g i) →
      v ∈ Submodule.span D (Set.range fun i => (1 : D) ⊗ₜ[A] g i))
    (hsp : ∀ i, (1 : k) ⊗ₜ[A] g i ∈
      Submodule.span k (Set.range fun j => (1 : k) ⊗ₜ[A] g (a j))) (i : I) :
    (1 : D) ⊗ₜ[A] g i ∈ Submodule.span D (Set.range fun j => (1 : D) ⊗ₜ[A] g (a j)) := by
  set N := Submodule.span D (Set.range fun i => (1 : D) ⊗ₜ[A] g i)
  set N' := Submodule.span D (Set.range fun j => (1 : D) ⊗ₜ[A] g (a j))
  have hN' : N' ≤ N := Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨a j, rfl⟩)
  let ρ : D ⊗[A] M →ₗ[D] k ⊗[A] M := AlgebraTensorModule.rTensor A M (Algebra.linearMap D k)
  have hker : ∀ v, ρ v = 0 → ∃ w, v = π • w := by
    intro v hv
    obtain ⟨w, rfl⟩ := (rTensor_exact M
      ((Algebra.linearMap D k).restrictScalars A).exact_subtype_ker_map hs v).mp hv
    clear hv
    induction w with
    | zero => exact ⟨0, by rw [map_zero, smul_zero]⟩
    | add x y hx hy =>
      obtain ⟨x', hx⟩ := hx
      obtain ⟨y', hy⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx, hy, smul_add]⟩
    | tmul d m =>
      obtain ⟨e, he⟩ := hk d.1 d.2
      exact ⟨e ⊗ₜ m, by
        rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, he, smul_tmul', smul_eq_mul]⟩
  have hle : N ≤ N' ⊔ IsLocalRing.maximalIdeal D • N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (1 : k) ⊗ₜ[A] g i ∈ N'.map ρ := by
      rw [Submodule.map_span, ← Set.range_comp]
      have h2 := hsp i
      rw [← Submodule.restrictScalars_mem D, Submodule.restrictScalars_span D k hs] at h2
      simpa [ρ, Function.comp_def] using h2
    obtain ⟨n, hn, hρ⟩ := h1
    obtain ⟨w, hw⟩ := hker ((1 : D) ⊗ₜ[A] g i - n) (by rw [map_sub, hρ]; simp [ρ])
    have hwN : w ∈ N := hsat w (hw ▸ sub_mem (Submodule.subset_span ⟨i, rfl⟩) (hN' hn))
    have : (1 : D) ⊗ₜ[A] g i = n + π • w := by rw [← hw]; abel
    change (1 : D) ⊗ₜ[A] g i ∈ _
    rw [this]
    exact Submodule.add_mem_sup hn (Submodule.smul_mem_smul hπ hwN)
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian N)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.SS.DefectZero

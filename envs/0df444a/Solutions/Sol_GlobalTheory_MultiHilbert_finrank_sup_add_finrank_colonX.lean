-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.finrank_sup_add_finrank_colonX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:38.970802+00:00
-- url     : https://prove2.me/submissions/1377ad72-544f-4ec0-b8fd-10811d2c69c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_component_X_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n, weightedHomogeneousComponent w n F ∈ I) (i : σ) (n : M)
    [Module.Finite K (weightedHomogeneousSubmodule K w (n + w i))]
    [Module.Finite K (weightedHomogeneousSubmodule K w n)] :
    Module.finrank K ↥(weightedHomogeneousSubmodule K w (n + w i) ⊓
        (I ⊔ Ideal.span {X i}).restrictScalars K) +
      Module.finrank K ↥(weightedHomogeneousSubmodule K w n ⊓ (colonX I i).restrictScalars K) =
    Module.finrank K ↥(weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) +
      Module.finrank K ↥(weightedHomogeneousSubmodule K w n) := by
  set μ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := LinearMap.mulLeft K (X i) with hμ
  have hinj : Function.Injective μ := fun a b h => mul_left_cancel₀ (X_ne_zero i) h
  have hmul : ∀ G ∈ weightedHomogeneousSubmodule K w n,
      X i * G ∈ weightedHomogeneousSubmodule K w (n + w i) := by
    intro G hG
    rw [add_comm]
    exact (isWeightedHomogeneous_X K w i).mul hG
  haveI : Module.Finite K ↥(weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K)
    ((weightedHomogeneousSubmodule K w n).map μ)
  have e1 : (weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) ⊔
      ((weightedHomogeneousSubmodule K w n).map μ) =
      weightedHomogeneousSubmodule K w (n + w i) ⊓ (I ⊔ Ideal.span {X i}).restrictScalars K := by
    apply le_antisymm
    · refine sup_le (fun F hF => ⟨hF.1, Ideal.mem_sup_left hF.2⟩) ?_
      rintro _ ⟨G, hG, rfl⟩
      exact ⟨hmul G hG, Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))⟩
    · rintro F ⟨hF, hF'⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
        (show F ∈ I ⊔ Ideal.span {X i} from hF')
      obtain ⟨G, rfl⟩ := Ideal.mem_span_singleton.1 hb
      have hc := IsWeightedHomogeneous.weightedHomogeneousComponent_same hF
      rw [← hc, map_add, component_X_mul]
      exact Submodule.add_mem_sup ⟨weightedHomogeneousComponent_mem _ _ _, hI a ha _⟩
        ⟨_, weightedHomogeneousComponent_mem _ _ _, rfl⟩
  have e2 : (weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) ⊓
      ((weightedHomogeneousSubmodule K w n).map μ) =
      (weightedHomogeneousSubmodule K w n ⊓ (colonX I i).restrictScalars K).map μ := by
    apply le_antisymm
    · rintro _ ⟨⟨-, h2⟩, G, hG, rfl⟩
      exact ⟨G, ⟨hG, h2⟩, rfl⟩
    · rintro _ ⟨G, ⟨hG, h2⟩, rfl⟩
      exact ⟨⟨hmul G hG, h2⟩, G, hG, rfl⟩
  rw [e1, e2, ← (Submodule.equivMapOfInjective μ hinj _).finrank_eq,
    ← (Submodule.equivMapOfInjective μ hinj _).finrank_eq] at h
  exact h
end GlobalTheory.MultiHilbert

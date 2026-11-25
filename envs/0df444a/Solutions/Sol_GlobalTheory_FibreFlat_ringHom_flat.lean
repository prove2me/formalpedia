-- Prove2me | solution 1 for GlobalTheory.FibreFlat.ringHom_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:26.556565+00:00
-- url     : https://prove2.me/submissions/4de3ea95-b360-4df8-8d34-15d0edfdb25d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Theorems.Thm_GlobalTheory_FibreFlat_includeRight_bijective
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_flat_of_flat_residueField_baseChange_dvr
import Theorems.Thm_GlobalTheory_ringHom_flat_of_square


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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct IsLocalRing
open GlobalTheory
open GlobalTheory.FibreFlat
variable {T : Type*} (K : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
  [Algebra T K] [IsFractionRing T K]
namespace GlobalTheory.FibreFlat
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra T A] [Algebra T B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat T B] (φ : A →ₐ[T] B)
    (hK : (Algebra.TensorProduct.map (AlgHom.id T K) φ : K ⊗[T] A →+* K ⊗[T] B).Flat)
    (hκ : (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
      ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat) : (φ : A →+* B).Flat := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have key : ∀ (P : Ideal B) [P.IsPrime],
      (((IsScalarTower.toAlgHom T B (Localization.AtPrime P)).comp φ : A →ₐ[T] _) :
        A →+* Localization.AtPrime P).Flat := by
    intro P _
    let l := IsScalarTower.toAlgHom T B (Localization.AtPrime P)
    have hl : (l : B →+* Localization.AtPrime P).Flat :=
      RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ P.primeCompl)
    have hbc : ∀ (L : Type _) [CommRing L] [Algebra T L],
        (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat →
        (Algebra.TensorProduct.map (AlgHom.id T L) (l.comp φ) :
          L ⊗[T] A →+* L ⊗[T] Localization.AtPrime P).Flat := by
      intro L _ _ h
      rw [Algebra.TensorProduct.map_id_comp]
      exact h.comp (RingHom.Flat.lTensor (S := T) L hl)
    by_cases hu : IsUnit (algebraMap T (Localization.AtPrime P) π)
    · have := IsLocalization.flat K (nonZeroDivisors T)
      refine ringHom_flat_of_square
        (α := (Algebra.TensorProduct.includeRight : A →ₐ[T] K ⊗[T] A))
        (β := (Algebra.TensorProduct.includeRight : _ →ₐ[T] K ⊗[T] Localization.AtPrime P))
        (φ' := (Algebra.TensorProduct.map (AlgHom.id T K) (l.comp φ) :
          K ⊗[T] A →+* K ⊗[T] Localization.AtPrime P)) (by ext a; simp [l]) ?_
        (.of_bijective (includeRight_bijective K hπ hu)) ?_
      · have h1 : (algebraMap A (A ⊗[T] K)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
        exact h1.comp (g := (Algebra.TensorProduct.comm T A K : A ⊗[T] K →+* K ⊗[T] A))
          (.of_bijective (Algebra.TensorProduct.comm T A K).bijective)
      · rw [Algebra.TensorProduct.map_id_comp]
        exact hK.comp (RingHom.Flat.lTensor (S := T) K hl)
    · have : IsLocalHom (algebraMap T (Localization.AtPrime P)) := by
        refine ((local_hom_TFAE (algebraMap T (Localization.AtPrime P))).out 0 2).mpr ?_
        rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
          Ideal.span_singleton_le_iff_mem]
        exact hu
      exact flat_of_flat_residueField_baseChange_dvr _ (hbc _ hκ)
  letI := (φ : A →+* B).toAlgebra
  change Module.Flat A B
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun P _ => ?_
  exact RingHom.flat_algebraMap_iff.mp (key P)
end GlobalTheory.FibreFlat

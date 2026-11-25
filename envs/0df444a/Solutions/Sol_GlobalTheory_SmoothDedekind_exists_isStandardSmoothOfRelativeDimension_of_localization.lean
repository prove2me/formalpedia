-- Prove2me | solution 1 for GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:48:37.852068+00:00
-- url     : https://prove2.me/submissions/90ea6fa7-3dd2-435e-bdf6-7408c5d2a7f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
import Theorems.Thm_GlobalTheory_SmoothDedekind_exists_isStandardSmoothOfRelativeDimension_of_isLocalization
import Theorems.Thm_GlobalTheory_SmoothDedekind_finrank_kaehler_eq_of_formallyUnramified
import Theorems.Thm_GlobalTheory_SmoothDedekind_le_ringKrullDim_quotient_of_ringEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace GlobalTheory.SmoothDedekind
theorem _root_.solution (o V K : Type) [CommRing o]
    [IsNoetherianRing o] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [PerfectField (ResidueField V)] [Field K] [Algebra o V] [Algebra V K] [Algebra o K]
    [IsScalarTower o V K] [IsFractionRing V K] (M : Submonoid o) [IsLocalization M V]
    {A : Type} [CommRing A] [Algebra o A] [Algebra.FiniteType o A] [Module.Flat o A] {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[o] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[o] A) ⧸ p))
    (x : Ideal (ResidueField V ⊗[o] A)) [x.IsMaximal]
    (hx : Module.finrank ((ResidueField V ⊗[o] A) ⧸ x) x.Cotangent ≤ d) :
    ∃ f ∉ x.comap (Algebra.TensorProduct.includeRight : A →ₐ[o] ResidueField V ⊗[o] A).toRingHom,
      Algebra.IsStandardSmoothOfRelativeDimension d o (Localization.Away f) := by
  let ρ : V →ₐ[o] ResidueField V := IsScalarTower.toAlgHom o V _
  have hρ : Function.Surjective ρ := residue_surjective
  let φ : V ⊗[o] A →+* ResidueField V ⊗[o] A :=
    (Algebra.TensorProduct.map ρ (AlgHom.id o A)).toRingHom
  have hφ : Function.Surjective φ :=
    LinearMap.rTensor_surjective A (g := ρ.toLinearMap) hρ
  have hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V (V ⊗[o] A)) := by
    have h := Algebra.TensorProduct.rTensor_ker (R := o) (C := A) ρ hρ
    rw [show RingHom.ker ρ = maximalIdeal V from ker_residue] at h
    exact h
  have hd' := le_ringKrullDim_quotient_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange o V K K A).toRingEquiv hd
  obtain ⟨h₁, -, h₂, h₃, -⟩ :=
    isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V K hd' φ hφ hker x hx
  have : Algebra.FinitePresentation V (V ⊗[o] A) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨-, -, h₄⟩ :=
    isSmoothAt_of_flat_of_isRegularLocalRing V φ hφ hker x (Localization.AtPrime x)
  rw [h₃] at h₄
  let L := Localization.AtPrime (x.comap φ)
  have h₅ : Module.finrank L Ω[L⁄V] = d := by exact_mod_cast h₄
  have : Algebra.FinitePresentation o A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.FormallyEtale o V := .of_isLocalization M
  have : Algebra.FormallySmooth o L := .comp o V L
  have := IsLocalization.tensorRight (S := A) V M
  have hL := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A M) L (x.comap φ)
  have hq : (x.comap φ).comap (algebraMap A (V ⊗[o] A)) = x.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[o] ResidueField V ⊗[o] A).toRingHom := by
    rw [Ideal.comap_comap]
    congr 1
  rw [← hq]
  exact exists_isStandardSmoothOfRelativeDimension_of_isLocalization o _ L
    ((finrank_kaehler_eq_of_formallyUnramified o V L).trans h₅)
end GlobalTheory.SmoothDedekind

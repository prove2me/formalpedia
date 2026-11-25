-- Prove2me | solution 1 for GlobalTheory.StabFlat.localization_of_isStandardSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:32:37.014152+00:00
-- url     : https://prove2.me/submissions/b32a9c49-49f5-4f99-8b7c-3c0985e0192e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth
import Theorems.Thm_GlobalTheory_StabFlat_height_of_etale_mvPolynomial
import Theorems.Thm_GlobalTheory_NilpotentLift_isPushout_quotient_map
import Theorems.Thm_GlobalTheory_isRegularRing_of_etale
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat
namespace GlobalTheory.StabFlat
theorem _root_.solution {V R A : Type} [CommRing V] [IsNoetherianRing V] [CommRing R] [CommRing A]
    {ϖ : V} (h₀ : ϖ ∈ nonZeroDivisors V) [(Ideal.span {ϖ}).IsMaximal] {g : ℕ} {ρ : V →+* R}
    (hρ : ρ.IsStandardSmoothOfRelativeDimension g) (n : Ideal R) [n.IsMaximal] [Algebra R A]
    [IsLocalization.AtPrime A n] (hn : ρ ϖ ∈ n) :
    IsNoetherianRing A ∧ algebraMap R A (ρ ϖ) ∈ nonZeroDivisors A ∧
      IsRegularLocalRing (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) ∧
      ringKrullDim (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) = g := by
  have hq : (Ideal.quotientMap ((Ideal.span {ϖ}).map ρ) ρ Ideal.le_comap_map).IsStandardSmoothOfRelativeDimension g := by
    have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange.{0} g)
    exact MorphismProperty.of_isPushout
      (P := RingHom.toMorphismProperty (@RingHom.IsStandardSmoothOfRelativeDimension g))
      (NilpotentLift.isPushout_quotient_map (Ideal.span {ϖ}) (CommRingCat.ofHom ρ)).flip hρ
  letI := ρ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension g V R := hρ
  have : Algebra.IsStandardSmooth V R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing V R
  refine ⟨IsLocalization.isNoetherianRing n.primeCompl A inferInstance, ?_, ?_⟩
  · have h₁ : IsSMulRegular R ϖ := Module.Flat.isSMulRegular_of_nonZeroDivisors h₀
    refine IsLocalization.map_nonZeroDivisors_le n.primeCompl A ⟨ρ ϖ, ?_, rfl⟩
    exact mem_nonZeroDivisors_iff_left.2 fun x hx => h₁.right_eq_zero_of_smul hx
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  set J := (Ideal.span {ϖ}).map ρ with hJ
  obtain ⟨φ, -, hφ⟩ := hq.exists_etale_mvPolynomial
  have hJ' : J = Ideal.span {ρ ϖ} := by rw [hJ, Ideal.map_span, Set.image_singleton]
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker, hJ', Ideal.span_singleton_le_iff_mem]
  letI := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin g) (V ⧸ Ideal.span {ϖ})) (R ⧸ J) := hφ.toAlgebra
  have : IsRegularRing (R ⧸ J) := isRegularRing_of_etale (MvPolynomial (Fin g) (V ⧸ Ideal.span {ϖ})) _
  have hm : (n.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (Ideal.span {algebraMap R A (ρ ϖ)}).comap (algebraMap R A) := by
    rw [hJ', Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton_self _
  letI : Algebra (R ⧸ J) (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ Ideal.span {algebraMap R A (ρ ϖ)})
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker, hJ', Ideal.map_span, Set.image_singleton])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  refine ⟨?_, (IsLocalization.AtPrime.ringKrullDim_eq_height (n.map (Ideal.Quotient.mk J)) _).trans
    (height_of_etale_mvPolynomial (V ⧸ Ideal.span {ϖ}) (R ⧸ J) g _)⟩
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv
end GlobalTheory.StabFlat

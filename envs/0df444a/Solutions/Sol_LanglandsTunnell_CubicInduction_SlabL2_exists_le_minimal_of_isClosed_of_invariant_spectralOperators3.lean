-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_isClosed_of_invariant_spectralOperators3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fa1b6683-eddc-5ce2-a571-1f585f582435

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isCompactOperator_of_ne_bot_of_invariant_spectralOperators3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL SlabL2.exists_isCompactOperator_of_ne_bot_of_invariant_spectralOperators3"
namespace B1Body
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
open scoped InnerProductSpace

variable {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}

scoped instance completeSpace_cuspidalSubspace : CompleteSpace ↥(cuspidalSubspace ω a b Φ₀) :=
  (isClosed_cuspidalSubspace ω a b Φ₀).isComplete.completeSpace_coe

def Stab (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) : Prop :=
  IsClosed (N : Set ↥(cuspidalSubspace ω a b Φ₀)) ∧ ∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ N, r x ∈ N

theorem adjoint_mem {r : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)}
    (hr : r ∈ spectralOperators3 ω a b Φ₀) :
    ContinuousLinearMap.adjoint r ∈ spectralOperators3 ω a b Φ₀ := by
  rcases hr with hr | ⟨S, hS, hadj⟩
  · exact Or.inr ⟨r, hr, fun x y => ContinuousLinearMap.adjoint_inner_left r y x⟩
  · have h : r = ContinuousLinearMap.adjoint S := (ContinuousLinearMap.eq_adjoint_iff r S).mpr hadj
    rw [h, ContinuousLinearMap.adjoint_adjoint]
    exact Or.inl hS

theorem stab_orthogonal {N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)} (hN : Stab ω a b Φ₀ N) :
    Stab ω a b Φ₀ Nᗮ := by
  refine ⟨Submodule.isClosed_orthogonal N, fun r hr x hx => ?_⟩
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro v hv
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hx _ (hN.2 _ (adjoint_mem hr) v hv)

theorem exists_stab_hull (K : Set ↥(cuspidalSubspace ω a b Φ₀)) :
    ∃ N₀ : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), Stab ω a b Φ₀ N₀ ∧ K ⊆ N₀ ∧ ∀ N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), Stab ω a b Φ₀ N → K ⊆ N → N₀ ≤ N := by
  refine ⟨sInf {N | Stab ω a b Φ₀ N ∧ K ⊆ N}, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Submodule.coe_sInf]
    exact isClosed_biInter fun N hN => hN.1.1
  · intro r hr x hx
    rw [Submodule.mem_sInf] at hx ⊢
    exact fun N hN => hN.1.2 r hr x (hx N hN)
  · intro x hx
    rw [SetLike.mem_coe, Submodule.mem_sInf]
    exact fun N hN => hN.2 hx
  · intro N hN hKN
    exact sInf_le ⟨hN, hKN⟩

theorem adjoint_stab {A : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)} (hA : ∀ N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), Stab ω a b Φ₀ N → ∀ x ∈ N, A x ∈ N)
    (N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (hN : Stab ω a b Φ₀ N) : ∀ x ∈ N, ContinuousLinearMap.adjoint A x ∈ N := by
  intro x hx
  haveI : CompleteSpace ↥N := hN.1.completeSpace_coe
  haveI : N.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace N
  rw [← Submodule.orthogonal_orthogonal N, Submodule.mem_orthogonal]
  intro v hv
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hAv : A v ∈ Nᗮ := hA _ (stab_orthogonal hN) v hv
  rw [Submodule.mem_orthogonal'] at hAv
  exact hAv x hx

theorem eigen_split {B : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)} (hB : ∀ N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), Stab ω a b Φ₀ N → ∀ x ∈ N, B x ∈ N)
    (N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (hN : Stab ω a b Φ₀ N) [N.HasOrthogonalProjection] {lam : ℂ} {k : ↥(cuspidalSubspace ω a b Φ₀)}
    (hk : B k = lam • k) :
    B (N.starProjection k) = lam • N.starProjection k ∧ k - N.starProjection k ∈ Nᗮ := by
  set m : ↥(cuspidalSubspace ω a b Φ₀) := N.starProjection k with hm
  have hmN : m ∈ N := Submodule.starProjection_apply_mem N k
  have hn : k - m ∈ Nᗮ := Submodule.sub_starProjection_mem_orthogonal k
  refine ⟨?_, hn⟩
  have h1 : B m - lam • m ∈ N := N.sub_mem (hB N hN m hmN) (N.smul_mem lam hmN)
  have h2 : B m - lam • m ∈ Nᗮ := by
    have hBn : B (k - m) ∈ Nᗮ := hB _ (stab_orthogonal hN) _ hn
    have hln : lam • (k - m) ∈ Nᗮ := Nᗮ.smul_mem lam hn
    have e : B m - lam • m = -(B (k - m) - lam • (k - m)) := by
      rw [map_sub, hk, smul_sub]
      abel
    rw [e]
    exact Nᗮ.neg_mem (Nᗮ.sub_mem hBn hln)
  have h0 : B m - lam • m = 0 := by
    have : B m - lam • m ∈ N ⊓ Nᗮ := ⟨h1, h2⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  exact sub_eq_zero.mp h0

end LanglandsTunnell.CubicInduction.B1Body
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.B1Body"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.B1Body"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.B1Body"
open scoped InnerProductSpace

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (_hWc : IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)))
    (_hWi : ∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W, r x ∈ W) (_hW : W ≠ ⊥) :
    ∃ W₀ : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), W₀ ≤ W ∧
      IsClosed (W₀ : Set ↥(cuspidalSubspace ω a b Φ₀)) ∧
      (∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W₀, r x ∈ W₀) ∧ W₀ ≠ ⊥ ∧
      ∀ W' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), W' ≤ W₀ →
        IsClosed (W' : Set ↥(cuspidalSubspace ω a b Φ₀)) →
        (∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W', r x ∈ W') → W' = ⊥ ∨ W' = W₀ := by
  classical

  obtain ⟨A, hAc, hAstab, x₀, hx₀W, hAx₀⟩ :=
    SlabL2.exists_isCompactOperator_of_ne_bot_of_invariant_spectralOperators3 ω _hω a b Φ₀ _hΦ₀ W _hWc _hWi _hW
  have hAstab' : ∀ N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), Stab ω a b Φ₀ N → ∀ x ∈ N, A x ∈ N :=
    fun N hN => hAstab N hN.1 hN.2

  set B : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀) := star A * A with hBdef
  have hBapply : ∀ x, B x = ContinuousLinearMap.adjoint A (A x) := fun x => rfl
  have hBc : IsCompactOperator B := hAc.clm_comp (ContinuousLinearMap.adjoint A)
  have hBsa : IsSelfAdjoint B := IsSelfAdjoint.star_mul_self A
  have hBstab : ∀ N : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), Stab ω a b Φ₀ N → ∀ x ∈ N, B x ∈ N :=
    fun N hN x hx => by
      rw [hBapply]
      exact adjoint_stab hAstab' N hN _ (hAstab' N hN x hx)
  have hWs : Stab ω a b Φ₀ W := ⟨_hWc, _hWi⟩

  haveI : CompleteSpace ↥W := _hWc.completeSpace_coe
  haveI : W.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W
  have hBW : ∀ x ∈ W, B x ∈ W := hBstab W hWs
  set P : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀) := W.starProjection with hPdef
  have hPsa : IsSelfAdjoint P := (isStarProjection_starProjection (U := W)).isSelfAdjoint
  set C : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀) := P * B * P with hCdef
  have hCapply : ∀ x, C x = P (B (P x)) := fun x => by
    rw [hCdef, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  have hCc : IsCompactOperator C := by
    have h := (hBc.comp_clm P).clm_comp P
    have e : (C : ↥(cuspidalSubspace ω a b Φ₀) → ↥(cuspidalSubspace ω a b Φ₀)) =
        (P : ↥(cuspidalSubspace ω a b Φ₀) → ↥(cuspidalSubspace ω a b Φ₀)) ∘
          ((B : ↥(cuspidalSubspace ω a b Φ₀) → ↥(cuspidalSubspace ω a b Φ₀)) ∘
            (P : ↥(cuspidalSubspace ω a b Φ₀) → ↥(cuspidalSubspace ω a b Φ₀))) := by
      funext x
      simp only [Function.comp_apply, hCapply]
    rw [e]
    exact h
  have hPadj : ContinuousLinearMap.adjoint P = P := (ContinuousLinearMap.isSelfAdjoint_iff').mp hPsa
  have hBadj : ContinuousLinearMap.adjoint B = B := (ContinuousLinearMap.isSelfAdjoint_iff').mp hBsa
  have hCsa : IsSelfAdjoint C := by
    refine (ContinuousLinearMap.isSelfAdjoint_iff').mpr ((ContinuousLinearMap.eq_adjoint_iff C C).mpr ?_).symm
    intro x y
    rw [hCapply, hCapply]
    have s1 : ⟪P (B (P x)), y⟫_ℂ = ⟪B (P x), P y⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right P (B (P x)) y, hPadj]
    have s2 : ⟪B (P x), P y⟫_ℂ = ⟪P x, B (P y)⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right B (P x) (P y), hBadj]
    have s3 : ⟪P x, B (P y)⟫_ℂ = ⟪x, P (B (P y))⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right P x (B (P y)), hPadj]
    rw [s1, s2, s3]
  have hC0 : C ≠ 0 := by
    intro h
    have hPx : P x₀ = x₀ := Submodule.starProjection_eq_self_iff.mpr hx₀W
    have hPBx : P (B x₀) = B x₀ := Submodule.starProjection_eq_self_iff.mpr (hBW x₀ hx₀W)
    have h3 : ⟪C x₀, x₀⟫_ℂ = 0 := by rw [h, ContinuousLinearMap.zero_apply, inner_zero_left]
    rw [hCapply, hPx, hPBx, hBapply, ContinuousLinearMap.adjoint_inner_left, inner_self_eq_zero] at h3
    exact hAx₀ h3
  obtain ⟨lam, hlamE, hlam0⟩ : ∃ lam : ℂ,
      Module.End.HasEigenvalue (C : Module.End ℂ ↥(cuspidalSubspace ω a b Φ₀)) lam ∧ lam ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hC0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hCc hCsa.isSymmetric).mp hno)

  set E : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) :=
    Module.End.eigenspace (B : Module.End ℂ ↥(cuspidalSubspace ω a b Φ₀)) lam with hE
  haveI hEfd : FiniteDimensional ℂ ↥E := ContinuousLinearMap.finite_dimensional_eigenspace hBc lam hlam0
  have hWE : W ⊓ E ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp (Module.End.hasEigenvalue_iff.mp hlamE)
    have hCv : C v = lam • v := Module.End.mem_eigenspace_iff.mp hv
    have hvW : v ∈ W := by
      have h1 : lam • v ∈ W := by
        rw [← hCv, hCapply]
        exact Submodule.starProjection_apply_mem W _
      have h2 : v = lam⁻¹ • (lam • v) := (inv_smul_smul₀ hlam0 v).symm
      rw [h2]
      exact W.smul_mem _ h1
    have hBv : B v = lam • v := by
      have hPv : P v = v := Submodule.starProjection_eq_self_iff.mpr hvW
      have hPBv : P (B v) = B v := Submodule.starProjection_eq_self_iff.mpr (hBW v hvW)
      rw [← hCv, hCapply, hPv, hPBv]
    exact (Submodule.ne_bot_iff _).mpr ⟨v, ⟨hvW, Module.End.mem_eigenspace_iff.mpr hBv⟩, hv0⟩

  let P : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) → Prop := fun N => Stab ω a b Φ₀ N ∧ N ≤ W ∧ N ⊓ E ≠ ⊥
  have hex : ∃ k, ∃ N, P N ∧ Module.finrank ℂ ↥(N ⊓ E) = k := ⟨_, W, ⟨hWs, le_rfl, hWE⟩, rfl⟩
  obtain ⟨N, ⟨hNs, hNW, hNE⟩, hNd⟩ := Nat.find_spec hex
  have hmin : ∀ N', P N' → Nat.find hex ≤ Module.finrank ℂ ↥(N' ⊓ E) :=
    fun N' hN' => Nat.find_min' hex ⟨N', hN', rfl⟩
  set K : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) := N ⊓ E with hK
  haveI hKfd : FiniteDimensional ℂ ↥K := Submodule.finiteDimensional_of_le inf_le_right

  obtain ⟨N₀, hN₀s, hKN₀, hN₀min⟩ := exists_stab_hull (ω := ω) (a := a) (b := b) (Φ₀ := Φ₀)
    (K : Set ↥(cuspidalSubspace ω a b Φ₀))
  have hKN₀' : K ≤ N₀ := fun x hx => hKN₀ hx
  have hN₀N : N₀ ≤ N := hN₀min N hNs (fun x hx => hx.1)
  have hN₀W : N₀ ≤ W := hN₀N.trans hNW
  have hKE : K ≤ E := inf_le_right
  have hKN₀E : K ≤ N₀ ⊓ E := le_inf hKN₀' hKE
  have hK0 : K ≠ ⊥ := hNE
  have hN₀0 : N₀ ≠ ⊥ := fun h => hK0 (le_bot_iff.1 (h ▸ hKN₀'))
  refine ⟨N₀, hN₀W, hN₀s.1, hN₀s.2, hN₀0, fun W' hW'N₀ hW'c hW'i => ?_⟩
  have hW's : Stab ω a b Φ₀ W' := ⟨hW'c, hW'i⟩
  by_cases hW'E : W' ⊓ E = ⊥
  ·
    left
    haveI : CompleteSpace ↥W' := hW'c.completeSpace_coe
    haveI : W'.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W'
    have hKperp : (K : Set ↥(cuspidalSubspace ω a b Φ₀)) ⊆ W'ᗮ := by
      intro k hk
      have hkE : B k = lam • k := Module.End.mem_eigenspace_iff.1 (hKE hk)
      obtain ⟨hBm, hkm⟩ := eigen_split hBstab W' hW's hkE
      have hmE : W'.starProjection k ∈ E := Module.End.mem_eigenspace_iff.2 hBm
      have hm0 : W'.starProjection k = 0 := by
        have : W'.starProjection k ∈ W' ⊓ E := ⟨Submodule.starProjection_apply_mem W' k, hmE⟩
        rw [hW'E] at this
        exact (Submodule.mem_bot ℂ).1 this
      rw [hm0, sub_zero] at hkm
      exact hkm
    have hN₀le : N₀ ≤ W'ᗮ := hN₀min _ (stab_orthogonal hW's) hKperp
    have : W' ≤ W' ⊓ W'ᗮ := le_inf le_rfl (hW'N₀.trans hN₀le)
    rw [Submodule.inf_orthogonal_eq_bot] at this
    exact le_bot_iff.1 this
  ·
    right
    have hP : P W' := ⟨hW's, hW'N₀.trans hN₀W, hW'E⟩
    have hle : W' ⊓ E ≤ K := inf_le_inf_right E (hW'N₀.trans hN₀N)
    have h1 : Nat.find hex ≤ Module.finrank ℂ ↥(W' ⊓ E) := hmin W' hP
    have h2 : Module.finrank ℂ ↥(W' ⊓ E) ≤ Module.finrank ℂ ↥K := Submodule.finrank_mono hle
    have heq : W' ⊓ E = K := Submodule.eq_of_le_of_finrank_eq hle (le_antisymm h2 (hNd ▸ h1))
    have hKW' : (K : Set ↥(cuspidalSubspace ω a b Φ₀)) ⊆ W' := fun x hx => (heq ▸ hx : x ∈ W' ⊓ E).1
    exact le_antisymm hW'N₀ (hN₀min W' hW's hKW')

end S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3 (solution)

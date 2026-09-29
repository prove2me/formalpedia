-- Prove2me | solution 1 for ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a264860d-53ce-5787-8801-722ca1548bae

import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Differentials
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Theorems.Thm_AlgebraicCurve_pullbackDiff_smul
import Theorems.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import Theorems.Thm_ModularCurve_exists_traceCensus
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Theorems.Thm_AlgebraicCurve_isTraceDiff_traceDiff
import Theorems.Thm_ModularCurve_theta_qExpand
import Theorems.Thm_ModularCurve_theta_qTwist
import Theorems.Thm_ModularCurve_PhiGen_weightTwo_coeff_sum_slots
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_extendScalars_full_prime
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jq_extendScalars_full
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

p2m_open "ModularCurve P2MW.S_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D.ModularCurve ModularCurve.PhiGen P2MW.S_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D.ModularCurve.PhiGen AlgebraicCurve"

namespace ModularCurve p2m_export "ModularCurve" "heckeBetaBar qExpand qExpand_coeff_mul jq modularFunctionFieldFull coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full qTwist thetaL thetaL_apply IsQExpansionDiffAlong qExpansionDiffAlong exists_traceCensus isQExpansionDiffAlong_qExpansionDiffAlong theta_qExpand theta_qTwist transcendental_coeffEmb_jq finiteDimensional_extendScalars_full_prime isSeparable_adjoin_jq_extendScalars_full" namespace IsQExpansionDiffAlong end ModularCurve.IsQExpansionDiffAlong
namespace ModularCurve.IsQExpansionDiffAlong
p2m_open_scoped "ModularCurve" in
private theorem _root_.ModularCurve.IsQExpansionDiffAlong.thetaL_eq_of_D_eq_smul_map {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] {σ : F' →ₐ[K] LaurentSeries L} {φ : Ω[F'⁄K] →ₗ[K] LaurentSeries L} (hφ : IsQExpansionDiffAlong σ φ) {x : F} {y h : F'} (hD : KaehlerDifferential.D K F' y = h • KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F x)) : thetaL L (σ y) = σ h * thetaL L (σ (algebraMap F F' x)) := by
  rw [← hφ.1 y, hD, hφ.2, KaehlerDifferential.map_D, hφ.1]

end ModularCurve.IsQExpansionDiffAlong
p2m_export "" "ModularCurve.IsQExpansionDiffAlong.thetaL_eq_of_D_eq_smul_map"

namespace ModularCurve p2m_export "ModularCurve" "heckeBetaBar qExpand qExpand_coeff_mul jq modularFunctionFieldFull coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full qTwist thetaL thetaL_apply IsQExpansionDiffAlong qExpansionDiffAlong exists_traceCensus isQExpansionDiffAlong_qExpansionDiffAlong theta_qExpand theta_qTwist transcendental_coeffEmb_jq finiteDimensional_extendScalars_full_prime isSeparable_adjoin_jq_extendScalars_full" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] {σ₀ : F →ₐ[K] LaurentSeries L} {φ₀ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ₀ : IsQExpansionDiffAlong σ₀ φ₀) {t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]} (ht : IsTraceDiff K F F' t) (β : F →ₐ[K] F') {x : F} {h : F'} (hD : KaehlerDifferential.D K F' (β x) = h • KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F x)) (f : F) : φ₀ (t (pullbackDiff β (f • KaehlerDifferential.D K F x))) = σ₀ (Algebra.trace F F' (β f * h)) * thetaL L (σ₀ x) := by
  rw [pullbackDiff_smul, pullbackDiff_D, hD, smul_smul, ht, hφ₀.2, hφ₀.1]

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.sum_mul_thetaL_eq_trace_mul_thetaL {K F F' L ι : Type*} [Fintype ι] [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] (σ₀ : F →ₐ[K] LaurentSeries L) (ε : LaurentSeries L →+* LaurentSeries L) (σ : ι → (F' →ₐ[K] LaurentSeries L)) {φ : ι → (Ω[F'⁄K] →ₗ[K] LaurentSeries L)} (hφ : ∀ i, IsQExpansionDiffAlong (σ i) (φ i)) (hcen : ∀ z : F', ε (σ₀ (Algebra.trace F F' z)) = ∑ i, σ i z) (hα : ∀ (i : ι) (z : F), σ i (algebraMap F F' z) = ε (σ₀ z)) {x : F} {y h : F'} (hD : KaehlerDifferential.D K F' y = h • KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F x)) (u : F') : ∑ i, σ i u * thetaL L (σ i y) = ε (σ₀ (Algebra.trace F F' (u * h))) * thetaL L (ε (σ₀ x)) := by
  rw [hcen, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hφ i).thetaL_eq_of_D_eq_smul_map hD, hα, map_mul, mul_assoc]

namespace KaehlerDifferential p2m_export "KaehlerDifferential" "finite D map_D map span_D_eq_top_of_transcendental" end KaehlerDifferential
p2m_open_scoped "KaehlerDifferential" in
private theorem KaehlerDifferential.exists_D_eq_smul_map_of_span_eq_top {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] {x : F} (hspan : Submodule.span F' ({KaehlerDifferential.D K F' (algebraMap F F' x)} : Set (KaehlerDifferential K F')) = ⊤) (y : F') : ∃ h : F', KaehlerDifferential.D K F' y = h • KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F x) := by
  have hy : KaehlerDifferential.D K F' y ∈ Submodule.span F'
      ({KaehlerDifferential.D K F' (algebraMap F F' x)} : Set (KaehlerDifferential K F')) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨h, hh⟩ := Submodule.mem_span_singleton.mp hy
  exact ⟨h, by rw [KaehlerDifferential.map_D, hh]⟩

p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 1600000 in
private theorem ModularCurve.nsmul_qExpand_qExpansionDiff_traceDiff_pullbackDiff_heckeBetaBar (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N) (ζ : Lˣ) (ξ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ) (hξ : IsPrimitiveRoot (ξ : L) (N * ℓ)) (hξN : ξ ^ N = ζ) (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) (x : laurentBaseChange L (modularFunctionFieldFull N)) (hx : Transcendental L x) [Algebra.IsSeparable (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) x} : Set (IntermediateField.extendScalars hle))) (IntermediateField.extendScalars hle)] (f : laurentBaseChange L (modularFunctionFieldFull N)) : ℓ • qExpand L ℓ (qExpansionDiffAlong (laurentBaseChange L (modularFunctionFieldFull N)).val (traceDiff L (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) (pullbackDiff (heckeBetaBar L N ℓ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] IntermediateField.extendScalars hle) (f • KaehlerDifferential.D L (laurentBaseChange L (modularFunctionFieldFull N)) x)))) = (ℓ * ℓ) • qExpand L (ℓ * ℓ) ((f : LaurentSeries L) * thetaL L (x : LaurentSeries L)) + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) ((f : LaurentSeries L) * thetaL L (x : LaurentSeries L)) := by
  obtain ⟨σ, ha, hb, hc, hd⟩ := exists_traceCensus L N ℓ hN ζ ξ hζ hξ hξN hle
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero (laurentBaseChange L (modularFunctionFieldFull N)) :=
    charZero_of_injective_algebraMap (algebraMap L (laurentBaseChange L (modularFunctionFieldFull N))).injective
  haveI := finiteDimensional_extendScalars_full_prime L N ℓ hN hle
  have ht := isTraceDiff_traceDiff L (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle)
  have hx' : Transcendental L (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) x) :=
    (transcendental_algebraMap_iff (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle)).injective).mpr hx
  obtain ⟨h, hD⟩ := KaehlerDifferential.exists_D_eq_smul_map_of_span_eq_top
    (KaehlerDifferential.span_D_eq_top_of_transcendental L _ hx')
    ((heckeBetaBar L N ℓ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] IntermediateField.extendScalars hle) x)
  have h2 := qExpansionDiff_traceDiff_pullbackDiff_smul_D
    (isQExpansionDiffAlong_qExpansionDiffAlong (laurentBaseChange L (modularFunctionFieldFull N)).val) ht
    (heckeBetaBar L N ℓ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] IntermediateField.extendScalars hle) hD f
  have h3 := sum_mul_thetaL_eq_trace_mul_thetaL (laurentBaseChange L (modularFunctionFieldFull N)).val (qExpand L ℓ) σ
    (fun i => isQExpansionDiffAlong_qExpansionDiffAlong (σ i)) (fun z => hd z) (fun i z => ha i z) hD
    ((heckeBetaBar L N ℓ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] IntermediateField.extendScalars hle) f)
  have tq : ∀ (M : ℕ) [NeZero M] (s : LaurentSeries L), thetaL L (qExpand L M s) = M • qExpand L M (thetaL L s) :=
    fun M _ s => theta_qExpand M s
  have tt : ∀ (u : Lˣ) (s : LaurentSeries L), thetaL L (qTwist u s) = qTwist u (thetaL L s) :=
    fun u s => theta_qTwist u s
  have hβ : ∀ g : laurentBaseChange L (modularFunctionFieldFull N),
      (heckeBetaBar L N ℓ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] IntermediateField.extendScalars hle) g
        = ⟨(heckeBetaBar L N ℓ g : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mpr (heckeBetaBar L N ℓ g).2⟩ :=
    fun g => Subtype.ext rfl
  rw [tq] at h3
  erw [h2]
  rw [map_mul, ← mul_smul_comm]
  erw [← h3]
  rw [Fin.sum_univ_succ]
  erw [hβ f, hβ x, hb f, hb x]
  rw [tq, mul_smul_comm, ← map_mul (qExpand L (ℓ * ℓ)), Finset.sum_range]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by erw [hc b f, hc b x]; rw [tt, ← map_mul (qTwist (ζ ^ (b : ℕ)))]

namespace ModularCurve p2m_export "ModularCurve" "heckeBetaBar qExpand qExpand_coeff_mul jq modularFunctionFieldFull coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full qTwist thetaL thetaL_apply IsQExpansionDiffAlong qExpansionDiffAlong exists_traceCensus isQExpansionDiffAlong_qExpansionDiffAlong theta_qExpand theta_qTwist transcendental_coeffEmb_jq finiteDimensional_extendScalars_full_prime isSeparable_adjoin_jq_extendScalars_full" namespace PhiGen p2m_export "ModularCurve.PhiGen" "weightTwo_coeff_sum_slots" end ModularCurve.PhiGen
p2m_open_scoped "ModularCurve ModularCurve.PhiGen" in
private theorem ModularCurve.PhiGen.coeff_of_nsmul_qExpand_eq_weightTwo_sum {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [NeZero ℓ] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) {s g : LaurentSeries K} (hs : ℓ • qExpand K ℓ s = (ℓ * ℓ) • qExpand K (ℓ * ℓ) g + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) g) (n : ℤ) : s.coeff n = g.coeff ((ℓ : ℤ) * n) + if (ℓ : ℤ) ∣ n then (ℓ : K) * g.coeff (n / ℓ) else 0 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hℓ : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  have h : (ℓ • qExpand K ℓ s).coeff ((ℓ : ℤ) * n)
      = ((ℓ * ℓ) • qExpand K (ℓ * ℓ) g + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) g).coeff ((ℓ : ℤ) * n) := by
    rw [hs]
  rw [weightTwo_coeff_sum_slots ℓ ζ hζ g n, HahnSeries.coeff_nsmul, Pi.smul_apply, qExpand_coeff_mul,
    nsmul_eq_mul] at h
  exact mul_left_cancel₀ hℓ h

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeff_qExpansionDiff_traceDiff_pullbackDiff_heckeBetaBar (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N) (ζ : Lˣ) (ξ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ) (hξ : IsPrimitiveRoot (ξ : L) (N * ℓ)) (hξN : ξ ^ N = ζ) (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) (x : laurentBaseChange L (modularFunctionFieldFull N)) (hx : Transcendental L x) [Algebra.IsSeparable (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) x} : Set (IntermediateField.extendScalars hle))) (IntermediateField.extendScalars hle)] (f : laurentBaseChange L (modularFunctionFieldFull N)) (n : ℤ) : (qExpansionDiffAlong (laurentBaseChange L (modularFunctionFieldFull N)).val (traceDiff L (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) (pullbackDiff (heckeBetaBar L N ℓ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] IntermediateField.extendScalars hle) (f • KaehlerDifferential.D L (laurentBaseChange L (modularFunctionFieldFull N)) x)))).coeff n = ((f : LaurentSeries L) * thetaL L (x : LaurentSeries L)).coeff ((ℓ : ℤ) * n) + if (ℓ : ℤ) ∣ n then (ℓ : L) * ((f : LaurentSeries L) * thetaL L (x : LaurentSeries L)).coeff (n / ℓ) else 0 :=
  coeff_of_nsmul_qExpand_eq_weightTwo_sum ℓ ζ hζ
    (nsmul_qExpand_qExpansionDiff_traceDiff_pullbackDiff_heckeBetaBar L N ℓ hN ζ ξ hζ hξ hξN hle x hx f) n

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeff_qExpansionDiff_traceDiff_pullbackDiff_heckeBetaBar_jq (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N) (ζ : Lˣ) (ξ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ) (hξ : IsPrimitiveRoot (ξ : L) (N * ℓ)) (hξN : ξ ^ N = ζ) (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) [Algebra.IsSeparable (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (IntermediateField.extendScalars hle))) (IntermediateField.extendScalars hle)] (f : laurentBaseChange L (modularFunctionFieldFull N)) (n : ℤ) : (qExpansionDiffAlong (laurentBaseChange L (modularFunctionFieldFull N)).val (traceDiff L (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) (pullbackDiff (heckeBetaBar L N ℓ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] IntermediateField.extendScalars hle) (f • KaehlerDifferential.D L (laurentBaseChange L (modularFunctionFieldFull N)) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩)))).coeff n = ((f : LaurentSeries L) * thetaL L (coeffEmb L jq)).coeff ((ℓ : ℤ) * n) + if (ℓ : ℤ) ∣ n then (ℓ : L) * ((f : LaurentSeries L) * thetaL L (coeffEmb L jq)).coeff (n / ℓ) else 0 :=
  coeff_qExpansionDiff_traceDiff_pullbackDiff_heckeBetaBar L N ℓ hN ζ ξ hζ hξ hξN hle
    ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ (transcendental_coeffEmb_jq L N) f n

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeff_qExpansionDiff_heckeDiff_jq (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N) (ζ : Lˣ) (ξ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ) (hξ : IsPrimitiveRoot (ξ : L) (N * ℓ)) (hξN : ξ ^ N = ζ) (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) (f : laurentBaseChange L (modularFunctionFieldFull N)) (n : ℤ) : (qExpansionDiffAlong (laurentBaseChange L (modularFunctionFieldFull N)).val (traceDiff L (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) (pullbackDiff (heckeBetaBar L N ℓ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] IntermediateField.extendScalars hle) (f • KaehlerDifferential.D L (laurentBaseChange L (modularFunctionFieldFull N)) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩)))).coeff n = ((f : LaurentSeries L) * thetaL L (coeffEmb L jq)).coeff ((ℓ : ℤ) * n) + if (ℓ : ℤ) ∣ n then (ℓ : L) * ((f : LaurentSeries L) * thetaL L (coeffEmb L jq)).coeff (n / ℓ) else 0 := by
  haveI := isSeparable_adjoin_jq_extendScalars_full L N (N * ℓ) hle
  exact coeff_qExpansionDiff_traceDiff_pullbackDiff_heckeBetaBar_jq L N ℓ hN ζ ξ hζ hξ hξN hle f n

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D.ModularCurve AlgebraicCurve in

theorem solution {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] {σ₀ : F →ₐ[K] LaurentSeries L} {φ₀ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ₀ : IsQExpansionDiffAlong σ₀ φ₀) {t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]} (ht : IsTraceDiff K F F' t) (β : F →ₐ[K] F') {x : F} {h : F'} (hD : KaehlerDifferential.D K F' (β x) = h • KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F x)) (f : F) : φ₀ (t (pullbackDiff β (f • KaehlerDifferential.D K F x))) = σ₀ (Algebra.trace F F' (β f * h)) * thetaL L (σ₀ x) :=
  ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D hφ₀ ht β hD f

#print axioms solution

end S_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D
end P2MW
export P2MW.S_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D (solution)

-- Prove2me | solution 1 for ModularCurve.JZero.exists_galoisStable_rep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b5969a28-3f03-5748-b998-a3c7d0a5f7e8

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_cuspInftyBar
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Theorems.Thm_MWFL_exists_finiteDimensional_fixingSubgroup_smul_eq_fun
import Theorems.Thm_MWFL_exists_finiteDimensional_fixingSubgroup_smul_eq_place
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_galoisStable_rep
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

set_option autoImplicit false

open ModularCurve AlgebraicCurve

#check @ModularCurve.deg_eq_one_modularFunctionFieldBar
#check @ModularCurve.arithmeticGalois_smul_cuspInftyBar
#check @ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional
#check @MWFL.exists_finiteDimensional_fixingSubgroup_smul_eq_fun

namespace P4M

open AlgebraicCurve ModularCurve

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem log_mono {x y : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) (hy : y ≠ 0) (h : x ≤ y) :
    WithZero.log x ≤ WithZero.log y :=
  (WithZero.log_le_log hx hy).mpr h

private theorem ord_add_min (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have hvf := v.adicValuation_ne_zero hf
  have hvg := v.adicValuation_ne_zero hg
  have hvfg := v.adicValuation_ne_zero hfg
  have hmax : v.adicValuation (f + g) ≤ max (v.adicValuation f) (v.adicValuation g) :=
    v.adicValuation.map_add f g
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
    rw [hm] at hmax
  · refine le_trans (min_le_left _ _) ?_
    show -(WithZero.log (v.adicValuation f)) ≤ -(WithZero.log (v.adicValuation (f + g)))
    have := log_mono hvfg hvf hmax
    omega
  · refine le_trans (min_le_right _ _) ?_
    show -(WithZero.log (v.adicValuation g)) ≤ -(WithZero.log (v.adicValuation (f + g)))
    have := log_mono hvfg hvg hmax
    omega

private theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  show -(WithZero.log (v.adicValuation (-f))) = -(WithZero.log (v.adicValuation f))
  rw [v.adicValuation.map_neg]

private theorem ne_zero_of_one_le_ord (v : Place K F) {x : F} (h : 1 ≤ v.ord x) : x ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  omega

private theorem ord_mul_inv (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f * g⁻¹) = v.ord f - v.ord g := by
  rw [v.ord_mul hf (inv_ne_zero hg), v.ord_inv, sub_eq_add_neg]

private theorem one_le_ord_of_mem_maximalIdeal (v : Place K F) {a : v.toValuationSubring}
    (hmem : a ∈ IsLocalRing.maximalIdeal v.toValuationSubring) (ha : (a : F) ≠ 0) :
    1 ≤ v.ord (a : F) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨b, rfl⟩ := hmem
  have hcoe : ((p * b : v.toValuationSubring) : F) = (p : F) * (b : F) := rfl
  have hpF : ((p : v.toValuationSubring) : F) ≠ 0 := by
    simpa using hp.ne_zero
  have hbF : ((b : v.toValuationSubring) : F) ≠ 0 := by
    intro h0
    exact ha (by rw [hcoe, h0, mul_zero])
  have hb0 : 0 ≤ v.ord (b : F) := (v.mem_iff_ord_nonneg hbF).mp b.2
  rw [hcoe, v.ord_mul hpF hbF, v.ord_coe_irreducible hp]
  omega

end Generic

section Modular

variable (N : ℕ) [NeZero N]

private theorem divisor_eq_zero_of_effective
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (heff : ∀ v, 0 ≤ D v) (h0 : Divisor.degree D = 0) : D = 0 := by
  have hsum : ∑ v ∈ D.support, D v * (v.deg : ℤ) = 0 := by
    rw [← h0]; rfl
  have hsum1 : ∑ v ∈ D.support, D v = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ModularCurve.deg_eq_one_modularFunctionFieldBar N v]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => heff v).mp hsum1
  ext v
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra h
  exact h (hz v (Finsupp.mem_support_iff.mpr h))

private def IsValueAt (f : modularFunctionFieldBar N) (c : AlgebraicClosure ℚ) : Prop :=
  f = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ∨
    1 ≤ (cuspInftyBar N).ord
      (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)

private theorem isValueAt_algebraMap (c : AlgebraicClosure ℚ) :
    IsValueAt N (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) c :=
  Or.inl rfl

private theorem isValueAt_one : IsValueAt N 1 1 :=
  Or.inl (map_one (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N))).symm

omit [NeZero N] in
private theorem algebraMap_ne_zero {c : AlgebraicClosure ℚ} (hc : c ≠ 0) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ≠ 0 := fun h =>
  hc ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
    (by rw [h, map_zero]))

private theorem exists_isValueAt {f : modularFunctionFieldBar N}
    (h : 0 ≤ (cuspInftyBar N).ord f) : ∃ c, IsValueAt N f c := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, Or.inl (by rw [map_zero])⟩
  have hfA : f ∈ (cuspInftyBar N).toValuationSubring :=
    ((cuspInftyBar N).mem_iff_ord_nonneg hf).mpr h
  have hrank : Module.finrank (AlgebraicClosure ℚ) (cuspInftyBar N).ResidueField = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (1 : (cuspInftyBar N).ResidueField) one_ne_zero).mp hrank
    (IsLocalRing.residue (cuspInftyBar N).toValuationSubring ⟨f, hfA⟩)
  have hsmul : c • (1 : (cuspInftyBar N).ResidueField)
      = algebraMap (AlgebraicClosure ℚ) (cuspInftyBar N).ResidueField c := by
    rw [Algebra.smul_def, mul_one]
  have halg : algebraMap (AlgebraicClosure ℚ) (cuspInftyBar N).ResidueField c
      = IsLocalRing.residue (cuspInftyBar N).toValuationSubring
          (algebraMap (AlgebraicClosure ℚ) (cuspInftyBar N).toValuationSubring c) := by
    rw [IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ)
      (cuspInftyBar N).toValuationSubring (cuspInftyBar N).ResidueField]
    rfl
  have hres : IsLocalRing.residue (cuspInftyBar N).toValuationSubring
      (⟨f, hfA⟩ - algebraMap (AlgebraicClosure ℚ) (cuspInftyBar N).toValuationSubring c)
      = 0 := by
    rw [map_sub, ← halg, ← hsmul, hc, sub_self]
  have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hres
  have hcoe : ((⟨f, hfA⟩ - algebraMap (AlgebraicClosure ℚ)
        (cuspInftyBar N).toValuationSubring c : (cuspInftyBar N).toValuationSubring) :
        modularFunctionFieldBar N)
      = f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c := by
    rw [show ((⟨f, hfA⟩ - algebraMap (AlgebraicClosure ℚ)
        (cuspInftyBar N).toValuationSubring c : (cuspInftyBar N).toValuationSubring) :
        modularFunctionFieldBar N)
      = f - ((algebraMap (AlgebraicClosure ℚ) (cuspInftyBar N).toValuationSubring c :
          (cuspInftyBar N).toValuationSubring) : modularFunctionFieldBar N) from rfl,
      (cuspInftyBar N).coe_algebraMap]
  rcases eq_or_ne (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) 0
    with h0 | h0
  · exact ⟨c, Or.inl (sub_eq_zero.mp h0)⟩
  · refine ⟨c, Or.inr ?_⟩
    have hne : ((⟨f, hfA⟩ - algebraMap (AlgebraicClosure ℚ)
        (cuspInftyBar N).toValuationSubring c : (cuspInftyBar N).toValuationSubring) :
        modularFunctionFieldBar N) ≠ 0 := by
      rw [hcoe]; exact h0
    have := one_le_ord_of_mem_maximalIdeal (cuspInftyBar N) hmem hne
    rwa [hcoe] at this

private theorem value_ne_zero {f : modularFunctionFieldBar N} {c : AlgebraicClosure ℚ}
    (hf : f ≠ 0) (h0 : (cuspInftyBar N).ord f = 0) (hv : IsValueAt N f c) : c ≠ 0 := by
  rintro rfl
  rcases hv with heq | h1
  · rw [map_zero] at heq
    exact hf heq
  · rw [map_zero, sub_zero, h0] at h1
    omega

private theorem ord_eq_zero_of_value {f : modularFunctionFieldBar N} {c : AlgebraicClosure ℚ}
    (hc : c ≠ 0) (hv : IsValueAt N f c) :
    f ≠ 0 ∧ (cuspInftyBar N).ord f = 0 := by
  rcases hv with rfl | h1
  · exact ⟨algebraMap_ne_zero N hc, Place.ord_algebraMap _ _⟩
  · have hsub : f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ≠ 0 :=
      ne_zero_of_one_le_ord _ h1
    have hfne : f ≠ 0 := by
      rintro rfl
      rw [zero_sub, ord_neg, Place.ord_algebraMap] at h1
      omega
    refine ⟨hfne, ?_⟩
    have hup : 0 ≤ (cuspInftyBar N).ord f := by
      have hrw : f = (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
          + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c := by ring
      have hmin := ord_add_min (cuspInftyBar N) hsub
        (algebraMap_ne_zero N hc) (by rw [← hrw]; exact hfne)
      rw [← hrw, Place.ord_algebraMap] at hmin
      omega
    have hlow : ¬ 1 ≤ (cuspInftyBar N).ord f := by
      intro hge
      have hrw : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
          = f + -(f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
        ring
      have hne2 : -(f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
          ≠ 0 := neg_ne_zero.mpr hsub
      have hmin := ord_add_min (cuspInftyBar N) hfne hne2
        (by rw [← hrw]; exact algebraMap_ne_zero N hc)
      rw [← hrw, Place.ord_algebraMap, ord_neg] at hmin
      omega
    omega

private theorem isValueAt_unique {f : modularFunctionFieldBar N} {c d : AlgebraicClosure ℚ}
    (h1 : IsValueAt N f c) (h2 : IsValueAt N f d) : c = d := by
  by_contra hne
  have hcd : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
      ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d := fun h =>
    hne ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective h)
  rcases h1 with heq1 | hge1 <;> rcases h2 with heq2 | hge2
  · exact hcd (heq1.symm.trans heq2)
  · rw [heq1, ← map_sub, Place.ord_algebraMap] at hge2
    omega
  · rw [heq2, ← map_sub, Place.ord_algebraMap] at hge1
    omega
  · have hsub1 : f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ≠ 0 :=
      ne_zero_of_one_le_ord _ hge1
    have hsub2 : f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d ≠ 0 :=
      ne_zero_of_one_le_ord _ hge2
    have hkey : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c - d)
        = (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d)
          + -(f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
      rw [map_sub]; ring
    have hne2 : -(f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
        ≠ 0 := neg_ne_zero.mpr hsub1
    have hmapne : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c - d)
        ≠ 0 := algebraMap_ne_zero N (sub_ne_zero.mpr hne)
    have hmin := ord_add_min (cuspInftyBar N) hsub2 hne2 (by rw [← hkey]; exact hmapne)
    rw [← hkey, Place.ord_algebraMap, ord_neg] at hmin
    omega

private theorem isValueAt_mul {f g : modularFunctionFieldBar N} {c d : AlgebraicClosure ℚ}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (h0f : (cuspInftyBar N).ord f = 0) (h0g : (cuspInftyBar N).ord g = 0)
    (hvf : IsValueAt N f c) (hvg : IsValueAt N g d) :
    IsValueAt N (f * g) (c * d) := by
  rcases eq_or_ne (f * g)
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c * d)) with heq | hne
  · exact Or.inl heq
  refine Or.inr ?_
  have hdne : d ≠ 0 := value_ne_zero N hg h0g hvg
  rcases hvf with heqf | hgef <;> rcases hvg with heqg | hgeg
  · exact absurd (by rw [heqf, heqg, map_mul]) hne
  · have hkey : f * g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c * d)
        = f * (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d) := by
      rw [heqf, map_mul]; ring
    rw [hkey, (cuspInftyBar N).ord_mul hf (ne_zero_of_one_le_ord _ hgeg)]
    omega
  · have hkey : f * g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c * d)
        = (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) * g := by
      rw [heqg, map_mul]; ring
    rw [hkey, (cuspInftyBar N).ord_mul (ne_zero_of_one_le_ord _ hgef) hg]
    omega
  · have hsub1 := ne_zero_of_one_le_ord _ hgef
    have hsub2 := ne_zero_of_one_le_ord _ hgeg
    have hkey : f * g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c * d)
        = f * (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d)
          + (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
            * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d := by
      rw [map_mul]; ring
    have ht1 : f * (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d)
        ≠ 0 := mul_ne_zero hf hsub2
    have ht2 : (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
        * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d ≠ 0 :=
      mul_ne_zero hsub1 (algebraMap_ne_zero N hdne)
    have hsumne : f * (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d)
        + (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
          * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) d ≠ 0 := by
      rw [← hkey]
      exact sub_ne_zero.mpr hne
    have hmin := ord_add_min (cuspInftyBar N) ht1 ht2 hsumne
    rw [(cuspInftyBar N).ord_mul hf hsub2,
      (cuspInftyBar N).ord_mul hsub1 (algebraMap_ne_zero N hdne),
      Place.ord_algebraMap] at hmin
    rw [hkey]
    omega

private theorem isValueAt_inv {f : modularFunctionFieldBar N} {c : AlgebraicClosure ℚ}
    (hf : f ≠ 0) (h0 : (cuspInftyBar N).ord f = 0) (hc : c ≠ 0) (hv : IsValueAt N f c) :
    IsValueAt N f⁻¹ c⁻¹ := by
  rcases hv with rfl | h1
  · exact Or.inl
      (map_inv₀ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) c).symm
  · refine Or.inr ?_
    have hcF := algebraMap_ne_zero N hc
    have hsubne : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c - f
        ≠ 0 := by
      intro h
      exact ne_zero_of_one_le_ord _ h1
        (by rw [show f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
            = -(algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c - f) from
            (neg_sub _ _).symm, h, neg_zero])
    have h1' : f * f⁻¹ = 1 := mul_inv_cancel₀ hf
    have h2' : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
        * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹ = 1 :=
      mul_inv_cancel₀ hcF
    have hkey : f⁻¹ - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c⁻¹
        = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c - f) * f⁻¹
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹ := by
      rw [map_inv₀]
      calc f⁻¹ - (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹
          = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
              * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹) * f⁻¹
            - (f * f⁻¹)
              * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹ := by
            rw [h1', h2', one_mul, one_mul]
        _ = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c - f) * f⁻¹
              * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹ := by
            ring
    rw [hkey, (cuspInftyBar N).ord_mul (mul_ne_zero hsubne (inv_ne_zero hf))
        (inv_ne_zero hcF),
      (cuspInftyBar N).ord_mul hsubne (inv_ne_zero hf),
      (cuspInftyBar N).ord_inv, (cuspInftyBar N).ord_inv, Place.ord_algebraMap]
    have hflip : (cuspInftyBar N).ord
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c - f)
        = (cuspInftyBar N).ord
          (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
      rw [show algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c - f
          = -(f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) from
          (neg_sub _ _).symm, ord_neg]
    omega

private theorem isValueAt_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {f : modularFunctionFieldBar N} {c : AlgebraicClosure ℚ} (hv : IsValueAt N f c) :
    IsValueAt N (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f) (σ c) := by
  have hmap : arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
        • algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (σ c) := by
    rw [SemilinearAut.smul_algebraMap]
    rfl
  rcases hv with rfl | h1
  · exact Or.inl hmap
  · refine Or.inr ?_
    have hrw : arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (σ c)
        = arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
          • (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
      rw [smul_sub, hmap]
    rw [hrw]
    have hord := SemilinearAut.ord_smul (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ)
      (cuspInftyBar N)
      (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
    rw [ModularCurve.arithmeticGalois_smul_cuspInftyBar] at hord
    rw [hord]
    exact h1

private theorem eq_algebraMap_of_forall_ord_nonneg {f : modularFunctionFieldBar N} (hf : f ≠ 0)
    (h : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ v.ord f) :
    ∃ c, f = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c := by
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hall : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord f = 0 := by
    obtain ⟨Df, hDf, hdeg⟩ :=
      HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf
    have hDf0 : Df = 0 := divisor_eq_zero_of_effective N
      (fun v => by rw [hDf v]; exact h v) hdeg
    intro v
    have hv := hDf v
    rw [hDf0] at hv
    simpa using hv.symm
  obtain ⟨c, hc⟩ := exists_isValueAt N (h (cuspInftyBar N))
  rcases hc with heq | h1
  · exact ⟨c, heq⟩
  · exfalso
    have hcne : c ≠ 0 := value_ne_zero N hf (hall (cuspInftyBar N)) (Or.inr h1)
    have hgne : f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ≠ 0 :=
      ne_zero_of_one_le_ord _ h1
    have hg0 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        0 ≤ v.ord (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
      intro v
      have hrw : f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
          = f + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (-c) := by
        rw [map_neg]; ring
      have hmin := ord_add_min v hf (algebraMap_ne_zero N (neg_ne_zero.mpr hcne))
        (by rw [← hrw]; exact hgne)
      rw [← hrw, hall v, Place.ord_algebraMap] at hmin
      omega
    obtain ⟨Dg, hDg, hdegg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
      (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) hgne
    have hDg0 : Dg = 0 := divisor_eq_zero_of_effective N
      (fun v => by rw [hDg v]; exact hg0 v) hdegg
    have h0 := hDg (cuspInftyBar N)
    rw [hDg0] at h0
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h0
    omega

private theorem eq_of_ord_eq_of_isValueAt_one {x y : modularFunctionFieldBar N}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hord : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      v.ord x = v.ord y)
    (hvx : IsValueAt N x 1) (hvy : IsValueAt N y 1) : x = y := by
  have hx0 : (cuspInftyBar N).ord x = 0 := (ord_eq_zero_of_value N one_ne_zero hvx).2
  have hy0 : (cuspInftyBar N).ord y = 0 := (ord_eq_zero_of_value N one_ne_zero hvy).2
  have hyi : y⁻¹ ≠ 0 := inv_ne_zero hy
  have hr0 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 ≤ v.ord (x * y⁻¹) := by
    intro v
    rw [ord_mul_inv v hx hy, hord v]
    omega
  obtain ⟨c, hc⟩ := eq_algebraMap_of_forall_ord_nonneg N (mul_ne_zero hx hyi) hr0
  have hvinv : IsValueAt N y⁻¹ 1 := by
    have := isValueAt_inv N hy hy0 one_ne_zero hvy
    rwa [inv_one] at this
  have hyi0 : (cuspInftyBar N).ord y⁻¹ = 0 := by
    rw [(cuspInftyBar N).ord_inv, hy0]
    omega
  have hv1 : IsValueAt N (x * y⁻¹) 1 := by
    have := isValueAt_mul N hx hyi hx0 hyi0 hvx hvinv
    rwa [mul_one] at this
  have hvc : IsValueAt N (x * y⁻¹) c := by
    rw [hc]
    exact isValueAt_algebraMap N c
  have hc1 : c = 1 := isValueAt_unique N hvc hv1
  have hxy1 : x * y⁻¹ = 1 := by
    rw [hc, hc1, map_one]
  calc x = x * y⁻¹ * y := (inv_mul_cancel_right₀ hy x).symm
    _ = 1 * y := by rw [hxy1]
    _ = y := one_mul y

private theorem smul_divisor_apply_cusp (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D) (cuspInftyBar N)
      = D (cuspInftyBar N) := by
  rw [SemilinearAut.divisor_smul_apply]
  congr 1
  rw [inv_smul_eq_iff, ModularCurve.arithmeticGalois_smul_cuspInftyBar]

private theorem exists_normalized_single (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (w : modularFunctionFieldBar N) (hw0 : w ≠ 0)
    (hwd : ∀ v, v.ord w = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v - D₀ v) :
    ∃ w' : modularFunctionFieldBar N, w' ≠ 0 ∧
      (∀ v, v.ord w' = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v - D₀ v) ∧
      IsValueAt N w' 1 := by
  have hwcusp : (cuspInftyBar N).ord w = 0 := by
    rw [hwd (cuspInftyBar N), smul_divisor_apply_cusp N σ D₀]
    omega
  obtain ⟨c, hc⟩ := exists_isValueAt N (le_of_eq hwcusp.symm)
  have hcne : c ≠ 0 := value_ne_zero N hw0 hwcusp hc
  have hicne : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹ ≠ 0 :=
    inv_ne_zero (algebraMap_ne_zero N hcne)
  refine ⟨w * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹,
    mul_ne_zero hw0 hicne, fun v => ?_, ?_⟩
  · rw [v.ord_mul hw0 hicne, v.ord_inv, Place.ord_algebraMap]
    have := hwd v
    omega
  · have hval2 : IsValueAt N
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹ c⁻¹ := by
      rw [← map_inv₀]
      exact isValueAt_algebraMap N c⁻¹
    have hi0 : (cuspInftyBar N).ord
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)⁻¹ = 0 := by
      rw [(cuspInftyBar N).ord_inv, Place.ord_algebraMap]
      omega
    have := isValueAt_mul N hw0 hicne hwcusp hi0 hc hval2
    rwa [mul_inv_cancel₀ hcne] at this

set_option maxHeartbeats 6400000 in

private theorem cocycle_eq (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (x y z : modularFunctionFieldBar N) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (hxd : ∀ v, v.ord x = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v - D₀ v)
    (hyd : ∀ v, v.ord y = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ • D₀) v - D₀ v)
    (hzd : ∀ v, v.ord z
      = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) (σ * τ) • D₀) v - D₀ v)
    (hxv : IsValueAt N x 1) (hyv : IsValueAt N y 1) (hzv : IsValueAt N z 1) :
    z = x * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • y := by
  have hsm0 : arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • y ≠ 0 := by
    intro h
    apply hy0
    have h2 := congrArg
      (fun w => (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ)⁻¹ • w) h
    simpa [inv_smul_smul] using h2
  have hsmord : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      v.ord (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • y)
        = ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ)⁻¹ • v).ord y := by
    intro v
    have h3 := SemilinearAut.ord_smul (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ)
      ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ)⁻¹ • v) y
    rwa [smul_inv_smul] at h3
  have hfixinv : (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ)⁻¹ • cuspInftyBar N
      = cuspInftyBar N := by
    rw [inv_smul_eq_iff, ModularCurve.arithmeticGalois_smul_cuspInftyBar]
  have hxcusp : (cuspInftyBar N).ord x = 0 :=
    (ord_eq_zero_of_value N one_ne_zero hxv).2
  have hsmcusp : (cuspInftyBar N).ord
      (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • y) = 0 := by
    rw [hsmord (cuspInftyBar N), hfixinv]
    exact (ord_eq_zero_of_value N one_ne_zero hyv).2
  have hsmval : IsValueAt N (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • y) 1 := by
    have h4 := isValueAt_smul N σ hyv
    rwa [map_one] at h4
  refine eq_of_ord_eq_of_isValueAt_one N hz0 (mul_ne_zero hx0 hsm0) ?_ hzv ?_
  · intro v
    rw [v.ord_mul hx0 hsm0, hsmord v, hzd v, hxd v, hyd _,
      show (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ • D₀)
          ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ)⁻¹ • v)
        = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
            • (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ • D₀)) v from
        (SemilinearAut.divisor_smul_apply _ _ _).symm,
      show D₀ ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ)⁻¹ • v)
        = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v from
        (SemilinearAut.divisor_smul_apply _ _ _).symm,
      ← mul_smul, ← map_mul]
    omega
  · have h5 := isValueAt_mul N hx0 hsm0 hxcusp hsmcusp hxv hsmval
    rwa [mul_one] at h5

set_option maxHeartbeats 3200000 in

private theorem exists_normalized_cocycle (K' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hprin : ∀ σ ∈ K'.fixingSubgroup, ∃ w : modularFunctionFieldBar N, w ≠ 0 ∧
      ∀ v, v.ord w = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v - D₀ v) :
    ∃ u : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → modularFunctionFieldBar N,
      (∀ σ ∈ K'.fixingSubgroup, u σ ≠ 0 ∧
        (∀ v, v.ord (u σ)
          = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v - D₀ v) ∧
        IsValueAt N (u σ) 1) ∧
      (∀ σ ∈ K'.fixingSubgroup, ∀ τ ∈ K'.fixingSubgroup,
        u (σ * τ) = u σ * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • u τ) ∧
      (∀ τ ∈ K'.fixingSubgroup,
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ • D₀ = D₀ → u τ = 1) := by
  classical
  have hnorm : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ w : modularFunctionFieldBar N, σ ∈ K'.fixingSubgroup →
        (w ≠ 0 ∧ (∀ v, v.ord w
            = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v - D₀ v) ∧
          IsValueAt N w 1) := by
    intro σ
    by_cases hσ : σ ∈ K'.fixingSubgroup
    · obtain ⟨w, hw0, hwd⟩ := hprin σ hσ
      obtain ⟨w', hw'⟩ := exists_normalized_single N σ D₀ w hw0 hwd
      exact ⟨w', fun _ => hw'⟩
    · exact ⟨1, fun hmem => absurd hmem hσ⟩
  choose u hu using hnorm
  refine ⟨u, fun σ hσ => hu σ hσ, ?_, ?_⟩
  · intro σ hσ τ hτ
    obtain ⟨hs0, hsspec, hsval⟩ := hu σ hσ
    obtain ⟨ht0, htspec, htval⟩ := hu τ hτ
    obtain ⟨hst0, hstspec, hstval⟩ := hu (σ * τ) (mul_mem hσ hτ)
    exact cocycle_eq N σ τ D₀ (u σ) (u τ) (u (σ * τ)) hs0 ht0 hst0 hsspec htspec hstspec
      hsval htval hstval
  · intro τ hτ hfix
    obtain ⟨ht0, htspec, htval⟩ := hu τ hτ
    refine eq_of_ord_eq_of_isValueAt_one N ht0 one_ne_zero ?_ htval (isValueAt_one N)
    intro v
    rw [htspec v, hfix, Place.ord_one]
    omega

end Modular

end P4M

private theorem cure_isAlgebraic : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
private theorem cure_isAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  (isAlgClosure_iff (k := ℚ) (K := AlgebraicClosure ℚ)).mpr ⟨inferInstance, cure_isAlgebraic⟩
attribute [local instance] cure_isAlgClosure
#synth IsGalois ℚ (AlgebraicClosure ℚ)

section Aux2A2
variable (N : ℕ) [NeZero N]
local notation "aG" => arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N)
local notation "F̄" => modularFunctionFieldBar N
local notation "ℚ̄" => AlgebraicClosure ℚ

omit [NeZero N] in

private theorem P4_smul_divisor_eq_of_support_fixed (g : SemilinearAut ℚ̄ F̄)
    (D : Divisor ℚ̄ F̄) (hD : ∀ v ∈ D.support, g • v = v) :
    g • D = D := by
  rw [SemilinearAut.divisor_smul_def,
    Finsupp.mapDomain_congr (f := (g • ·)) (g := id) (fun v hv => hD v hv),
    Finsupp.mapDomain_id]

private theorem P4_finite_level (D : Divisor ℚ̄ F̄) (f₀ : F̄) :
    ∃ L₀ : IntermediateField ℚ ℚ̄, FiniteDimensional ℚ L₀ ∧
      (∀ σ ∈ L₀.fixingSubgroup, aG σ • D = D) ∧
      (∀ σ ∈ L₀.fixingSubgroup, aG σ • f₀ = f₀) := by
  classical

  have chP : ∀ v : Place ℚ̄ F̄, ∃ Lv : IntermediateField ℚ ℚ̄,
      FiniteDimensional ℚ Lv ∧ ∀ σ ∈ Lv.fixingSubgroup, aG σ • v = v :=
    MWFL.exists_finiteDimensional_fixingSubgroup_smul_eq_place N
  obtain ⟨Lf, hLfFD, hLf⟩ := MWFL.exists_finiteDimensional_fixingSubgroup_smul_eq_fun N f₀
  set Lv : Place ℚ̄ F̄ → IntermediateField ℚ ℚ̄ := fun v => (chP v).choose with hLvdef
  have hLvFD : ∀ v, FiniteDimensional ℚ (Lv v) := fun v => (chP v).choose_spec.1
  have hLvFix : ∀ v, ∀ σ ∈ (Lv v).fixingSubgroup, aG σ • v = v :=
    fun v => (chP v).choose_spec.2

  refine ⟨(⨆ v ∈ D.support, Lv v) ⊔ Lf, ?_, ?_, ?_⟩
  · haveI : ∀ v, FiniteDimensional ℚ (Lv v) := hLvFD
    exact IntermediateField.finiteDimensional_sup _ _
  · intro σ hσ
    refine P4_smul_divisor_eq_of_support_fixed N (aG σ) D (fun v hv => ?_)
    have hle : Lv v ≤ (⨆ v ∈ D.support, Lv v) ⊔ Lf :=
      (le_iSup_of_le v (le_iSup (fun (_ : v ∈ D.support) => Lv v) hv)).trans le_sup_left
    exact hLvFix v σ (IntermediateField.fixingSubgroup_le hle hσ)
  · intro σ hσ
    exact hLf σ (IntermediateField.fixingSubgroup_le le_sup_right hσ)

#check @P4_finite_level

private theorem P4_fixingSubgroup_finiteIndex (L₀ : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ L₀] :
    L₀.fixingSubgroup.FiniteIndex :=
  ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index _ L₀]; exact Module.finrank_pos.ne'⟩

omit [NeZero N] in

private theorem P4_ord_smul_eq_inv_smul (g : SemilinearAut ℚ̄ F̄) (v : Place ℚ̄ F̄) (f : F̄) :
    v.ord (g • f) = (g⁻¹ • v).ord f := by
  have h := SemilinearAut.ord_smul g (g⁻¹ • v) f
  rwa [smul_inv_smul] at h

omit [NeZero N] in

private def P4_rieszSubmodule (D : Divisor ℚ̄ F̄) : Submodule ℚ̄ F̄ where
  carrier := {f | f = 0 ∨ ∀ v : Place ℚ̄ F̄, 0 ≤ D v + v.ord f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hfV hgV
    rcases eq_or_ne (f + g) 0 with h0 | h0
    · exact Or.inl h0
    rcases eq_or_ne f 0 with rfl | hfne
    · rwa [zero_add]
    rcases eq_or_ne g 0 with rfl | hgne
    · rwa [add_zero]
    have hf : ∀ v : Place ℚ̄ F̄, 0 ≤ D v + v.ord f := hfV.resolve_left hfne
    have hg : ∀ v : Place ℚ̄ F̄, 0 ≤ D v + v.ord g := hgV.resolve_left hgne
    refine Or.inr (fun v => ?_)
    have hmin := P4M.ord_add_min v hfne hgne h0
    rcases min_cases (v.ord f) (v.ord g) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] at hmin
    · linarith [hf v]
    · linarith [hg v]
  smul_mem' := by
    intro c f hfV
    rcases eq_or_ne c 0 with rfl | hc
    · rw [zero_smul]; exact Or.inl rfl
    rcases eq_or_ne f 0 with rfl | hfne
    · rw [smul_zero]; exact Or.inl rfl
    have hf : ∀ v : Place ℚ̄ F̄, 0 ≤ D v + v.ord f := hfV.resolve_left hfne
    refine Or.inr (fun v => ?_)
    have hcne : algebraMap ℚ̄ (F̄ : Type _) c ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (algebraMap ℚ̄ (F̄ : Type _)).injective]; exact hc
    rw [Algebra.smul_def, v.ord_mul hcne hfne, v.ord_algebraMap, zero_add]
    exact hf v

omit [NeZero N] in
private theorem P4_mem_rieszSubmodule {D : Divisor ℚ̄ F̄} {f : F̄} :
    f ∈ P4_rieszSubmodule N D ↔ (f = 0 ∨ ∀ v : Place ℚ̄ F̄, 0 ≤ D v + v.ord f) := Iff.rfl

omit [NeZero N] in

private theorem P4_twistStable (D : Divisor ℚ̄ F̄) (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄)
    (u : F̄) (hu0 : u ≠ 0)
    (hu : ∀ v, v.ord u = (aG σ • D) v - D v)
    {f : F̄} (hf : f ∈ P4_rieszSubmodule N D) :
    u * (aG σ • f) ∈ P4_rieszSubmodule N D := by
  rcases eq_or_ne f 0 with rfl | hfne
  · rw [smul_zero, mul_zero]; exact Or.inl rfl
  have hfV : ∀ v : Place ℚ̄ F̄, 0 ≤ D v + v.ord f := hf.resolve_left hfne
  have hσf : aG σ • f ≠ 0 := by
    rw [SemilinearAut.smul_def]; exact (RingEquiv.map_ne_zero_iff _).mpr hfne
  refine Or.inr (fun v => ?_)
  rw [v.ord_mul hu0 hσf, hu v, SemilinearAut.divisor_smul_apply,
    P4_ord_smul_eq_inv_smul N (aG σ) v f]
  have hkey := hfV ((aG σ)⁻¹ • v)
  linarith

omit [NeZero N] in

private theorem P4_pic0_mk_eq_mk {D E : Divisor.degZero (K := ℚ̄) (F := F̄)} :
    Pic0.mk D = Pic0.mk E ↔
      ((D : Divisor ℚ̄ F̄) - E : Divisor ℚ̄ F̄) ∈ Divisor.principal (K := ℚ̄) (F := F̄) := by
  change QuotientAddGroup.mk D = QuotientAddGroup.mk E ↔ _
  rw [eq_comm, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have hcoe : ((-E + D : Divisor.degZero (K := ℚ̄) (F := F̄)) : Divisor ℚ̄ F̄)
      = (D : Divisor ℚ̄ F̄) - E := by
    change ((Divisor.degZero (K := ℚ̄) (F := F̄)).subtype) (-E + D) = _
    rw [map_add, map_neg, neg_add_eq_sub]; rfl
  rw [show ((-E + D : Divisor.degZero (K := ℚ̄) (F := F̄)) : Divisor ℚ̄ F̄)
      = (D : Divisor ℚ̄ F̄) - E from hcoe]

omit [NeZero N] in

private theorem P4_smul_sub_mem_principal (E₀ : Divisor.degZero (K := ℚ̄) (F := F̄))
    (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (hfix : σ • Pic0.mk E₀ = Pic0.mk E₀) :
    ((aG σ • (E₀ : Divisor ℚ̄ F̄)) - E₀ : Divisor ℚ̄ F̄)
      ∈ Divisor.principal (K := ℚ̄) (F := F̄) := by
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk] at hfix
  have h := (P4_pic0_mk_eq_mk N).mp hfix
  rw [SemilinearAut.coe_degZeroSMulHom] at h
  exact h

end Aux2A2

private theorem p4n_cure_isAlgebraic : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
private theorem p4n_cure_isAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  (isAlgClosure_iff (k := ℚ) (K := AlgebraicClosure ℚ)).mpr ⟨inferInstance, p4n_cure_isAlgebraic⟩

section P4Aux1Descent

variable {N : ℕ}

private theorem p4n_smul_algebraMap_mul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (a : AlgebraicClosure ℚ) (f : modularFunctionFieldBar N) :
    arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ •
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a * f) =
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (σ a) *
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f := by
  rw [smul_mul', SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois]
  rfl

private theorem p4n_finiteIndex_fixingSubgroup (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L₀] : L₀.fixingSubgroup.FiniteIndex :=
  ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index _ L₀]; exact Module.finrank_pos.ne'⟩

set_option maxHeartbeats 3200000 in

private theorem p4n_descent (Γ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀]
    (u : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → modularFunctionFieldBar N)
    (f₀ : modularFunctionFieldBar N) (hf₀ : f₀ ≠ 0)
    (W : Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hcoc : ∀ σ ∈ Γ, ∀ τ ∈ Γ,
      u (σ * τ) = u σ * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • u τ)
    (hlev : ∀ τ ∈ Γ, τ ∈ L₀.fixingSubgroup →
      u τ = 1 ∧ arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ • f₀ = f₀)
    (hf₀W : f₀ ∈ W)
    (hW : ∀ σ ∈ Γ, ∀ f ∈ W, u σ * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f ∈ W) :
    ∃ f ∈ W, f ≠ 0 ∧
      ∀ σ ∈ Γ, u σ * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f = f := by
  classical

  haveI : L₀.fixingSubgroup.FiniteIndex := p4n_finiteIndex_fixingSubgroup L₀
  let H : Subgroup Γ := L₀.fixingSubgroup.subgroupOf Γ
  haveI : H.FiniteIndex := inferInstance
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _

  have hmul : ∀ σ ∈ Γ, ∀ τ ∈ Γ, ∀ f : modularFunctionFieldBar N,
      u (σ * τ) * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) (σ * τ) • f =
        u σ * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ •
          (u τ * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ • f) := by
    intro σ hσ τ hτ f
    rw [hcoc σ hσ τ hτ]
    simp only [map_mul, mul_smul, smul_mul', mul_assoc]

  have hHfix : ∀ τ ∈ Γ, τ ∈ L₀.fixingSubgroup →
      ∀ a : L₀, u τ * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ •
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a * f₀) =
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a * f₀ := by
    intro τ hτ hτL a
    obtain ⟨hu1, hfix⟩ := hlev τ hτ hτL
    rw [p4n_smul_algebraMap_mul, hfix, hu1, one_mul,
      (IntermediateField.mem_fixingSubgroup_iff L₀ _).mp hτL (a : AlgebraicClosure ℚ) a.2]

  have hout : ∀ (γ : Γ) (a : L₀),
      u (((QuotientGroup.mk γ : Γ ⧸ H).out : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) *
          arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) (((QuotientGroup.mk γ : Γ ⧸ H).out : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) •
            (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a * f₀) =
        u (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) •
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a * f₀) := by
    intro γ a
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H γ
    rw [hh, Subgroup.coe_mul Γ γ (h : Γ), hmul _ γ.2 _ (h : Γ).2,
      hHfix _ (h : Γ).2 (Subgroup.mem_subgroupOf.mp h.2) a]

  let w : L₀ → modularFunctionFieldBar N := fun a =>
    ∑ q : Γ ⧸ H, u ((q.out : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) ((q.out : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) •
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a * f₀)

  have hwW : ∀ a, w a ∈ W := by
    intro a
    refine Submodule.sum_mem _ fun q _ => hW _ (q.out : Γ).2 _ ?_
    rw [← Algebra.smul_def]
    exact W.smul_mem _ hf₀W

  have hwfix : ∀ (a : L₀) (σ : Γ),
      u (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • w a = w a := by
    intro a σ
    simp only [w, Finset.smul_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun q => ?_
    have key : MulAction.toPerm σ q = QuotientGroup.mk (σ * q.out) := by
      rw [MulAction.toPerm_apply]
      exact (MulAction.Quotient.coe_smul_out H σ q).symm
    rw [key, hout (σ * q.out) a, Subgroup.coe_mul Γ σ q.out, hmul _ σ.2 _ (q.out : Γ).2]

  obtain ⟨a, ha⟩ : ∃ a : L₀, w a ≠ 0 := by
    by_contra! hzero
    let χ : Γ ⧸ H → (L₀ →* modularFunctionFieldBar N) := fun q =>
      { toFun := fun a => algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (((q.out : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
        map_one' := by simp
        map_mul' := fun a b => by simp }
    have hχ : ∀ (q : Γ ⧸ H) (a : L₀), χ q a = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (((q.out : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a) := fun q a => rfl

    have hχinj : Function.Injective χ := by
      intro q₁ q₂ h
      rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul Γ q₁.out⁻¹ q₂.out, Subgroup.coe_inv Γ q₁.out,
        IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' := congrArg (fun φ : L₀ →* modularFunctionFieldBar N => φ ⟨x, hx⟩) h
      simp only [hχ] at hx'
      have hinj := (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective hx'
      rw [AlgEquiv.mul_apply, ← hinj, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have hli : LinearIndependent (modularFunctionFieldBar N)
        (fun q : Γ ⧸ H => ((χ q : L₀ →* modularFunctionFieldBar N) : L₀ → modularFunctionFieldBar N)) :=
      (linearIndependent_monoidHom L₀ (modularFunctionFieldBar N)).comp χ hχinj

    have hg := Fintype.linearIndependent_iff.mp hli
      (fun q => u ((q.out : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) ((q.out : Γ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • f₀) ?_
      (QuotientGroup.mk 1)
    · have h1 := hout 1 1
      simp only [OneMemClass.coe_one, map_one, one_mul, one_smul] at h1
      rw [(hlev 1 Γ.one_mem L₀.fixingSubgroup.one_mem).1, one_mul] at h1
      exact hf₀ (h1.symm.trans hg)
    · funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hχ]
      have hx := hzero x
      simp only [w, p4n_smul_algebraMap_mul] at hx
      refine Eq.trans ?_ hx
      exact Finset.sum_congr rfl fun q _ => by ring
  exact ⟨w a, hwW a, ha, fun σ hσ => hwfix a ⟨σ, hσ⟩⟩

end P4Aux1Descent

set_option maxHeartbeats 3200000 in
theorem solution (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f)
    (c : JZero N) (hc : c ∈ JZero N ^+ ↥K.fixingSubgroup) :
    ∃ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
      (∀ v, 0 ≤ D v) ∧
      (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
          + (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
          arithmeticGalois (modularFunctionFieldFull N) σ • D = D) ∧
      Pic0.mk E = c := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N

  obtain ⟨E₀, hE₀⟩ := Pic0.mk_surjective c
  set inftyDiv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 with hinftyDiv
  set D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    (E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) + inftyDiv with hD₀def
  have hinfty_smul : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • inftyDiv = inftyDiv := by
    intro σ
    rw [hinftyDiv, Finsupp.smul_single, smul_eq_mul, mul_one, SemilinearAut.smul_single,
      arithmeticGalois_smul_cuspInftyBar N σ]
  have hdegD₀ : Divisor.degree D₀ = g' := by
    rw [hD₀def, map_add, (Divisor.mem_degZero.mp E₀.2), zero_add, hinftyDiv,
      Finsupp.smul_single, smul_eq_mul, mul_one, Divisor.degree_single,
      deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N), Nat.cast_one, mul_one]
  obtain ⟨f₀, hf₀ne, hf₀V⟩ := hR D₀ (hdegD₀ ▸ le_refl _)

  have hprin : ∀ σ ∈ K.fixingSubgroup, ∃ w : modularFunctionFieldBar N, w ≠ 0 ∧
      ∀ v, v.ord w
        = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v - D₀ v := by
    intro σ hσ
    have hfix : σ • Pic0.mk E₀ = Pic0.mk E₀ := hE₀ ▸ (hc ⟨σ, hσ⟩)
    obtain ⟨w, hwne, hw⟩ := P4_smul_sub_mem_principal N E₀ σ hfix
    refine ⟨w, hwne, fun v => ?_⟩
    have key : (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v - D₀ v
        = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ •
            (E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) v
          - (E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v := by
      rw [hD₀def, smul_add, hinfty_smul σ]
      simp only [Finsupp.add_apply]
      ring
    rw [key, ← Finsupp.sub_apply, hw v]

  obtain ⟨L₀, hL₀FD, hDfix, hf₀fix⟩ := P4_finite_level N D₀ f₀
  haveI := hL₀FD
  haveI := P4_fixingSubgroup_finiteIndex L₀

  obtain ⟨u, hu, hcoc, hu1⟩ := P4M.exists_normalized_cocycle N K D₀ hprin

  have hlev : ∀ τ ∈ K.fixingSubgroup, τ ∈ L₀.fixingSubgroup →
      u τ = 1 ∧ arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ • f₀ = f₀ :=
    fun τ hτ hτL => ⟨hu1 τ hτ (hDfix τ hτL), hf₀fix τ hτL⟩

  have hf₀W : f₀ ∈ P4_rieszSubmodule N D₀ := Or.inr hf₀V
  have hW : ∀ σ ∈ K.fixingSubgroup, ∀ f ∈ P4_rieszSubmodule N D₀,
      u σ * arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f
        ∈ P4_rieszSubmodule N D₀ := by
    intro σ hσ f hf
    obtain ⟨hu0, huspec, _⟩ := hu σ hσ
    exact P4_twistStable N D₀ σ (u σ) hu0 huspec hf

  obtain ⟨f, hfW, hfne, hfeq⟩ := p4n_descent K.fixingSubgroup L₀ u f₀ hf₀ne
    (P4_rieszSubmodule N D₀) hcoc hlev hf₀W hW
  have hfV : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 ≤ D₀ v + v.ord f := ((P4_mem_rieszSubmodule N).mp hfW).resolve_left hfne

  obtain ⟨Df, hDf, hDfdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hfne
  set D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := D₀ + Df with hDdef
  set EDf : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) :=
    ⟨Df, Divisor.mem_degZero.mpr hDfdeg⟩ with hEDfdef
  refine ⟨D, E₀ + EDf, ?_, ?_, ?_, ?_⟩
  ·
    intro v
    rw [hDdef, Finsupp.add_apply, hDf]
    exact hfV v
  ·
    rw [AddSubgroup.coe_add, hDdef, hD₀def]
    exact add_right_comm _ _ _
  ·
    intro σ hσ
    obtain ⟨hu0, huspec, _⟩ := hu σ hσ
    have hσf : arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f
        ≠ 0 := by
      rw [SemilinearAut.smul_def]
      exact (RingEquiv.map_ne_zero_iff _).mpr hfne
    ext v
    have hDfv1 : (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
          • Df) v
        = v.ord (arithmeticGalois (L := AlgebraicClosure ℚ)
            (modularFunctionFieldFull N) σ • f) := by
      rw [SemilinearAut.divisor_smul_apply, hDf, ← P4_ord_smul_eq_inv_smul N
        (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ) v f]
    have h2 : v.ord (u σ) + v.ord (arithmeticGalois (L := AlgebraicClosure ℚ)
        (modularFunctionFieldFull N) σ • f) = v.ord f := by
      rw [← v.ord_mul hu0 hσf, hfeq σ hσ]
    have h1 := huspec v
    calc (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D) v
        = (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D₀) v
          + (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
              • Df) v := by
          rw [hDdef, smul_add, Finsupp.add_apply]
      _ = D₀ v + v.ord f := by rw [hDfv1]; omega
      _ = D v := by
          have hDv : D v = D₀ v + v.ord f := by
            rw [hDdef, Finsupp.add_apply, hDf]
          exact hDv.symm
  ·
    have hcoe : ((E₀ + EDf : Divisor.degZero (K := AlgebraicClosure ℚ)
          (F := ↥(modularFunctionFieldBar N))) : Divisor (AlgebraicClosure ℚ)
          (modularFunctionFieldBar N))
        - (E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = Df := by
      rw [AddSubgroup.coe_add]
      exact add_sub_cancel_left _ _
    have hDfprin : Df ∈ Divisor.principal (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar N)) := ⟨f, hfne, hDf⟩
    rw [← hE₀]
    exact (P4_pic0_mk_eq_mk N).mpr (by rw [hcoe]; exact hDfprin)

end S_ModularCurve_JZero_exists_galoisStable_rep
end P2MW
export P2MW.S_ModularCurve_JZero_exists_galoisStable_rep (solution)

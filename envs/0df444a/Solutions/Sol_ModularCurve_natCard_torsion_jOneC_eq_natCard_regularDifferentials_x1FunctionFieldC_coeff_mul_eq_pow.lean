-- Prove2me | solution 1 for ModularCurve.natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a4e50ffa-6c9c-5eb2-b2ed-c6e20ab11b38

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicGeometry_KwPthPowerKerDExpansionEngine
import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Theorems.Thm_ModularCurve_theta_mul
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_cartierOperator_existsUnique
import Theorems.Thm_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_apply_eq_inv_smul_D
import Theorems.Thm_AlgebraicCurve_Pic0_range_eq_setOf_cartier_fixed_and_isRegularDiff
import Theorems.Thm_AlgebraicCurve_regularDiffs_eq_regularDifferentials_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero"
p2m_attr_erase "simp" "AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace X1Serre

namespace CartierQExp

open ModularCurve HahnSeries IntermediateField AlgebraicCurve.KwPke AlgebraicCurve.KwCart

section Laurent

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

theorem coeff_pow_char_mul (s : LaurentSeries k) (m : ℤ) :
    (s ^ p).coeff (m * p) = (s.coeff m) ^ p := by
  rw [pow_char_eq_map_frobenius_qExpand p s, HahnSeries.map_coeff, mul_comm,
    qExpand_coeff_mul, frobenius_def]

theorem coeff_pow_char_of_not_dvd (s : LaurentSeries k) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    (s ^ p).coeff n = 0 := by
  rw [pow_char_eq_map_frobenius_qExpand p s, HahnSeries.map_coeff,
    qExpand_coeff_of_not_dvd p s hn, map_zero]

theorem coeff_mul_eq_zero_of_support (x z : LaurentSeries k)
    (hx : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → x.coeff n = 0) (hz : ∀ m : ℤ, z.coeff (m * p) = 0) (n : ℤ) :
    (x * z).coeff (n * p) = 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  by_cases hi : (p : ℤ) ∣ ij.1
  · obtain ⟨c, hc⟩ := hi
    have hj : ij.2 = (n - c) * p := by
      have : ij.2 = n * p - ij.1 := by rw [← hsum]; ring
      rw [this, hc]; ring
    rw [hj, hz, mul_zero]
  · rw [hx _ hi, zero_mul]

theorem coeff_pow_mul_eq_pow (h z w : LaurentSeries k)
    (hzw : ∀ m : ℤ, z.coeff (m * p) = (w.coeff m) ^ p) (n : ℤ) :
    (h ^ p * z).coeff (n * p) = ((h * w).coeff n) ^ p := by
  have hsplit : h ^ p * z = (h * w) ^ p + h ^ p * (z - w ^ p) := by ring
  rw [hsplit, HahnSeries.coeff_add, coeff_pow_char_mul p (h * w) n,
    coeff_mul_eq_zero_of_support p (h ^ p) (z - w ^ p) (fun m hm => coeff_pow_char_of_not_dvd p h hm)
      (fun m => by rw [HahnSeries.coeff_sub, hzw, coeff_pow_char_mul p w m, sub_self]) n,
    add_zero]

theorem coeff_thetaL_mul_char (y : LaurentSeries k) (m : ℤ) :
    (thetaL k y).coeff (m * p) = 0 := by
  rw [thetaL_apply, theta_coeff, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast,
    CharP.cast_eq_zero k p, mul_zero, zero_mul]

theorem thetaL_pow_succ (T : LaurentSeries k) (i : ℕ) :
    thetaL k (T ^ (i + 1)) = (i + 1) • (T ^ i * thetaL k T) := by
  induction i with
  | zero => rw [zero_add, pow_one, pow_zero, one_mul, one_smul]
  | succ i ih =>
    rw [pow_succ, thetaL_apply, theta_mul, ← thetaL_apply, ← thetaL_apply, ih, mul_smul_comm,
      ← mul_assoc, ← pow_succ', add_comm, ← succ_nsmul]

theorem coeff_pow_mul_thetaL_eq_zero (T : LaurentSeries k) {i : ℕ} (hi : ((i + 1 : ℕ) : k) ≠ 0)
    (m : ℤ) : (T ^ i * thetaL k T).coeff (m * p) = 0 := by
  have h := congrArg (fun y : LaurentSeries k => y.coeff (m * p)) (thetaL_pow_succ (k := k) T i)
  beta_reduce at h
  rw [coeff_thetaL_mul_char p, HahnSeries.coeff_nsmul, Pi.smul_apply, nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h.symm with h0 | h0
  · exact absurd h0 hi
  · exact h0

theorem coeff_pow_pred_mul_thetaL (T : LaurentSeries k) (m : ℤ) :
    (T ^ (p - 1) * thetaL k T).coeff (m * p) = ((thetaL k T).coeff m) ^ p := by
  by_cases hT : T = 0
  · subst hT
    rw [map_zero, mul_zero, HahnSeries.coeff_zero, HahnSeries.coeff_zero,
      zero_pow hp.out.ne_zero]
  · have hrw : T ^ (p - 1) * thetaL k T = T ^ p * (T⁻¹ * thetaL k T) := by
      rw [← mul_assoc, ← pow_sub_one_mul hp.out.ne_zero, mul_assoc (T ^ (p - 1)),
        mul_inv_cancel₀ hT, mul_one]
    rw [hrw, coeff_pow_mul_eq_pow p T _ (T⁻¹ * thetaL k T)
      (fun m' => coeff_inv_mul_thetaL_mul_char_eq_pow k p T hT m') m, ← mul_assoc,
      mul_inv_cancel₀ hT, one_mul]

end Laurent

section Sep

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kaehler_adjoin_eq_zero {t : F}
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (ω : Ω[F⁄K⟮t⟯]) : ω = 0 := by
  have hsurj : Function.Surjective (KaehlerDifferential.map K K⟮t⟯ F F) :=
    KaehlerDifferential.map_surjective_of_surjective K K⟮t⟯ F F Function.surjective_id
  have hzero : KaehlerDifferential.map K K⟮t⟯ F F = 0 := by
    have hle : (⊤ : Submodule F Ω[F⁄K]) ≤ LinearMap.ker (KaehlerDifferential.map K K⟮t⟯ F F) := by
      rw [← hspan, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        LinearMap.mem_ker, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply]
      exact (KaehlerDifferential.D K⟮t⟯ F).map_algebraMap (AdjoinSimple.gen K t)
    exact LinearMap.ker_eq_top.mp (top_le_iff.mp hle)
  obtain ⟨η, rfl⟩ := hsurj ω
  rw [hzero, LinearMap.zero_apply]

theorem isSeparable_adjoin_of_span_D_eq_top [Algebra.EssFiniteType K F] {t : F}
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) :
    Algebra.IsSeparable K⟮t⟯ F := by
  haveI : Subsingleton Ω[F⁄K⟮t⟯] := ⟨fun a b => by
    rw [kaehler_adjoin_eq_zero hspan a, kaehler_adjoin_eq_zero hspan b]⟩
  haveI : Algebra.FormallyUnramified K⟮t⟯ F := ⟨inferInstance⟩
  haveI : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  exact Algebra.FormallyUnramified.isSeparable K⟮t⟯ F

theorem isSeparable_of_subfield_le {A B : Subfield F} (hAB : A ≤ B) {x : F}
    (hx : IsSeparable A x) : IsSeparable B x := by
  letI : Algebra A B := (Subfield.inclusion hAB).toAlgebra
  haveI : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact IsSeparable.tower_top B hx

variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem algebraMap_mem_pthPowers [CharP K p] [PerfectField K] (c : K) :
    algebraMap K F c ∈ kw_pke_pthPowers F p := by
  haveI := PerfectField.toPerfectRing (K := K) p
  obtain ⟨c', hc'⟩ := surjective_frobenius K p c
  rw [kw_pke_mem_pthPowers_iff]
  exact ⟨algebraMap K F c', by rw [← map_pow, ← frobenius_def, hc']⟩

theorem hsep_of_span_D_eq_top [CharP K p] [PerfectField K] [Algebra.EssFiniteType K F] {t : F}
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) (x : F) :
    IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x := by
  haveI := isSeparable_adjoin_of_span_D_eq_top hspan
  have hx : IsSeparable K⟮t⟯ x := Algebra.IsSeparable.isSeparable K⟮t⟯ x
  have hle : K⟮t⟯.toSubfield ≤ (kw_pke_expansionField (ℓ := p) t).toSubfield := by
    change Subfield.closure (Set.range (algebraMap K F) ∪ {t}) ≤ _
    rw [Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | hy)
    · exact ((kw_pke_expansionField (ℓ := p) t).algebraMap_mem
        ⟨algebraMap K F c, algebraMap_mem_pthPowers c⟩ :)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.mem_adjoin_simple_self _ y
  exact isSeparable_of_subfield_le hle hx

end Sep

section CartierCoord

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]
variable (C : Ω[F⁄K] →+ Ω[F⁄K])
  (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
  (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)

include hsemi hker in

theorem apply_pow_smul_D_eq_zero (t : F) {i : ℕ} (hi : ((i + 1 : ℕ) : F) ≠ 0) :
    C (t ^ i • KaehlerDifferential.D K F t) = 0 := by
  set a : F := ((i + 1 : ℕ) : F)⁻¹ with ha
  have hn : ((i + 1 : ℕ) : F) ^ p = ((i + 1 : ℕ) : F) := by
    rw [← frobenius_def, map_natCast]
  have hap : a ^ p = a := by
    rw [ha, inv_pow, hn]
  have hD : KaehlerDifferential.D K F (t ^ (i + 1)) =
      ((i + 1 : ℕ) : F) • (t ^ i • KaehlerDifferential.D K F t) := by
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_smul, ← Nat.cast_smul_eq_nsmul F,
      smul_smul, mul_comm]
  have hrw : t ^ i • KaehlerDifferential.D K F t =
      a ^ p • KaehlerDifferential.D K F (t ^ (i + 1)) := by
    rw [hap, hD, smul_smul, ha, inv_mul_cancel₀ hi, one_smul]
  rw [hrw, hsemi, hker, smul_zero]

variable (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)

def lastIdx : Fin p := ⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩

omit [CharP F p] in
theorem val_lastIdx : ((lastIdx : Fin p) : ℕ) = p - 1 := rfl

theorem natCast_succ_ne_zero {i : Fin p} (hi : i ≠ lastIdx) : ((i + 1 : ℕ) : F) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff F p] at h
  have hlt : (i : ℕ) + 1 < p := by
    have h1 : (i : ℕ) < p := i.2
    have h2 : (i : ℕ) ≠ p - 1 := fun h' => hi (Fin.ext (by rw [h', val_lastIdx]))
    omega
  exact absurd (Nat.le_of_dvd (Nat.succ_pos _) h) (not_le.mpr hlt)

variable (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
  (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
  (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x)
  (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)

def coordRoot (ω : Ω[F⁄K]) (i : Fin p) : F :=
  kw_cart_root (kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω) i)

theorem eq_sum_coordRoot_pow_smul (ω : Ω[F⁄K]) :
    ω = ∑ i : Fin p, coordRoot t hdt hspan hsep hdeg ω i ^ p •
      (t ^ (i : ℕ) • KaehlerDifferential.D K F t) := by
  conv_lhs => rw [kw_cart_dtCoord_spec t hdt hspan ω,
    kw_cart_repr_spec t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, coordRoot, kw_cart_root_pow]

include hsemi hker hlog in

theorem apply_eq_coordRoot_last_smul (ω : Ω[F⁄K]) :
    C ω = coordRoot t hdt hspan hsep hdeg ω lastIdx • KaehlerDifferential.D K F t := by
  conv_lhs => rw [eq_sum_coordRoot_pow_smul t hdt hspan hsep hdeg ω]
  rw [map_sum]
  rw [Finset.sum_eq_single (lastIdx : Fin p)]
  · rw [hsemi, val_lastIdx, hlog]
  · intro i _ hi
    rw [hsemi, apply_pow_smul_D_eq_zero C hsemi hker t (natCast_succ_ne_zero hi), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end CartierCoord

section Assembly

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (p : ℕ) [hp : Fact p.Prime] [CharP K p] [CharP F p] [PerfectField K]
  [AlgebraicCurve.IsCurveOver K F]

theorem coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartier_laws
    (hft : Algebra.EssFiniteType K F) (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (σ : F →ₐ[K] LaurentSeries K) (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (ω : Ω[F⁄K]) (n : ℤ) :
    (qExpansionDiffAlong σ (C ω)).coeff n ^ p = (qExpansionDiffAlong σ ω).coeff (n * p) := by
  haveI := hft
  have hspan := kw_cart_hspan_of_isCurveOver hdt
  have hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x :=
    hsep_of_span_D_eq_top (K := K) (p := p) hspan
  have hdeg := kw_cart_minpoly_natDegree_eq (ℓ := p) hdt

  have hω := eq_sum_coordRoot_pow_smul t hdt hspan hsep hdeg ω
  have hC := apply_eq_coordRoot_last_smul C hsemi hker hlog t hdt hspan hsep hdeg ω
  set g := coordRoot t hdt hspan hsep hdeg ω with hg
  set T : LaurentSeries K := σ t with hT
  have hqC : qExpansionDiffAlong σ (C ω) = σ (g lastIdx) * thetaL K T := by
    rw [hC, qExpansionDiffAlong_smul, qExpansionDiffAlong_D]
  have hqω : qExpansionDiffAlong σ ω =
      ∑ i : Fin p, σ (g i) ^ p * (T ^ (i : ℕ) * thetaL K T) := by
    conv_lhs => rw [hω]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_smul, qExpansionDiffAlong_D, map_pow,
      map_pow]
  rw [hqC, hqω, HahnSeries.coeff_sum, Finset.sum_eq_single (lastIdx : Fin p)]
  · rw [val_lastIdx, coeff_pow_mul_eq_pow p _ _ (thetaL K T) (coeff_pow_pred_mul_thetaL p T) n]
  · intro i _ hi
    have hz : ∀ m : ℤ, (T ^ (i : ℕ) * thetaL K T).coeff (m * p) =
        ((0 : LaurentSeries K).coeff m) ^ p := fun m => by
      rw [HahnSeries.coeff_zero, zero_pow hp.out.ne_zero,
        coeff_pow_mul_thetaL_eq_zero p T (natCast_succ_ne_zero (F := K) hi) m]
    rw [coeff_pow_mul_eq_pow p _ _ 0 hz n, mul_zero, HahnSeries.coeff_zero,
      zero_pow hp.out.ne_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Assembly

end CartierQExp

section QExpInj

open ModularCurve

variable {K : Type*} [Field K]

theorem thetaL_jqModC_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have hc := congrArg (fun s : LaurentSeries K => s.coeff (-1 : ℤ)) h
  beta_reduce at hc
  rw [thetaL_apply, theta_coeff, coeff_jqModC_neg_one, HahnSeries.coeff_zero, zsmul_eq_mul,
    mul_one, Int.cast_neg, Int.cast_one, neg_eq_zero] at hc
  exact one_ne_zero hc

variable {F : Type*} [Field F] [Algebra K F] (σ : F →ₐ[K] LaurentSeries K)

theorem D_ne_zero_of_thetaL_ne_zero (y : F) (hy : thetaL K (σ y) ≠ 0) :
    KaehlerDifferential.D K F y ≠ 0 := by
  intro h0
  apply hy
  have h : thetaL K (σ y) = qExpansionDiffAlong σ (KaehlerDifferential.D K F y) :=
    (qExpansionDiffAlong_D σ y).symm
  rw [h, h0, map_zero]

theorem qExpansionDiffAlong_injective [AlgebraicCurve.IsCurveOver K F] (y : F)
    (hy : thetaL K (σ y) ≠ 0) :
    Function.Injective (qExpansionDiffAlong σ) := by
  have hDy := D_ne_zero_of_thetaL_ne_zero σ y hy
  have hspan := (finrank_eq_one_iff_of_nonzero' (KaehlerDifferential.D K F y) hDy).mp
    AlgebraicCurve.IsCurveOver.finrank_kaehler
  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨g, rfl⟩ := hspan ω
  rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_D] at hω
  rcases mul_eq_zero.mp hω with hg | hθ
  · rw [(map_eq_zero σ).mp hg, zero_smul]
  · exact absurd hθ hy

end QExpInj

section Bridge

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
  [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]

theorem isRegularDiff_of_mem_regularDifferentials (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) : IsRegularDiff K F ω := by
  intro v
  obtain ⟨f, hf, hωf⟩ := hω v
  obtain ⟨π, hπ, hdc⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have hu : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨π, hπ⟩
  obtain ⟨w, hw0, hw⟩ :=
    exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver v v.uniformizer_alt π hu hπ
  have hDu : KaehlerDifferential.D K F v.uniformizer_alt ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v hu
  have hDπ : KaehlerDifferential.D K F π ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v hπ
  have hwne : w ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hw
    exact hDπ hw
  have hωu : ω = (f * w) • KaehlerDifferential.D K F v.uniformizer_alt := by
    rw [hωf, hdc, hw, smul_smul]
  have h1 : Place.diffCoeff v.uniformizer_alt ω • KaehlerDifferential.D K F v.uniformizer_alt =
      (f * w) • KaehlerDifferential.D K F v.uniformizer_alt :=
    (Place.diffCoeff_smul_D ⟨f * w, hωu⟩).trans hωu
  have hcoef : Place.diffCoeff v.uniformizer_alt ω = f * w := smul_left_injective F hDu h1
  rw [Place.ordDiff_def, hcoef]
  by_cases hf0 : f = 0
  · rw [hf0, zero_mul, Place.ord_zero]
  · rw [Place.ord_mul _ hf0 hwne, hw0, add_zero]
    exact (Place.mem_iff_ord_nonneg v hf0).mp hf

omit [PerfectField K] in

theorem mem_regularDifferentials_of_isRegularDiff [PerfectField K] {ω : Ω[F⁄K]}
    (h : IsRegularDiff K F ω) : ω ∈ regularDifferentials K F := by
  rw [← regularDiffs_eq_regularDifferentials_of_perfectField]
  exact mem_regularDiffs_of_isRegularDiff h

end Bridge

section Main

open ModularCurve AlgebraicCurve

theorem natCard_torsion_pic0_eq_natCard_regularDifferentials_coeff_mul_eq_pow
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (F : Type*) [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    (σ : F →ₐ[K] LaurentSeries K) (y : F) (hy : thetaL K (σ y) ≠ 0) :
    Nat.card {z : Pic0 K F // p • z = 0} =
      Nat.card {ω : ↥(regularDifferentials K F) //
        ∀ n : ℤ, (qExpansionDiffAlong σ (ω : Ω[F⁄K])).coeff (n * p) =
          (qExpansionDiffAlong σ (ω : Ω[F⁄K])).coeff n ^ p} := by
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p

  obtain ⟨t, ht, hfd, hsep⟩ :=
    AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := hfd
  haveI := hsep
  have hdt : KaehlerDifferential.D K F t ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K t ht

  obtain ⟨C, ⟨hsemi, hker, hlog⟩, -⟩ := AlgebraicCurve.cartierOperator_existsUnique (K := K) (F := F) p t

  obtain ⟨δ, hδinj, hδ⟩ :=
    Pic0.exists_injective_addMonoidHom_torsion_apply_eq_inv_smul_D K F p t ht hsep hdt
  have hrange := Pic0.range_eq_setOf_cartier_fixed_and_isRegularDiff p t C hsemi hker hlog δ hδ

  have hcart : ∀ (ω : Ω[F⁄K]) (n : ℤ),
      (qExpansionDiffAlong σ (C ω)).coeff n ^ p = (qExpansionDiffAlong σ ω).coeff (n * p) :=
    CartierQExp.coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartier_laws p inferInstance t hdt
      σ C hsemi hker hlog
  have hinj := qExpansionDiffAlong_injective σ y hy

  have hfix : ∀ ω : Ω[F⁄K], C ω = ω ↔
      ∀ n : ℤ, (qExpansionDiffAlong σ ω).coeff (n * p) = (qExpansionDiffAlong σ ω).coeff n ^ p := by
    intro ω
    constructor
    · intro hC n
      rw [← hcart ω n, hC]
    · intro hcoef
      have hq : qExpansionDiffAlong σ (C ω) = qExpansionDiffAlong σ ω := by
        ext n
        apply frobenius_inj K p
        rw [frobenius_def, frobenius_def, hcart ω n, hcoef n]
      exact hinj hq

  have e₁ : {z : Pic0 K F // p • z = 0} ≃ ↥(Pic0.torsion K F p) :=
    Equiv.subtypeEquivRight fun z => by
      rw [← natCast_zsmul]
      exact (Pic0.mem_torsion (K := K) (F := F)).symm
  have e₂ : ↥(Pic0.torsion K F p) ≃ ↥(Set.range δ) := Equiv.ofInjective δ hδinj
  have e₃ : ↥(Set.range δ) ≃ {ω : Ω[F⁄K] // C ω = ω ∧ IsRegularDiff K F ω} := Equiv.setCongr hrange
  have e₄ : {ω : Ω[F⁄K] // C ω = ω ∧ IsRegularDiff K F ω} ≃
      {ω : Ω[F⁄K] // ω ∈ regularDifferentials K F ∧
        ∀ n : ℤ, (qExpansionDiffAlong σ ω).coeff (n * p) = (qExpansionDiffAlong σ ω).coeff n ^ p} :=
    Equiv.subtypeEquivRight fun ω => by
      rw [hfix ω]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨mem_regularDifferentials_of_isRegularDiff h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, isRegularDiff_of_mem_regularDifferentials t h1⟩
  have e₅ := (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun ω : Ω[F⁄K] => ω ∈ regularDifferentials K F)
    (fun ω : Ω[F⁄K] => ∀ n : ℤ, (qExpansionDiffAlong σ ω).coeff (n * p) =
      (qExpansionDiffAlong σ ω).coeff n ^ p)).symm
  exact Nat.card_congr ((((e₁.trans e₂).trans e₃).trans e₄).trans e₅)

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]

end Main

end X1Serre

end

open ModularCurve X1Serre in
theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) :
    Nat.card {y : ModularCurve.JOneC M k // p • y = 0} =
      Nat.card {ω : ↥(AlgebraicCurve.regularDifferentials k ↥(ModularCurve.x1FunctionFieldC k M)) //
        ∀ n : ℤ, (ModularCurve.qExpansionDiffAlong (ModularCurve.x1FunctionFieldC k M).val
            (ω : Ω[↥(ModularCurve.x1FunctionFieldC k M)⁄k])).coeff (n * p) =
          (ModularCurve.qExpansionDiffAlong (ModularCurve.x1FunctionFieldC k M).val
            (ω : Ω[↥(ModularCurve.x1FunctionFieldC k M)⁄k])).coeff n ^ p} := by

  obtain ⟨x, hxj, hxt, hxfd⟩ :
      ∃ x : ↥(x1FunctionFieldC k M), (x : LaurentSeries k) = jqModC k ∧ Transcendental k x ∧
        FiniteDimensional (IntermediateField.adjoin k ({x} : Set ↥(x1FunctionFieldC k M)))
          ↥(x1FunctionFieldC k M) :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed k
      (CongruenceSubgroup.Gamma1 M) (T_mem_Gamma1 M)
  have hcurve : AlgebraicCurve.IsCurveOver k ↥(x1FunctionFieldC k M) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxt hxfd
  have hft : Algebra.EssFiniteType k ↥(x1FunctionFieldC k M) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxt hxfd
  have hy : thetaL k ((x1FunctionFieldC k M).val x) ≠ 0 := by
    rw [IntermediateField.coe_val, hxj]; exact thetaL_jqModC_ne_zero
  exact @natCard_torsion_pic0_eq_natCard_regularDifferentials_coeff_mul_eq_pow k _ _ p _ _
    ↥(x1FunctionFieldC k M) _ _ hcurve hft (x1FunctionFieldC k M).val x hy

end S_ModularCurve_natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow
end P2MW
export P2MW.S_ModularCurve_natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow (solution)

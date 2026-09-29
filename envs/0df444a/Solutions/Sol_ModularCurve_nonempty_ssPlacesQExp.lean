-- Prove2me | solution 1 for ModularCurve.nonempty_ssPlacesQExp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7e9be30a-7390-5068-a701-211d157dec39

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_ssPlacesQExp
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve AlgebraicCurve IntermediateField Polynomial
open scoped MatrixGroups

theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] :
    (ssPlacesQExp K Γ p).Nonempty := by
  classical
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
  have hT : ModularGroup.T ∈ Γ := hΓ₁ (by
    refine (CongruenceSubgroup.Gamma1_mem M _).mpr ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T])

  obtain ⟨a, ha⟩ := ModularCurve.ssJSet_nonempty (q := p) (k := K)

  obtain ⟨j, hj, htr, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI := hfd
  haveI : Algebra.IsAlgebraic (↥K⟮j⟯) ↥(qExpFunctionFieldC K Γ) := Algebra.IsAlgebraic.of_finite _ _

  have hjmem : jqModC K ∈ qExpFunctionFieldC K Γ := by rw [← hj]; exact j.2
  have hjeq : j = ⟨jqModC K, hjmem⟩ := Subtype.ext hj
  haveI : Algebra.IsSeparable (↥K⟮j⟯) ↥(qExpFunctionFieldC K Γ) := by
    rw [hjeq]
    haveI : Algebra.IsAlgebraic ↥K⟮(⟨jqModC K, hjmem⟩ : ↥(qExpFunctionFieldC K Γ))⟯ ↥(qExpFunctionFieldC K Γ) := by rw [← hjeq]; infer_instance
    exact ModularCurve.isSeparable_adjoin_jqModC_of_isAlgebraic K (qExpFunctionFieldC K Γ) hjmem

  let e : RatFunc K ≃ₐ[K] ↥K⟮j⟯ := RatFunc.algEquivOfTranscendental j htr
  let v₀ : Place K ↥K⟮j⟯ := Place.congrEquiv e.toRingEquiv (fun c => e.commutes c) (RationalFunctionField.placeOfPoint K a)
  have hord₀ : v₀.ord (AdjoinSimple.gen K j - algebraMap K _ a) = 1 := by
    have h := Place.ord_congrRingEquiv e.toRingEquiv (fun c => e.commutes c) (RationalFunctionField.placeOfPoint K a)
      (algebraMap (Polynomial K) (RatFunc K) (X - C a))
    rw [RationalFunctionField.ord_placeOfPoint_algebraMap a (X_sub_C_ne_zero a), rootMultiplicity_X_sub_C_self,
      Nat.cast_one] at h
    have heX : e RatFunc.X = AdjoinSimple.gen K j := Subtype.ext (RatFunc.algEquivOfTranscendental_X j htr)
    have he : e.toRingEquiv (algebraMap (Polynomial K) (RatFunc K) (X - C a)) = AdjoinSimple.gen K j - algebraMap K _ a := by
      show e (algebraMap (Polynomial K) (RatFunc K) (X - C a)) = _
      rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub, heX, ← RatFunc.algebraMap_eq_C, AlgEquiv.commutes]
    rw [he] at h
    exact h

  obtain ⟨W, hW⟩ := AlgebraicCurve.Place.exists_restrict_eq (K := K) (F' := ↥K⟮j⟯) (M := ↥(qExpFunctionFieldC K Γ)) v₀

  have hpos : 0 < W.ord ((j : ↥(qExpFunctionFieldC K Γ)) - algebraMap K ↥(qExpFunctionFieldC K Γ) a) := by
    have h := W.ord_restrict (F := ↥K⟮j⟯) (AdjoinSimple.gen K j - algebraMap K _ a)
    rw [hW, hord₀, mul_one] at h
    have hmap : algebraMap (↥K⟮j⟯) ↥(qExpFunctionFieldC K Γ) (AdjoinSimple.gen K j - algebraMap K _ a) = (j : ↥(qExpFunctionFieldC K Γ)) - algebraMap K ↥(qExpFunctionFieldC K Γ) a := by
      rw [map_sub, AdjoinSimple.algebraMap_gen, ← IsScalarTower.algebraMap_apply]
    rw [hmap] at h
    rw [h]
    exact_mod_cast W.ramificationIndex_pos (F := ↥K⟮j⟯)

  have hne : (j : ↥(qExpFunctionFieldC K Γ)) - algebraMap K ↥(qExpFunctionFieldC K Γ) a ≠ 0 := by
    intro h0
    apply htr
    have : (j : ↥(qExpFunctionFieldC K Γ)) = algebraMap K ↥(qExpFunctionFieldC K Γ) a := sub_eq_zero.mp h0
    rw [this]
    exact isAlgebraic_algebraMap a

  have hmem : (j : ↥(qExpFunctionFieldC K Γ)) - algebraMap K ↥(qExpFunctionFieldC K Γ) a ∈ W.toValuationSubring := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
    obtain ⟨u, hu⟩ := W.exists_unit_mul_zpow hne hπ
    rw [hu, show W.ord ((j : ↥(qExpFunctionFieldC K Γ)) - algebraMap K ↥(qExpFunctionFieldC K Γ) a) =
        (((W.ord ((j : ↥(qExpFunctionFieldC K Γ)) - algebraMap K ↥(qExpFunctionFieldC K Γ) a)).toNat : ℕ) : ℤ)
        from (Int.toNat_of_nonneg hpos.le).symm, zpow_natCast]
    exact mul_mem (u : W.toValuationSubring).2 (pow_mem (π : W.toValuationSubring).2 _)
  have hjW : (j : ↥(qExpFunctionFieldC K Γ)) ∈ W.toValuationSubring := by
    have h := add_mem hmem (W.algebraMap_mem' a)
    rwa [sub_add_cancel] at h

  have hmax : (⟨_, hmem⟩ : W.toValuationSubring) ∈ IsLocalRing.maximalIdeal W.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 := W.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change W.ord ((j : ↥(qExpFunctionFieldC K Γ)) - algebraMap K ↥(qExpFunctionFieldC K Γ) a) = 0 at h0
    omega
  have hres : IsLocalRing.residue W.toValuationSubring ⟨(j : ↥(qExpFunctionFieldC K Γ)), hjW⟩ =
      algebraMap K W.ResidueField a := by
    have hsplit : (⟨(j : ↥(qExpFunctionFieldC K Γ)), hjW⟩ : W.toValuationSubring) =
        ⟨_, hmem⟩ + ⟨algebraMap K ↥(qExpFunctionFieldC K Γ) a, W.algebraMap_mem' a⟩ := by
      apply Subtype.ext
      show (j : ↥(qExpFunctionFieldC K Γ)) = ((j : ↥(qExpFunctionFieldC K Γ)) - algebraMap K _ a) + algebraMap K _ a
      rw [sub_add_cancel]
    rw [hsplit, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add]
    exact W.residue_algebraMap a
  refine ⟨W, ?_⟩
  rw [mem_ssPlacesQExp_iff]
  refine ⟨j, a, hj, ⟨hjW, hres⟩, ?_⟩
  convert ha

#print axioms solution

end S_ModularCurve_nonempty_ssPlacesQExp
end P2MW
export P2MW.S_ModularCurve_nonempty_ssPlacesQExp (solution)

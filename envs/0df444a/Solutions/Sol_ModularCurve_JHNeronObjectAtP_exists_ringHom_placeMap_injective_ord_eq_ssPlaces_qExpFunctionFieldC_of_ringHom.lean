-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_ringHom_placeMap_injective_ord_eq_ssPlaces_qExpFunctionFieldC_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1bce632c-a841-5696-b5d5-ec963c2098a1

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_ringHom_placeMap_injective_ord_eq_ssPlaces_qExpFunctionFieldC_of_ringHom
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open scoped MatrixGroups

namespace KappaKPlaces

theorem aux (p : ℕ) [Fact p.Prime]
    (κ K : Type*) [Field κ] [Field K] [IsAlgClosed κ] [IsAlgClosed K] [CharP κ p] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (ι : κ →+* K) :
    ∃ (eK : ↥(ModularCurve.qExpFunctionFieldC κ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC K Γ))
      (plK : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) → AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
      (∀ g : ↥(ModularCurve.qExpFunctionFieldC κ Γ),
        ((eK g : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) = ModularCurve.coeffMap ι (g : LaurentSeries κ)) ∧
      (∀ (g : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)),
        (plK v).ord (eK g) = v.ord g) ∧
      (∀ V : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
        V ∈ ModularCurve.ssPlacesQExp K Γ p → ∃ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), plK v = V) ∧
      Function.Injective plK ∧
      (∀ (g : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (V : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
        V ∉ Set.range plK → V.ord (eK g) = 0) ∧
      (∀ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ),
        plK v ∈ ModularCurve.ssPlacesQExp K Γ p ↔ v ∈ ModularCurve.ssPlacesQExp κ Γ p) := by
  classical
  letI : Algebra κ K := ι.toAlgebra
  haveI : AlgebraicCurve.IsCurveOver κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed κ Γ hT
  haveI : AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  obtain ⟨xκ, -, hxκtr, hxκfin⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ Γ hT
  obtain ⟨xK, -, hxKtr, hxKfin⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT

  have hmem : ∀ g : ↥(ModularCurve.qExpFunctionFieldC κ Γ),
      ModularCurve.coeffMap (algebraMap κ K) (g : LaurentSeries κ) ∈ ModularCurve.qExpFunctionFieldC K Γ := by
    intro g
    rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC κ K Γ]
    exact IntermediateField.subset_adjoin K _ ⟨(g : LaurentSeries κ), g.2, rfl⟩
  let eK : ↥(ModularCurve.qExpFunctionFieldC κ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    ((ModularCurve.coeffMap (algebraMap κ K)).comp (SubringClass.subtype (ModularCurve.qExpFunctionFieldC κ Γ))).codRestrict
      (ModularCurve.qExpFunctionFieldC K Γ) (fun g => hmem g)
  have heK' : ∀ g : ↥(ModularCurve.qExpFunctionFieldC κ Γ),
      ((eK g : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) =
        ModularCurve.coeffMap (algebraMap κ K) (g : LaurentSeries κ) := fun _ => rfl
  have heK : ∀ g : ↥(ModularCurve.qExpFunctionFieldC κ Γ),
      ((eK g : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) = ModularCurve.coeffMap ι (g : LaurentSeries κ) :=
    fun _ => rfl
  obtain ⟨ext, hinj, hpre, huniq, himg, hord, hval, hss, hssSurj, hFr⟩ :=
    ModularCurve.exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed p κ K Γ
      ⟨xκ, hxκtr, hxκfin⟩ ⟨xK, hxKtr, hxKfin⟩ eK heK'
  refine ⟨eK, ext, heK, fun g v => hord v g, hssSurj, hinj, ?_, fun v => (hss v).symm⟩

  intro g V hV
  have htop : V.toValuationSubring.comap eK = ⊤ := by
    by_contra h
    exact hV (himg V h)
  have hall : ∀ f : ↥(ModularCurve.qExpFunctionFieldC κ Γ), eK f ∈ V.toValuationSubring := by
    intro f
    have h : f ∈ V.toValuationSubring.comap eK := by rw [htop]; exact ValuationSubring.mem_top f
    exact (ValuationSubring.mem_comap.mp h)
  by_cases hg : g = 0
  · rw [hg, map_zero]; exact V.ord_zero
  · let u : (V.toValuationSubring)ˣ :=
      { val := ⟨eK g, hall g⟩
        inv := ⟨eK g⁻¹, hall g⁻¹⟩
        val_inv := Subtype.ext (by
          show eK g * eK g⁻¹ = 1
          rw [← map_mul, mul_inv_cancel₀ hg, map_one])
        inv_val := Subtype.ext (by
          show eK g⁻¹ * eK g = 1
          rw [← map_mul, inv_mul_cancel₀ hg, map_one]) }
    exact V.ord_coe_unit u

end KappaKPlaces

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (ι : IsLocalRing.ResidueField ↥Pl →+* K) :
    ∃ (eK : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl) →+* ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
      (plK : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) → AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl), ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ι (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) ∧
      (∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) (v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))), (plK v).ord (eK g) = v.ord g) ∧

      (∀ V : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
        V ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p →
          ∃ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)), plK v = V) ∧
      Function.Injective plK ∧

      (∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) (V : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
        V ∉ Set.range plK → V.ord (eK g) = 0) ∧
      (∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
        plK v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p ↔
          v ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (M / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) hp.pos).ne'⟩
  exact KappaKPlaces.aux p (IsLocalRing.ResidueField ↥Pl) K
    (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) (ModularCurve.translation_mem_GammaH _ _) ι

end S_ModularCurve_JHNeronObjectAtP_exists_ringHom_placeMap_injective_ord_eq_ssPlaces_qExpFunctionFieldC_of_ringHom
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_ringHom_placeMap_injective_ord_eq_ssPlaces_qExpFunctionFieldC_of_ringHom (solution)

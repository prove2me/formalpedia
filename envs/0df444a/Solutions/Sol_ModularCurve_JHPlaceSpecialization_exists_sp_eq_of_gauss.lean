-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_sp_eq_of_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/37dd4d1c-c60b-52f8-854d-e28ef88868b5

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_sp_eq_of_gauss
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace PSPPackAux

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
  (A : ValuationSubring (AlgebraicClosure ℚ))
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

theorem deg_sp
    (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (P : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    (sp P).deg = P.deg := by
  have hCO₁ : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
      (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM)).1
  haveI : (JHNeronObjectAtP.ΓN p M H hpM).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  have hCO₂ : IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)
      (ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM))
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed (sp P), IsCurveOver.deg_eq_one_of_isAlgClosed P]

variable (R : RegularProlongation A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
    (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
  (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →
    Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

set_option quotPrecheck false in
local notation "HDIV" => ∀ f : R.integers, R.residue f ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
      ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f)

noncomputable def cr (hdiv : HDIV) : ConstantReduction A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
    (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) where
  integers := R.integers
  residue := R.residue
  placeMap := sp
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem
  deg_placeMap := deg_sp p M H hpM A sp
  mapDomain_placeMap := hdiv

include R in

theorem d5 (hdiv : HDIV) (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hD : ∀ v, D v = v.ord f) :
    ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
      ∀ v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
        Finsupp.mapDomain sp D v' = v'.ord g := by
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hres
  exact ⟨R.residue ⟨_, hc⟩, hres, fun Q =>
    hdiv ⟨_, hc⟩ hres D (fun P => by rw [hD P]; exact (ConstantReduction.ord_smul P hc0 f).symm) Q⟩

theorem d0 (hdiv : HDIV)
    (hq : ∀ (y : LaurentSeries ↥A)
      (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)))
    (g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hg : ((g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hg0 : g ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hD : ∀ v, D v = v.ord f)
    (v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :
    Finsupp.mapDomain sp D v' = v'.ord g := by
  have hyF : coeffMap A.subtype y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := hy ▸ f.2
  obtain ⟨hint, hres'⟩ := hq y hyF
  have hfeq : (⟨coeffMap A.subtype y, hyF⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = f :=
    Subtype.ext hy
  have hg' : R.residue ⟨_, hint⟩ = g := Subtype.ext (hres'.trans hg.symm)
  have hne : R.residue ⟨_, hint⟩ ≠ 0 := hg' ▸ hg0
  have key := hdiv ⟨_, hint⟩ hne D (fun P => by rw [hD P, ← hfeq]) v'
  rwa [hg'] at key

end PSPPackAux

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (R : RegularProlongation A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (hgauss : ∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ∈ R.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (hres : ∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
      (((f : R.integers) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
      ((R.residue f : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y =
        coeffMap (IsLocalRing.residue ↥A) x)

    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
        ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f))

    (huniq : ∀ sp' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
          ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp)

    (hq : ∀ (y : LaurentSeries ↥A)
      (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hsurj : Function.Surjective sp)
    (hinert : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) = sp w))
    (hfrob : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (sp w)))
    :
    ∃ Psp : JHPlaceSpecialization p M H hpM A, Psp.sp = sp := by
  refine ⟨{ sp := sp
            spPic0 := (PSPPackAux.cr p M H hpM A R sp hdiv).pic0Map
            d0_qexp := PSPPackAux.d0 p M H hpM A R sp hdiv hq
            d4 := hsurj
            d5 := PSPPackAux.d5 p M H hpM A R sp hdiv
            d6_inertia := hinert
            d6_frobenius := hfrob
            spPic0_compat := fun D => ⟨(PSPPackAux.cr p M H hpM A R sp hdiv).degZeroMap D, rfl,
              (PSPPackAux.cr p M H hpM A R sp hdiv).pic0Map_mk D⟩ }, rfl⟩

end S_ModularCurve_JHPlaceSpecialization_exists_sp_eq_of_gauss
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_sp_eq_of_gauss (solution)

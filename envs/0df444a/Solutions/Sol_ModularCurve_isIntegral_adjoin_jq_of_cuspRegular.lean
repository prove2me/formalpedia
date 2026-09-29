-- Prove2me | solution 1 for ModularCurve.isIntegral_adjoin_jq_of_cuspRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/da9c5e34-7412-55ba-8500-de2f41a9fb3d

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_adjoin_jq_of_cuspRegular
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

namespace E147CM

open AlgebraicCurve ModularCurve IsLocalRing

theorem isIntegral_adjoin_of_cuspRegular (M' : ℕ) [NeZero M']
    (G : ↥(modularFunctionFieldBar M'))
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord G) :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))} : Set ↥(modularFunctionFieldBar M'))) G := by
  classical
  set jF : ↥(modularFunctionFieldBar M') := (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) with hjFdef
  by_cases hG0 : G = 0
  · rw [hG0]; exact isIntegral_zero

  haveI : (CongruenceSubgroup.Gamma0 M').FiniteIndex := inferInstance
  haveI hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jF} : Set ↥(modularFunctionFieldBar M')))
      ↥(modularFunctionFieldBar M') := by
    refine ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma0 M')
      ?_ (AlgebraicClosure ℚ) (modularFunctionFieldBar M') ?_ jF (by rw [hjFdef])
    · rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
    · show laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M') = _
      rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]

  let R : Subalgebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    Algebra.adjoin (AlgebraicClosure ℚ) ({jF} : Set ↥(modularFunctionFieldBar M'))
  let IC : Subalgebra ↥R ↥(modularFunctionFieldBar M') := integralClosure ↥R ↥(modularFunctionFieldBar M')
  rw [← mem_integralClosure_iff ↥R ↥(modularFunctionFieldBar M')]
  show G ∈ IC
  by_contra hnot
  obtain ⟨V, hVle, hGV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn (R := IC.toSubring) hnot
  have hRV : ∀ x : ↥(modularFunctionFieldBar M'), x ∈ R → x ∈ V := fun x hx =>
    hVle (show x ∈ IC from (mem_integralClosure_iff ↥R ↥(modularFunctionFieldBar M')).mpr (isIntegral_algebraMap (R := ↥R) (A := ↥(modularFunctionFieldBar M')) (x := ⟨x, hx⟩)))
  have hjV : jF ∈ V := hRV _ (Algebra.subset_adjoin (Set.mem_singleton _))
  have hKV : ∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') c ∈ V :=
    fun c => hRV _ (Subalgebra.algebraMap_mem R c)
  by_cases hVtop : V = ⊤
  · exact hGV (hVtop.symm ▸ ValuationSubring.mem_top G)
  obtain ⟨P, hP⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional jF V hKV hVtop
  apply hGV
  rw [← hP]
  apply AlgebraicCurve.Place.mem_of_ord_nonneg P hG0
  apply hreg
  exact AlgebraicCurve.Place.ord_nonneg_of_mem P (hP.symm ▸ hjV)

end E147CM

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M' : ℕ) [NeZero M']
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) :
    IsIntegral ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) g := by
  classical

  have hcore := E147CM.isIntegral_adjoin_of_cuspRegular M'
    (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) hcusp
  set R₀ : Subalgebra ℚ (LaurentSeries ℚ) := Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) with hR₀
  let ε : LaurentSeries ℚ →+* LaurentSeries (AlgebraicClosure ℚ) := coeffEmb (AlgebraicClosure ℚ)
  have hεinj : Function.Injective ε := ε.injective
  let S' : Subalgebra (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) := Algebra.adjoin (AlgebraicClosure ℚ) ({ε jq} : Set (LaurentSeries (AlgebraicClosure ℚ)))

  let RF : Subalgebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))} : Set ↥(modularFunctionFieldBar M'))
  have hRFS : ∀ x : ↥(modularFunctionFieldBar M'), x ∈ RF → (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ S' := by
    intro x hx
    have hle : RF ≤ S'.comap (modularFunctionFieldBar M').val :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Algebra.subset_adjoin (Set.mem_singleton _)))
    exact hle hx
  let φ : ↥RF →+* ↥S' := ((modularFunctionFieldBar M').val.toRingHom.comp RF.val.toRingHom).codRestrict S' (fun x => hRFS x.1 x.2)
  have hS : IsIntegral ↥S' (ε g) :=
    hcore.map_of_comp_eq φ (modularFunctionFieldBar M').val.toRingHom (by ext x; rfl)

  letI algR₀Λ : Algebra ↥R₀ (LaurentSeries (AlgebraicClosure ℚ)) := (ε.comp (algebraMap ↥R₀ (LaurentSeries ℚ))).toAlgebra
  have halgR₀Λ : ∀ r : ↥R₀, algebraMap ↥R₀ (LaurentSeries (AlgebraicClosure ℚ)) r = ε (r : LaurentSeries ℚ) := fun _ => rfl
  have hratS : ∀ c : ℚ, ((c : LaurentSeries (AlgebraicClosure ℚ))) ∈ S' := by
    intro c
    rw [← eq_ratCast ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp (Rat.castHom (AlgebraicClosure ℚ))) c, RingHom.comp_apply]
    exact Subalgebra.algebraMap_mem S' _
  have hR₀S : ∀ r : ↥R₀, ε (r : LaurentSeries ℚ) ∈ S' := by
    intro r
    have hr : (r : LaurentSeries ℚ) ∈ Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) := by rw [← hR₀]; exact r.2
    refine Algebra.adjoin_induction (p := fun y _ => ε y ∈ S') ?_ ?_ ?_ ?_ hr
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · intro c
      rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) c, map_ratCast]
      exact hratS c
    · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
    · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy
  letI algR₀S : Algebra ↥R₀ ↥S' := ((ε.comp (algebraMap ↥R₀ (LaurentSeries ℚ))).codRestrict S' (fun r => hR₀S r)).toAlgebra
  haveI : IsScalarTower ↥R₀ ↥S' (LaurentSeries (AlgebraicClosure ℚ)) := IsScalarTower.of_algebraMap_eq (R := ↥R₀) (S := ↥S') (A := LaurentSeries (AlgebraicClosure ℚ)) (fun _ => rfl)
  have hjqR₀ : jq ∈ R₀ := by rw [hR₀]; exact Algebra.subset_adjoin (Set.mem_singleton jq)
  have hint : ∀ y : LaurentSeries (AlgebraicClosure ℚ), y ∈ S' → IsIntegral ↥R₀ y := by
    intro y hy
    refine Algebra.adjoin_induction (p := fun y _ => IsIntegral ↥R₀ y) ?_ ?_ ?_ ?_ hy
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have : ε jq = algebraMap ↥R₀ (LaurentSeries (AlgebraicClosure ℚ)) ⟨jq, hjqR₀⟩ := rfl
      rw [this]; exact isIntegral_algebraMap
    · intro c
      have h1 : IsIntegral ℚ c := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c).isIntegral
      exact h1.map_of_comp_eq (algebraMap ℚ ↥R₀) (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) (RingHom.ext_rat _ _)
    · intro x y _ _ hx hy; exact hx.add hy
    · intro x y _ _ hx hy; exact hx.mul hy
  let valR₀ : ↥S' →ₐ[↥R₀] LaurentSeries (AlgebraicClosure ℚ) :=
    { toFun := fun x => (x : LaurentSeries (AlgebraicClosure ℚ)), map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  haveI : Algebra.IsIntegral ↥R₀ ↥S' :=
    ⟨fun x => (isIntegral_algHom_iff valR₀ (fun a b h => Subtype.ext h)).mp (hint x x.2)⟩

  have hR₀εg : IsIntegral ↥R₀ (ε g) := isIntegral_trans (ε g) hS
  let εR₀ : LaurentSeries ℚ →ₐ[↥R₀] LaurentSeries (AlgebraicClosure ℚ) :=
    { toFun := ε, map_one' := map_one ε, map_mul' := fun a b => map_mul ε a b, map_zero' := map_zero ε,
      map_add' := fun a b => map_add ε a b, commutes' := fun _ => rfl }
  exact (isIntegral_algHom_iff εR₀ hεinj).mp hR₀εg

end S_ModularCurve_isIntegral_adjoin_jq_of_cuspRegular
end P2MW
export P2MW.S_ModularCurve_isIntegral_adjoin_jq_of_cuspRegular (solution)

-- Prove2me | solution 1 for ModularCurve.exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/25c9573c-e02e-5e78-a194-51949d20aa01

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

namespace EIdemAux

open TateModule

variable {p : ℕ} [Fact p.Prime] {Mg : Type} [AddCommGroup Mg]

section lift

variable (hdiv : ∀ y : Mg, ∃ z : Mg, (p : ℤ) • z = y)

noncomputable def liftSeq (v : Mg) : ℕ → Mg
  | 0 => 0
  | 1 => v
  | (n + 2) => (hdiv (liftSeq v (n + 1))).choose

include hdiv in
omit [Fact p.Prime] in
theorem smul_liftSeq_succ (v : Mg) (hv : (p : ℤ) • v = 0) (n : ℕ) :
    (p : ℤ) • liftSeq hdiv v (n + 1) = liftSeq hdiv v n := by
  cases n with
  | zero => exact hv
  | succ n => exact (hdiv (liftSeq hdiv v (n + 1))).choose_spec

include hdiv in
omit [Fact p.Prime] in
theorem pow_smul_liftSeq (v : Mg) (hv : (p : ℤ) • v = 0) (n : ℕ) :
    ((p ^ n : ℕ) : ℤ) • liftSeq hdiv v n = 0 := by
  induction n with
  | zero => show ((p ^ 0 : ℕ) : ℤ) • (0 : Mg) = 0; rw [smul_zero]
  | succ n ih => rw [pow_succ, Nat.cast_mul, mul_smul, smul_liftSeq_succ hdiv v hv n, ih]

noncomputable def liftTate (v : Mg) (hv : (p : ℤ) • v = 0) : TateModule p Mg :=
  ⟨liftSeq hdiv v, fun n => ⟨pow_smul_liftSeq hdiv v hv n, smul_liftSeq_succ hdiv v hv n⟩⟩

omit [Fact p.Prime] in
theorem proj_one_liftTate (v : Mg) (hv : (p : ℤ) • v = 0) : proj p Mg 1 (liftTate hdiv v hv) = v := rfl

end lift

section act

variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p Mg)]
  [IsScalarTower ℤ_[p] 𝕋 (TateModule p Mg)]

theorem proj_one_smul_eq_of_proj_one_eq (t : 𝕋) {x x' : TateModule p Mg}
    (h : proj p Mg 1 x = proj p Mg 1 x') : proj p Mg 1 (t • x) = proj p Mg 1 (t • x') := by
  rw [← sub_eq_zero, ← map_sub, ← smul_sub]
  have hd : proj p Mg 1 (x - x') = 0 := by rw [map_sub, h, sub_self]
  rw [← pow_smul_shiftOfProjEqZero 1 (x - x') hd, pow_one, smul_algebra_smul_comm,
    show ((p : ℤ_[p])) = ((p : ℕ) : ℤ_[p]) from rfl, proj_apply, natCast_padicInt_smul_apply, ← proj_apply]
  have := torsionBy_proj 1 (t • shiftOfProjEqZero 1 (x - x') hd)
  rwa [pow_one] at this

omit [Fact p.Prime] in
theorem proj_one_mem (z : TateModule p Mg) : (p : ℤ) • proj p Mg 1 z = 0 := by
  have := torsionBy_proj 1 z
  rwa [pow_one] at this

variable (hdiv : ∀ y : Mg, ∃ z : Mg, (p : ℤ) • z = y)
  (A : AddSubgroup Mg) (hA : ∀ v : Mg, v ∈ A ↔ (p : ℤ) • v = 0)

noncomputable def act (t : 𝕋) (v : ↥A) : ↥A :=
  ⟨proj p Mg 1 (t • liftTate hdiv (v : Mg) ((hA v).mp v.2)), (hA _).mpr (proj_one_mem _)⟩

theorem coe_act_of_proj_eq (t : 𝕋) (v : ↥A) (x : TateModule p Mg) (hx : proj p Mg 1 x = v) :
    (act hdiv A hA t v : Mg) = proj p Mg 1 (t • x) :=
  proj_one_smul_eq_of_proj_one_eq t (by rw [proj_one_liftTate, hx])

theorem act_map_add (t : 𝕋) (v w : ↥A) : act hdiv A hA t (v + w) = act hdiv A hA t v + act hdiv A hA t w := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, coe_act_of_proj_eq hdiv A hA t (v + w)
    (liftTate hdiv (v : Mg) ((hA v).mp v.2) + liftTate hdiv (w : Mg) ((hA w).mp w.2))
    (by rw [map_add, proj_one_liftTate, proj_one_liftTate]; rfl), smul_add, map_add]
  rfl

noncomputable def actHom (t : 𝕋) : ↥A →+ ↥A :=
  { toFun := act hdiv A hA t
    map_zero' := by
      have h := act_map_add hdiv A hA t 0 0
      rw [add_zero] at h
      exact add_left_cancel (h.symm.trans (add_zero _).symm)
    map_add' := act_map_add hdiv A hA t }

@[scoped simp] theorem actHom_apply (t : 𝕋) (v : ↥A) : actHom hdiv A hA t v = act hdiv A hA t v := rfl

omit [Fact p.Prime] [Algebra ℤ_[p] 𝕋] [IsScalarTower ℤ_[p] 𝕋 (TateModule p Mg)] in
theorem act_add (t t' : 𝕋) (v : ↥A) : act hdiv A hA (t + t') v = act hdiv A hA t v + act hdiv A hA t' v := by
  apply Subtype.ext
  show proj p Mg 1 ((t + t') • _) = proj p Mg 1 (t • _) + proj p Mg 1 (t' • _)
  rw [add_smul, map_add]

theorem act_mul (t t' : 𝕋) (v : ↥A) : act hdiv A hA (t * t') v = act hdiv A hA t (act hdiv A hA t' v) := by
  apply Subtype.ext
  rw [coe_act_of_proj_eq hdiv A hA t (act hdiv A hA t' v) (t' • liftTate hdiv (v : Mg) ((hA v).mp v.2)) rfl]
  show proj p Mg 1 ((t * t') • _) = proj p Mg 1 (t • (t' • _))
  rw [mul_smul]

theorem act_comm (t t' : 𝕋) (v : ↥A) :
    act hdiv A hA t (act hdiv A hA t' v) = act hdiv A hA t' (act hdiv A hA t v) := by
  rw [← act_mul, ← act_mul, mul_comm]

theorem coe_act_algebraMap (c : ℤ_[p]) (v : ↥A) :
    (act hdiv A hA (algebraMap ℤ_[p] 𝕋 c) v : Mg) = ((c.appr 1 : ℕ) : ℤ) • (v : Mg) := by
  show proj p Mg 1 ((algebraMap ℤ_[p] 𝕋 c) • _) = _
  rw [algebraMap_smul, proj_apply, TateModule.smul_apply, ← proj_apply, proj_one_liftTate]

omit [Fact p.Prime] [Algebra ℤ_[p] 𝕋] [IsScalarTower ℤ_[p] 𝕋 (TateModule p Mg)] in

theorem coe_act_of_levelwise {G : Type} (f : G → (Mg →+ Mg)) (op : G → 𝕋)
    (hop : ∀ (g : G) (x : TateModule p Mg) (n : ℕ),
      ((op g • x : TateModule p Mg) : ℕ → Mg) n = f g ((x : ℕ → Mg) n))
    (g : G) (v : ↥A) : (act hdiv A hA (op g) v : Mg) = f g (v : Mg) := by
  show proj p Mg 1 (op g • _) = _
  rw [proj_apply, hop, ← proj_apply, proj_one_liftTate]

variable {G : Type} (f : G → (Mg →+ Mg)) (op : G → 𝕋)
  (hop : ∀ (g : G) (x : TateModule p Mg) (n : ℕ),
    ((op g • x : TateModule p Mg) : ℕ → Mg) n = f g ((x : ℕ → Mg) n))

include hop in
theorem act_aeval_mem (B : AddSubgroup Mg) (hB : ∀ (g : G) (x : Mg), x ∈ B → f g x ∈ B)
    (P : MvPolynomial G ℤ_[p]) : ∀ v : ↥A, (v : Mg) ∈ B → (act hdiv A hA (MvPolynomial.aeval op P) v : Mg) ∈ B := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro v hv
    rw [MvPolynomial.algHom_C, coe_act_algebraMap]
    exact B.zsmul_mem hv _
  | add P Q hP hQ =>
    intro v hv
    rw [map_add, act_add, AddSubgroup.coe_add]
    exact B.add_mem (hP v hv) (hQ v hv)
  | mul_X P g hP =>
    intro v hv
    rw [map_mul, MvPolynomial.aeval_X, act_mul]
    apply hP
    rw [coe_act_of_levelwise hdiv A hA f op hop]
    exact hB g _ hv

include hop in
theorem act_aeval_selfAdjoint [Module (ZMod p) ↥A] (b : LinearMap.BilinForm (ZMod p) ↥A)
    (hsa : ∀ (g : G) (x y x' y' : ↥A), (x' : Mg) = f g (x : Mg) → (y' : Mg) = f g (y : Mg) → b x' y = b x y')
    (P : MvPolynomial G ℤ_[p]) :
    ∀ x y : ↥A, b (act hdiv A hA (MvPolynomial.aeval op P) x) y = b x (act hdiv A hA (MvPolynomial.aeval op P) y) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro x y
    have hx : act hdiv A hA (MvPolynomial.aeval op (MvPolynomial.C c)) x = ((c.appr 1 : ℕ) : ℤ) • x :=
      Subtype.ext (by rw [MvPolynomial.algHom_C, coe_act_algebraMap, AddSubgroupClass.coe_zsmul])
    have hy : act hdiv A hA (MvPolynomial.aeval op (MvPolynomial.C c)) y = ((c.appr 1 : ℕ) : ℤ) • y :=
      Subtype.ext (by rw [MvPolynomial.algHom_C, coe_act_algebraMap, AddSubgroupClass.coe_zsmul])
    rw [hx, hy, ← Int.cast_smul_eq_zsmul (ZMod p), ← Int.cast_smul_eq_zsmul (ZMod p), map_smul,
      LinearMap.smul_apply, map_smul]
  | add P Q hP hQ =>
    intro x y
    rw [map_add, act_add, act_add, map_add, LinearMap.add_apply, map_add, hP, hQ]
  | mul_X P g hP =>
    intro x y
    rw [map_mul, MvPolynomial.aeval_X, act_mul, act_mul, hP,
      hsa g x (act hdiv A hA (MvPolynomial.aeval op P) y) (act hdiv A hA (op g) x)
        (act hdiv A hA (op g) (act hdiv A hA (MvPolynomial.aeval op P) y))
        (coe_act_of_levelwise hdiv A hA f op hop g x) (coe_act_of_levelwise hdiv A hA f op hop g _),
      act_comm]

end act

end EIdemAux
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH.EIdemAux"

namespace EIdemAux

open TateModule

theorem main {p : ℕ} [Fact p.Prime] {Mg : Type} [AddCommGroup Mg]
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p Mg)] [IsScalarTower ℤ_[p] 𝕋 (TateModule p Mg)]
    (hdiv : ∀ y : Mg, ∃ z : Mg, (p : ℤ) • z = y)
    (A : AddSubgroup Mg) (hA : ∀ v : Mg, v ∈ A ↔ (p : ℤ) • v = 0) [Module (ZMod p) ↥A]
    {G : Type} (f : G → (Mg →+ Mg)) (op : G → 𝕋)
    (hop : ∀ (g : G) (x : TateModule p Mg), op g • x = TateModule.rep p Mg (AddMonoid.End Mg) (f g) x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) (e : 𝕋) :
    ∃ ε : ↥A →+ ↥A,
      (∀ v : ↥A, ∃ x : TateModule p Mg, TateModule.proj p Mg 1 x = v) ∧
      (∀ (x : TateModule p Mg) (v : ↥A), (v : Mg) = TateModule.proj p Mg 1 x →
        ((ε v : ↥A) : Mg) = TateModule.proj p Mg 1 (e • x)) ∧
      (∀ B : AddSubgroup Mg, (∀ (g : G) (x : Mg), x ∈ B → f g x ∈ B) →
        ∀ v : ↥A, (v : Mg) ∈ B → ((ε v : ↥A) : Mg) ∈ B) ∧
      (∀ b : LinearMap.BilinForm (ZMod p) ↥A,
        (∀ (g : G) (x y x' y' : ↥A), (x' : Mg) = f g (x : Mg) → (y' : Mg) = f g (y : Mg) → b x' y = b x y') →
        ∀ x y, b (ε x) y = b x (ε y)) := by
  have hop' : ∀ (g : G) (x : TateModule p Mg) (n : ℕ),
      ((op g • x : TateModule p Mg) : ℕ → Mg) n = f g ((x : ℕ → Mg) n) := fun g x n => by
    rw [hop]; rfl
  obtain ⟨P, rfl⟩ : ∃ P : MvPolynomial G ℤ_[p], MvPolynomial.aeval op P = e := by
    have : e ∈ (MvPolynomial.aeval (R := ℤ_[p]) op).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, hgen]; exact Algebra.mem_top
    exact this
  refine ⟨actHom hdiv A hA (MvPolynomial.aeval op P), fun v => ?_, fun x v hxv => ?_, fun B hB v hv => ?_,
    fun b hsa x y => ?_⟩
  · exact ⟨liftTate hdiv (v : Mg) ((hA v).mp v.2), rfl⟩
  · exact coe_act_of_proj_eq hdiv A hA _ v x hxv.symm
  · exact act_aeval_mem hdiv A hA f op hop' B hB P v hv
  · exact act_aeval_selfAdjoint hdiv A hA f op hop' b hsa P x y

end EIdemAux
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH.EIdemAux"

theorem EIdemAux.jH_divisible (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (y : ModularCurve.JH M H) : ∃ z : ModularCurve.JH M H, (p : ℤ) • z = y := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  have hfg : ∃ x : ModularCurve.xHFunctionFieldBar M H, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (ModularCurve.xHFunctionFieldBar M H)))
        (ModularCurve.xHFunctionFieldBar M H) :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ)
      (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
  haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) := by
    obtain ⟨x, hx, hfd⟩ := hfg
    haveI := hfd
    exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  obtain ⟨z, hz⟩ := AlgebraicCurve.Pic0.exists_nsmul_eq (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H)
    hfg p (Fact.out : p.Prime).ne_zero y
  exact ⟨z, by rw [natCast_zsmul, hz]⟩

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (e : 𝕋) (he : IsIdempotentElem e) :
    ∃ ε : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) →+
        ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),

      (∀ v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),
        ∃ x : TateModule p (ModularCurve.JH M H), TateModule.proj p (ModularCurve.JH M H) 1 x = v) ∧

      (∀ (x : TateModule p (ModularCurve.JH M H))
        (v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (v : ModularCurve.JH M H) = TateModule.proj p (ModularCurve.JH M H) 1 x →
        ((ε v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) :
          ModularCurve.JH M H) = TateModule.proj p (ModularCurve.JH M H) 1 (e • x)) ∧

      (∀ A : AddSubgroup (ModularCurve.JH M H),
        (∀ (g : CohCarrier.Gen M S) (x : ModularCurve.JH M H), x ∈ A → ModularCurve.genOpH M H S g x ∈ A) →
        ∀ v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),
          (v : ModularCurve.JH M H) ∈ A →
          ((ε v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) :
            ModularCurve.JH M H) ∈ A) ∧

      (∀ b : LinearMap.BilinForm (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),
        (∀ (g : CohCarrier.Gen M S)
          (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
          (x' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (x : ModularCurve.JH M H) →
          (y' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (y : ModularCurve.JH M H) → b x' y = b x y') →
        ∀ x y, b (ε x) y = b x (ε y)) := by
  exact EIdemAux.main (EIdemAux.jH_divisible p M H) _ (fun v => AlgebraicCurve.Pic0.mem_torsion)
    (ModularCurve.genOpH M H S) op hop hgen e

end S_ModularCurve_exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH
end P2MW
export P2MW.S_ModularCurve_exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH (solution)

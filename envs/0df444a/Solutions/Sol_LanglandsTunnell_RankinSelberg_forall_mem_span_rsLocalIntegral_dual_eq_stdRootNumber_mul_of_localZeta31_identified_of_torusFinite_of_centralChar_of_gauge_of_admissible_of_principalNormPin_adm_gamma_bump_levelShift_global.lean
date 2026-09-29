-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_stdRootNumber_mul_of_localZeta31_identified_of_torusFinite_of_centralChar_of_gauge_of_admissible_of_principalNormPin_adm_gamma_bump_levelShift_global
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c708f245-b6fb-5d34-9e24-2fa6319c2743

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global
import Theorems.Thm_LanglandsTunnell_Converse_exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt_of_norm_eq_one
import Theorems.Thm_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_Converse_finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor
import Theorems.Thm_LanglandsTunnell_Converse_pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
import Theorems.Thm_LanglandsTunnell_RankinSelberg_two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_two_mul_conductorExponent_le
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_stdRootNumber_mul_of_localZeta31_identified_of_torusFinite_of_centralChar_of_gauge_of_admissible_of_principalNormPin_adm_gamma_bump_levelShift_global
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix LocalGL2.Kirillov.fintype_Qm LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.mem_sigmaCentralizer_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one"
p2m_attr_erase "simp" "LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LanglandsTunnell.CubicInduction.fnTwist3_apply LocalGL2.Kirillov.zG_coe LocalGL2.Kirillov.wG_coe LocalGL2.Kirillov.dg_coe LocalGL2.Kirillov.rT_apply LocalGL2.Kirillov.rT_one Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

namespace VPSAsm

open Complex

theorem exists_hasConductorExponentAt_le
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ)
    (h : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1) :
    ∃ c' ≤ c, LanglandsTunnell.TateLocal.HasConductorExponentAt F v χ c' := by
  classical
  have hex : ∃ m, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v m, χ u = 1 := ⟨c, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun m hm => ?_⟩
  have hmin := Nat.find_min hex hm
  push Not at hmin
  exact hmin

theorem hasConductorExponentAt_of_eqOn_units
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (χ χ' : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ)
    (heq : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ' u = χ u)
    (h : LanglandsTunnell.TateLocal.HasConductorExponentAt F v χ c) :
    LanglandsTunnell.TateLocal.HasConductorExponentAt F v χ' c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [heq u ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff F v).mp hu).1]
    exact h.1 u hu
  · obtain ⟨u, hu, hne⟩ := h.2 m hm
    refine ⟨u, hu, ?_⟩
    rw [heq u ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff F v).mp hu).1]
    exact hne

theorem modulus_coe_eq_one_of_valued_eq_one
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) (hu : Valued.v (u : v.adicCompletion F) = 1) :
    (((modulus (u : v.adicCompletion F) : NNReal) : ℝ) : ℂ) = 1 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v]
  have h1 : ‖(u : v.adicCompletion F)‖ = 1 := by
    rw [NumberField.FinitePlace.norm_def, hu, map_one, NNReal.coe_one]
  rw [coe_nnnorm, h1, Complex.ofReal_one]

theorem isAdmissibleTwist_mul (F : Type) [Field F] [NumberField F]
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (h₁ : LanglandsTunnell.Converse.IsAdmissibleTwist F χ₁) (h₂ : LanglandsTunnell.Converse.IsAdmissibleTwist F χ₂) :
    LanglandsTunnell.Converse.IsAdmissibleTwist F (χ₁ * χ₂) := by
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.mul_apply, h₁.1 u, h₂.1 u, mul_one]
  · show Continuous fun x => χ₁ x * χ₂ x
    exact h₁.2.1.mul h₂.2.1
  · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h₁.2.2 x, h₂.2.2 x, mul_one]

theorem isAdmissibleTwist_inv (F : Type) [Field F] [NumberField F]
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (h : LanglandsTunnell.Converse.IsAdmissibleTwist F χ) :
    LanglandsTunnell.Converse.IsAdmissibleTwist F χ⁻¹ := by
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.inv_apply, h.1 u, inv_one]
  · show Continuous fun x => (χ x)⁻¹
    exact h.2.1.inv
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h.2.2 x, inv_one]

theorem principalSeries2_scalar_mul (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (((χ 0 z : ℂˣ) : ℂ) * ((χ 1 z : ℂˣ) : ℂ)) * f g := by
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) z = diagonal2 p (fun _ => z) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, diagonal2, Matrix.diagonal]
  rw [hsc, (mem_principalSeries2_iff.mp hf).2.2]
  have hh : halfModulus2 p (fun _ => z) = 1 := by
    simp [halfModulus2]
  rw [hh, mul_one]
  simp [torusChar2, Fin.prod_univ_two]

theorem scalar_mul_comm (p : HeightOneSpectrum (𝓞 ℚ)) (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, mul_comm]

theorem primeFibre_finite (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (p : HeightOneSpectrum (𝓞 ℚ)) :
    (primeFibre ℚ K p).Finite := by
  haveI : Module.IsTorsionFree (𝓞 ℚ) (𝓞 K) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    have h := ((algebraMap (𝓞 ℚ) (𝓞 K)).comp Rat.ringOfIntegersEquiv.symm.toRingHom).injective_int
    intro a b hab
    have hab' : ((algebraMap (𝓞 ℚ) (𝓞 K)).comp Rat.ringOfIntegersEquiv.symm.toRingHom)
          (Rat.ringOfIntegersEquiv a) =
        ((algebraMap (𝓞 ℚ) (𝓞 K)).comp Rat.ringOfIntegersEquiv.symm.toRingHom)
          (Rat.ringOfIntegersEquiv b) := by
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
      exact hab
    exact Rat.ringOfIntegersEquiv.injective (h hab')
  have hfin := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)
  refine (hfin.preimage (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  intro 𝔓 h𝔓
  simp only [mem_primeFibre] at h𝔓
  refine ⟨𝔓.isPrime, ?_⟩
  rw [Ideal.liesOver_iff, ← h𝔓]
  rfl

noncomputable def kOf (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (p : HeightOneSpectrum (𝓞 ℚ))
    (a : HeightOneSpectrum (𝓞 K) → ℤ) : ℤ :=
  -∑ w ∈ (primeFibre_finite K p).toFinset, ((p.asIdeal.inertiaDeg' w.asIdeal : ℕ) : ℤ) * a w

theorem absNorm_eq_pow_of_mem_primeFibre (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (p : HeightOneSpectrum (𝓞 ℚ))
    (w : HeightOneSpectrum (𝓞 K)) (hw : w ∈ primeFibre ℚ K p) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm p.asIdeal ^ (p.asIdeal.inertiaDeg' w.asIdeal) := by
  haveI : w.asIdeal.LiesOver p.asIdeal := by
    rw [Ideal.liesOver_iff, ← (mem_primeFibre ℚ p w).mp hw]
    rfl
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.asIdeal p.asIdeal p.isPrime p.ne_bot

theorem prod_cpow_eq_cpow_sum {ι : Type} (s : Finset ι) (x : ℂ) (hx : x ≠ 0) (g : ι → ℂ) :
    ∏ i ∈ s, x ^ (g i) = x ^ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, Complex.cpow_add _ _ hx, ih]

theorem finprod_mul_cpow_zpow_eq (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (p : HeightOneSpectrum (𝓞 ℚ))
    (e : HeightOneSpectrum (𝓞 K) → ℂ) (a : HeightOneSpectrum (𝓞 K) → ℤ) (σ : ℂ) :
    ∏ᶠ w ∈ primeFibre ℚ K p, (e w * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - σ)) ^ (a w)) =
      (∏ᶠ w ∈ primeFibre ℚ K p, (e w * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (a w))) *
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((kOf K p a : ℂ) * σ) := by
  classical
  have hfin := primeFibre_finite K p
  have hq0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin]
  have key : ∀ w ∈ hfin.toFinset,
      e w * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - σ)) ^ (a w) =
        (e w * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (a w)) *
          (Ideal.absNorm p.asIdeal : ℂ) ^ (-((((p.asIdeal.inertiaDeg' w.asIdeal : ℕ) : ℤ) * a w : ℤ) : ℂ) * σ) := by
    intro w hw
    have hw' : w ∈ primeFibre ℚ K p := hfin.mem_toFinset.mp hw
    have hNw : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) = (Ideal.absNorm p.asIdeal : ℂ) ^ (p.asIdeal.inertiaDeg' w.asIdeal) := by
      rw [absNorm_eq_pow_of_mem_primeFibre K p w hw']
      push_cast
      rfl
    have hNw0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by rw [hNw]; exact pow_ne_zero _ hq0
    have hsplit : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - σ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-σ) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hNw0]
    rw [hsplit, mul_zpow, ← mul_assoc]
    congr 1
    rw [← Complex.cpow_int_mul, hNw]
    have harg : ((Ideal.absNorm p.asIdeal : ℂ) ^ (p.asIdeal.inertiaDeg' w.asIdeal)).arg = 0 := by
      rw [← Nat.cast_pow]; exact Complex.natCast_arg
    rw [← Complex.cpow_nat_mul' (by rw [Complex.natCast_arg, mul_zero]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [Complex.natCast_arg, mul_zero]; exact Real.pi_pos.le)]
    congr 1
    push_cast
    ring
  rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib, prod_cpow_eq_cpow_sum _ _ hq0]
  congr 1
  congr 1
  rw [kOf, ← Finset.sum_mul]
  push_cast
  rw [Finset.sum_neg_distrib]

theorem cancel_aux (C₀ C₁ X A B : ℂ) (hAB : A * B = 1) :
    (C₀ * A * X) * (C₁ * B * X) = (C₀ * X) * (C₁ * X) := by
  calc (C₀ * A * X) * (C₁ * B * X) = (C₀ * X) * (C₁ * X) * (A * B) := by ring
    _ = (C₀ * X) * (C₁ * X) := by rw [hAB, mul_one]

theorem count_factors_eq_of_pow_dvd_not_dvd {R : Type} [CommRing R] [IsDedekindDomain R]
    (p : HeightOneSpectrum R) (N : Ideal R) (hN : N ≠ ⊥) (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N) :
    (Associates.mk p.asIdeal).count (Associates.mk N).factors = b := by
  classical
  have h0 : Associates.mk N ≠ 0 := mt Associates.mk_eq_zero.mp hN
  have hirr : Irreducible (Associates.mk p.asIdeal) := Associates.irreducible_mk.mpr p.irreducible
  have h1 : b ≤ (Associates.mk p.asIdeal).count (Associates.mk N).factors := by
    rw [← Associates.prime_pow_dvd_iff_le h0 hirr, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
    exact hNb.1
  have h2 : ¬ b + 1 ≤ (Associates.mk p.asIdeal).count (Associates.mk N).factors := by
    rw [← Associates.prime_pow_dvd_iff_le h0 hirr, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
    exact hNb.2
  omega

theorem central_trivial_on_higherUnits (p : HeightOneSpectrum (𝓞 ℚ)) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)
    (b : ℕ) (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N) :
    ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, ω u = 1 := by
  classical
  intro u hu
  obtain ⟨hu1, hub⟩ := (LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff ℚ p).mp hu
  have hbd : NumberField.AdelicLevel.idealBound (𝓞 ℚ) N p = WithZero.exp (-(b : ℤ)) := by
    rw [NumberField.AdelicLevel.idealBound_of_ne_bot hN, count_factors_eq_of_pow_dvd_not_dvd p N hN b hNb]

  have hsub : ∀ x : (p.adicCompletion ℚ)ˣ, Valued.v (x : p.adicCompletion ℚ) = 1 →
      (b = 0 ∨ Valued.v ((x : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(b : ℤ))) →
      Valued.v ((x : p.adicCompletion ℚ) - 1) ≤ NumberField.AdelicLevel.idealBound (𝓞 ℚ) N p := by
    intro x hx1 hxb
    rw [hbd]
    rcases hxb with hb0 | hle
    · subst hb0
      simp only [CharP.cast_eq_zero, neg_zero, WithZero.exp_zero]
      refine (Valuation.map_sub _ _ _).trans ?_
      rw [hx1, map_one, max_self]
    · exact hle
  have hinv1 : Valued.v ((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]
  have hinvb : b = 0 ∨ Valued.v (((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
    rcases hub with hb0 | hle
    · exact Or.inl hb0
    · right
      have : ((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1 =
          ((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * (1 - (u : p.adicCompletion ℚ)) := by
        rw [mul_sub, mul_one, Units.inv_mul]
      rw [this, map_mul, hinv1, one_mul, Valuation.map_sub_swap]
      exact hle
  have hmemO : ∀ x : (p.adicCompletion ℚ)ˣ, Valued.v (x : p.adicCompletion ℚ) = 1 →
      ∀ i j : Fin 2, ((Matrix.GeneralLinearGroup.scalar (Fin 2) x : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈
        p.adicCompletionIntegers ℚ := by
    intro x hx i j
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hij : i = j
    · subst hij; simp [Matrix.GeneralLinearGroup.scalar, hx]
    · simp [Matrix.GeneralLinearGroup.scalar, hij]
  have hloc : ∀ x : (p.adicCompletion ℚ)ˣ, Valued.v (x : p.adicCompletion ℚ) = 1 →
      (b = 0 ∨ Valued.v ((x : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(b : ℤ))) →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) x : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
    intro x hx hxb
    refine ⟨hmemO x hx, ?_, ?_⟩
    · simp [Matrix.GeneralLinearGroup.scalar]
    · have : ((Matrix.GeneralLinearGroup.scalar (Fin 2) x : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = x := by
        simp [Matrix.GeneralLinearGroup.scalar]
      rw [this]
      exact hsub x hx hxb
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
    rw [AdelicDock.mem_localLevelOne_iff]
    refine ⟨hloc u hu1 hub, ?_⟩
    rw [← map_inv]
    exact hloc u⁻¹ hinv1 hinvb
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hw₂ne
  have h1 := hw₂K _ hz g₀
  rw [scalar_mul_comm, hcentral] at h1
  have h2 : ((ω u : ℂˣ) : ℂ) = 1 := (mul_eq_right₀ hg₀).mp h1
  exact Units.ext h2

theorem isAdmissibleTwist_one (F : Type) [Field F] [NumberField F] :
    LanglandsTunnell.Converse.IsAdmissibleTwist F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :=
  ⟨fun _ => rfl, continuous_const, fun _ => by simp⟩

end VPSAsm

namespace Ws23RekeyDC

open LanglandsTunnell.TateLocal NumberField.TateGlobal LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg

theorem algebra_ringOfIntegers_rat_ext (R : Type) [CommRing R] (i₁ i₂ : Algebra (𝓞 ℚ) R) : i₁ = i₂ := by
  have h : ∀ f g : 𝓞 ℚ →+* R, f = g := fun f g => by
    have hh : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
      Subsingleton.elim _ _
    refine RingHom.ext fun r => ?_
    have := RingHom.congr_fun hh (Rat.ringOfIntegersEquiv r)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] at this
    exact this
  exact Algebra.algebra_ext _ _ (RingHom.congr_fun (h _ _))

theorem place_twist (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : LanglandsTunnell.Converse.IsAdmissibleTwist K μ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (b : ℕ) (W : p.Extension (𝓞 K))
    (hfl : 2 * (p.asIdeal.ramificationIdx' W.1.asIdeal * b) + 1 ≤
      LanglandsTunnell.TateLocal.conductorExponentAt K W.1 (NumberField.TateGlobal.localChar μ W.1)) :
    ∃ d sgn : (p.adicCompletion ℚ)ˣ,
      ∀ (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
      ∀ (cη : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ηA p) cη → cη ≤ b →
        LanglandsTunnell.TateLocal.stdRootNumberAt K W.1
            (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) W.1) =
          ((NumberField.TateGlobal.localChar ηA p d : ℂˣ) : ℂ) *
            LanglandsTunnell.TateLocal.stdRootNumberAt K W.1 (NumberField.TateGlobal.localChar μ W.1) ∧
        ((NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) W.1 (-1) : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.localChar μ W.1 (-1) : ℂˣ) : ℂ) * ((NumberField.TateGlobal.localChar ηA p sgn : ℂˣ) : ℂ) := by
  classical
  obtain ⟨-, -, hμu⟩ := hμ

  have hχ : HasConductorExponentAt K W.1 (NumberField.TateGlobal.localChar μ W.1)
      (conductorExponentAt K W.1 (NumberField.TateGlobal.localChar μ W.1)) := by
    have hne : {c | HasConductorExponentAt K W.1 (NumberField.TateGlobal.localChar μ W.1) c}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : conductorExponentAt K W.1 (NumberField.TateGlobal.localChar μ W.1) = 0 := by
        rw [LanglandsTunnell.TateLocal.conductorExponentAt, hemp, Nat.sInf_empty]
      omega
    exact Nat.sInf_mem hne
  have hu : ‖((NumberField.TateGlobal.localChar μ W.1 (NumberField.AdelicLevel.uniformizerUnit K W.1) : ℂˣ) : ℂ)‖ = 1 := by
    rw [NumberField.TateGlobal.localChar_apply]; exact hμu _
  by_cases ha : 2 ≤ conductorExponentAt K W.1 (NumberField.TateGlobal.localChar μ W.1)
  ·
    obtain ⟨c, hc⟩ :=
      exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt K W.1
        (NumberField.TateGlobal.localChar μ W.1) _ hχ
    refine ⟨(Units.map (Algebra.norm (p.adicCompletion ℚ)) c)⁻¹, Units.map (Algebra.norm (p.adicCompletion ℚ)) (-1 : (W.1.adicCompletion K)ˣ),
      fun ηA hηA cη hcη hcb => ?_⟩
    obtain ⟨-, -, hηu⟩ := hηA
    have E := NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ ηA p W
    rw [mul_comm μ] at E
    obtain ⟨b', hθ, hb'le⟩ :=
      exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul ℚ K p W (NumberField.TateGlobal.localChar ηA p) cη hcη
    have hm : p.asIdeal.ramificationIdx' W.1.asIdeal * cη ≤ p.asIdeal.ramificationIdx' W.1.asIdeal * b :=
      Nat.mul_le_mul_left _ hcb
    have huθ : ‖((((NumberField.TateGlobal.localChar ηA p).comp (Units.map (Algebra.norm (p.adicCompletion ℚ))))
        (NumberField.AdelicLevel.uniformizerUnit K W.1) : ℂˣ) : ℂ)‖ = 1 := by
      rw [MonoidHom.comp_apply, NumberField.TateGlobal.localChar_apply]; exact hηu _
    rw [E]
    refine ⟨?_, ?_⟩
    · rw [mul_comm (NumberField.TateGlobal.localChar μ W.1),
        stdRootNumberAt_mul_of_two_mul_conductorExponent_le K W.1 (NumberField.TateGlobal.localChar μ W.1) _ _ b' hχ hθ ha
          (by omega) hu huθ c hc, MonoidHom.comp_apply, map_inv, Units.val_inv_eq_inv_val]
    · rw [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply]
  ·
    refine ⟨Units.map (Algebra.norm (p.adicCompletion ℚ)) (NumberField.AdelicLevel.uniformizerUnit K W.1) ^
        ((conductorExponentAt K W.1 (NumberField.TateGlobal.localChar μ W.1) : ℤ) + addCharLevel (NumberField.StandardAddChar.psiLocal K W.1)),
      Units.map (Algebra.norm (p.adicCompletion ℚ)) (-1 : (W.1.adicCompletion K)ˣ), fun ηA hηA cη hcη hcb => ?_⟩
    obtain ⟨-, -, hηu⟩ := hηA
    have E := NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ ηA p W
    rw [mul_comm μ] at E
    obtain ⟨b', hθ, hb'le⟩ :=
      exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul ℚ K p W (NumberField.TateGlobal.localChar ηA p) cη hcη
    have hm : p.asIdeal.ramificationIdx' W.1.asIdeal * cη ≤ p.asIdeal.ramificationIdx' W.1.asIdeal * b :=
      Nat.mul_le_mul_left _ hcb
    obtain rfl : b' = 0 := by omega
    have huθ : ‖((((NumberField.TateGlobal.localChar ηA p).comp (Units.map (Algebra.norm (p.adicCompletion ℚ))))
        (NumberField.AdelicLevel.uniformizerUnit K W.1) : ℂˣ) : ℂ)‖ = 1 := by
      rw [MonoidHom.comp_apply, NumberField.TateGlobal.localChar_apply]; exact hηu _
    rw [E]
    refine ⟨?_, ?_⟩
    · rw [stdRootNumberAt_mul_of_hasConductorExponentAt_zero K W.1 (NumberField.TateGlobal.localChar μ W.1) _ _ hχ hθ hu huθ
          (psiLocal_ne_one K W.1), MonoidHom.comp_apply, map_zpow, Units.val_zpow_eq_zpow_val]
    · rw [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply]

end Ws23RekeyDC

open scoped Classical in

open LanglandsTunnell.TateLocal NumberField.TateGlobal LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg in

theorem Ws23Rekey.deligne_const
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : LanglandsTunnell.Converse.IsAdmissibleTwist K μ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (lam : ℂ) (b : ℕ)
    (hfloorb : ∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
      2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) :
    ∃ (Cst : ℂ) (yst : (p.adicCompletion ℚ)ˣ) (est : ℕ),
      ∀ (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
      ∀ (cη : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ηA p) cη → cη ≤ b →
        lam * (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
            ((NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
          (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
            (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
              (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w))) =
        Cst * ((NumberField.TateGlobal.localChar ηA p yst : ℂˣ) : ℂ) ^ est := by
  classical

  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
    Ws23RekeyDC.algebra_ringOfIntegers_rat_ext _ _ _
  have hF : (primeFibre ℚ K p).Finite := by
    have : Finite (p.Extension (𝓞 K)) := HeightOneSpectrum.Extension.finite (𝓞 ℚ) ℚ K (𝓞 K) p
    refine (Set.finite_range (fun W : p.Extension (𝓞 K) => W.1)).subset ?_
    intro x hx
    exact ⟨⟨x, (mem_primeFibre ℚ p x).1 hx⟩, rfl⟩

  have hpl : ∀ W : p.Extension (𝓞 K), ∃ d sgn : (p.adicCompletion ℚ)ˣ,
      ∀ (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
      ∀ (cη : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ηA p) cη → cη ≤ b →
        stdRootNumberAt K W.1 (localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) W.1) =
          ((localChar ηA p d : ℂˣ) : ℂ) * stdRootNumberAt K W.1 (localChar μ W.1) ∧
        ((localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) W.1 (-1) : ℂˣ) : ℂ) =
          ((localChar μ W.1 (-1) : ℂˣ) : ℂ) * ((localChar ηA p sgn : ℂˣ) : ℂ) := fun W =>
    Ws23RekeyDC.place_twist K μ hμ p b W (by
      have h := hfloorb W.1 ((mem_primeFibre ℚ p W.1).2 W.2)
      rwa [W.2] at h)
  choose d sgn hds using hpl

  refine ⟨lam * (∏ᶠ w ∈ primeFibre ℚ K p, ((localChar μ w (-1) : ℂˣ) : ℂ)) *
      ∏ᶠ w ∈ primeFibre ℚ K p, stdRootNumberAt K w (localChar μ w) *
        (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w),
    ∏ᶠ w ∈ primeFibre ℚ K p, (if hw : w.under (𝓞 ℚ) = p then sgn ⟨w, hw⟩ * d ⟨w, hw⟩ else 1),
    1, fun ηA hηA cη hcη hcb => ?_⟩

  have hsign : ∀ w ∈ primeFibre ℚ K p,
      ((localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ) =
        ((localChar μ w (-1) : ℂˣ) : ℂ) *
          ((localChar ηA p (if hw : w.under (𝓞 ℚ) = p then sgn ⟨w, hw⟩ else 1) : ℂˣ) : ℂ) := by
    intro w hw
    have hw' : w.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p w).1 hw
    rw [dif_pos hw']
    exact (hds ⟨w, hw'⟩ ηA hηA cη hcη hcb).2
  have heps : ∀ w ∈ primeFibre ℚ K p,
      stdRootNumberAt K w (localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w) =
        ((localChar ηA p (if hw : w.under (𝓞 ℚ) = p then d ⟨w, hw⟩ else 1) : ℂˣ) : ℂ) *
          (stdRootNumberAt K w (localChar μ w) *
            (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w)) := by
    intro w hw
    have hw' : w.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p w).1 hw
    rw [dif_pos hw', (hds ⟨w, hw'⟩ ηA hηA cη hcη hcb).1, mul_assoc]
  rw [finprod_mem_congr rfl hsign, finprod_mem_congr rfl heps, finprod_mem_mul_distrib hF, finprod_mem_mul_distrib hF,
    pow_one]

  have hθ : ∀ (g : HeightOneSpectrum (𝓞 K) → (p.adicCompletion ℚ)ˣ),
      ∏ᶠ w ∈ primeFibre ℚ K p, ((localChar ηA p (g w) : ℂˣ) : ℂ) = ((localChar ηA p (∏ᶠ w ∈ primeFibre ℚ K p, g w) : ℂˣ) : ℂ) := by
    intro g
    rw [MonoidHom.map_finprod_mem g (localChar ηA p) hF, ← Units.coeHom_apply, MonoidHom.map_finprod_mem _ (Units.coeHom ℂ) hF]
    rfl
  rw [hθ, hθ]
  have hfg : ∀ w ∈ primeFibre ℚ K p,
      (if hw : w.under (𝓞 ℚ) = p then sgn ⟨w, hw⟩ else 1) * (if hw : w.under (𝓞 ℚ) = p then d ⟨w, hw⟩ else 1) =
        (if hw : w.under (𝓞 ℚ) = p then sgn ⟨w, hw⟩ * d ⟨w, hw⟩ else 1) := by
    intro w hw
    have hw' : w.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p w).1 hw
    rw [dif_pos hw', dif_pos hw', dif_pos hw']
  have hY : (∏ᶠ w ∈ primeFibre ℚ K p, (if hw : w.under (𝓞 ℚ) = p then sgn ⟨w, hw⟩ else 1)) *
      (∏ᶠ w ∈ primeFibre ℚ K p, (if hw : w.under (𝓞 ℚ) = p then d ⟨w, hw⟩ else 1)) =
      ∏ᶠ w ∈ primeFibre ℚ K p, (if hw : w.under (𝓞 ℚ) = p then sgn ⟨w, hw⟩ * d ⟨w, hw⟩ else 1) := by
    rw [← finprod_mem_mul_distrib hF]
    exact finprod_mem_congr rfl hfg
  rw [← hY, map_mul, Units.val_mul]
  ring

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : LanglandsTunnell.Converse.IsAdmissibleTwist K μ)
    (p : HeightOneSpectrum (𝓞 ℚ))

    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (kp : ℕ)
    (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) kp)

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)

    (hω₃u : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ω₃ x : ℂˣ) : ℂ)‖ = 1)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃base,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (d : ℕ)
    (hπ₀lev : ∃ W' ∈ gl3CyclicSubspace W₃base, W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p,
          ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)

    (lam : ℂ)
    (hId :
      ∀ b : ℕ,
              (∀ w ∈ primeFibre ℚ K p,
            2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
              LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
          ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
            LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η cη → cη ≤ b →
            ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
              NumberField.TateGlobal.localChar ηA p = η →
              LanglandsTunnell.Converse.IsAdmissibleTwist K
                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
              ∀ g : LocalGL3 p,
                letI := localBorel ℚ p
                ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                  IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
                    W₃base η g σ₀ ∧
                  (∀ s : ℂ, σ₀ < s.re →
                    localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base η s g *
                      Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                  IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                  (∀ s : ℂ, σ₁ < (1 - s).re →
                    localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
                      W₃base η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                      (lam *
                        (∏ᶠ w ∈ primeFibre ℚ K p,
                          ((NumberField.TateGlobal.localChar
                            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                        (∏ᶠ w ∈ primeFibre ℚ K p,
                          (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                              (NumberField.TateGlobal.localChar
                                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                            (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                              (LanglandsTunnell.Converse.pinnedExp K
                                  (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))))

    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (hfloor : ∀ w ∈ primeFibre ℚ K p,
      4 * (FractionalIdeal.count K w
            ((N.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))

    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hηA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA)
    (hηAN : LanglandsTunnell.Converse.IsAdmissibleTwist K
      (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
        ((NumberField.TateGlobal.localChar ηA p z : ℂˣ) : ℂ) * w₂base g)

    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)

    (hkC : 6 * (b + 3 * d + 3) + 7 ≤ kp)

    (Δ : ℕ) (hΔ : 6 * d + 18 + Δ ≤ kp)

    (hbumpAll : ∀ (ξA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ξA →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → NumberField.TateGlobal.IsUnramifiedCharAt ξA v) →
      (∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ ξA v 0 0) →
      ∀ B : ℕ, 2 * d + 6 ≤ B → LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ξA p) B →
      ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 p =>
          ((NumberField.TateGlobal.localChar ξA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W₃base g),
        (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p (3 * B + Δ), ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
        (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
          W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
          ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
        W₀ (iotaGL 1) = 1)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))
    (hβ : ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 ∧
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

    (hΓ :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W₃base,
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              R₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                (R₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((r : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),

          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂ =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (lam ^ 2 *
                ((∏ᶠ w ∈ primeFibre ℚ K p,
                    ((NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                  ∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ)) *
                ((∏ᶠ w ∈ primeFibre ℚ K p,
                    (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                      (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 + s)) ^
                        (LanglandsTunnell.Converse.pinnedExp K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))) *
                  ∏ᶠ w ∈ primeFibre ℚ K p,
                    (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar μ w) *
                      (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 + s)) ^
                        (LanglandsTunnell.Converse.pinnedExp K μ w)))) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by
  classical

  have hωtriv := VPSAsm.central_trivial_on_higherUnits p N _hN w₂base hw₂K hw₂ne (NumberField.TateGlobal.localChar ηA p)
    hcentral b hNb
  obtain ⟨c₀, hc0b, hc₀⟩ := VPSAsm.exists_hasConductorExponentAt_le ℚ p (NumberField.TateGlobal.localChar ηA p) b hωtriv

  have h1A : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) := VPSAsm.isAdmissibleTwist_one ℚ
  have h1AN : LanglandsTunnell.Converse.IsAdmissibleTwist K ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) := by
    rw [MonoidHom.one_comp]; exact VPSAsm.isAdmissibleTwist_one K
  have h1loc : NumberField.TateGlobal.localChar (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) p = 1 := MonoidHom.ext fun _ => rfl
  have h1c : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) p) 0 := by
    rw [h1loc]; exact LanglandsTunnell.TateLocal.hasConductorExponentAt_one_zero ℚ p

  have hfloorb := LanglandsTunnell.RankinSelberg.two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor
    K μ p N hfloor b hNb
  have hId0 := hId b hfloorb (NumberField.TateGlobal.localChar ηA p) c₀ hc₀ hc0b ηA hηA rfl hηAN
  have hId1 := hId b hfloorb (1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) 0 (LanglandsTunnell.TateLocal.hasConductorExponentAt_one_zero ℚ p)
    (Nat.zero_le b) (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) h1A h1loc h1AN

  have hP4c0 := LanglandsTunnell.Converse.pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
    K μ p b hfloorb ηA c₀ hc₀ hc0b
  have hP4c1 := LanglandsTunnell.Converse.pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
    K μ p b hfloorb (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) 0 h1c (Nat.zero_le b)
  have hG0 : ∀ s : ℂ, (lam * (∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))) =
      (lam * (∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w)))) *
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((VPSAsm.kOf K p (fun w => LanglandsTunnell.Converse.pinnedExp K μ w) : ℂ) * s) := by
    intro s
    have h1 : (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))) = (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w))) :=
      finprod_mem_congr rfl fun w hw => by rw [hP4c0 w hw]
    rw [h1, VPSAsm.finprod_mul_cpow_zpow_eq K p (fun w => LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)) (fun w => LanglandsTunnell.Converse.pinnedExp K μ w) s]
    ring
  have hG1 : ∀ s : ℂ, (lam * (∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))) =
      (lam * (∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w)))) *
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((VPSAsm.kOf K p (fun w => LanglandsTunnell.Converse.pinnedExp K μ w) : ℂ) * s) := by
    intro s
    have h1 : (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))) = (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w))) :=
      finprod_mem_congr rfl fun w hw => by rw [hP4c1 w hw]
    rw [h1, VPSAsm.finprod_mul_cpow_zpow_eq K p (fun w => LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)) (fun w => LanglandsTunnell.Converse.pinnedExp K μ w) s]
    ring
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℂ, C₀ = lam * (∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w))) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℂ, C₁ = lam * (∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w))) := ⟨_, rfl⟩
  obtain ⟨kμ, hkμ⟩ : ∃ kμ : ℤ, kμ = VPSAsm.kOf K p (fun w => LanglandsTunnell.Converse.pinnedExp K μ w) := ⟨_, rfl⟩
  rw [← hC₀, ← hkμ] at hG0
  rw [← hC₁, ← hkμ] at hG1
  have hB0 : ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (NumberField.TateGlobal.localChar ηA p) g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (NumberField.TateGlobal.localChar ηA p) s g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) ((NumberField.TateGlobal.localChar ηA p))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) W₃base (NumberField.TateGlobal.localChar ηA p) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) * (C₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((kμ : ℂ) * s))) := by
    intro g
    obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, hc30, h30, hc31, h31⟩ := hId0 g
    exact ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, hc30, h30, hc31, fun s hs => by rw [← hG0 s]; exact h31 s hs⟩
  have hB1 : ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) s g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) ((1 : (p.adicCompletion ℚ)ˣ →* ℂˣ))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) W₃base (1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) * (C₁ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((kμ : ℂ) * s))) := by
    intro g
    obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, hc30, h30, hc31, h31⟩ := hId1 g
    exact ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, hc30, h30, hc31, fun s hs => by rw [← hG1 s]; exact h31 s hs⟩

  have hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((NumberField.TateGlobal.localChar χA p x : ℂˣ) : ℂ)‖ = 1 := fun x => by
    rw [NumberField.TateGlobal.localChar_apply]; exact hχA.2.2 _
  have hθu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((NumberField.TateGlobal.localChar ηA p z : ℂˣ) : ℂ)‖ = 1 := fun z => by
    rw [NumberField.TateGlobal.localChar_apply]; exact hηA.2.2 _

  obtain ⟨Cst, yst, est, hDC⟩ := Ws23Rekey.deligne_const K μ hμ p lam b hfloorb
  have hGgen : ∀ (ηA' : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hηA' : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA') (cη : ℕ)
      (hcη : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ηA' p) cη) (hcb : cη ≤ b) (s : ℂ),
      (lam * (∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar (ηA'.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA'.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K (ηA'.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))) =
      (Cst * ((NumberField.TateGlobal.localChar ηA' p yst : ℂˣ) : ℂ) ^ est) *
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((VPSAsm.kOf K p (fun w => LanglandsTunnell.Converse.pinnedExp K μ w) : ℂ) * s) := by
    intro ηA' hηA' cη hcη hcb s
    have hP4c := LanglandsTunnell.Converse.pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
      K μ p b hfloorb ηA' cη hcη hcb
    have h1 : (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA'.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K (ηA'.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))) = (∏ᶠ w ∈ primeFibre ℚ K p, (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA'.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (LanglandsTunnell.Converse.pinnedExp K μ w))) :=
      finprod_mem_congr rfl fun w hw => by rw [hP4c w hw]
    rw [h1, VPSAsm.finprod_mul_cpow_zpow_eq K p (fun w => LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA'.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)) (fun w => LanglandsTunnell.Converse.pinnedExp K μ w) s,
      ← hDC ηA' hηA' cη hcη hcb]
    try ring
  have h31all : ∃ (Cst : ℂ) (yst : (p.adicCompletion ℚ)ˣ) (est : ℕ) (kst : ℤ),
      ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η cη → cη ≤ b →
      (∀ z : (p.adicCompletion ℚ)ˣ, ‖((η z : ℂˣ) : ℂ)‖ = 1) →
      ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base η g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base η s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              ((Cst * ((η yst : ℂˣ) : ℂ) ^ est) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((kst : ℂ) * s))) := by
    refine ⟨Cst, yst, est, VPSAsm.kOf K p (fun w => LanglandsTunnell.Converse.pinnedExp K μ w), fun η cη hη hcb hu g => ?_⟩
    obtain ⟨ηA', hηA', hloc⟩ :=
      LanglandsTunnell.Converse.exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt_of_norm_eq_one p η cη hη hu
    subst hloc
    have hηAN' := LanglandsTunnell.Converse.isAdmissibleTwist_comp_idelicNorm_genuineBaseChange ℚ K ηA' hηA'
    obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, hc30, h30, hc31, h31⟩ := hId b hfloorb _ cη hη hcb ηA' hηA' rfl hηAN' g
    exact ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, hc30, h30, hc31, fun s hs => by rw [← hGgen ηA' hηA' cη hη hcb s]; exact h31 s hs⟩

  have hW1 := LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global
    p W₃base hW₃law hW₃sm hW₃ne ω₃ hω₃u hω₃ hW₃irr hW₃adm hWgauge (NumberField.TateGlobal.localChar χA p) hχu kp hkp d hπ₀lev
    ![NumberField.TateGlobal.localChar ηA p, 1] rfl hθu ![C₀, C₁] ![kμ, kμ] (Fin.forall_fin_two.mpr ⟨hB0, hB1⟩)
    N _hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral b hNb hωtriv hkC Δ hΔ hbumpAll h31all hπ hϖ hw₂gr hβ w₀p hw₀p hΓ

  have hP4 := LanglandsTunnell.Converse.finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor
    K _hdeg μ hμ p lam b hfloorb ηA (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) hηA h1A hηAN h1AN c₀ 0 hc₀ h1c hc0b (Nat.zero_le b)
  have hmo : ηA * (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) = ηA := MonoidHom.ext fun _ => mul_one _

  intro μ₂ _ μN₂ _ w₂ hw₂ W₃ hW₃
  obtain ⟨P, Pd, m, md, σ₂, σ₃, hI, hId', hR, hRd, hE⟩ := hW1 μ₂ μN₂ w₂ hw₂ W₃ hW₃
  refine ⟨P, Pd, m, md, σ₂, σ₃, hI, hId', hR, hRd, fun s => ?_⟩
  have h4 := hP4 (-s)
  rw [hG0 (-s), hG1 (-s), hmo] at h4
  simp only [sub_neg_eq_add] at h4
  have hEs := hE s
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hEs
  rw [hEs, h4]

end S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_stdRootNumber_mul_of_localZeta31_identified_of_torusFinite_of_centralChar_of_gauge_of_admissible_of_principalNormPin_adm_gamma_bump_levelShift_global
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_stdRootNumber_mul_of_localZeta31_identified_of_torusFinite_of_centralChar_of_gauge_of_admissible_of_principalNormPin_adm_gamma_bump_levelShift_global (solution)

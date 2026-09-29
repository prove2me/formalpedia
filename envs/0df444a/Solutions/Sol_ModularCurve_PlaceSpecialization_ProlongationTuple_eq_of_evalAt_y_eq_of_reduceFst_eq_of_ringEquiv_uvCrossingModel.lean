-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.eq_of_evalAt_y_eq_of_reduceFst_eq_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ad81e129-6b4a-52cb-9fca-c9292ae211fd

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_forall_evalAt_eq_of_reduceFst_eq
import Theorems.Thm_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver
import Theorems.Thm_IsLocalRing_exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic
import Theorems.Thm_IsLocalRing_eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_evalAt_y_eq_of_reduceFst_eq_of_ringEquiv_uvCrossingModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace SolE4_j1

section Glue

variable {S T M : Type*} [CommRing S] [CommRing T] [CommRing M]

private theorem map_map_span_pair_j1 (f : S →+* T) (ι : T ≃+* M) {a b : S} {p t α : M} (hα : IsUnit α)
    (ha : ι (f a) = p) (hb : ι (f b) = t * α) :
    Ideal.map ι (Ideal.map f (Ideal.span {a, b})) = Ideal.span {p, t} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton, ha, hb, Ideal.span_insert, Ideal.span_insert p, Ideal.span_singleton_mul_right_unit hα]

private theorem span_triple_eq_sup_j1 (a b c : M) :
    Ideal.span {a, b, c} = Ideal.span {a, b} ⊔ Ideal.span {a, c} := by
  rw [← Ideal.span_union]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

private theorem maximalIdeal_eq_span_triple_j1 [IsLocalRing M] {ϖ x y g' h' : M}
    (hm : maximalIdeal M = Ideal.span {ϖ, g', h'}) (hg : Ideal.span {ϖ, g'} = Ideal.span {ϖ, x})
    (hh : Ideal.span {ϖ, h'} = Ideal.span {ϖ, y}) : maximalIdeal M = Ideal.span {ϖ, x, y} := by
  rw [hm, span_triple_eq_sup_j1 ϖ g' h', hg, hh, ← span_triple_eq_sup_j1]

private theorem one_le_exponent_j1 [IsLocalRing M] {p U₀ V₀ X Y ω : M} {E₀ : ℕ}
    (hP : (Ideal.span {p, U₀}).IsPrime) (hP' : (Ideal.span {p, V₀}).IsPrime) (hω : IsUnit ω)
    (hXY : X * Y = p ^ E₀ * ω) (hX : ∃ γ, IsUnit γ ∧ X - γ * U₀ ∈ Ideal.span {p, V₀}) : 1 ≤ E₀ := by
  by_contra hlt
  have hE₀ : E₀ = 0 := by omega
  rw [hE₀, pow_zero, one_mul] at hXY
  have hXYu : IsUnit (X * Y) := hXY ▸ hω
  have hXu : IsUnit X := isUnit_of_mul_isUnit_left hXYu
  obtain ⟨γ, -, hγ⟩ := hX
  have h₁ : X - γ * U₀ ∈ maximalIdeal M := le_maximalIdeal hP'.ne_top hγ
  have h₂ : U₀ ∈ maximalIdeal M := le_maximalIdeal hP.ne_top (Ideal.subset_span (by simp))
  have hXm : X ∈ maximalIdeal M := by
    have h := add_mem h₁ (Ideal.mul_mem_left _ γ h₂)
    rwa [sub_add_cancel] at h
  exact mem_nonunits_iff.mp ((mem_maximalIdeal X).mp hXm) hXu

end Glue

section Model

variable {W : Type*} [CommRing W]

private theorem U_mul_V_j1 (π : W) (E : ℕ) : U (π ^ E) * V (π ^ E) = const (π ^ E) π ^ E := by
  have h : U (π ^ E) * V (π ^ E) = const (π ^ E) (π ^ E) := by
    show Ideal.Quotient.mk (uvCrossingIdeal W (π ^ E)) (MvPowerSeries.X 0)
        * Ideal.Quotient.mk (uvCrossingIdeal W (π ^ E)) (MvPowerSeries.X 1)
      = Ideal.Quotient.mk (uvCrossingIdeal W (π ^ E)) (MvPowerSeries.C (π ^ E))
    rw [← map_mul]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self _)
  rw [h, ← constHom_apply (π ^ E) (π ^ E), map_pow, constHom_apply]

section BranchReduction

variable {π : W} {E : ℕ}

private def coeffRed_j1 (π : W) (E : ℕ) (hE : 1 ≤ E) : W ⧸ Ideal.span {π ^ E} →+* W ⧸ Ideal.span {π} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self π (Nat.one_le_iff_ne_zero.mp hE)))

private theorem coeffRed_mk_j1 (hE : 1 ≤ E) (a : W) :
    coeffRed_j1 π E hE (Ideal.Quotient.mk (Ideal.span {π ^ E}) a) = Ideal.Quotient.mk (Ideal.span {π}) a :=
  Ideal.Quotient.factor_mk _ a

private noncomputable def branchRed_j1 (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E})) :
    UVCrossingModel W (π ^ E) →+* PowerSeries (W ⧸ Ideal.span {π}) :=
  (PowerSeries.map (coeffRed_j1 π E hE)).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {T})))

private theorem branchRed_apply_j1 (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (r : UVCrossingModel W (π ^ E)) :
    branchRed_j1 hE T e r = PowerSeries.map (coeffRed_j1 π E hE) (e (Ideal.Quotient.mk (Ideal.span {T}) r)) :=
  rfl

private theorem branchRed_self_j1 (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E})) :
    branchRed_j1 hE T e T = 0 := by
  rw [branchRed_apply_j1, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self T), map_zero, map_zero]

private theorem branchRed_const_j1 (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heC : ∀ a : W, e (Ideal.Quotient.mk _ (const (π ^ E) a))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) a))
    (a : W) :
    branchRed_j1 hE T e (const (π ^ E) a) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) a) := by
  rw [branchRed_apply_j1, heC, PowerSeries.map_C, coeffRed_mk_j1]

private theorem branchRed_eq_X_j1 (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    {S : UVCrossingModel W (π ^ E)} (heS : e (Ideal.Quotient.mk _ S) = PowerSeries.X) :
    branchRed_j1 hE T e S = PowerSeries.X := by
  rw [branchRed_apply_j1, heS, PowerSeries.map_X]

private theorem branchRed_eq_zero_iff_j1 (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heC : ∀ a : W, e (Ideal.Quotient.mk _ (const (π ^ E) a))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) a))
    (r : UVCrossingModel W (π ^ E)) :
    branchRed_j1 hE T e r = 0 ↔ r ∈ Ideal.span {const (π ^ E) π, T} := by
  constructor
  · intro hr
    rw [branchRed_apply_j1] at hr

    have hcoef : ∀ n, ∃ b : W, PowerSeries.coeff n (e (Ideal.Quotient.mk (Ideal.span {T}) r))
        = Ideal.Quotient.mk (Ideal.span {π ^ E}) (π * b) := by
      intro n
      have hn := congrArg (PowerSeries.coeff n) hr
      rw [PowerSeries.coeff_map, map_zero] at hn
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PowerSeries.coeff n (e (Ideal.Quotient.mk (Ideal.span {T}) r)))
      rw [← ha, coeffRed_mk_j1] at hn
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hn)
      exact ⟨b, by rw [← ha, ← hb, mul_comm]⟩
    choose b hb using hcoef
    have hg : e (Ideal.Quotient.mk (Ideal.span {T}) r)
        = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) π)
          * PowerSeries.mk fun n => Ideal.Quotient.mk (Ideal.span {π ^ E}) (b n) := by
      ext n
      simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← map_mul, hb n]

    obtain ⟨s, hs⟩ :=
      Ideal.Quotient.mk_surjective (e.symm (PowerSeries.mk fun n => Ideal.Quotient.mk (Ideal.span {π ^ E}) (b n)))
    have hr' : Ideal.Quotient.mk (Ideal.span {T}) r = Ideal.Quotient.mk (Ideal.span {T}) (const (π ^ E) π * s) := by
      apply e.injective
      rw [map_mul (Ideal.Quotient.mk (Ideal.span {T})), map_mul e, heC π, hs, RingEquiv.apply_symm_apply, hg]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hr')
    exact Ideal.mem_span_pair.mpr ⟨s, t, by linear_combination ht⟩
  · intro hr
    obtain ⟨a, d, had⟩ := Ideal.mem_span_pair.mp hr
    rw [← had, map_add, map_mul, map_mul, branchRed_self_j1, branchRed_const_j1 hE T e heC, mul_zero, add_zero,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), map_zero, mul_zero]

private theorem isPrime_span_const_and_notMem_j1 (hπ : (Ideal.span {π}).IsPrime) (hE : 1 ≤ E)
    (T S : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heS : e (Ideal.Quotient.mk _ S) = PowerSeries.X)
    (heC : ∀ a : W, e (Ideal.Quotient.mk _ (const (π ^ E) a))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) a)) :
    (Ideal.span {const (π ^ E) π, T}).IsPrime ∧ S ∉ Ideal.span {const (π ^ E) π, T} := by
  haveI := hπ
  haveI : IsDomain (W ⧸ Ideal.span {π}) := Ideal.Quotient.isDomain _
  have hker : RingHom.ker (branchRed_j1 hE T e) = Ideal.span {const (π ^ E) π, T} := by
    ext r
    rw [RingHom.mem_ker]
    exact branchRed_eq_zero_iff_j1 hE T e heC r
  refine ⟨?_, fun hS => ?_⟩
  · rw [← hker]
    exact RingHom.ker_isPrime _
  have h0 := (branchRed_eq_zero_iff_j1 hE T e heC S).mpr hS
  rw [branchRed_eq_X_j1 hE T e heS] at h0
  exact PowerSeries.X_ne_zero h0

end BranchReduction

private theorem branch_U_j1 {π : W} (hπ : (Ideal.span {π}).IsPrime) (E : ℕ) (hE : 1 ≤ E) :
    (Ideal.span {const (π ^ E) π, U (π ^ E)}).IsPrime ∧
      V (π ^ E) ∉ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  obtain ⟨e, heV, -, heC⟩ := exists_ringEquiv_quotient_span_U_powerSeries (π ^ E)
  exact isPrime_span_const_and_notMem_j1 hπ hE (U (π ^ E)) (V (π ^ E)) e heV heC

private theorem branch_V_j1 {π : W} (hπ : (Ideal.span {π}).IsPrime) (E : ℕ) (hE : 1 ≤ E) :
    (Ideal.span {const (π ^ E) π, V (π ^ E)}).IsPrime ∧
      U (π ^ E) ∉ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
  obtain ⟨e, heU, -, heC⟩ := exists_ringEquiv_quotient_span_V_powerSeries (π ^ E)
  exact isPrime_span_const_and_notMem_j1 hπ hE (V (π ^ E)) (U (π ^ E)) e heU heC

end Model

section Eval

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

private theorem evalAt_zero_j1 (v : Place L F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap L v.ResidueField), v.residueInv_algebraMap]

private theorem evalAt_add_j1 (v : Place L F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  refine v.algebraMap_residueField_injective ?_
  have hsum := v.algebraMap_evalAt hv (add_mem hf hg)
  rw [hsum, map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  exact map_add (residue v.toValuationSubring) ⟨f, hf⟩ ⟨g, hg⟩

private theorem evalAt_mul_j1 (v : Place L F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  refine v.algebraMap_residueField_injective ?_
  have hprod := v.algebraMap_evalAt hv (mul_mem hf hg)
  rw [hprod, map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  exact map_mul (residue v.toValuationSubring) ⟨f, hf⟩ ⟨g, hg⟩

private theorem evalAt_algebraMap_j1 (v : Place L F) (a : L) : v.evalAt (algebraMap L F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap L F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) = algebraMap L v.toValuationSubring a :=
    Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply L v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]

end Eval

section Contraction

variable {L : Type*} [Field L] {A : ValuationSubring L} {B : Type*} [CommRing B] [IsLocalRing B]

private theorem contraction_j1 (e e' : B →+* L) (hA : ∀ g, e g ∈ A) (hA' : ∀ g, e' g ∈ A) {ϖ x y u : B} {E₀ : ℕ}
    (hmax : maximalIdeal B = Ideal.span {ϖ, x, y})
    (hres : ∀ g : B, ∃ o : B, e o = e' o ∧ g - o ∈ maximalIdeal B)
    (hϖ : e ϖ = e' ϖ) (hy : e y = e' y) (hxy : x * y = ϖ ^ E₀ * u) (hy0 : e y ≠ 0)
    (hu1 : A.valuation (e u) = 1) {ρ : A.ValueGroup} (hρϖ : A.valuation (e ϖ) ≤ ρ)
    (hρx : A.valuation (e x) ≤ ρ) (hρy : A.valuation (e y) ≤ ρ) :
    ∀ n : ℕ, ∀ g : B, A.valuation (e g - e' g) ≤ ρ ^ n := by

  have h₁ : e x * e y = e ϖ ^ E₀ * e u := by
    simpa only [map_mul, map_pow] using congrArg (fun z => e z) hxy
  have h₂ : e' x * e y = e ϖ ^ E₀ * e' u := by
    have h := congrArg (fun z => e' z) hxy
    simp only [map_mul, map_pow] at h
    rwa [← hy, ← hϖ] at h
  have h₃ : (e x - e' x) * e u * e y = e x * (e u - e' u) * e y := by
    linear_combination e' u * h₁ - e u * h₂
  have hxd : A.valuation (e x - e' x) = A.valuation (e x) * A.valuation (e u - e' u) := by
    have h := congrArg (fun z => A.valuation z) (mul_right_cancel₀ hy0 h₃)
    simp only [Valuation.map_mul, hu1, mul_one] at h
    exact h
  intro n
  induction n with
  | zero =>
    intro g
    rw [pow_zero]
    exact A.valuation_le_one ⟨_, sub_mem (hA g) (hA' g)⟩
  | succ n ih =>
    intro g
    obtain ⟨o, ho, hgo⟩ := hres g
    rw [hmax, Ideal.mem_span_insert] at hgo
    obtain ⟨a, z, hz, hgz⟩ := hgo
    rw [Ideal.mem_span_insert] at hz
    obtain ⟨b, z', hz', hzz'⟩ := hz
    rw [Ideal.mem_span_singleton'] at hz'
    obtain ⟨c, hc⟩ := hz'
    have hg : g = o + (a * ϖ + (b * x + c * y)) := by
      rw [hc, ← hzz', ← hgz]
      ring
    have hval : e g - e' g
        = (e a - e' a) * e ϖ + (((e b - e' b) * e x + e' b * (e x - e' x)) + (e c - e' c) * e y) := by
      rw [hg]
      simp only [map_add, map_mul]
      rw [ho, ← hϖ, ← hy]
      ring
    have hb' : A.valuation (e' b) ≤ 1 := A.valuation_le_one ⟨_, hA' b⟩
    have t₁ : A.valuation ((e a - e' a) * e ϖ) ≤ ρ ^ (n + 1) := by
      rw [Valuation.map_mul, pow_succ]
      exact mul_le_mul' (ih a) hρϖ
    have t₂ : A.valuation ((e b - e' b) * e x) ≤ ρ ^ (n + 1) := by
      rw [Valuation.map_mul, pow_succ]
      exact mul_le_mul' (ih b) hρx
    have t₃ : A.valuation (e' b * (e x - e' x)) ≤ ρ ^ (n + 1) := by
      rw [Valuation.map_mul, hxd, pow_succ']
      calc A.valuation (e' b) * (A.valuation (e x) * A.valuation (e u - e' u))
          ≤ 1 * (ρ * ρ ^ n) := mul_le_mul' hb' (mul_le_mul' hρx (ih u))
        _ = ρ * ρ ^ n := one_mul _
    have t₄ : A.valuation ((e c - e' c) * e y) ≤ ρ ^ (n + 1) := by
      rw [Valuation.map_mul, pow_succ]
      exact mul_le_mul' (ih c) hρy
    rw [hval]
    refine (A.valuation.map_add _ _).trans (max_le t₁ ?_)
    refine (A.valuation.map_add _ _).trans (max_le ?_ t₄)
    exact (A.valuation.map_add _ _).trans (max_le t₂ t₃)

end Contraction

section Finish

private theorem valuation_q_lt_one_j1 (q : ℕ) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := by
  have hmem : ((q : ℕ) : A) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h := hunit.map red
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  have h := (A.valuation_lt_one_iff ((q : ℕ) : A)).mp hmem
  simpa using h

private theorem eq_zero_of_forall_le_pow_j1 {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} (hq : q.Prime)
    (hAq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1) {ρ : A.ValueGroup}
    (hρ : ∃ ε : AlgebraicClosure ℚ, ε ≠ 0 ∧ A.valuation ε = ρ) (hρ1 : ρ < 1) {δ : AlgebraicClosure ℚ}
    (hδ : ∀ n : ℕ, A.valuation δ ≤ ρ ^ n) : δ = 0 := by
  by_contra hδ0
  obtain ⟨ε, hε0, rfl⟩ := hρ
  obtain ⟨a, ha, b, hab⟩ := A.exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic hq hAq hε0
  obtain ⟨c, hc, d, hcd⟩ := A.exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic hq hAq hδ0
  set t := A.valuation ((q : ℕ) : AlgebraicClosure ℚ) with ht
  have ht0 : t ≠ 0 := by
    rw [ht, ne_eq, Valuation.zero_iff]
    exact Nat.cast_ne_zero.mpr hq.ne_zero

  have hpow_lt : ∀ {s : A.ValueGroup}, s < 1 → ∀ m : ℕ, s ^ (m + 1) < 1 := fun {s} hs m => by
    rw [pow_succ]
    exact lt_of_le_of_lt ((mul_le_mul_left (pow_le_one' hs.le m) s).trans (one_mul s).le) hs

  have hnat : ∀ z : ℤ, t ^ z ≤ 1 → ∃ n : ℕ, t ^ z = t ^ n := by
    intro z hz
    rcases z with n | m
    · exact ⟨n, by rw [Int.ofNat_eq_natCast, zpow_natCast]⟩
    · exfalso
      rw [zpow_negSucc] at hz
      have h := mul_le_mul_right hz (t ^ (m + 1))
      rw [mul_inv_cancel₀ (pow_ne_zero _ ht0), mul_one] at h
      exact absurd (lt_of_le_of_lt h (hpow_lt hAq m)) (lt_irrefl _)
  have hεa : A.valuation ε ^ a < 1 := by
    rw [← Nat.sub_add_cancel ha]
    exact hpow_lt hρ1 (a - 1)
  obtain ⟨B, hB⟩ := hnat b (by rw [← hab]; exact hεa.le)
  obtain ⟨D, hD⟩ := hnat d (by rw [← hcd]; exact pow_le_one' ((hδ 0).trans (pow_zero _).le) c)
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [hab, hB, pow_zero] at hεa
    exact lt_irrefl _ hεa
  set m := D + 1 with hm
  have h₁ : A.valuation δ ^ c ≤ t ^ (B * m * c) := by
    calc A.valuation δ ^ c ≤ (A.valuation ε ^ (a * m)) ^ c := pow_le_pow_left' (hδ (a * m)) c
      _ = t ^ (B * m * c) := by rw [pow_mul (A.valuation ε) a m, hab, hB, pow_mul t (B * m) c, pow_mul t B m]
  rw [hcd, hD] at h₁
  have hle : m ≤ B * m * c :=
    calc m = 1 * m * 1 := by ring
      _ ≤ B * m * c := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pos_of_ne_zero hB0) le_rfl) hc
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  rw [hr, pow_add, hm, pow_succ] at h₁
  have h₂ : t ^ D * t * t ^ r ≤ t ^ D * t := by
    calc t ^ D * t * t ^ r ≤ t ^ D * t * 1 := mul_le_mul_right (pow_le_one' hAq.le r) _
      _ = t ^ D * t := mul_one _
  have h₃ := mul_le_mul_right (h₁.trans h₂) (t ^ D)⁻¹
  rw [inv_mul_cancel₀ (pow_ne_zero _ ht0), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht0), one_mul] at h₃
  exact (not_le.mpr hAq) h₃

end Finish

section Node

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))

private noncomputable def evalHom_j1 (P₁ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hP₁ : P.reduceFst P₁ = w) :
    ↥(R.nodeIntegersOver K w) →+* AlgebraicClosure ℚ where
  toFun g := P₁.evalAt (g : ↥(modularFunctionFieldBar (N * q)))
  map_one' := by
    simp only [OneMemClass.coe_one]
    exact P₁.evalAt_one
  map_mul' g₁ g₂ := by
    simp only [MulMemClass.coe_mul]
    exact evalAt_mul_j1 P₁ (isRational_place_modularFunctionFieldBar (N * q) P₁)
      (R.mem_toValuationSubring_of_mem_nodeIntegers g₁.2.1 hP₁)
      (R.mem_toValuationSubring_of_mem_nodeIntegers g₂.2.1 hP₁)
  map_zero' := by
    simp only [ZeroMemClass.coe_zero]
    exact evalAt_zero_j1 P₁
  map_add' g₁ g₂ := by
    simp only [AddMemClass.coe_add]
    exact evalAt_add_j1 P₁ (isRational_place_modularFunctionFieldBar (N * q) P₁)
      (R.mem_toValuationSubring_of_mem_nodeIntegers g₁.2.1 hP₁)
      (R.mem_toValuationSubring_of_mem_nodeIntegers g₂.2.1 hP₁)

private theorem evalHom_apply_j1 (P₁ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hP₁ : P.reduceFst P₁ = w) (g : ↥(R.nodeIntegersOver K w)) :
    evalHom_j1 R K w P₁ hP₁ g = P₁.evalAt (g : ↥(modularFunctionFieldBar (N * q))) := rfl

private theorem evalHom_nodeConst_j1 (P₁ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hP₁ : P.reduceFst P₁ = w) (o : ↥(NodeLocalized.coeffSubring A K)) :
    evalHom_j1 R K w P₁ hP₁ (R.nodeConst K w o) = (o : AlgebraicClosure ℚ) := by
  rw [evalHom_apply_j1, R.coe_nodeConst]
  exact evalAt_algebraMap_j1 P₁ _

private theorem map_nodeConst_j1 [IsLocalRing ↥(R.nodeIntegersOver K w)] (ϖ : ↥(NodeLocalized.coeffSubring A K))
    {W : Type*} [CommRing W] (π : W) (E : ℕ)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o) :
    ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π := by
  rw [← hσπ]
  exact hconst π

section Transport

variable {B₀ C₀ M₀ : Type*} [CommRing B₀] [CommRing C₀] [CommRing M₀]

private theorem transport_mul_j1 (f : B₀ →+* C₀) (ι : C₀ ≃+* M₀) {x y ϖ u : B₀} {n : ℕ}
    (hxy : x * y = ϖ ^ n * u) {p : M₀} (hϖ : ι (f ϖ) = p) : ι (f x) * ι (f y) = p ^ n * ι (f u) := by
  rw [← map_mul ι, ← map_mul f, hxy, map_mul f, map_mul ι, map_pow f, map_pow ι, hϖ]

end Transport

private theorem map_x_mul_y_j1 [IsAlgClosed k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) {W : Type*} [CommRing W] (π : W) (E : ℕ)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) :
    ι (algebraMap _ _ c.x) * ι (algebraMap _ _ c.y) = const (π ^ E) π ^ E₀ * ι (algebraMap _ _ u) :=
  transport_mul_j1 _ ι hxy hϖ

private theorem isUnit_map_j1 [IsLocalRing ↥(R.nodeIntegersOver K w)] {W : Type*} [CommRing W] (π : W) (E : ℕ)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) : IsUnit (ι (algebraMap _ _ u)) :=
  (hu.map (algebraMap _ (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))).map ι

private theorem map_x_branch_j1 [IsAlgClosed k] [DecidableEq k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    {W : Type*} [CommRing W] (π : W) (E : ℕ)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) :
    ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ c.x) - γ * U (π ^ E) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
  obtain ⟨γ, hγ, h⟩ := hres₂ c.x 1 c.nodeResidue₂_x_ne_zero (by rw [Nat.cast_one]; exact c.x_snd)
  rw [pow_one] at h
  exact ⟨γ, hγ, h⟩

private theorem map_y_branch_j1 [IsAlgClosed k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    {W : Type*} [CommRing W] (π : W) (E : ℕ)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (c : R.NodeCoordinates K w) :
    ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ c.y) - γ * V (π ^ E) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  obtain ⟨γ, hγ, h⟩ := hres₁ c.y 1 c.nodeResidue₁_y_ne_zero (by rw [Nat.cast_one]; exact c.y_fst)
  rw [pow_one] at h
  exact ⟨γ, hγ, h⟩

private theorem maximalIdeal_eq_j1 [IsAlgClosed k] [DecidableEq k]
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) :
    1 ≤ E₀ ∧ maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} := by
  obtain ⟨hdom, hloc, -⟩ := UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow π hπ E hE
  haveI := hdom
  haveI := hloc
  have hπP : (Ideal.span {π}).IsPrime := (PrincipalIdealRing.isMaximal_of_irreducible hπ).isPrime
  obtain ⟨hPU, hVU⟩ := branch_U_j1 hπP E hE
  obtain ⟨hPV, hUV⟩ := branch_V_j1 hπP E hE
  have hϖ' := map_nodeConst_j1 R K w ϖ π E σ hσπ ι hconst
  have hXY := map_x_mul_y_j1 R K w ϖ π E ι hϖ' c E₀ u hxy
  have hω := isUnit_map_j1 R K w π E ι u hu
  have hX := map_x_branch_j1 R K w π E ι hres₂ c
  have hY := map_y_branch_j1 R K w π E ι hres₁ c
  have hE₀ : 1 ≤ E₀ := one_le_exponent_j1 hPU hPV hω hXY hX
  obtain ⟨-, α, β, hα, hβ, hXα, hYβ⟩ :=
    IsLocalRing.eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime
      hE hE₀ (U_mul_V_j1 π E) hPU hPV hUV hVU hω hXY hX hY
  have hg := map_map_span_pair_j1 (algebraMap ↥(R.nodeIntegersOver K w)
    (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) ι hα hϖ' hXα
  have hh := map_map_span_pair_j1 (algebraMap ↥(R.nodeIntegersOver K w)
    (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) ι hβ hϖ' hYβ
  obtain ⟨g', h', ω', -, -, hm, -, -, -, -, hg', hh'⟩ :=
    IsLocalRing.exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel π hπ E hE ι
      (R.nodeConst K w ϖ) c.x c.y hϖ' hg hh
  exact ⟨hE₀, maximalIdeal_eq_span_triple_j1 hm hg' hh'⟩

private theorem agree_j1 [IsAlgClosed k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hvalA : R.ValueIntegralityLaw w)
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) (hE₀ : 1 ≤ E₀)
    (hmax : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (P₁ P₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hP₁ : P.reduceFst P₁ = w) (hP₂ : P.reduceFst P₂ = w)
    (hy : P₁.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q)))
      = P₂.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q)))) :
    ∀ g : ↥(R.nodeIntegersOver K w),
      P₁.evalAt (g : ↥(modularFunctionFieldBar (N * q))) = P₂.evalAt (g : ↥(modularFunctionFieldBar (N * q))) := by
  set e := evalHom_j1 R K w P₁ hP₁ with he
  set e' := evalHom_j1 R K w P₂ hP₂ with he'
  have hA : ∀ g, e g ∈ A := fun g => by
    rw [he, evalHom_apply_j1]
    exact hvalA _ g.2.1 P₁ hP₁
  have hA' : ∀ g, e' g ∈ A := fun g => by
    rw [he', evalHom_apply_j1]
    exact hvalA _ g.2.1 P₂ hP₂
  have hconst : ∀ o, e (R.nodeConst K w o) = e' (R.nodeConst K w o) := fun o => by
    rw [he, he', evalHom_nodeConst_j1, evalHom_nodeConst_j1]
  have hres' : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o, e o = e' o ∧ g - o ∈ maximalIdeal ↥(R.nodeIntegersOver K w) := by
    intro g
    obtain ⟨o, ho⟩ := hres g
    exact ⟨R.nodeConst K w o, hconst o, (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr ho)⟩
  have hy' : e c.y = e' c.y := by
    rw [he, he', evalHom_apply_j1, evalHom_apply_j1]
    exact hy

  have hx0 : c.x ≠ 0 := by
    intro h
    have h' : (c.x : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [h, ZeroMemClass.coe_zero]
    apply c.nodeResidue₂_x_ne_zero
    rw [show (⟨c.x, c.x.2.1⟩ : ↥(R.nodeIntegers w)) = 0 from Subtype.ext h', map_zero]
  have hy0 : c.y ≠ 0 := by
    intro h
    have h' : (c.y : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [h, ZeroMemClass.coe_zero]
    apply c.nodeResidue₁_y_ne_zero
    rw [show (⟨c.y, c.y.2.1⟩ : ↥(R.nodeIntegers w)) = 0 from Subtype.ext h', map_zero]
  have hϖB : R.nodeConst K w ϖ ≠ 0 := by
    intro h0
    have h : c.x * c.y = 0 := by rw [hxy, h0, zero_pow (by omega), zero_mul]
    exact mul_ne_zero hx0 hy0 h
  have hϖv : e (R.nodeConst K w ϖ) ≠ 0 := by
    rw [he, evalHom_nodeConst_j1]
    intro h
    exact hϖB (by rw [ZeroMemClass.coe_eq_zero.mp h, map_zero])
  have hu1 : A.valuation (e u) = 1 := by
    have hle : A.valuation (e u) ≤ 1 := A.valuation_le_one ⟨_, hA u⟩
    have hnot : ¬ A.valuation (e u) < 1 := by
      intro hlt
      rw [he, evalHom_apply_j1] at hlt
      exact mem_nonunits_iff.mp ((mem_maximalIdeal u).mp
        ((R.valuation_evalAt_lt_one_iff_mem_maximalIdeal K w hvalA P₁ hP₁ u).mp hlt)) hu
    exact le_antisymm hle (not_lt.mp hnot)
  have heu : e u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  have hxyv : e c.x * e c.y ≠ 0 := by
    have h : e c.x * e c.y = e (R.nodeConst K w ϖ) ^ E₀ * e u := by
      simpa only [map_mul, map_pow] using congrArg (fun z => e z) hxy
    rw [h]
    exact mul_ne_zero (pow_ne_zero _ hϖv) heu
  have hxv : e c.x ≠ 0 := left_ne_zero_of_mul hxyv
  have hyv : e c.y ≠ 0 := right_ne_zero_of_mul hxyv

  have hgen : ∀ z : ↥(R.nodeIntegersOver K w), z ∈ ({R.nodeConst K w ϖ, c.x, c.y} : Set _) →
      A.valuation (e z) < 1 := by
    intro z hz
    rw [he, evalHom_apply_j1]
    refine (R.valuation_evalAt_lt_one_iff_mem_maximalIdeal K w hvalA P₁ hP₁ z).mpr ?_
    rw [hmax]
    exact Ideal.subset_span hz
  have hvϖ := hgen (R.nodeConst K w ϖ) (by simp)
  have hvx := hgen c.x (by simp)
  have hvy := hgen c.y (by simp)
  set ρ := max (max (A.valuation (e (R.nodeConst K w ϖ))) (A.valuation (e c.x))) (A.valuation (e c.y)) with hρ
  have hρ1 : ρ < 1 := max_lt (max_lt hvϖ hvx) hvy
  have hρε : ∃ ε : AlgebraicClosure ℚ, ε ≠ 0 ∧ A.valuation ε = ρ := by
    rcases max_choice (max (A.valuation (e (R.nodeConst K w ϖ))) (A.valuation (e c.x))) (A.valuation (e c.y))
      with h | h
    · rcases max_choice (A.valuation (e (R.nodeConst K w ϖ))) (A.valuation (e c.x)) with h' | h'
      · exact ⟨_, hϖv, by rw [hρ, h, h']⟩
      · exact ⟨_, hxv, by rw [hρ, h, h']⟩
    · exact ⟨_, hyv, by rw [hρ, h]⟩
  have hcontr := contraction_j1 (ρ := ρ) e e' hA hA' hmax hres' (hconst ϖ) hy' hxy hyv hu1
    (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _)
  intro g
  have hq : q.Prime := Fact.out
  have hδ := eq_zero_of_forall_le_pow_j1 hq (valuation_q_lt_one_j1 q red) hρε hρ1 (fun n => hcontr n g)
  have hδ' := sub_eq_zero.mp hδ
  rw [he, he', evalHom_apply_j1, evalHom_apply_j1] at hδ'
  exact hδ'

end Node

end SolE4_j1

open SolE4_j1 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hvalA : R.ValueIntegralityLaw w)
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) :
    ∀ V V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → P.reduceFst V' = w →
      V.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q)))
        = V'.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q))) →
      V = V' := by
  have _ := hmodel
  have _ := hord
  have _ := hϖ
  intro V₁ V₂ hV₁ hV₂ hy
  obtain ⟨hE₀, hmax⟩ := maximalIdeal_eq_j1 R K w ϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c E₀ u hu hxy
  have hht := IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two ι
    (UVCrossingModel.ringKrullDim_le_two π hπ E hE)
  exact R.eq_of_forall_evalAt_eq_of_reduceFst_eq K w hht
    (fun z hz => R.exists_mul_eq_of_mem_fieldOver_nodeIntegersOver hqN K w hw z hz) V₁ V₂ hV₁ hV₂
    (agree_j1 R K w hvalA hres ϖ c E₀ u hu hxy hE₀ hmax V₁ V₂ hV₁ hV₂ hy)

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_evalAt_y_eq_of_reduceFst_eq_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_evalAt_y_eq_of_reduceFst_eq_of_ringEquiv_uvCrossingModel (solution)

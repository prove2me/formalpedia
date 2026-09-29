-- Prove2me | solution 1 for ModularCurve.DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6a8b44ab-0077-5a37-971a-2ff8f4bd82b1

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int.ModularCurve AlgebraicCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldFull IgusaScheme.jFull IgusaScheme.chartAlg IgusaScheme IgusaScheme.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd"
namespace ChartRedLevelP
p2m_open "ModularCurve"

section Descent

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (N : Submonoid A) [IsLocalization N B]
  (p : ℕ)

theorem span_natCast_eq_map : Ideal.span {((p : ℕ) : B)} = (Ideal.span {((p : ℕ) : A)}).map (algebraMap A B) := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

theorem comap_span_natCast (hN : ∀ m ∈ N, ∃ u v : A, u * (p : A) + v * m = 1)
    (hinj : Function.Injective (algebraMap A B)) :
    (Ideal.span {((p : ℕ) : B)}).comap (algebraMap A B) = Ideal.span {((p : ℕ) : A)} := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap, span_natCast_eq_map (A := A) (B := B) p,
      IsLocalization.mem_map_algebraMap_iff N B] at hx
    obtain ⟨⟨⟨a, ha⟩, ⟨m, hm⟩⟩, h⟩ := hx
    simp only at h
    have h' : x * m = a := hinj (by rw [map_mul]; exact h)
    obtain ⟨u, v, huv⟩ := hN m hm
    have : x = u * x * (p : A) + v * (x * m) := by
      calc x = x * (u * (p : A) + v * m) := by rw [huv, mul_one]
        _ = u * x * (p : A) + v * (x * m) := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)) ?_
    rw [h']
    exact Ideal.mul_mem_left _ _ ha
  · rw [← Ideal.map_le_iff_le_comap, ← span_natCast_eq_map (A := A) (B := B) p]

theorem isReduced_quotient_of_isReduced_quotient (hN : ∀ m ∈ N, ∃ u v : A, u * (p : A) + v * m = 1)
    (hinj : Function.Injective (algebraMap A B))
    [h : IsReduced (B ⧸ Ideal.span {((p : ℕ) : B)})] : IsReduced (A ⧸ Ideal.span {((p : ℕ) : A)}) := by
  have hle : Ideal.span {((p : ℕ) : A)} ≤ (Ideal.span {((p : ℕ) : B)}).comap (algebraMap A B) := by
    rw [comap_span_natCast N p hN hinj]
  refine isReduced_of_injective (Ideal.quotientMap (Ideal.span {((p : ℕ) : B)}) (algebraMap A B) hle) ?_
  apply Ideal.quotientMap_injective'
  rw [comap_span_natCast N p hN hinj]

theorem ncard_minimalPrimes_eq (hN : ∀ m ∈ N, ∃ u v : A, u * (p : A) + v * m = 1)
    (hinj : Function.Injective (algebraMap A B)) :
    (Ideal.span {((p : ℕ) : A)}).minimalPrimes.ncard = (Ideal.span {((p : ℕ) : B)}).minimalPrimes.ncard := by
  rw [← comap_span_natCast N p hN hinj, IsLocalization.minimalPrimes_comap N B]
  refine Set.ncard_image_of_injective _ ?_
  intro J J' h
  have hJ := IsLocalization.map_comap N B J
  have hJ' := IsLocalization.map_comap N B J'
  rw [Ideal.under_def] at hJ hJ'
  rw [← hJ, ← hJ']
  exact congrArg _ h

end Descent

section LevelOneMul

open scoped ModularCurve.IgusaScheme

variable (p : ℕ) [hp : Fact p.Prime] [NeZero p]

abbrev Fld : Type := ↥(modularFunctionFieldFull (1 * p))

abbrev Rp : Type := ↥(GaloisRep.ratLocalizedAt p)

def M : Submonoid ℤ :=
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)
  (Ideal.span {(p : ℤ)}).primeCompl

theorem isPrime_span : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)

scoped instance isLocalization_Rp : IsLocalization (M p) (Rp p) := by
  haveI := isPrime_span p
  exact GaloisRep.isLocalization_ratLocalizedAt hp.out

theorem mem_M_iff (s : ℤ) : s ∈ M p ↔ ¬ (p : ℤ) ∣ s := by
  haveI := isPrime_span p
  show s ∈ (Ideal.span {(p : ℤ)}).primeCompl ↔ _
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]

theorem coprime_of_mem_M {A : Type*} [CommRing A] (m : A) (hm : m ∈ (M p).map (algebraMap ℤ A)) :
    ∃ u v : A, u * (p : A) + v * m = 1 := by
  obtain ⟨s, hs, rfl⟩ := hm
  have hs' : ¬ (p : ℤ) ∣ s := (mem_M_iff p s).mp hs
  have hcop : IsCoprime (p : ℤ) s :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp.out).irreducible).mpr hs'
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨(u : A), (v : A), ?_⟩
  have := congrArg (algebraMap ℤ A) huv
  simpa using this

abbrev AZ (S : Set (Fld p)) := ↥(TwoChartIntegralModel.chartAlg ℤ (Fld p) S)
abbrev AP (S : Set (Fld p)) := ↥(TwoChartIntegralModel.chartAlg (Rp p) (Fld p) S)

scoped instance algAZAP (S : Set (Fld p)) : Algebra (AZ p S) (AP p S) :=
  (TwoChartIntegralModel.chartBaseChange ℤ (Fld p) (Rp p) S).toAlgebra

scoped instance isLoc (S : Set (Fld p)) : IsLocalization ((M p).map (algebraMap ℤ (AZ p S))) (AP p S) :=
  TwoChartIntegralModel.isLocalization_chartAlg ℤ (Fld p) (Rp p) (M p) S

theorem algebraMap_AZ_injective (S : Set (Fld p)) : Function.Injective (algebraMap (AZ p S) (AP p S)) := by
  intro x y h
  apply Subtype.ext
  have := congrArg (fun z : AP p S => (z : Fld p)) h
  simpa [RingHom.algebraMap_toAlgebra, TwoChartIntegralModel.coe_chartBaseChange] using this

theorem igusa_chartAlg_eq (S : Set (Fld p)) : IgusaScheme.chartAlg (1 * p) p S = TwoChartIntegralModel.chartAlg (Rp p) (Fld p) S :=
  Subalgebra.ext fun _ => Iff.rfl

theorem descend (S : Set (Fld p))
    (h : IsReduced (↥(IgusaScheme.chartAlg (1 * p) p S) ⧸ Ideal.span {((p : ℕ) : ↥(IgusaScheme.chartAlg (1 * p) p S))}) ∧
      (Ideal.span {((p : ℕ) : ↥(IgusaScheme.chartAlg (1 * p) p S))}).minimalPrimes.ncard = 2) :
    IsReduced (AZ p S ⧸ Ideal.span {((p : ℕ) : AZ p S)}) ∧
      (Ideal.span {((p : ℕ) : AZ p S)}).minimalPrimes.ncard = 2 := by
  rw [igusa_chartAlg_eq p S] at h
  obtain ⟨hred, hcard⟩ := h
  haveI := hred
  refine ⟨isReduced_quotient_of_isReduced_quotient ((M p).map (algebraMap ℤ (AZ p S))) p
      (coprime_of_mem_M p) (algebraMap_AZ_injective p S), ?_⟩
  rw [ncard_minimalPrimes_eq ((M p).map (algebraMap ℤ (AZ p S))) p (coprime_of_mem_M p) (algebraMap_AZ_injective p S)]
  exact hcard

theorem level_one_mul :
    IsReduced (AZ p {IgusaScheme.jFull (1 * p)} ⧸ Ideal.span {((p : ℕ) : AZ p {IgusaScheme.jFull (1 * p)})}) ∧
    (Ideal.span {((p : ℕ) : AZ p {IgusaScheme.jFull (1 * p)})}).minimalPrimes.ncard = 2 ∧
    IsReduced (AZ p {(IgusaScheme.jFull (1 * p))⁻¹} ⧸ Ideal.span {((p : ℕ) : AZ p {(IgusaScheme.jFull (1 * p))⁻¹})}) ∧
    (Ideal.span {((p : ℕ) : AZ p {(IgusaScheme.jFull (1 * p))⁻¹})}).minimalPrimes.ncard = 2 := by
  have hp1 : ¬ p ∣ 1 := fun h => hp.out.ne_one (Nat.dvd_one.mp h)
  obtain ⟨h1, h2, h3, h4⟩ :=
    ModularCurve.IgusaScheme.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd 1 p hp1
  obtain ⟨a, b⟩ := descend p {IgusaScheme.jFull (1 * p)} ⟨h1, h2⟩
  obtain ⟨c, d⟩ := descend p {(IgusaScheme.jFull (1 * p))⁻¹} ⟨h3, h4⟩
  exact ⟨a, b, c, d⟩

end LevelOneMul

def CStatement (n : ℕ) [NeZero n] (p : ℕ) : Prop :=
    IsReduced (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull n) (IgusaScheme.jFull n)) ⧸ Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull n) (IgusaScheme.jFull n)))}) ∧
    (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull n) (IgusaScheme.jFull n)))}).minimalPrimes.ncard = 2 ∧
    IsReduced (↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull n) (IgusaScheme.jFull n)) ⧸ Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull n) (IgusaScheme.jFull n)))}) ∧
    (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull n) (IgusaScheme.jFull n)))}).minimalPrimes.ncard = 2

theorem transportC {n : ℕ} [NeZero n] (p : ℕ) [NeZero p] (h : n = p) (H : CStatement n p) : CStatement p p := by
  subst h
  exact H

theorem levelP (p : ℕ) [Fact p.Prime] [NeZero p] : CStatement p p :=
  transportC p (Nat.one_mul p) (level_one_mul p)

end ModularCurve.ChartRedLevelP
p2m_reactivate "P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int.ModularCurve P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int.ModularCurve.ChartRedLevelP"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int.ModularCurve P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int.ModularCurve.ChartRedLevelP"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int.ModularCurve AlgebraicCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    IsReduced (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}) ∧
    (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes.ncard = 2 ∧
    IsReduced (↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}) ∧
    (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes.ncard = 2 :=
  ModularCurve.ChartRedLevelP.levelP p

end S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
end P2MW
export P2MW.S_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int (solution)

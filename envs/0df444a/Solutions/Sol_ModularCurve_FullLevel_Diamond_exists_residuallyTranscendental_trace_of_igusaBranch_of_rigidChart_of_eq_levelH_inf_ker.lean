-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart_of_eq_levelH_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/e6a32d4e-0588-5229-9509-a5d396cbb71e

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff

import Theorems.Thm_ModularCurve_FullLevel_Diamond_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart_of_eq_levelH_inf_ker
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace S3C4Glue

open IsLocalRing Polynomial

theorem isUnit_mk_iff {K : Type} [Field K] (O : Subring K) (x : K) (hx : x ∈ O) :
    IsUnit (⟨x, hx⟩ : ↥O) ↔ ∃ y : K, y ∈ O ∧ x * y = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨((u⁻¹ : (↥O)ˣ) : ↥O), ((u⁻¹ : (↥O)ˣ) : ↥O).2, ?_⟩
    have h := congrArg (fun z : ↥O => (z : K)) u.mul_inv
    rw [hu] at h
    simpa using h
  · rintro ⟨y, hy, hxy⟩
    exact IsUnit.of_mul_eq_one (b := (⟨y, hy⟩ : ↥O)) (Subtype.ext hxy)

theorem mem_maximalIdeal_comap_iff {k K : Type} [Field k] [Field K] [Algebra k K]
    (K₀ : IntermediateField k K) (V : ValuationSubring K) (f : ↥K₀) (hf : f ∈ V.comap (algebraMap ↥K₀ K)) :
    (⟨f, hf⟩ : ↥(V.comap (algebraMap ↥K₀ K))) ∈ IsLocalRing.maximalIdeal ↥(V.comap (algebraMap ↥K₀ K)) ↔
      (⟨(f : K), hf⟩ : ↥V) ∈ IsLocalRing.maximalIdeal ↥V := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  rw [isUnit_mk_iff (V.comap (algebraMap ↥K₀ K)).toSubring f hf]
  rw [isUnit_mk_iff V.toSubring (f : K) hf]
  constructor
  · rintro ⟨y, hy, hfy⟩
    exact ⟨(y : K), hy, by exact_mod_cast congrArg (fun z : ↥K₀ => (z : K)) hfy⟩
  · rintro ⟨y, hy, hfy⟩
    have hf0 : (f : K) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hfy; exact zero_ne_one hfy
    have hyeq : y = ((f⁻¹ : ↥K₀) : K) := by
      rw [eq_inv_of_mul_eq_one_right hfy]; push_cast; rfl
    refine ⟨f⁻¹, ?_, ?_⟩
    · show ((f⁻¹ : ↥K₀) : K) ∈ V; rw [← hyeq]; exact hy
    · exact mul_inv_cancel₀ (fun h0 => hf0 (by rw [h0]; rfl))

theorem C3aux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ :=
    Algebra.IsAlgebraic.of_injective (k₀.val) (k₀.val).toRingHom.injective
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

end S3C4Glue

open S3C4Glue in

theorem jOf_fixed_harness
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (γ : SL(2, ℤ)) (hγq : γ ∈ CongruenceSubgroup.Gamma q) (hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) :
    τ ⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ = ⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hob73 := S3C4Glue.C3aux_exists_emb k₀ q ξ hξ
  obtain ⟨ι, hι'⟩ := hob73
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := ⟨ι, hι'⟩

  have hx0 : coeffEmb ↥k₀ jq ∈ ModularCurve.laurentBaseChange ↥k₀ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact coeffEmb_mem_laurentBaseChange ↥k₀ (modularFunctionField_le_full M' (jq_mem M'))
  have hjq : coeffEmb ↥k₀ jq = ModularCurve.jqModC ↥k₀ := ModularCurve.map_jqModC (algebraMap ℚ ↥k₀)
  have heq : ModularCurve.jqNModC ↥k₀ q = ModularCurve.qExpand ↥k₀ q (coeffEmb ↥k₀ jq) := by
    rw [hjq, ModularCurve.jqNModC]
  exact (ModularCurve.FullLevel.Diamond.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM'
    ℓg hℓg hℓg12 hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ _ hx0).2 ⟨_, hjK⟩ heq γ hγ0 τ hτ

open S3C4Glue in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)

    (hover :
    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
        (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
      ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
        (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
            algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ)
    (K₀ : IntermediateField ↥k₀ ↥Kℓ) (hK₀ : K₀ = IntermediateField.fixedField G)
    (Õ : Subring ↥Kℓ)
    (Wx : ValuationSubring ↥Kℓ)
    (hOWx : ∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx)
    (hWxdvr : IsDiscreteValuationRing ↥Wx)
    (hCWx : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx)
    (hVA : ∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x)
    (hcentre : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y)
    (hne : ∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx)
    (hVj : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
        ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :
    ∃ t : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)), ∀ p : Polynomial ↥k₀, (∀ i, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
        (∃ hm : Polynomial.aeval (t : ↥K₀) p ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hm⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) →
          ∀ i, ∃ hc : algebraMap ↥k₀ ↥K₀ (p.coeff i) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hc⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)) := by
  classical

  have hfix : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ ⟨_, hjK⟩ = ⟨_, hjK⟩ := by
    intro τ hτ
    have hob74 := hGatt τ hτ
    obtain ⟨γ, hγq, hγ0, hatt⟩ := hob74
    exact jOf_fixed_harness q M' hqM' ℓg hℓg hℓg12 hℓgM' k₀ ξ hξ H₁ hH₁ Kℓ hKℓ hjK γ hγq hγ0 τ hatt
  have hF : (⟨_, hjK⟩ : ↥Kℓ) ∈ K₀ := by rw [hK₀, IntermediateField.mem_fixedField_iff]; exact hfix
  have hjWx : (⟨_, hjK⟩ : ↥Kℓ) ∈ Wx := hCWx ⟨_, hjC⟩
  refine ⟨⟨⟨_, hF⟩, hjWx⟩, ?_⟩
  intro p hpA hm i

  have hlift : p ∈ Polynomial.lifts (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨p.coeff n, hpA n⟩, rfl⟩
  have hob75 := (Polynomial.mem_lifts _).mp hlift
  obtain ⟨p', hp'⟩ := hob75

  obtain ⟨hm1, hm2⟩ := hm
  have heval : ((Polynomial.aeval ((⟨⟨_, hF⟩, hjWx⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) : ↥K₀) p : ↥K₀) : ↥Kℓ) =
      Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p'.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) := by
    rw [hp']
    change algebraMap ↥K₀ ↥Kℓ (Polynomial.aeval (⟨_, hF⟩ : ↥K₀) p) = _
    rw [← Polynomial.aeval_algebraMap_apply]
    rfl
  have hmWx : ∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p'.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx,
      (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx := by
    have hm1' : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p'.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx := by
      rw [← heval]; exact hm1
    refine ⟨hm1', ?_⟩
    have h2 := (S3C4Glue.mem_maximalIdeal_comap_iff K₀ Wx _ hm1).mp hm2
    have hel : (⟨_, hm1'⟩ : ↥Wx) =
        ⟨(((Polynomial.aeval ((⟨⟨_, hF⟩, hjWx⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) : ↥K₀) p : ↥K₀) : ↥Kℓ)), hm1⟩ :=
      Subtype.ext heval.symm
    rw [hel]; exact h2
  have hci : p'.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := hVj p' hmWx i

  have hcoeff : p.coeff i = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ (p'.coeff i) := by rw [← hp', Polynomial.coeff_map]
  have hcW : algebraMap ↥k₀ ↥Kℓ (p.coeff i) ∈ Wx := (hVA _).mpr ⟨p'.coeff i, hcoeff.symm⟩
  have hcK₀ : algebraMap ↥k₀ ↥K₀ (p.coeff i) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ) := hcW
  refine ⟨hcK₀, ?_⟩
  rw [S3C4Glue.mem_maximalIdeal_comap_iff K₀ Wx _ hcK₀]

  show (⟨algebraMap ↥k₀ ↥Kℓ (p.coeff i), hcW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply (IsLocalRing.mem_maximalIdeal _).mp hci
  have hob76 := (S3C4Glue.isUnit_mk_iff Wx.toSubring _ hcW).mp hu
  obtain ⟨v, hvW, hv⟩ := hob76

  have hc0 : algebraMap ↥k₀ ↥Kℓ (p.coeff i) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hv; exact zero_ne_one hv
  have hveq : v = algebraMap ↥k₀ ↥Kℓ (p.coeff i)⁻¹ := by
    rw [eq_inv_of_mul_eq_one_right hv, map_inv₀]
  have hob77 := (hVA _).mp (hveq ▸ hvW)
  obtain ⟨a', ha'⟩ := hob77
  refine isUnit_iff_exists_inv.mpr ⟨a', ?_⟩
  apply IsFractionRing.injective ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀
  rw [map_mul, map_one, ha', ← hcoeff]
  have hci0 : (p.coeff i) ≠ 0 := fun h0 => hc0 (by rw [h0, map_zero])
  exact mul_inv_cancel₀ hci0

end S_ModularCurve_FullLevel_Diamond_exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart_of_eq_levelH_inf_ker
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart_of_eq_levelH_inf_ker (solution)

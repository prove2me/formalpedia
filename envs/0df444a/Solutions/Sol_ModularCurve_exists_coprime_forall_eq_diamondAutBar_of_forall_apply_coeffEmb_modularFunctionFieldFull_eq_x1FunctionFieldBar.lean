-- Prove2me | solution 1 for ModularCurve.exists_coprime_forall_eq_diamondAutBar_of_forall_apply_coeffEmb_modularFunctionFieldFull_eq_x1FunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/440e45cd-06df-533a-80f1-7b10be54339e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ShimuraCovering
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_xHFunctionField_iff
import Theorems.Thm_ModularCurve_laurentBaseChange_deck_galois_package
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coprime_forall_eq_diamondAutBar_of_forall_apply_coeffEmb_modularFunctionFieldFull_eq_x1FunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace RigX0

open IntermediateField ModularCurve AlgebraicCurve

section BaseChange

variable {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

theorem isBaseChangeAutOf_unique {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    {σ σ' : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀}
    (h : IsBaseChangeAutOf L σ₀ σ) (h' : IsBaseChangeAutOf L σ₀ σ') : σ = σ' := by
  apply AlgEquiv.ext
  rintro ⟨x, hx⟩
  have hx' : x ∈ IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      apply Subtype.ext
      exact (h ⟨z, hz⟩).trans (h' ⟨z, hz⟩).symm
  | algebraMap c =>
      have : (⟨algebraMap L (LaurentSeries L) c, IntermediateField.algebraMap_mem _ c⟩ :
          laurentBaseChange L F₀) = algebraMap L (laurentBaseChange L F₀) c := rfl
      rw [this, AlgEquiv.commutes, AlgEquiv.commutes]
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz]

variable (L) [Algebra.IsAlgebraic ℚ L]

theorem baseChangeAut_eq_geomAut (σ₀ : F₀ ≃ₐ[ℚ] F₀) :
    baseChangeAut L σ₀ = geomAut L F₀ σ₀ := by
  have hgeom : IsBaseChangeAutOf L σ₀ (geomAut L F₀ σ₀) := fun y =>
    coe_geomAut_coeffEmb L F₀ σ₀ y
  exact isBaseChangeAutOf_unique (isBaseChangeAutOf_baseChangeAut ⟨_, hgeom⟩) hgeom

theorem diamondAutBar_eq_geomAut (M d : ℕ) :
    diamondAutBar M d = geomAut (AlgebraicClosure ℚ) (x1FunctionField M) (diamondAut M d) :=
  baseChangeAut_eq_geomAut (AlgebraicClosure ℚ) (diamondAut M d)

end BaseChange

end RigX0

end

open RigX0 IntermediateField in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (ρ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))

    (hρ : ∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
        (hf : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ ModularCurve.x1FunctionFieldBar (M * p)),
        ρ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ =
          ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩) :
    ∃ d : ℕ, d.Coprime (M * p) ∧
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ρ x = ModularCurve.diamondAutBar (M * p) d x := by
  classical

  have pp : p.Prime := Fact.out
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) pp.ne_zero⟩

  have hle : ModularCurve.xHFunctionField (M * p) ⊤ ≤ ModularCurve.x1FunctionField (M * p) :=
    ModularCurve.xHFunctionFieldC_le_x1 ℚ (M * p) ⊤
  have hF₀ : ModularCurve.xHFunctionField (M * p) ⊤ = ModularCurve.modularFunctionFieldFull (M * p) := by
    rw [ModularCurve.xHFunctionField, ModularCurve.xHFunctionFieldC_top,
      ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]

  obtain ⟨δ, hδ, hgalois⟩ := ModularCurve.exists_monoidHom_diamondAut_mem_xHFunctionField_iff (M * p) ⊤
    (fun d hd => ModularCurve.exists_isDiamondAut (M * p) hd)
  have hfix : ∀ (u : (⊤ : Subgroup (ZMod (M * p))ˣ)) (x : ModularCurve.x1FunctionField (M * p)),
      (x : LaurentSeries ℚ) ∈ ModularCurve.xHFunctionField (M * p) ⊤ → δ u x = x :=
    fun u x hx => (hgalois x).mp hx u
  have hgal : ∀ x : ModularCurve.x1FunctionField (M * p), (∀ u : (⊤ : Subgroup (ZMod (M * p))ˣ), δ u x = x) →
      (x : LaurentSeries ℚ) ∈ ModularCurve.xHFunctionField (M * p) ⊤ :=
    fun x hx => (hgalois x).mpr hx

  obtain ⟨hrange, -, -⟩ :=
    ModularCurve.laurentBaseChange_deck_galois_package (AlgebraicClosure ℚ) hle δ hfix hgal
  set φ : (⊤ : Subgroup (ZMod (M * p))ˣ) →*
      (↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p))) :=
    (ModularCurve.geomAut (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField (M * p))).comp δ with hφ

  have hρbar : ∀ y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHFunctionField (M * p) ⊤)),
      ρ (ModularCurve.inclusionBar (AlgebraicClosure ℚ) hle y) = ModularCurve.inclusionBar (AlgebraicClosure ℚ) hle y := by
    have key : (ρ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p))).comp
          (ModularCurve.inclusionBar (AlgebraicClosure ℚ) hle) =
        ModularCurve.inclusionBar (AlgebraicClosure ℚ) hle := by
      refine IntermediateField.algHom_ext_of_eq_adjoin (AlgebraicClosure ℚ)
        (S := ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHFunctionField (M * p) ⊤))
        (s := ⇑(ModularCurve.coeffEmb (AlgebraicClosure ℚ)) '' ((ModularCurve.xHFunctionField (M * p) ⊤ : Set (LaurentSeries ℚ)))) rfl ?_
      rintro _ ⟨y, hy, rfl⟩
      have hyfull : y ∈ ModularCurve.modularFunctionFieldFull (M * p) := hF₀ ▸ hy

      have hmem : ModularCurve.coeffEmb (AlgebraicClosure ℚ) y ∈ ModularCurve.x1FunctionFieldBar (M * p) :=
        ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hle hy)
      have hinc : ModularCurve.inclusionBar (AlgebraicClosure ℚ) hle
            ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) y, IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩⟩ =
          (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) y, hmem⟩ : ↥(ModularCurve.x1FunctionFieldBar (M * p))) :=
        Subtype.ext (ModularCurve.coe_inclusionBar (AlgebraicClosure ℚ) hle _)
      change ρ (ModularCurve.inclusionBar (AlgebraicClosure ℚ) hle
          ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) y, IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩⟩) = _
      rw [hinc]
      exact hρ ⟨y, hyfull⟩ hmem
    intro y
    exact AlgHom.congr_fun key y

  letI : MulSemiringAction (⊤ : Subgroup (ZMod (M * p))ˣ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) :=
    MulSemiringAction.compHom _ φ
  have hsmul : ∀ (u : (⊤ : Subgroup (ZMod (M * p))ˣ)) (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))), u • x = φ u x :=
    fun u x => rfl
  have hρK : ∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)),
      x ∈ FixedPoints.subfield (⊤ : Subgroup (ZMod (M * p))ˣ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) → ρ x = x := by
    intro x hx
    have hx' : x ∈ IntermediateField.fixedField φ.range := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro _ ⟨u, rfl⟩
      rw [← hsmul]
      exact hx u
    rw [← hrange] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact hρbar y
  let ρK : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[FixedPoints.subfield (⊤ : Subgroup (ZMod (M * p))ˣ) ↥(ModularCurve.x1FunctionFieldBar (M * p))]
      ↥(ModularCurve.x1FunctionFieldBar (M * p)) :=
    AlgEquiv.ofRingEquiv (f := (ρ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃+* ↥(ModularCurve.x1FunctionFieldBar (M * p))))
      (fun k => hρK k k.2)

  obtain ⟨u, hu⟩ := FixedPoints.toAlgAut_surjective (⊤ : Subgroup (ZMod (M * p))ˣ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) ρK
  refine ⟨(((u : (ZMod (M * p))ˣ) : ZMod (M * p))).val, ZMod.val_coe_unit_coprime _, fun x => ?_⟩
  have h1 : ρ x = ρK x := rfl
  have h2 : (MulSemiringAction.toAlgAut (⊤ : Subgroup (ZMod (M * p))ˣ)
      (FixedPoints.subfield (⊤ : Subgroup (ZMod (M * p))ˣ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
      ↥(ModularCurve.x1FunctionFieldBar (M * p)) u) x = u • x := rfl
  rw [h1, ← hu, h2, hsmul, hφ, MonoidHom.comp_apply, hδ u, diamondAutBar_eq_geomAut]

#print axioms solution

end S_ModularCurve_exists_coprime_forall_eq_diamondAutBar_of_forall_apply_coeffEmb_modularFunctionFieldFull_eq_x1FunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_exists_coprime_forall_eq_diamondAutBar_of_forall_apply_coeffEmb_modularFunctionFieldFull_eq_x1FunctionFieldBar (solution)

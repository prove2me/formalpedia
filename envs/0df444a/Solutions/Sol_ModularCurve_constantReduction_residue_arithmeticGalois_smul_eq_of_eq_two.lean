-- Prove2me | solution 1 for ModularCurve.constantReduction_residue_arithmeticGalois_smul_eq_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a22a94d0-4910-58aa-895c-04076e55a245

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups
open scoped Pointwise

noncomputable section

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace R0Sol

section Inertia

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_inertiaSubgroupIn_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ h : σ ∈ A.decompositionSubgroup K, (⟨σ, h⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hτI, rfl⟩
    exact ⟨hτ, hτI⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

theorem apply_mem_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) : σ x ∈ A ↔ x ∈ A := by
  have hσ' : σ⁻¹ • A = A :=
    MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup K).inv_mem hσ)
  calc σ x ∈ A ↔ σ • x ∈ A := Iff.rfl
    _ ↔ x ∈ σ⁻¹ • A := by rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    _ ↔ x ∈ A := by rw [hσ']

theorem residue_apply_eq {A : ValuationSubring L} {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K)
    {x : L} (hx : x ∈ A) :
    IsLocalRing.residue A ⟨σ x, (apply_mem_iff (mem_inertiaSubgroupIn_iff.mp hσ).1 x).mpr hx⟩ =
      IsLocalRing.residue A ⟨x, hx⟩ := by
  obtain ⟨hd, hI⟩ := mem_inertiaSubgroupIn_iff.mp hσ
  set a : A := ⟨x, hx⟩
  set g : A.decompositionSubgroup K := ⟨σ, hd⟩
  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g = 1 := MonoidHom.mem_ker.mp hI
  have happ : (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g) (IsLocalRing.residue A a)
      = g • (IsLocalRing.residue A a) := rfl
  have hres : IsLocalRing.residue A (g • a) = IsLocalRing.residue A a := by
    rw [IsLocalRing.ResidueField.residue_smul, ← happ, hker]
    rfl
  have hcoe : (g • a : A) = ⟨σ x, (apply_mem_iff hd x).mpr hx⟩ := Subtype.ext rfl
  rw [← hcoe]
  exact hres

def restrictAut (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.decompositionSubgroup K) : A →+* A where
  toFun x := ⟨σ x, (apply_mem_iff hσ x).mpr x.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' x y := Subtype.ext (map_mul σ (x : L) (y : L))
  map_zero' := Subtype.ext (map_zero σ)
  map_add' x y := Subtype.ext (map_add σ (x : L) (y : L))

theorem subtype_comp_restrictAut (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.decompositionSubgroup K) :
    A.subtype.comp (restrictAut A σ hσ) = (σ : L →+* L).comp A.subtype :=
  RingHom.ext fun _ => rfl

theorem residue_comp_restrictAut (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.inertiaSubgroupIn K) :
    (IsLocalRing.residue ↥A).comp (restrictAut A σ (mem_inertiaSubgroupIn_iff.mp hσ).1) = IsLocalRing.residue ↥A :=
  RingHom.ext fun x => residue_apply_eq hσ x.2

end Inertia

section Generic

variable {F Fbar : Type*} [Field F] [Field Fbar] (O : ValuationSubring F) (res : ↥O →+* Fbar)
  (hker : RingHom.ker res = maximalIdeal ↥O)

include hker in
theorem isUnit_of_res_ne_zero {Y : F} (hY : Y ∈ O) (h : res ⟨Y, hY⟩ ≠ 0) : IsUnit (⟨Y, hY⟩ : ↥O) := by
  by_contra hu
  have : (⟨Y, hY⟩ : ↥O) ∈ maximalIdeal ↥O := (IsLocalRing.mem_maximalIdeal _).mpr hu
  rw [← hker, RingHom.mem_ker] at this
  exact h this

theorem inv_mem_of_isUnit {Y : F} (hY : Y ∈ O) (h : IsUnit (⟨Y, hY⟩ : ↥O)) : Y⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := h
  have h1 := congrArg Subtype.val (Units.mul_inv u)
  rw [MulMemClass.coe_mul, OneMemClass.coe_one, hu] at h1

  rw [inv_eq_of_mul_eq_one_right h1]
  exact ((u⁻¹ : (↥O)ˣ) : ↥O).2

include hker in

theorem mem_of_fracForm {f Y X C : F} (hf : f ∈ O) (hY : Y ∈ O) (hX : X ∈ O) (hXu : res ⟨X, hX⟩ ≠ 0)
    (heq : f * Y = C * X) : C ∈ O := by
  have hXunit := isUnit_of_res_ne_zero O res hker hX hXu
  have hX0 : X ≠ 0 := fun h0 => by
    apply hXu
    have : (⟨X, hX⟩ : ↥O) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hC : C = f * Y * X⁻¹ := by
    field_simp
    exact heq.symm
  rw [hC]
  exact mul_mem (mul_mem hf hY) (inv_mem_of_isUnit O hX hXunit)

include hker in

theorem transfer (T : F →+* F) {f Y X C : F} (hf : f ∈ O) (hY : Y ∈ O) (hX : X ∈ O) (hC : C ∈ O)
    (hYu : res ⟨Y, hY⟩ ≠ 0) (hXu : res ⟨X, hX⟩ ≠ 0) (heq : f * Y = C * X)
    (hTY : T Y ∈ O) (hTX : T X ∈ O) (hTC : T C ∈ O)
    (hrY : res ⟨T Y, hTY⟩ = res ⟨Y, hY⟩) (hrX : res ⟨T X, hTX⟩ = res ⟨X, hX⟩) (hrC : res ⟨T C, hTC⟩ = res ⟨C, hC⟩) :
    ∃ hTf : T f ∈ O, res ⟨T f, hTf⟩ = res ⟨f, hf⟩ := by

  have hTYu : res ⟨T Y, hTY⟩ ≠ 0 := by rw [hrY]; exact hYu
  have hTYunit := isUnit_of_res_ne_zero O res hker hTY hTYu
  have hTY0 : T Y ≠ 0 := fun h0 => by
    apply hTYu
    have : (⟨T Y, hTY⟩ : ↥O) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have heqT : T f * T Y = T C * T X := by rw [← map_mul, ← map_mul, heq]
  have hTf_eq : T f = T C * T X * (T Y)⁻¹ := by
    field_simp
    exact heqT
  have hTf : T f ∈ O := by
    rw [hTf_eq]
    exact mul_mem (mul_mem hTC hTX) (inv_mem_of_isUnit O hTY hTYunit)
  refine ⟨hTf, ?_⟩

  have e1 : (⟨f, hf⟩ : ↥O) * ⟨Y, hY⟩ = ⟨C, hC⟩ * ⟨X, hX⟩ := Subtype.ext heq
  have e2 : (⟨T f, hTf⟩ : ↥O) * ⟨T Y, hTY⟩ = ⟨T C, hTC⟩ * ⟨T X, hTX⟩ := Subtype.ext heqT
  have r1 := congrArg res e1
  have r2 := congrArg res e2
  rw [map_mul, map_mul] at r1 r2
  rw [hrY, hrX, hrC, ← r1] at r2
  exact mul_right_cancel₀ hYu r2

end Generic

section Modular

variable (M' : ℕ) [NeZero M']

local notation "Lbar" => AlgebraicClosure ℚ
local notation "G₀" => ModularCurve.arithmeticGalois (modularFunctionFieldFull M')

theorem T_mem_gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]
  simp

theorem gaussFrac (A : ValuationSubring Lbar) (f : ↥(modularFunctionFieldBar M')) (hf : f ≠ 0) :
    ∃ (c : Lbar) (x y : LaurentSeries ↥A), c ≠ 0 ∧
      coeffMap (IsLocalRing.residue ↥A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      coeffMap A.subtype x ∈ modularFunctionFieldBar M' ∧ coeffMap A.subtype y ∈ modularFunctionFieldBar M' ∧
      (f : LaurentSeries Lbar) * coeffMap A.subtype y = algebraMap Lbar (LaurentSeries Lbar) c * coeffMap A.subtype x := by
  have hmem : (f : LaurentSeries Lbar) ∈ laurentBaseChange Lbar (qExpFunctionFieldC ℚ (Gamma0 M')) := by
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact f.2
  have hf1 : (f : LaurentSeries Lbar) ≠ 0 := fun h => hf (ZeroMemClass.coe_eq_zero.mp h)
  have hf' : (⟨(f : LaurentSeries Lbar), hmem⟩ : ↥(laurentBaseChange Lbar (qExpFunctionFieldC ℚ (Gamma0 M')))) ≠ 0 :=
    fun h => hf1 ((ZeroMemClass.coe_eq_zero
      (x := (⟨(f : LaurentSeries Lbar), hmem⟩ : ↥(laurentBaseChange Lbar (qExpFunctionFieldC ℚ (Gamma0 M')))))).mpr h)
  obtain ⟨c, x, y, hc, hx, hy, hxF, hyF, heq⟩ :=
    ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC Lbar A (Gamma0 M') (T_mem_gamma0 M') _ hf'
  refine ⟨c, x, y, hc, hx, hy, ?_, ?_, heq⟩
  · rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull] at hxF
    exact hxF
  · rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull] at hyF
    exact hyF

def g0S (τ : Lbar ≃ₐ[ℚ] Lbar) : SemilinearAut Lbar ↥(modularFunctionFieldBar M') := G₀ τ

theorem coe_g0S_smul (τ : Lbar ≃ₐ[ℚ] Lbar) (v : ↥(modularFunctionFieldBar M')) :
    ((g0S M' τ • v : ↥(modularFunctionFieldBar M')) : LaurentSeries Lbar) = coeffMap (τ : Lbar →+* Lbar) (v : LaurentSeries Lbar) :=
  ModularCurve.coe_arithmeticGalois_smul (modularFunctionFieldFull M') τ v

theorem g0S_smul_algebraMap (τ : Lbar ≃ₐ[ℚ] Lbar) (c : Lbar) :
    g0S M' τ • algebraMap Lbar ↥(modularFunctionFieldBar M') c = algebraMap Lbar ↥(modularFunctionFieldBar M') (τ c) := by
  rw [SemilinearAut.smul_algebraMap]
  rfl

theorem res_congr {F Fbar : Type*} [Field F] [Field Fbar] (O : ValuationSubring F) (res : ↥O →+* Fbar)
    {v w : F} (e : v = w) (hv : v ∈ O) (hw : w ∈ O) : res ⟨v, hv⟩ = res ⟨w, hw⟩ := by
  subst e
  rfl

end Modular

end R0Sol

open R0Sol

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hf' : ModularCurve.arithmeticGalois (modularFunctionFieldFull M') τ • f ∈ R₀.integers, R₀.residue ⟨ModularCurve.arithmeticGalois (modularFunctionFieldFull M') τ • f, hf'⟩ = R₀.residue ⟨f, hf⟩ := by
  intro τ hτ f hf
  have hd : τ ∈ A.decompositionSubgroup ℚ := (mem_inertiaSubgroupIn_iff.mp hτ).1

  have key : ∀ (Z : ↥(modularFunctionFieldBar M')) (z : LaurentSeries ↥A),
      (Z : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype z →
      ∃ h : Z ∈ R₀.integers,
        ((R₀.residue ⟨Z, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) z := by
    intro Z z hZz
    obtain ⟨Z, hZ⟩ := Z
    change Z = _ at hZz
    subst hZz
    exact hR₀ z hZ

  let T : ↥(modularFunctionFieldBar M') →+* ↥(modularFunctionFieldBar M') :=
    (SemilinearAut.toRingAut (g0S M' τ) : ↥(modularFunctionFieldBar M') ≃+* ↥(modularFunctionFieldBar M')).toRingHom
  have hT : ∀ v, T v = g0S M' τ • v := fun v => rfl
  show ∃ hf' : T f ∈ R₀.integers, R₀.residue ⟨T f, hf'⟩ = R₀.residue ⟨f, hf⟩
  by_cases hf0 : f = 0
  · subst hf0
    have h0 : T 0 = 0 := map_zero T
    have hT0 : T 0 ∈ R₀.integers := by rw [h0]; exact hf
    exact ⟨hT0, res_congr R₀.integers R₀.residue h0 hT0 hf⟩
  obtain ⟨c, x, y, hc, hx, hy, hxF, hyF, heq⟩ := gaussFrac M' A f hf0

  obtain ⟨hYO, hYres⟩ := key ⟨_, hyF⟩ y rfl
  obtain ⟨hXO, hXres⟩ := key ⟨_, hxF⟩ x rfl
  have heqF : f * (⟨_, hyF⟩ : ↥(modularFunctionFieldBar M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') c * ⟨_, hxF⟩ := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul,
      show ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') c : ↥(modularFunctionFieldBar M')) :
          LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c from
        IntermediateField.coe_algebraMap_apply (modularFunctionFieldBar M') c]
    exact heq
  have hYu : R₀.residue ⟨_, hYO⟩ ≠ 0 := by
    intro h; apply hy; rw [← hYres, h, ZeroMemClass.coe_zero]
  have hXu : R₀.residue ⟨_, hXO⟩ ≠ 0 := by
    intro h; apply hx; rw [← hXres, h, ZeroMemClass.coe_zero]
  have hC : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') c ∈ R₀.integers :=
    mem_of_fracForm R₀.integers R₀.residue R₀.ker_residue hf hYO hXO hXu heqF
  have hcA : c ∈ A := (R₀.algebraMap_mem_iff c).mp hC
  have hτcA : τ c ∈ A := (apply_mem_iff hd c).mpr hcA

  have hTcoe : ∀ (z : LaurentSeries ↥A) (hz : coeffMap A.subtype z ∈ modularFunctionFieldBar M'),
      ((T ⟨_, hz⟩ : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap A.subtype (coeffMap (restrictAut A τ hd) z) := by
    intro z hz
    rw [hT, coe_g0S_smul, coeffMap_coeffMap, coeffMap_coeffMap, subtype_comp_restrictAut]
  have hTres : ∀ (z : LaurentSeries ↥A),
      coeffMap (IsLocalRing.residue ↥A) (coeffMap (restrictAut A τ hd) z) = coeffMap (IsLocalRing.residue ↥A) z := by
    intro z
    rw [coeffMap_coeffMap, residue_comp_restrictAut A τ hτ]
  obtain ⟨hTYO, hTYres⟩ := key (T ⟨_, hyF⟩) _ (hTcoe y hyF)
  obtain ⟨hTXO, hTXres⟩ := key (T ⟨_, hxF⟩) _ (hTcoe x hxF)
  rw [hTres] at hTYres hTXres
  have hrY : R₀.residue ⟨T ⟨_, hyF⟩, hTYO⟩ = R₀.residue ⟨_, hYO⟩ := Subtype.ext (by rw [hTYres, hYres])
  have hrX : R₀.residue ⟨T ⟨_, hxF⟩, hTXO⟩ = R₀.residue ⟨_, hXO⟩ := Subtype.ext (by rw [hTXres, hXres])
  have hTC_eq : T (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') c) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (τ c) := by
    rw [hT]; exact g0S_smul_algebraMap M' τ c
  have hTCO : T (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') c) ∈ R₀.integers := by
    rw [hTC_eq]; exact (R₀.algebraMap_mem_iff _).mpr hτcA
  have hrC : R₀.residue ⟨_, hTCO⟩ = R₀.residue ⟨_, hC⟩ := by
    rw [res_congr R₀.integers R₀.residue hTC_eq hTCO ((R₀.algebraMap_mem_iff _).mpr hτcA)]
    have e1 := R₀.residue_algebraMap ⟨τ c, hτcA⟩
    have e2 := R₀.residue_algebraMap ⟨c, hcA⟩
    rw [residue_apply_eq hτ hcA] at e1
    exact e1.trans e2.symm
  exact transfer R₀.integers R₀.residue R₀.ker_residue T hf hYO hXO hC hYu hXu heqF hTYO hTXO hTCO hrY hrX hrC

end
end S_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq_of_eq_two
end P2MW
export P2MW.S_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq_of_eq_two (solution)

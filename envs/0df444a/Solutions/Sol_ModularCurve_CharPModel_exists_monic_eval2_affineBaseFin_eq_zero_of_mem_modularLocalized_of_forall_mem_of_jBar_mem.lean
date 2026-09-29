-- Prove2me | solution 1 for ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4f9d107c-1a4a-5d7a-bcc5-70b894c48f0c

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_le
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

open AlgebraicCurve

universe u v w

namespace JacJ9GLN

open ModularCurve ModularCurve.CharPModel IsLocalRing

namespace JacJ9GaussPoles
open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mem_of_monic_eval_eq_zero (V : ValuationSubring F) {Q : F[X]} (hQ : Q.Monic)
    (hc : ∀ i, Q.coeff i ∈ V) {u : F} (hu : Q.eval u = 0) : u ∈ V := by
  by_contra hnot
  have hinv : u⁻¹ ∈ V := (V.mem_or_inv_mem u).resolve_left hnot
  have hu0 : u ≠ 0 := fun h => hnot (h ▸ zero_mem V)
  have hQ0 : Q.natDegree ≠ 0 := fun h0 => by
    have hc : Q.coeff 0 = 1 := by
      have := hQ.coeff_natDegree
      rwa [h0] at this
    have h1 : Q = 1 := by
      rw [eq_C_of_natDegree_eq_zero h0, hc, C_1]
    rw [h1, eval_one] at hu
    exact one_ne_zero hu
  obtain ⟨n, hn⟩ : ∃ n, Q.natDegree = n + 1 := Nat.exists_eq_add_one_of_ne_zero hQ0
  rw [eval_eq_sum_range, hn, Finset.sum_range_succ, ← hn, hQ.coeff_natDegree, one_mul, hn] at hu

  have key : u = -(∑ i ∈ Finset.range (n + 1), Q.coeff i * u⁻¹ ^ (n - i)) := by
    have h2 : u ^ (n + 1) = -(∑ i ∈ Finset.range (n + 1), Q.coeff i * u ^ i) := eq_neg_of_add_eq_zero_right hu
    have h3 : u = u ^ (n + 1) * u⁻¹ ^ n := by
      rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, mul_one]
    conv_lhs => rw [h3]
    rw [h2, neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_assoc]
    congr 1
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi'
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, one_mul]
  apply hnot
  rw [key]
  exact neg_mem (sum_mem fun i _ => mul_mem (hc i) (pow_mem hinv _))

private theorem mem_of_mem_adjoin (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) {x : F}
    (hx : x ∈ V) {c : F} (hc : c ∈ Algebra.adjoin K ({x} : Set F)) : c ∈ V := by
  let S : Subalgebra K F :=
    { V.toSubring.toSubsemiring with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({x} : Set F) ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx)
  exact hle hc

private theorem exists_forall_mul_inv_pow_mem {x : F} {c : F} (hc : c ∈ Algebra.adjoin K ({x} : Set F)) :
    ∃ d : ℕ, ∀ V : ValuationSubring F, (∀ a : K, algebraMap K F a ∈ V) → x ∉ V →
      ∀ e : ℕ, d ≤ e → c * x⁻¹ ^ e ∈ V := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hc
  obtain ⟨q, rfl⟩ := hc
  refine ⟨q.natDegree, fun V hK hxV e hde => ?_⟩
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ zero_mem V)
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  rw [aeval_eq_sum_range, Finset.sum_mul]
  refine sum_mem fun i hi => ?_
  have hi' : i ≤ e := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hde
  obtain ⟨d', hd'⟩ := Nat.exists_eq_add_of_le hi'
  rw [Algebra.smul_def, mul_assoc, hd', pow_add, ← mul_assoc (x ^ i), ← mul_pow, mul_inv_cancel₀ hx0, one_pow,
    one_mul]
  exact mul_mem (hK _) (pow_mem hxinv _)

variable (K) in

private theorem forall_mem_and_exists_forall_mul_inv_pow_mem {x t : F}
    (ht : IsIntegral (Algebra.adjoin K ({x} : Set F)) t) :
    (∀ V : ValuationSubring F, (∀ a : K, algebraMap K F a ∈ V) → x ∈ V → t ∈ V) ∧
    ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ a : K, algebraMap K F a ∈ V) → x ∉ V → t * (x ^ m)⁻¹ ∈ V := by
  obtain ⟨p, hpm, hpe⟩ := ht

  set P : F[X] := p.map (algebraMap (Algebra.adjoin K ({x} : Set F)) F) with hP_def
  have hPm : P.Monic := hpm.map _
  have hPe : P.eval t = 0 := by rw [hP_def, eval_map]; exact hpe
  have hPc : ∀ i, P.coeff i ∈ Algebra.adjoin K ({x} : Set F) := by
    intro i
    rw [hP_def, coeff_map]
    exact (p.coeff i).2
  refine ⟨fun V hK hxV => mem_of_monic_eval_eq_zero V hPm (fun i => mem_of_mem_adjoin V hK hxV (hPc i)) hPe, ?_⟩

  choose dOf hdOf using fun i => exists_forall_mul_inv_pow_mem (K := K) (hPc i)
  refine ⟨(Finset.range (P.natDegree + 1)).sup dOf, fun V hK hxV => ?_⟩
  set m : ℕ := (Finset.range (P.natDegree + 1)).sup dOf with hm_def
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ zero_mem V)
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV

  have hroot : (P.scaleRoots (x⁻¹ ^ m)).eval (x⁻¹ ^ m * t) = 0 := by
    have h := scaleRoots_eval₂_eq_zero (RingHom.id F) (s := x⁻¹ ^ m) (by rw [eval₂_id]; exact hPe)
    rw [eval₂_id] at h
    simpa using h
  have hcoeff : ∀ i, (P.scaleRoots (x⁻¹ ^ m)).coeff i ∈ V := by
    intro i
    rw [coeff_scaleRoots, ← pow_mul]
    by_cases hi : i ≤ P.natDegree
    · rcases eq_or_lt_of_le hi with rfl | hlt
      · rw [Nat.sub_self, mul_zero, pow_zero, mul_one, hPm.coeff_natDegree]
        exact one_mem V
      · apply hdOf i V hK hxV
        have h1 : dOf i ≤ m := Finset.le_sup (f := dOf) (Finset.mem_range.mpr (Nat.lt_succ_of_lt hlt))
        have h2 : 1 ≤ P.natDegree - i := Nat.sub_pos_of_lt hlt
        calc dOf i ≤ m := h1
          _ = m * 1 := (mul_one m).symm
          _ ≤ m * (P.natDegree - i) := Nat.mul_le_mul_left m h2
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), zero_mul]
      exact zero_mem V
  have hmem := mem_of_monic_eval_eq_zero V ((monic_scaleRoots_iff (x⁻¹ ^ m)).mpr hPm) hcoeff hroot
  rw [inv_pow, mul_comm] at hmem
  exact hmem

end JacJ9GaussPoles

namespace JacJ9Restrict
open AlgebraicCurve IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {Ω : Type*} [Field Ω] [Algebra L Ω]
  {E E' : IntermediateField L Ω} (h : E ≤ E') {Fb' : Type u} [Field Fb'] [Algebra (ResidueField A) Fb']
  (R' : RegularProlongation A E' Fb')

private noncomputable def ints : ValuationSubring E :=
  R'.integers.comap (IntermediateField.inclusion h).toRingHom

private theorem mem_ints {u : E} : u ∈ ints h R' ↔ IntermediateField.inclusion h u ∈ R'.integers := Iff.rfl

private noncomputable def toInt : ints h R' →+* R'.integers :=
  RingHom.codRestrict ((IntermediateField.inclusion h).toRingHom.comp (ints h R').subtype) R'.integers
    fun u => u.2

private theorem coe_toInt (u : ints h R') : (toInt h R' u : E') = IntermediateField.inclusion h u := rfl

private noncomputable def res : ints h R' →+* Fb' := R'.residue.comp (toInt h R')

private theorem res_apply (u : ints h R') : res h R' u = R'.residue (toInt h R' u) := rfl

private theorem inv_mem_range {y : Fb'} (hy : y ∈ (res h R').range) : y⁻¹ ∈ (res h R').range := by
  obtain ⟨u, rfl⟩ := RingHom.mem_range.mp hy
  by_cases h0 : res h R' u = 0
  · rw [h0, inv_zero]
    exact zero_mem _
  rw [res_apply] at h0

  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp (R'.isUnit_of_residue_ne_zero h0)
  have hw' : IntermediateField.inclusion h (u : E) * (w : E') = 1 := by
    have := congrArg Subtype.val hw
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one, coe_toInt] using this
  have hinv : (u : E)⁻¹ ∈ ints h R' := by
    rw [mem_ints, map_inv₀, inv_eq_of_mul_eq_one_right hw']
    exact w.2
  have hmul : toInt h R' u * toInt h R' ⟨(u : E)⁻¹, hinv⟩ = 1 := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, coe_toInt, map_inv₀]
    exact mul_inv_cancel₀ (left_ne_zero_of_mul_eq_one hw')
  have hres : res h R' u * res h R' ⟨(u : E)⁻¹, hinv⟩ = 1 := by
    simp only [res_apply]
    rw [← map_mul, hmul, map_one]
  rw [RingHom.mem_range]
  exact ⟨⟨(u : E)⁻¹, hinv⟩, eq_inv_of_mul_eq_one_right hres⟩

private noncomputable def resField : Subfield Fb' :=
  { (res h R').range with inv_mem' := fun _ hy => inv_mem_range h R' hy }

private theorem mem_resField {y : Fb'} : y ∈ resField h R' ↔ y ∈ (res h R').range := Iff.rfl

private theorem toInt_algebraMap (a : A) (ha : algebraMap L E a ∈ ints h R') :
    toInt h R' ⟨algebraMap L E a, ha⟩ = ⟨algebraMap L E' a, (R'.algebraMap_mem_iff a).mpr a.2⟩ :=
  Subtype.ext ((IntermediateField.inclusion h).commutes (a : L))

private theorem algebraMap_mem_ints (a : A) : algebraMap L E a ∈ ints h R' := by
  rw [mem_ints, (IntermediateField.inclusion h).commutes]
  exact (R'.algebraMap_mem_iff a).mpr a.2

private theorem algebraMap_mem_resField (z : ResidueField A) :
    algebraMap (ResidueField A) Fb' z ∈ resField h R' := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  rw [← R'.residue_algebraMap a, mem_resField, RingHom.mem_range]
  exact ⟨⟨algebraMap L E a, algebraMap_mem_ints h R' a⟩,
    (res_apply h R' _).trans (congrArg R'.residue (toInt_algebraMap h R' a _))⟩

private noncomputable def resRestrict : ints h R' →+* resField h R' :=
  RingHom.codRestrict (res h R') (resField h R') fun u => (res h R').mem_range_self u

private theorem resRestrict_surjective : Function.Surjective (resRestrict h R') := fun y => by
  obtain ⟨u, hu⟩ := RingHom.mem_range.mp ((mem_resField h R').mp y.2)
  exact ⟨u, Subtype.ext hu⟩

private noncomputable def resFieldAlgebra : Algebra (ResidueField A) (resField h R') :=
  (RingHom.codRestrict (algebraMap (ResidueField A) Fb') (resField h R')
    (algebraMap_mem_resField h R')).toAlgebra

private noncomputable def restrict :
    letI := resFieldAlgebra h R'
    RegularProlongation A E (resField h R') :=
  letI := resFieldAlgebra h R'
  { integers := ints h R'
    residue := resRestrict h R'
    algebraMap_mem_iff := fun x => by
      show IntermediateField.inclusion h (algebraMap L E x) ∈ R'.integers ↔ x ∈ A
      rw [(IntermediateField.inclusion h).commutes]
      exact R'.algebraMap_mem_iff x
    residue_surjective := resRestrict_surjective h R'
    ker_residue := IsLocalRing.ker_eq_maximalIdeal _ (resRestrict_surjective h R')
    residue_algebraMap := fun a => by
      have e1 : R'.residue (toInt h R' ⟨algebraMap L E a, algebraMap_mem_ints h R' a⟩)
          = algebraMap (ResidueField A) Fb' (IsLocalRing.residue A a) :=
        (congrArg R'.residue (toInt_algebraMap h R' a _)).trans (R'.residue_algebraMap a)
      exact Subtype.ext e1
    exists_smul_mem := fun f hf => by
      obtain ⟨c, hc, hres⟩ :=
        R'.exists_smul_mem (IntermediateField.inclusion h f)
          ((map_ne_zero (IntermediateField.inclusion h)).mpr hf)
      have hsmul : IntermediateField.inclusion h (c • f) = c • IntermediateField.inclusion h f := by
        rw [Algebra.smul_def c f, map_mul, (IntermediateField.inclusion h).commutes, ← Algebra.smul_def]
      have hmem : c • f ∈ ints h R' := by
        rw [mem_ints, hsmul]
        exact hc
      refine ⟨c, hmem, fun h0 => hres ?_⟩
      have h1 : res h R' ⟨c • f, hmem⟩ = 0 := congrArg Subtype.val h0
      have e : toInt h R' ⟨c • f, hmem⟩ = ⟨c • IntermediateField.inclusion h f, hc⟩ :=
        Subtype.ext ((coe_toInt h R' _).trans hsmul)
      rw [res_apply, e] at h1
      exact h1 }

private theorem exists_regularProlongation_restrict :
    ∃ (Fb₀ : Type u) (_ : Field Fb₀) (_ : Algebra (ResidueField A) Fb₀) (R₀ : RegularProlongation A E Fb₀)
      (φ : Fb₀ →+* Fb'),
      (∀ u : E, u ∈ R₀.integers ↔ IntermediateField.inclusion h u ∈ R'.integers) ∧
      ∀ (u : E) (hu₀ : u ∈ R₀.integers) (hu : IntermediateField.inclusion h u ∈ R'.integers),
        φ (R₀.residue ⟨u, hu₀⟩) = R'.residue ⟨IntermediateField.inclusion h u, hu⟩ :=
  ⟨resField h R', inferInstance, resFieldAlgebra h R', restrict h R', (resField h R').subtype,
    fun _ => Iff.rfl, fun _ _ _ => rfl⟩

end JacJ9Restrict

section Series

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private def pack (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    LaurentSeries A where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (by
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    exact fun h0 => hn (Subtype.ext h0))

private theorem coeffMap_pack (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    coeffMap A.subtype (pack A x hx) = x := by
  ext n
  rfl

private theorem coeffMap_subtype_jqModC (N : ℕ) [NeZero N] :
    coeffMap A.subtype (jqModC A) = ((CharPModel.jBar N : modularFunctionFieldBar N) :
      LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [show coeffMap A.subtype (jqModC A) = (jqModC A).map A.subtype from rfl, map_jqModC,
    show ((CharPModel.jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) from rfl, map_jqModC]

private theorem coeffMap_residue_jqModC :
    coeffMap (residue A) (jqModC A) = jqModC (ResidueField A) := by
  rw [show coeffMap (residue A) (jqModC A) = (jqModC A).map (residue A) from rfl, map_jqModC]

end Series

section Transport

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))

private noncomputable def cA : A →+* affineBaseFin N A :=
  (constantsHom N A).codRestrict (affineBaseFin N A)
    (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩))

private noncomputable def jA : affineBaseFin N A :=
  ⟨CharPModel.jBar N, Subring.subset_closure (Or.inr rfl)⟩

private noncomputable def phi : Polynomial A →+* affineBaseFin N A :=
  Polynomial.eval₂RingHom (cA N A) (jA N A)

private theorem subtype_comp_phi :
    (affineBaseFin N A).subtype.comp (phi N A)
      = Polynomial.eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).comp A.subtype) (CharPModel.jBar N) := by
  apply Polynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, phi, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    rfl
  · rw [RingHom.comp_apply, phi, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rfl

end Transport

section Main

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
variable {k : Type u} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N)

include red in

private theorem liesOverPrime : A.LiesOverPrime q := by
  have hq0 : red (q : A) = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  have hqm : (q : A) ∈ maximalIdeal A :=
    (ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red _).mp hq0
  have h := ValuationSubring.coe_mem_nonunits_iff.mpr hqm
  rw [show ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) from map_natCast A.subtype q] at h
  exact h

omit [NeZero N] in
include red hqN in

private theorem natCast_residueField_ne_zero : ((N : ℕ) : ResidueField A) ≠ 0 := by
  intro h0
  apply hqN
  have h1 : residue A (N : A) = 0 := by rwa [map_natCast]
  rw [residue_eq_zero_iff] at h1
  have h2 : red (N : A) = 0 :=
    (ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red _).mpr h1
  rw [map_natCast] at h2
  exact (CharP.cast_eq_zero_iff k q N).mp h2

private theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have h2 := Finset.single_le_sum (s := N.divisors.filter Squarefree) (f := fun d => N / d)
    (fun _ _ => Nat.zero_le _) h1
  simp only [Nat.div_one] at h2
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) h2

set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero N] in

private theorem jBar_mem_integers (M : ℕ) [NeZero M]
    (R : RegularProlongation A (modularFunctionFieldBar M)
      (modularFunctionFieldFullC (ResidueField A) N))
    (hspec : ∀ (y : LaurentSeries A)
      (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar M) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldFullC (ResidueField A) N) :
          LaurentSeries (ResidueField A)) = coeffMap (residue A) y) :
    ∃ hj : CharPModel.jBar M ∈ R.integers,
      R.residue ⟨CharPModel.jBar M, hj⟩ = ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ := by
  have hser := coeffMap_subtype_jqModC A M
  have hmem : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar M := by
    rw [hser]; exact (CharPModel.jBar M).2
  have hsp := hspec (jqModC A) hmem
  obtain ⟨hint, hres⟩ := hsp
  have hxj : (⟨coeffMap A.subtype (jqModC A), hmem⟩ : modularFunctionFieldBar M) = CharPModel.jBar M :=
    Subtype.ext hser
  have hj : CharPModel.jBar M ∈ R.integers := by rw [← hxj]; exact hint
  refine ⟨hj, ?_⟩
  have h1 : (⟨CharPModel.jBar M, hj⟩ : R.integers) = ⟨⟨coeffMap A.subtype (jqModC A), hmem⟩, hint⟩ :=
    Subtype.ext hxj.symm
  rw [h1]
  apply Subtype.ext
  rw [hres]
  exact coeffMap_residue_jqModC A

set_option synthInstance.maxHeartbeats 1600000 in

private theorem transcendental_residue_jBar (M : ℕ) [NeZero M] {Fb : Type v} [Field Fb]
    [Algebra (ResidueField A) Fb] (R : RegularProlongation A (modularFunctionFieldBar M) Fb)
    (hj : CharPModel.jBar M ∈ R.integers) (ψ : Fb →ₐ[ResidueField A] (modularFunctionFieldFullC (ResidueField A) N))
    (hψ : ψ (R.residue ⟨CharPModel.jBar M, hj⟩)
      = ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩) :
    Transcendental (ResidueField A) (R.residue ⟨CharPModel.jBar M, hj⟩) := by
  have hinj : Function.Injective
      (algebraMap (modularFunctionFieldFullC (ResidueField A) N) (LaurentSeries (ResidueField A))) :=
    (algebraMap (modularFunctionFieldFullC (ResidueField A) N) (LaurentSeries (ResidueField A))).injective
  have htr : Transcendental (ResidueField A)
      (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :
        modularFunctionFieldFullC (ResidueField A) N) :=
    (transcendental_algebraMap_iff
      (a := (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :
        modularFunctionFieldFullC (ResidueField A) N)) hinj).mp
      (transcendental_jqModC (ResidueField A))
  rw [← hψ] at htr
  exact fun halg => htr ((isAlgebraic_algHom_iff ψ ψ.toRingHom.injective).mpr halg)

set_option synthInstance.maxHeartbeats 1600000 in
include red in

private theorem inclusion_mem_integers
    (R' : RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (ResidueField A) N))
    (hpin : ∀ f : modularFunctionFieldBar (N * q), f ∈ R'.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (t : modularFunctionFieldBar N)
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    IntermediateField.inclusion (modularFunctionFieldBar_le N (dvd_mul_right N q)) t ∈ R'.integers := by
  have ht' := (CharPReduction.mem_localizedAtKer A.toSubring red
    (CharPReduction.modularRing (N * q) A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring)).mp ht
  obtain ⟨r, s, hs, hts⟩ := ht'
  have hrA : ∀ n : ℤ, (r : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A := fun n =>
    CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring r.2 n
  have hsA : ∀ n : ℤ, (s : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A := fun n =>
    CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring s.2 n
  rw [hpin]
  refine ⟨pack A r hrA, pack A s hsA, ?_, ?_⟩
  · intro h0
    apply hs
    rw [CharPReduction.redKer, RingHom.mem_ker]
    ext n
    have hn := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff n) h0
    simp only [HahnSeries.coeff_zero] at hn ⊢
    have hn' : residue A ⟨(s : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hsA n⟩ = 0 := hn
    rw [residue_eq_zero_iff] at hn'
    rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
    exact (ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red _).mpr hn'
  · rw [coeffMap_pack, coeffMap_pack]
    exact hts

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 4000000 in

private theorem mem_integers_of_inclusion_mem
    (R : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldFullC (ResidueField A) N))
    (hjO : CharPModel.jBar N ∈ R.integers)
    (hx : Transcendental (ResidueField A) (R.residue ⟨CharPModel.jBar N, hjO⟩))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A)
        ({R.residue ⟨CharPModel.jBar N, hjO⟩} : Set (modularFunctionFieldFullC (ResidueField A) N)))
      (modularFunctionFieldFullC (ResidueField A) N))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({((⟨CharPModel.jBar N, hjO⟩ : R.integers) : modularFunctionFieldBar N)} :
            Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = Module.finrank
        (IntermediateField.adjoin (ResidueField A)
          ({R.residue ⟨CharPModel.jBar N, hjO⟩} : Set (modularFunctionFieldFullC (ResidueField A) N)))
        (modularFunctionFieldFullC (ResidueField A) N))
    (R' : RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (ResidueField A) N))
    (hspec' : ∀ (y : LaurentSeries A)
      (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q)),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R'.integers,
        ((R'.residue ⟨_, hint⟩ : modularFunctionFieldFullC (ResidueField A) N) :
          LaurentSeries (ResidueField A)) = coeffMap (residue A) y)
    (t : modularFunctionFieldBar N)
    (ht : IntermediateField.inclusion (modularFunctionFieldBar_le N (dvd_mul_right N q)) t
      ∈ R'.integers) :
    t ∈ R.integers := by
  have hle : modularFunctionFieldBar N ≤ modularFunctionFieldBar (N * q) :=
    modularFunctionFieldBar_le N (dvd_mul_right N q)
  have hpack := JacJ9Restrict.exists_regularProlongation_restrict hle R'
  obtain ⟨Fb₀, _, _, R₀, φ, hmem, hφ⟩ := hpack
  have ht0 : t ∈ R₀.integers := (hmem t).mpr ht

  have hserN := coeffMap_subtype_jqModC A N
  have hmem' : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (N * q) := by
    rw [hserN]; exact hle (CharPModel.jBar N).2
  have hsp' := hspec' (jqModC A) hmem'
  obtain ⟨hint', hres'⟩ := hsp'
  have hxj' : (⟨coeffMap A.subtype (jqModC A), hmem'⟩ : modularFunctionFieldBar (N * q))
      = IntermediateField.inclusion hle (CharPModel.jBar N) :=
    Subtype.ext (hserN.trans (IntermediateField.coe_inclusion hle (CharPModel.jBar N)).symm)
  have hj0' : IntermediateField.inclusion hle (CharPModel.jBar N) ∈ R'.integers := by
    rw [← hxj']; exact hint'
  have hj0 : CharPModel.jBar N ∈ R₀.integers := (hmem _).mpr hj0'
  have hres'' : R'.residue ⟨IntermediateField.inclusion hle (CharPModel.jBar N), hj0'⟩
      = ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ := by
    have h1 : (⟨IntermediateField.inclusion hle (CharPModel.jBar N), hj0'⟩ : R'.integers)
        = ⟨⟨coeffMap A.subtype (jqModC A), hmem'⟩, hint'⟩ := Subtype.ext hxj'.symm
    rw [h1]
    apply Subtype.ext
    rw [hres']
    exact coeffMap_residue_jqModC A

  have hφalg : ∀ c : ResidueField A, φ (algebraMap (ResidueField A) Fb₀ c)
      = algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) c := by
    intro c
    obtain ⟨a, ha⟩ := residue_surjective c
    rw [← ha]
    have h' : IntermediateField.inclusion hle
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a) ∈ R'.integers :=
      (hmem _).mp ((R₀.algebraMap_mem_iff a).mpr a.2)
    have hca : (⟨IntermediateField.inclusion hle
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a), h'⟩ : R'.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a,
            (R'.algebraMap_mem_iff a).mpr a.2⟩ :=
      Subtype.ext ((IntermediateField.inclusion hle).commutes (a : AlgebraicClosure ℚ))
    exact (congrArg φ (R₀.residue_algebraMap a).symm).trans
      ((hφ _ ((R₀.algebraMap_mem_iff a).mpr a.2) h').trans
        ((congrArg R'.residue hca).trans (R'.residue_algebraMap a)))
  let ψ : Fb₀ →ₐ[ResidueField A] modularFunctionFieldFullC (ResidueField A) N :=
    { φ with commutes' := hφalg }
  have hψ : ψ (R₀.residue ⟨CharPModel.jBar N, hj0⟩)
      = ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :=
    (hφ _ hj0 hj0').trans hres''
  have htr0 : Transcendental (ResidueField A) (R₀.residue ⟨CharPModel.jBar N, hj0⟩) :=
    transcendental_residue_jBar (A := A) (N := N) N R₀ hj0 ψ hψ

  have hagree : ∀ e : modularFunctionFieldBar N,
      e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({((⟨CharPModel.jBar N, hjO⟩ : R.integers) : modularFunctionFieldBar N)} :
          Set (modularFunctionFieldBar N)) →
      (e ∈ R₀.integers ↔ e ∈ R.integers) := by
    intro e he
    exact (RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue A R R₀
      (CharPModel.jBar N) hjO hj0 hx htr0 e he).symm
  have hV := RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R ⟨CharPModel.jBar N, hjO⟩ hx hfin hdeg
    R₀.integers hagree
  rw [← hV]
  exact ht0

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_monic_of_mem_integers
    (R : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldFullC (ResidueField A) N))
    (hjO : CharPModel.jBar N ∈ R.integers)
    (hx : Transcendental (ResidueField A) (R.residue ⟨CharPModel.jBar N, hjO⟩))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A)
        ({R.residue ⟨CharPModel.jBar N, hjO⟩} : Set (modularFunctionFieldFullC (ResidueField A) N)))
      (modularFunctionFieldFullC (ResidueField A) N))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({((⟨CharPModel.jBar N, hjO⟩ : R.integers) : modularFunctionFieldBar N)} :
            Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = Module.finrank
        (IntermediateField.adjoin (ResidueField A)
          ({R.residue ⟨CharPModel.jBar N, hjO⟩} : Set (modularFunctionFieldFullC (ResidueField A) N)))
        (modularFunctionFieldFullC (ResidueField A) N))
    (t : modularFunctionFieldBar N) (m : ℕ)
    (h1 : ∀ V : ValuationSubring (modularFunctionFieldBar N),
      (∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ V) →
        CharPModel.jBar N ∈ V → t ∈ V)
    (h2 : ∀ V : ValuationSubring (modularFunctionFieldBar N),
      (∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ V) →
        CharPModel.jBar N ∉ V → t * (CharPModel.jBar N ^ m)⁻¹ ∈ V)
    (htO : t ∈ R.integers) :
    ∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype t p = 0 := by
  have h3 : ∀ V : ValuationSubring (modularFunctionFieldBar N),
      (∀ e : modularFunctionFieldBar N,
        e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({((⟨CharPModel.jBar N, hjO⟩ : R.integers) : modularFunctionFieldBar N)} :
            Set (modularFunctionFieldBar N)) → (e ∈ V ↔ e ∈ R.integers)) → t ∈ V := by
    intro V hV
    rw [RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R ⟨CharPModel.jBar N, hjO⟩
      hx hfin hdeg V hV]
    exact htO
  have heng := RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring A R
    ⟨CharPModel.jBar N, hjO⟩ hx t m h1 h2 h3
  obtain ⟨p, hpm, -, hp0⟩ := heng
  refine ⟨p.map (phi N A), hpm.map _, ?_⟩
  rw [Polynomial.eval₂_map, subtype_comp_phi]
  exact hp0

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 4000000 in
include hqN in

private theorem main (t : modularFunctionFieldBar N)
    (htG : (t : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (htP : ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      CharPModel.jBar N ∈ u₀.toValuationSubring → t ∈ u₀.toValuationSubring) :
    ∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype t p = 0 := by

  have hpsi : 0 < ModularCurve.dedekindPsi N := JacJ9GLN.dedekindPsi_pos
  have hdegL0 : Module.finrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({CharPModel.jBar N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = ModularCurve.dedekindPsi N :=
    ModularCurve.CompEq.finrank_adjoin_jBar_eq_dedekindPsi N
  haveI : FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({CharPModel.jBar N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) :=
    Module.finite_of_finrank_pos (by rw [hdegL0]; exact hpsi)
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({CharPModel.jBar N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) :=
    Algebra.IsSeparable.of_integral _ _
  have hint : IsIntegral
      (Algebra.adjoin (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N))) t :=
    isIntegral_adjoin_of_forall_mem_toValuationSubring (CharPModel.jBar N) (CharPModel.jBar N) t htP
  have hpoles :=
    JacJ9GLN.JacJ9GaussPoles.forall_mem_and_exists_forall_mul_inv_pow_mem (AlgebraicClosure ℚ) hint
  obtain ⟨h1, m, h2⟩ := hpoles

  have hA : A.LiesOverPrime q := JacJ9GLN.liesOverPrime red
  have hR := ModularCurve.exists_regularProlongation_modularFunctionFieldBar N hqN A hA
  obtain ⟨R, hspec⟩ := hR
  have hj := JacJ9GLN.jBar_mem_integers (A := A) (N := N) N R hspec
  obtain ⟨hjO, hres⟩ := hj
  have hx : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨CharPModel.jBar N, hjO⟩) :=
    JacJ9GLN.transcendental_residue_jBar (A := A) (N := N) N R hjO (AlgHom.id _ _) hres
  have hN := JacJ9GLN.natCast_residueField_ne_zero red hqN
  have hdegL : Module.finrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({((⟨CharPModel.jBar N, hjO⟩ : R.integers) : modularFunctionFieldBar N)} :
          Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = ModularCurve.dedekindPsi N :=
    hdegL0
  have hdegR : Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({R.residue ⟨CharPModel.jBar N, hjO⟩} :
          Set (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)))
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) = ModularCurve.dedekindPsi N := by
    rw [hres]
    exact ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi _ N hN
  have hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({R.residue ⟨CharPModel.jBar N, hjO⟩} :
          Set (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)))
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) := by
    rw [hdegR]; exact hpsi
  have hdeg := hdegL.trans hdegR.symm

  have hR' := ModularCurve.exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd N q hqN A hA
  obtain ⟨R', hpin, hspec'⟩ := hR'
  have hincl := JacJ9GLN.inclusion_mem_integers red R' hpin t htG
  have htO : t ∈ R.integers :=
    JacJ9GLN.mem_integers_of_inclusion_mem R hjO hx hfin hdeg R' hspec' t hincl

  exact JacJ9GLN.exists_monic_of_mem_integers R hjO hx hfin hdeg t m h1 h2 htO

end Main

end JacJ9GLN

open ModularCurve ModularCurve.CharPModel in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N) :
    ∀ t : modularFunctionFieldBar N,
      (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red →
      (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        CharPModel.jBar N ∈ u₀.toValuationSubring → t ∈ u₀.toValuationSubring) →
      ∃ p : Polynomial (CharPModel.affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype t p = 0 := by
  intro t htG htP
  exact JacJ9GLN.main red hqN t htG htP

end S_ModularCurve_CharPModel_exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
end P2MW
export P2MW.S_ModularCurve_CharPModel_exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem (solution)

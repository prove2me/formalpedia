-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.isIntegrallyClosed_invariants_quotient_of_rigidChart_framed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f7c2906a-6532-5fee-843d-d075756f9d9c

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
import Definitions.Def_ModularCurve_RigidDescentHyps
import Mathlib
import Theorems.Thm_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed
import Theorems.Thm_DrinfeldCurve_isDedekindDomain_coordRing
import Definitions.Def_DrinfeldCurve_FunctionField
import Theorems.Thm_DrinfeldCurve_algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField
import Theorems.Thm_MulSemiringAction_mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top
import Theorems.Thm_Algebra_FormallySmooth_sup_eq_top_of_mem_minimalPrimes_span_of_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma
import Theorems.Thm_IsGaloisGroup_finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_quotField_ringHom_invariants_of_rigidChart_framed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 51200000

namespace C3GlueKit
namespace BC
open DrinfeldCurve MvPolynomial

variable (q : ℕ) [Fact q.Prime] {κ₀ κ : Type} [Field κ₀] [Field κ]
  [Algebra (GaloisField q 2) κ₀] [Algebra (GaloisField q 2) κ]

theorem map_drinfeldPoly (e : κ₀ →+* κ) : MvPolynomial.map e (drinfeldPoly q κ₀) = drinfeldPoly q κ := by
  simp [drinfeldPoly, MvPolynomial.map_X]

theorem map_drinfeldPoly_sub_one (e : κ₀ →+* κ) :
    MvPolynomial.map e (drinfeldPoly q κ₀ - 1) = drinfeldPoly q κ - 1 := by
  rw [map_sub, map_one, map_drinfeldPoly]

noncomputable def bc (e : κ₀ →+* κ) : CoordRing q κ₀ →+* CoordRing q κ :=
  Ideal.Quotient.lift (drinfeldIdeal q κ₀) ((mk q κ).toRingHom.comp (MvPolynomial.map e)) (by
    intro a ha
    rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [RingHom.comp_apply, map_mul, map_drinfeldPoly_sub_one]
    show mk q κ (MvPolynomial.map e b * (drinfeldPoly q κ - 1)) = 0
    rw [map_mul]
    have : mk q κ (drinfeldPoly q κ - 1) = 0 := by rw [map_sub, map_one, mk_drinfeldPoly, sub_self]
    rw [this, mul_zero])

theorem bc_mk (e : κ₀ →+* κ) (f : MvPolynomial (Fin 2) κ₀) : bc q e (mk q κ₀ f) = mk q κ (MvPolynomial.map e f) := rfl

theorem algebraMap_eq_mk_C (k : Type) [Field k] (c : k) : algebraMap k (CoordRing q k) c = mk q k (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

theorem bc_algebraMap (e : κ₀ →+* κ) (c : κ₀) : bc q e (algebraMap κ₀ (CoordRing q κ₀) c) = algebraMap κ (CoordRing q κ) (e c) := by
  rw [algebraMap_eq_mk_C, bc_mk, MvPolynomial.map_C, ← algebraMap_eq_mk_C]

theorem bc_x (e : κ₀ →+* κ) : bc q e (x q κ₀) = x q κ := by
  show bc q e (mk q κ₀ (X 0)) = mk q κ (X 0); rw [bc_mk, MvPolynomial.map_X]

theorem bc_y (e : κ₀ →+* κ) : bc q e (y q κ₀) = y q κ := by
  show bc q e (mk q κ₀ (X 1)) = mk q κ (X 1); rw [bc_mk, MvPolynomial.map_X]

theorem map_scalePoly (e : κ₀ →+* κ) (c : κ₀) (f : MvPolynomial (Fin 2) κ₀) :
    MvPolynomial.map e (scalePoly κ₀ c f) = scalePoly κ (e c) (MvPolynomial.map e f) := by
  have h : (MvPolynomial.map e).comp (scalePoly κ₀ c).toRingHom = (scalePoly κ (e c)).toRingHom.comp (MvPolynomial.map e) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.algHom_C,
        MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, scalePoly_X, map_mul,
        MvPolynomial.map_C, MvPolynomial.map_X]
  exact congrArg (fun φ : MvPolynomial (Fin 2) κ₀ →+* MvPolynomial (Fin 2) κ => φ f) h

variable {q} in
theorem e_ofZMod (e : κ₀ →+* κ) (he : ∀ c : GaloisField q 2, e (algebraMap (GaloisField q 2) κ₀ c) = algebraMap (GaloisField q 2) κ c)
    (a : ZMod q) : e (ofZMod q κ₀ a) = ofZMod q κ a := by
  show e ((algebraMap (GaloisField q 2) κ₀) (algebraMap (ZMod q) (GaloisField q 2) a)) = (algebraMap (GaloisField q 2) κ) (algebraMap (ZMod q) (GaloisField q 2) a)
  rw [he]

theorem map_substPoly (e : κ₀ →+* κ) (he : ∀ c : GaloisField q 2, e (algebraMap (GaloisField q 2) κ₀ c) = algebraMap (GaloisField q 2) κ c)
    (g : Matrix (Fin 2) (Fin 2) (ZMod q)) (f : MvPolynomial (Fin 2) κ₀) :
    MvPolynomial.map e (substPoly q κ₀ g f) = substPoly q κ g (MvPolynomial.map e f) := by
  have h : (MvPolynomial.map e).comp (substPoly q κ₀ g).toRingHom = (substPoly q κ g).toRingHom.comp (MvPolynomial.map e) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.algHom_C,
        MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, substPoly_X, map_sum, map_mul,
        MvPolynomial.map_C, MvPolynomial.map_X, e_ofZMod e he]
  exact congrArg (fun φ : MvPolynomial (Fin 2) κ₀ →+* MvPolynomial (Fin 2) κ => φ f) h

theorem e_scalarOf (e : κ₀ →+* κ) (he : ∀ c : GaloisField q 2, e (algebraMap (GaloisField q 2) κ₀ c) = algebraMap (GaloisField q 2) κ c)
    (ζ : (GaloisField q 2)ˣ) : e (scalarOf q κ₀ ζ) = scalarOf q κ ζ := he _

theorem bc_hAction (e : κ₀ →+* κ) (he : ∀ c : GaloisField q 2, e (algebraMap (GaloisField q 2) κ₀ c) = algebraMap (GaloisField q 2) κ c)
    (p : ↥(hSubgroup q)) (a : CoordRing q κ₀) :
    bc q e (hAction q κ₀ p a) = hAction q κ p (bc q e a) := by
  obtain ⟨f, rfl⟩ := mk_surjective q κ₀ a
  rw [hAction_mk, bc_mk, bc_mk, hAction_mk, map_scalePoly, map_substPoly q e he, e_scalarOf q e he]

theorem bc_comp (e : κ₀ →+* κ) {κ₁ : Type} [Field κ₁] [Algebra (GaloisField q 2) κ₁] (e' : κ →+* κ₁) (a : CoordRing q κ₀) :
    bc q e' (bc q e a) = bc q (e'.comp e) a := by
  obtain ⟨f, rfl⟩ := mk_surjective q κ₀ a
  rw [bc_mk, bc_mk, bc_mk, MvPolynomial.map_map]

theorem bc_id (a : CoordRing q κ₀) : bc q (RingHom.id κ₀) a = a := by
  obtain ⟨f, rfl⟩ := mk_surjective q κ₀ a
  rw [bc_mk, MvPolynomial.map_id]

noncomputable def bcEquiv (e : κ₀ ≃+* κ) : CoordRing q κ₀ ≃+* CoordRing q κ :=
  RingEquiv.ofRingHom (bc q (e : κ₀ →+* κ)) (bc q (e.symm : κ →+* κ₀))
    (by ext a; rw [RingHom.comp_apply, bc_comp, RingHom.id_apply]; convert bc_id q a; ext c; simp)
    (by ext a; rw [RingHom.comp_apply, bc_comp, RingHom.id_apply]; convert bc_id q a; ext c; simp)

theorem bcEquiv_apply (e : κ₀ ≃+* κ) (a : CoordRing q κ₀) : bcEquiv q e a = bc q (e : κ₀ →+* κ) a := rfl

end BC
end C3GlueKit

namespace C3GlueKit
open IsLocalRing

section residueIso
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def comapIncl (A : ValuationSubring L) : ↥(A.comap (algebraMap K L)) →+* ↥A where
  toFun a := ⟨algebraMap K L a, a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_comapIncl (A : ValuationSubring L) (a : ↥(A.comap (algebraMap K L))) :
    ((comapIncl A a : ↥A) : L) = algebraMap K L a := rfl

scoped instance isLocalHom_comapIncl (A : ValuationSubring L) : IsLocalHom (comapIncl (K := K) A) := by
  constructor
  intro a ha
  have ha0 : (a : K) ≠ 0 := by
    intro h
    apply ha.ne_zero
    apply Subtype.ext
    show algebraMap K L a = 0
    rw [h, map_zero]
  obtain ⟨u, hu⟩ := ha
  have hinvA : (algebraMap K L a)⁻¹ ∈ A := by
    have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A) * (comapIncl A a) = 1 := by rw [← hu, Units.inv_mul]
    have h2 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) * algebraMap K L a = 1 := by
      have := congrArg (fun z : ↥A => (z : L)) h1; simpa using this
    have h3 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) = (algebraMap K L a)⁻¹ :=
      eq_inv_of_mul_eq_one_left h2
    rw [← h3]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  have hinv : (a : K)⁻¹ ∈ A.comap (algebraMap K L) := by
    show algebraMap K L (a : K)⁻¹ ∈ A
    rw [map_inv₀]; exact hinvA
  refine isUnit_iff_exists_inv.mpr ⟨⟨(a : K)⁻¹, hinv⟩, Subtype.ext ?_⟩
  show (a : K) * (a : K)⁻¹ = 1
  exact mul_inv_cancel₀ ha0

theorem exists_residueField_equiv (A : ValuationSubring L)
    (hκ : ∀ a : L, a ∈ A → ∃ c : K, algebraMap K L c ∈ A ∧ ∃ h : a - algebraMap K L c ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A) :
    ∃ e : ResidueField ↥(A.comap (algebraMap K L)) ≃+* ResidueField ↥A,
      ∀ a : ↥(A.comap (algebraMap K L)), e (residue _ a) = residue ↥A ⟨algebraMap K L a, a.2⟩ := by
  let f := ResidueField.map (comapIncl (K := K) A)
  have hf : ∀ a : ↥(A.comap (algebraMap K L)), f (residue _ a) = residue ↥A ⟨algebraMap K L a, a.2⟩ := fun a => rfl
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := residue_surjective z
    obtain ⟨c, hc, hm, hmax⟩ := hκ (x : L) x.2
    refine ⟨residue _ ⟨c, hc⟩, ?_⟩
    rw [hf, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    have : x - (⟨algebraMap K L c, hc⟩ : ↥A) = ⟨_, hm⟩ := Subtype.ext rfl
    show x - ⟨algebraMap K L c, hc⟩ ∈ maximalIdeal ↥A
    rw [this]; exact hmax
  exact ⟨RingEquiv.ofBijective f ⟨f.injective, hsurj⟩, hf⟩

end residueIso
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace C3Kit3

open MvPolynomial DrinfeldCurve

theorem x_ne_zero (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] : DrinfeldCurve.x q k ≠ 0 := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hP1 : (Polynomial.X ^ q - Polynomial.X : Polynomial k).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] ; omega
  have hP : (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k).natDegree = q := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> rw [hP1]
    rw [Polynomial.natDegree_one]; omega
  have hP0 : (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hP; omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k)
    (by rw [Polynomial.degree_eq_natDegree hP0, hP]; exact_mod_cast (show q ≠ 0 by omega))
  have ha' : a ^ q - a + 1 = 0 := by
    have := ha.eq_zero
    simpa [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] using this
  have ha0 : a ≠ 0 := by rintro rfl; simp [zero_pow (show q ≠ 0 by omega)] at ha'

  let φ : MvPolynomial (Fin 2) k →ₐ[k] k := MvPolynomial.aeval ![a, 1]
  have hφ : ∀ f ∈ drinfeldIdeal q k, φ f = 0 := by
    intro f hf
    rw [drinfeldIdeal, Ideal.mem_span_singleton] at hf
    obtain ⟨g, rfl⟩ := hf
    rw [map_mul]
    have : φ (drinfeldPoly q k - 1) = 0 := by
      simp only [drinfeldPoly, φ, map_sub, map_mul, map_pow, map_one, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_pow, mul_one]
      linear_combination (-1 : k) * ha'
    rw [this, zero_mul]
  let ψ : CoordRing q k →ₐ[k] k := Ideal.Quotient.liftₐ (drinfeldIdeal q k) φ hφ
  have hψx : ψ (DrinfeldCurve.x q k) = a := by
    show Ideal.Quotient.liftₐ (drinfeldIdeal q k) φ hφ (Ideal.Quotient.mkₐ k (drinfeldIdeal q k) (X 0)) = a
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    simp [φ]
  intro hx
  apply ha0
  rw [← hψx, hx, map_zero]

theorem hAction_x_ne (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [Algebra (GaloisField q 2) k]
    (p : ↥(hSubgroup q))
    (hp1 : (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 = 1)
    (hp2 : scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 ≠ 1) :
    hAction q k p (DrinfeldCurve.x q k) ≠ DrinfeldCurve.x q k := by
  set s := scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 with hs
  have hact : hAction q k p (DrinfeldCurve.x q k) = s • DrinfeldCurve.x q k := by
    show hAction q k p (mk q k (X 0)) = s • mk q k (X 0)
    rw [hAction_mk, hp1]
    have : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1 := rfl
    rw [this, substPoly_one, AlgHom.id_apply, scalePoly_X, map_mul, ← hs]
    rw [show mk q k (C s) = algebraMap k (CoordRing q k) s from (mk q k).commutes s, Algebra.smul_def]
  intro h
  rw [hact] at h
  have h2 : (s - 1) • DrinfeldCurve.x q k = 0 := by rw [sub_smul, one_smul, h, sub_self]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hp2
  exact x_ne_zero q k ((inv_smul_smul₀ hs1 (DrinfeldCurve.x q k)).symm.trans (by rw [h2, smul_zero]))

end C3Kit3
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace C3GlueKit
namespace Scal
open DrinfeldCurve MvPolynomial

variable (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [Algebra (GaloisField q 2) κ]

def sc (c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) : ↥(hSubgroup q) :=
  ⟨((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), ((c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) : (GaloisField q 2)ˣ)),
    one_mem_hSubgroup_of_mem q c⟩

theorem sc_one : sc q 1 = 1 := Subtype.ext rfl

theorem sc_mul (c d : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) : sc q (c * d) = sc q c * sc q d :=
  Subtype.ext (Prod.ext (by simp [sc]) rfl)

def scHom : ↥(rootsOfUnity (q + 1) (GaloisField q 2)) →* ↥(hSubgroup q) where
  toFun := sc q
  map_one' := sc_one q
  map_mul' := sc_mul q

theorem scHom_apply (c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) : scHom q c = sc q c := rfl

theorem scHom_injective : Function.Injective (scHom q) := by
  intro c d h
  have := congrArg (fun p : ↥(hSubgroup q) => (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2) h
  exact Subtype.ext this

theorem sc_pow (c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) (k : ℕ) : sc q (c ^ k) = sc q c ^ k :=
  map_pow (scHom q) c k

theorem mem_rootsOfUnity_of_one_mem (c : (GaloisField q 2)ˣ)
    (h : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ hSubgroup q) : c ∈ rootsOfUnity (q + 1) (GaloisField q 2) := by
  rw [mem_hSubgroup_iff, Units.ext_iff, coe_hChar_apply] at h
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val]
  simpa using h

theorem sc_mk_eq (c : (GaloisField q 2)ˣ) (h : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ hSubgroup q) :
    sc q ⟨c, mem_rootsOfUnity_of_one_mem q c h⟩ = ⟨((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c), h⟩ := rfl

theorem hAction_sc_x (c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) :
    hAction q κ (sc q c) (x q κ) = algebraMap κ _ (scalarOf q κ c) * x q κ := by
  rw [sc, ← muAction_eq_hAction, muAction_x]

variable [IsAlgClosed κ]

theorem sc_eq_one_of_hAction_eq (c : ↥(rootsOfUnity (q + 1) (GaloisField q 2)))
    (h : ∀ a : CoordRing q κ, hAction q κ (sc q c) a = a) : c = 1 := by
  by_contra hc
  have hne : scalarOf q κ ((sc q c : ↥(hSubgroup q)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 ≠ 1 := by
    intro h1
    apply hc
    apply Subtype.ext; apply Units.ext
    have : algebraMap (GaloisField q 2) κ ((c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) : (GaloisField q 2)ˣ) = algebraMap (GaloisField q 2) κ 1 := by
      rw [map_one]; exact h1
    exact (algebraMap (GaloisField q 2) κ).injective this
  exact C3Kit3.hAction_x_ne q κ (sc q c) rfl hne (h _)

theorem sc_injective_on_hAction (c d : ↥(rootsOfUnity (q + 1) (GaloisField q 2)))
    (h : ∀ a : CoordRing q κ, hAction q κ (sc q c) a = hAction q κ (sc q d) a) : c = d := by
  have : c * d⁻¹ = 1 := by
    apply sc_eq_one_of_hAction_eq q κ
    intro a
    rw [sc_mul, map_mul, AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, ← map_mul, ← sc_mul, mul_inv_cancel, sc_one, map_one,
      AlgEquiv.one_apply]
  exact mul_inv_eq_one.mp this

theorem orderOf_hAction_sc (c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) :
    orderOf (hAction q κ (sc q c)) = orderOf c := by
  have hinj : Function.Injective ((hAction q κ).comp (scHom q)) := by
    intro c d h
    apply sc_injective_on_hAction q κ
    intro a
    exact congrArg (fun f : CoordRing q κ ≃ₐ[κ] CoordRing q κ => f a) h
  exact (orderOf_injective ((hAction q κ).comp (scHom q)) hinj c)

end Scal
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace C3GlueKit
namespace Ord
open DrinfeldCurve Scal

variable (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [Algebra (GaloisField q 2) κ] [IsAlgClosed κ]

theorem iterate_law {B : Type*} [CommRing B] (ρ : B →+* CoordRing q κ) (T : B → B)
    (c₀ : ↥(rootsOfUnity (q + 1) (GaloisField q 2)))
    (hT : ∀ b, ρ (T b) = hAction q κ (sc q c₀) (ρ b)) (k : ℕ) (b : B) :
    ρ (T^[k] b) = hAction q κ (sc q (c₀ ^ k)) (ρ b) := by
  induction k generalizing b with
  | zero => simp [sc_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', hT, ih, ← AlgEquiv.mul_apply, ← map_mul, ← sc_mul, ← pow_succ']

theorem orderOf_eq {B : Type*} [CommRing B] (ρ : B →+* CoordRing q κ) (hρ : Function.Surjective ρ) (T : B → B)
    (c₀ : ↥(rootsOfUnity (q + 1) (GaloisField q 2)))
    (hT : ∀ b, ρ (T b) = hAction q κ (sc q c₀) (ρ b))
    (n : ℕ) (hn : 0 < n) (hTn : ∀ b, T^[n] b = b)
    (hTk : ∀ k, 0 < k → k < n → ∃ c : ↥(rootsOfUnity (q + 1) (GaloisField q 2)), c ≠ 1 ∧
      ∀ b, ρ (T^[k] b) = hAction q κ (sc q c) (ρ b)) :
    orderOf c₀ = n := by

  have h1 : c₀ ^ n = 1 := by
    apply sc_eq_one_of_hAction_eq q κ
    intro a
    obtain ⟨b, rfl⟩ := hρ a
    rw [← iterate_law q κ ρ T c₀ hT n b, hTn]
  have hdvd : orderOf c₀ ∣ n := orderOf_dvd_of_pow_eq_one h1

  have h2 : ∀ k, 0 < k → k < n → c₀ ^ k ≠ 1 := by
    intro k hk hkn heq
    obtain ⟨c, hc1, hc⟩ := hTk k hk hkn
    apply hc1
    have : c = c₀ ^ k := by
      apply sc_injective_on_hAction q κ
      intro a
      obtain ⟨b, rfl⟩ := hρ a
      rw [← hc b, iterate_law q κ ρ T c₀ hT k b]
    rw [this, heq]
  have hpos : 0 < orderOf c₀ := orderOf_pos c₀
  have hle : orderOf c₀ ≤ n := Nat.le_of_dvd hn hdvd
  by_contra hne
  exact h2 (orderOf c₀) hpos (lt_of_le_of_ne hle hne) (pow_orderOf_eq_one c₀)

theorem natCard_zpowers_eq (c₀ : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) (n : ℕ) (h : orderOf c₀ = n) :
    Nat.card ↥(Subgroup.zpowers c₀) = n := by
  rw [Nat.card_zpowers, h]

end Ord
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace C3GlueKit
namespace Conj
open DrinfeldCurve Scal Ord

variable (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [Algebra (GaloisField q 2) κ] [IsAlgClosed κ]

theorem orderOf_eq_orderOf {B : Type*} [CommRing B] (ρ ρ' : B →+* CoordRing q κ)
    (hρ : Function.Surjective ρ) (hρ' : Function.Surjective ρ')
    (hker : ∀ b, ρ b = 0 ↔ ρ' b = 0) (T : B → B)
    (c d : ↥(rootsOfUnity (q + 1) (GaloisField q 2)))
    (hd : ∀ b, ρ (T b) = hAction q κ (sc q d) (ρ b)) (hc : ∀ b, ρ' (T b) = hAction q κ (sc q c) (ρ' b)) :
    orderOf c = orderOf d := by
  rw [orderOf_eq_orderOf_iff]
  intro m
  have key : ∀ (ρ₁ : B →+* CoordRing q κ) (e : ↥(rootsOfUnity (q + 1) (GaloisField q 2))), Function.Surjective ρ₁ →
      (∀ b, ρ₁ (T b) = hAction q κ (sc q e) (ρ₁ b)) → (e ^ m = 1 ↔ ∀ b, ρ₁ (T^[m] b) - ρ₁ b = 0) := by
    intro ρ₁ e hs he
    constructor
    · intro h1 b
      rw [iterate_law q κ ρ₁ T e he m b, h1, sc_one, map_one, AlgEquiv.one_apply, sub_self]
    · intro h
      apply sc_eq_one_of_hAction_eq q κ
      intro a
      obtain ⟨b, rfl⟩ := hs a
      rw [← iterate_law q κ ρ₁ T e he m b]
      exact sub_eq_zero.mp (h b)
  rw [key ρ' c hρ' hc, key ρ d hρ hd]
  constructor
  · intro h b; have := h b; rw [← map_sub] at this ⊢; exact (hker _).mpr this
  · intro h b; have := h b; rw [← map_sub] at this ⊢; exact (hker _).mp this

end Conj
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace C3GlueKit

theorem mem_zpowers_of_orderOf_dvd {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] (a b : G)
    (h : orderOf a ∣ orderOf b) : a ∈ Subgroup.zpowers b := by
  classical
  haveI := Fintype.ofFinite G
  set m := orderOf b with hm
  have hm0 : 0 < m := orderOf_pos b

  let S : Finset G := Finset.univ.filter (fun x : G => x ^ m = 1)
  have hS : S.card ≤ m := IsCyclic.card_pow_eq_one_le hm0
  have hsub : (Subgroup.zpowers b : Set G).toFinset ⊆ S := by
    intro x hx
    rw [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, pow_orderOf_eq_one, one_zpow]
  have hcard : (Subgroup.zpowers b : Set G).toFinset.card = m := by
    rw [hm, ← Fintype.card_zpowers, Set.toFinset_card]; rfl
  have heq : (Subgroup.zpowers b : Set G).toFinset = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hS)
  have ha : a ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, orderOf_dvd_iff_pow_eq_one.mp h⟩
  rw [← heq, Set.mem_toFinset] at ha
  exact ha

theorem mem_zpowers_of_orderOf_eq {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] (a b : G)
    (h : orderOf a = orderOf b) : a ∈ Subgroup.zpowers b :=
  mem_zpowers_of_orderOf_dvd a b (h ▸ dvd_rfl)

example (q : ℕ) [Fact q.Prime] : IsCyclic ↥(rootsOfUnity (q + 1) (GaloisField q 2)) := inferInstance

end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

open scoped Pointwise

namespace C3GlueKit
namespace Range

theorem exists_preimage {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    (ι : A →+* B) (ρ : B →+* R) (hρ : Function.Surjective ρ)
    (I : Ideal B) (hIP : I ≤ RingHom.ker ρ) (hI : ∀ (g : G) (b : B), b ∈ I → g • b ∈ I)
    (hmax : ∀ g : G, g • RingHom.ker ρ ≠ RingHom.ker ρ → RingHom.ker ρ ⊔ g • RingHom.ker ρ = ⊤)
    (hinf : ∀ b : B, (∀ g : G, g • b ∈ RingHom.ker ρ) → b ∈ I)
    (hlift : ∀ b : B, (∀ g : G, g • b - b ∈ I) → ∃ x : A, ι x - b ∈ I)
    (a : R) (hDa : ∀ g : G, g • RingHom.ker ρ = RingHom.ker ρ → ∀ b : B, ρ b = a → ρ (g • b) = a) :
    ∃ x : A, ρ (ι x) = a := by
  obtain ⟨b₁, hb₁⟩ := hρ a
  have hG5 := (MulSemiringAction.mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top
    I (RingHom.ker ρ) hIP hI hmax hinf).2 b₁ (fun g hg => by
      rw [RingHom.mem_ker, map_sub, hDa g hg b₁ hb₁, hb₁, sub_self])
  obtain ⟨r, hrG, hrb⟩ := hG5
  obtain ⟨x, hx⟩ := hlift r hrG
  refine ⟨x, ?_⟩
  have h1 : ρ (ι x) = ρ r := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker]; exact hIP hx
  have h2 : ρ r = ρ b₁ := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker]; exact hrb
  rw [h1, h2, hb₁]

theorem mem_of_invariant_of_mem_ker {B R : Type*} [CommRing B] [CommRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    (ρ : B →+* R)
    (I : Ideal B) (hIP : I ≤ RingHom.ker ρ) (hI : ∀ (g : G) (b : B), b ∈ I → g • b ∈ I)
    (hmax : ∀ g : G, g • RingHom.ker ρ ≠ RingHom.ker ρ → RingHom.ker ρ ⊔ g • RingHom.ker ρ = ⊤)
    (hinf : ∀ b : B, (∀ g : G, g • b ∈ RingHom.ker ρ) → b ∈ I)
    (b : B) (hb : ∀ g : G, g • b = b) (hbP : ρ b = 0) : b ∈ I :=
  (MulSemiringAction.mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top
    I (RingHom.ker ρ) hIP hI hmax hinf).1 b (fun g => by rw [hb g, sub_self]; exact I.zero_mem) hbP

end Range
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

section
open scoped Pointwise

namespace C3GlueKit
namespace PKit
open IsLocalRing

variable {k K O : Type*} [Field k] [Field K] [Algebra k K] [CommRing O] [Algebra O K]

theorem stab_of_smul_eq {M : Type*} [Group M] (φ : M →* (K ≃ₐ[k] K)) (B : Subalgebra O K) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W) [MulSemiringAction M ↥B]
    (hsmul : ∀ (g : M) (b : ↥B), ((g • b : ↥B) : K) = φ g b)
    (hR3e : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : K) = (g : K))
    (P : Ideal ↥B) (hP : ∀ b : ↥B, b ∈ P ↔ (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W)
    (g : M) (hg : g • P = P) :
    ∀ f : K, f ∈ W ↔ φ g f ∈ W := by

  have key : ∀ (g : M), g • P = P → ∀ f : K, f ∈ W → φ g f ∈ W := by
    intro g hg f hf
    obtain ⟨a, b, hb, hfab⟩ := (hR3e f).mp hf
    rw [hR3e]
    refine ⟨g • a, g • b, ?_, ?_⟩
    · intro hmax
      apply hb
      rw [← hP] at hmax ⊢
      have : g • b ∈ g • P := by rw [hg]; exact hmax
      exact Ideal.smul_mem_pointwise_smul_iff.mp this
    · rw [hsmul, hsmul, ← map_mul, hfab]
  intro f
  constructor
  · exact key g hg f
  · intro hf
    have hg' : g⁻¹ • P = P := by
      rw [inv_smul_eq_iff, hg]
    have := key g⁻¹ hg' _ hf
    rw [map_inv, ← AlgEquiv.mul_apply, inv_mul_cancel] at this
    exact this

theorem mem_minimalPrimes (B : Subalgebra O K) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (π : O) (hπW : algebraMap O K π ∈ W) (hπmax : maximalIdeal ↥W = Ideal.span {(⟨_, hπW⟩ : ↥W)})
    (hR3e : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : K) = (g : K))
    (P : Ideal ↥B) [P.IsPrime] (hP : ∀ b : ↥B, b ∈ P ↔ (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W)
    (hπB : ((algebraMap O ↥B π : ↥B) : K) = algebraMap O K π) :
    P ∈ (Ideal.span {algebraMap O ↥B π}).minimalPrimes := by
  have hπP : algebraMap O ↥B π ∈ P := by
    rw [hP, hπmax]
    have : (⟨((algebraMap O ↥B π : ↥B) : K), hBW _ (algebraMap O ↥B π).2⟩ : ↥W) = ⟨_, hπW⟩ := Subtype.ext hπB
    rw [this]; exact Ideal.mem_span_singleton_self _
  refine ⟨⟨‹P.IsPrime›, (Ideal.span_singleton_le_iff_mem _).mpr hπP⟩, ?_⟩
  rintro Q ⟨hQ, hπQ⟩ hQP

  intro b hb
  have hbW : (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W := (hP b).mp hb
  rw [hπmax, Ideal.mem_span_singleton'] at hbW
  obtain ⟨w, hw⟩ := hbW
  obtain ⟨g, h, hh, hwgh⟩ := (hR3e (w : K)).mp w.2
  have hhQ : h ∉ Q := fun hhQ => hh ((hP h).mp (hQP hhQ))
  have e0 : (w : K) * algebraMap O K π = (b : K) := congrArg Subtype.val hw
  have e1 : (b : K) * (h : K) = algebraMap O K π * (g : K) := by
    calc (b : K) * (h : K) = ((w : K) * algebraMap O K π) * (h : K) := by rw [e0]
      _ = algebraMap O K π * ((w : K) * (h : K)) := by ring
      _ = algebraMap O K π * (g : K) := by rw [hwgh]
  have e2 : b * h = algebraMap O ↥B π * g := by
    apply Subtype.ext
    show (b : K) * (h : K) = ((algebraMap O ↥B π : ↥B) : K) * (g : K)
    rw [hπB]; exact e1
  have hmem : b * h ∈ Q := by rw [e2]; exact Q.mul_mem_right _ ((Ideal.span_singleton_le_iff_mem _).mp hπQ)
  exact (hQ.mem_or_mem hmem).resolve_right hhQ

theorem smul_mem_minimalPrimes {R : Type*} [CommRing R] {M : Type*} [Group M] [MulSemiringAction M R]
    (I P : Ideal R) (g : M) (hI : g • I = I) (hP : P ∈ I.minimalPrimes) : g • P ∈ I.minimalPrimes := by
  obtain ⟨⟨hPp, hIP⟩, hmin⟩ := hP
  haveI := hPp
  refine ⟨⟨Ideal.IsPrime.smul g, ?_⟩, ?_⟩
  · rw [← hI]; exact Ideal.pointwise_smul_le_pointwise_smul_iff.mpr hIP
  · rintro Q ⟨hQ, hIQ⟩ hQP
    have h1 : g⁻¹ • Q ≤ P := by rw [← Ideal.subset_pointwise_smul_iff]; exact hQP
    haveI := hQ
    have h2 : I ≤ g⁻¹ • Q := by
      rw [← Ideal.pointwise_smul_subset_iff, hI]; exact hIQ
    have h3 := hmin ⟨Ideal.IsPrime.smul g⁻¹, h2⟩ h1
    rw [Ideal.pointwise_smul_subset_iff]; exact h3

end PKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace C3Kit2
open IsLocalRing

theorem hloc_reshape {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K]
    (Bt : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ Bt → f ∈ W)
    (hR3e : ∀ f : K, f ∈ W ↔ ∃ g h : ↥Bt, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : K) = (g : K)) :
    ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ Bt.toSubring ∧ h ∈ Bt.toSubring ∧
      (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g := by
  intro f
  rw [hR3e]
  constructor
  · rintro ⟨g, h, hh, hf⟩
    exact ⟨g, h, g.2, h.2, fun _ => hh, hf⟩
  · rintro ⟨g, h, hg, hh, hu, hf⟩
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, hu _, hf⟩
end C3Kit2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace C3GlueKit
namespace Rho
open DrinfeldCurve Scal

variable (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [Algebra (GaloisField q 2) κ] [IsDomain (CoordRing q κ)]

theorem muAction_eq_of_mem_zpowers (c₀ : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) (a : CoordRing q κ)
    (h : muAction q κ c₀ a = a) (ζ : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) (hζ : ζ ∈ Subgroup.zpowers c₀) :
    muAction q κ ζ a = a := by
  rw [Subgroup.zpowers_eq_closure] at hζ
  induction hζ using Subgroup.closure_induction with
  | mem σ hσ => rw [Set.mem_singleton_iff.mp hσ]; exact h
  | one => rw [map_one, AlgEquiv.one_apply]
  | mul σ τ _ _ ihσ ihτ => rw [map_mul, AlgEquiv.mul_apply, ihτ, ihσ]
  | inv σ _ ih =>
    have h2 : (muAction q κ σ)⁻¹ (muAction q κ σ a) = a := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [ih] at h2; rw [map_inv]; exact h2

theorem exists_rho {B₀ B O : Type*} [CommRing B₀] [CommRing B] [CommRing O] [Algebra O B₀]
    (ι₀ : B₀ →+* B) (ρ : B →+* CoordRing q κ)
    (c₀ : ↥(rootsOfUnity (q + 1) (GaloisField q 2)))
    (hfix : ∀ b : B₀, hAction q κ (sc q c₀) (ρ (ι₀ b)) = ρ (ι₀ b))
    (r : O → κ) (hconst : ∀ a : O, ρ (ι₀ (algebraMap O B₀ a)) = algebraMap κ (CoordRing q κ) (r a)) :
    ∃ ρ₁ : B₀ →+* ↥(quotField q κ (Subgroup.zpowers c₀)),
      (∀ b : B₀, ((ρ₁ b : ↥(quotField q κ (Subgroup.zpowers c₀))) : drinfeldFunctionField q κ) =
        algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (ρ (ι₀ b))) ∧
      (∀ b : B₀, ρ₁ b = 0 ↔ ρ (ι₀ b) = 0) ∧
      (∀ a : O, ρ₁ (algebraMap O B₀ a) = algebraMap κ ↥(quotField q κ (Subgroup.zpowers c₀)) (r a)) := by
  have hmem : ∀ b : B₀, algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (ρ (ι₀ b)) ∈ quotField q κ (Subgroup.zpowers c₀) := by
    intro b
    rw [(algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField q κ (Subgroup.zpowers c₀)).1]
    intro ζ
    apply muAction_eq_of_mem_zpowers q κ c₀ _ _ _ ζ.2
    rw [muAction_eq_hAction]; exact hfix b
  let f : B₀ →+* drinfeldFunctionField q κ := (algebraMap (CoordRing q κ) (drinfeldFunctionField q κ)).comp (ρ.comp ι₀)
  let ρ₁ : B₀ →+* ↥(quotField q κ (Subgroup.zpowers c₀)) := f.codRestrict (quotField q κ (Subgroup.zpowers c₀)).toSubring (fun b => hmem b)
  have hρ₁ : ∀ b, ((ρ₁ b : ↥(quotField q κ (Subgroup.zpowers c₀))) : drinfeldFunctionField q κ) = algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (ρ (ι₀ b)) := fun b => rfl
  refine ⟨ρ₁, hρ₁, fun b => ?_, fun a => ?_⟩
  · constructor
    · intro h
      have h1 := congrArg (fun z : ↥(quotField q κ (Subgroup.zpowers c₀)) => (z : drinfeldFunctionField q κ)) h
      simp only [hρ₁] at h1
      exact (IsFractionRing.injective (CoordRing q κ) (drinfeldFunctionField q κ)) (h1.trans (map_zero _).symm)
    · intro h; apply Subtype.ext; rw [hρ₁, h, map_zero]; rfl
  · apply Subtype.ext
    rw [hρ₁, hconst, ← IsScalarTower.algebraMap_apply]; rfl

end Rho
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace C3GlueKit
namespace FR
open DrinfeldCurve

variable (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [Algebra (GaloisField q 2) κ] [IsDomain (CoordRing q κ)]

theorem frac_and_range {B₀ B : Type*} [CommRing B₀] [CommRing B]
    (Cs : Subgroup ↥(rootsOfUnity (q + 1) (GaloisField q 2)))
    (ι₀ : B₀ →+* B) (ρ : B →+* CoordRing q κ)
    (ρ₁ : B₀ →+* ↥(quotField q κ Cs))
    (hρ₁ : ∀ b : B₀, ((ρ₁ b : ↥(quotField q κ Cs)) : drinfeldFunctionField q κ) =
        algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (ρ (ι₀ b)))
    (hpre : ∀ a : CoordRing q κ, (∀ ζ : ↥Cs, muAction q κ (ζ : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) a = a) →
      ∃ x : B₀, ρ (ι₀ x) = a) :
    (∀ z : ↥(quotField q κ Cs), ∃ g h : B₀, ρ₁ h ≠ 0 ∧ z * ρ₁ h = ρ₁ g) ∧
    (∀ z : ↥(quotField q κ Cs), z ∈ Set.range ρ₁ ↔
      (z : drinfeldFunctionField q κ) ∈ Set.range (algebraMap (CoordRing q κ) (drinfeldFunctionField q κ))) := by
  have hF := algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField q κ Cs
  have hinj := IsFractionRing.injective (CoordRing q κ) (drinfeldFunctionField q κ)
  refine ⟨fun z => ?_, fun z => ?_⟩
  · obtain ⟨g', h', hg', hh', hh0, hzh⟩ := hF.2 (z : drinfeldFunctionField q κ) z.2
    obtain ⟨g, hg⟩ := hpre g' hg'
    obtain ⟨h, hh⟩ := hpre h' hh'
    refine ⟨g, h, ?_, ?_⟩
    · intro h0
      apply hh0
      have h1 : ((ρ₁ h : ↥(quotField q κ Cs)) : drinfeldFunctionField q κ) = 0 := by rw [h0]; rfl
      rw [hρ₁, hh] at h1
      exact hinj (h1.trans (map_zero _).symm)
    · apply Subtype.ext
      show (z : drinfeldFunctionField q κ) * ((ρ₁ h : ↥(quotField q κ Cs)) : drinfeldFunctionField q κ) = ((ρ₁ g : ↥(quotField q κ Cs)) : drinfeldFunctionField q κ)
      rw [hρ₁, hρ₁, hg, hh]; exact hzh
  · constructor
    · rintro ⟨b, rfl⟩; exact ⟨ρ (ι₀ b), (hρ₁ b).symm⟩
    · rintro ⟨a, ha⟩
      have hmem : algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) a ∈ quotField q κ Cs := by rw [ha]; exact z.2
      obtain ⟨x, hx⟩ := hpre a ((hF.1 a).mp hmem)
      exact ⟨x, Subtype.ext (by rw [hρ₁, hx, ha])⟩

end FR
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

namespace S3GlueKit

open IsLocalRing

variable {K L : Type*} [Field K] [Field L]

def comapEquiv (e : K ≃+* L) (V : ValuationSubring L) : (V.comap (e : K →+* L)) ≃+* V where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by show e (e.symm y) ∈ V; rw [e.apply_symm_apply]; exact y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp] theorem coe_comapEquiv (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    ((comapEquiv e V x : V) : L) = e x := rfl

theorem isDiscreteValuationRing_comap (e : K ≃+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (V.comap (e : K →+* L)) :=
  let f := (comapEquiv e V).symm
  { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective f.toRingHom f.surjective
    toIsLocalRing := inferInstance
    not_a_field' := by
      intro h
      apply IsDiscreteValuationRing.not_a_field (R := V)
      rw [eq_bot_iff] at h ⊢
      intro y hy
      have : f y ∈ maximalIdeal _ := by
        rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
        exact fun hu => hy (by simpa using hu.map f.symm.toRingHom)
      have := h this
      rw [Ideal.mem_bot] at this ⊢
      simpa using congrArg f.symm this }

theorem mem_maximalIdeal_comap_iff (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    x ∈ maximalIdeal (V.comap (e : K →+* L)) ↔ (comapEquiv e V x) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact ⟨fun h => by simpa using h.map (comapEquiv e V).toRingHom,
    fun h => by simpa using h.map (comapEquiv e V).symm.toRingHom⟩

theorem maximalIdeal_comap_eq_span (e : K ≃+* L) (V : ValuationSubring L) (π : V)
    (h : maximalIdeal V = Ideal.span {π}) :
    maximalIdeal (V.comap (e : K →+* L)) = Ideal.span {(comapEquiv e V).symm π} := by
  apply le_antisymm
  · intro x hx
    rw [mem_maximalIdeal_comap_iff, h, Ideal.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Ideal.mem_span_singleton]
    refine ⟨(comapEquiv e V).symm c, ?_⟩
    apply (comapEquiv e V).injective
    rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact hc
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_comap_iff,
      RingEquiv.apply_symm_apply, h]
    exact Ideal.mem_span_singleton_self π

theorem exists_subring_image {R S : Type*} [Ring R] [Ring S] (s : Subring R) (f : R →+* S) :
    ∃ B : Subring S, ∀ y : S, y ∈ B ↔ ∃ x : R, x ∈ s ∧ y = f x :=
  ⟨s.map f, fun y => by
    rw [Subring.mem_map]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩⟩

theorem exists_namingBlock {k E : Type*} [Field k] [Field E] [Algebra k E]
    (O : Type*) [CommRing O] [Algebra O E] [Algebra O k] [IsScalarTower O k E]
    (S : Set (E ≃ₐ[k] E)) (Bt : Subalgebra O E) (Wt : ValuationSubring E) :
    ∃ (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E) (B₀ : Subalgebra O E) (W₀' : ValuationSubring K₀),
      G = Subgroup.closure S ∧ K₀ = IntermediateField.fixedField G ∧
      (∀ f : E, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ G → τ f = f) ∧
      (∀ f : K₀, f ∈ W₀' ↔ ((f : E)) ∈ Wt) := by
  refine ⟨Subgroup.closure S, IntermediateField.fixedField (Subgroup.closure S),
    { carrier := {f : E | f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.closure S → τ f = f}
      mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, algebraMap_mem' := ?_ },
    Wt.comap (algebraMap _ E), rfl, rfl, fun f => Iff.rfl, fun f => Iff.rfl⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Bt.mul_mem ha hb, fun τ hτ => by rw [map_mul, ha' τ hτ, hb' τ hτ]⟩
  · exact ⟨Bt.one_mem, fun τ _ => map_one τ⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Bt.add_mem ha hb, fun τ hτ => by rw [map_add, ha' τ hτ, hb' τ hτ]⟩
  · exact ⟨Bt.zero_mem, fun τ _ => map_zero τ⟩
  · intro a
    exact ⟨Bt.algebraMap_mem a, fun τ _ => by rw [IsScalarTower.algebraMap_apply O k E]; exact τ.commutes _⟩

theorem exists_comap_valuationSubring {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) :
    ∃ W : ValuationSubring K, W = V.comap (e : K →+* L) ∧ ∀ f : K, f ∈ W ↔ e f ∈ V :=
  ⟨_, rfl, fun f => Iff.rfl⟩

theorem exists_algebra_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) :
    ∃ alg : Algebra R S, ∀ a : R, @algebraMap R S _ _ alg a = ψ a :=
  ⟨ψ.toAlgebra, fun a => rfl⟩

theorem coe_comapEquiv_symm {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) (y : V) :
    (((comapEquiv e V).symm y : V.comap (e : K →+* L)) : K) = e.symm y := rfl

section algEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem algEquiv_symm_toRingEquiv_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv (algebraMap R B x) = algebraMap R A x := φ.symm.commutes x

theorem algEquiv_symm_toRingEquiv_symm_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv.symm (algebraMap R A x) = algebraMap R B x := φ.commutes x

theorem algEquiv_symm_toRingEquiv_apply_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv (φ x) = x := φ.symm_apply_apply x

theorem algEquiv_symm_toRingEquiv_symm_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv.symm x = φ x := rfl

end algEquiv
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit"

theorem exists_mem_and_maximalIdeal_eq_span {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (V : ValuationSubring L) (W : ValuationSubring K) (hW : W = V.comap (e : K →+* L))
    (π : L) (hπV : π ∈ V) (hmax : IsLocalRing.maximalIdeal V = Ideal.span {(⟨π, hπV⟩ : V)})
    (π' : K) (hπ' : e π' = π) :
    ∃ h : π' ∈ W, IsLocalRing.maximalIdeal W = Ideal.span {(⟨π', h⟩ : W)} := by
  subst hW
  have h : π' ∈ V.comap (e : K →+* L) := by show e π' ∈ V; rw [hπ']; exact hπV
  refine ⟨h, ?_⟩
  rw [maximalIdeal_comap_eq_span e V ⟨π, hπV⟩ hmax]
  congr 2
  apply Subtype.ext
  show e.symm π = π'
  rw [← hπ', e.symm_apply_apply]

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"

namespace C3Kit

section Action

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {R : Type*} [CommRing R] [Algebra R K]

def subalgAction (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B) : MulSemiringAction ↥G ↥B where
  smul τ b := ⟨(τ : K ≃ₐ[k] K) (b : K), h τ τ.2 b b.2⟩
  one_smul b := Subtype.ext rfl
  mul_smul σ τ b := Subtype.ext rfl
  smul_zero τ := Subtype.ext (map_zero _)
  smul_add τ a b := Subtype.ext (map_add _ _ _)
  smul_one τ := Subtype.ext (map_one _)
  smul_mul τ a b := Subtype.ext (map_mul _ _ _)

theorem subalgAction_smul_coe (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B) (τ : ↥G) (b : ↥B) :
    letI := subalgAction G B h
    (((τ • b) : ↥B) : K) = (τ : K ≃ₐ[k] K) (b : K) := rfl

def inclAlgebra (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) : Algebra ↥B₀ ↥B :=
  (Subalgebra.inclusion hle).toRingHom.toAlgebra

theorem inclAlgebra_algebraMap_coe (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) (x : ↥B₀) :
    letI := inclAlgebra B₀ B hle
    ((algebraMap ↥B₀ ↥B x : ↥B) : K) = (x : K) := rfl

theorem inclAlgebra_isScalarTower (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) :
    letI := inclAlgebra B₀ B hle
    IsScalarTower R ↥B₀ ↥B :=
  letI := inclAlgebra B₀ B hle
  IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext rfl)

theorem inclAlgebra_faithfulSMul (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) :
    letI := inclAlgebra B₀ B hle
    FaithfulSMul ↥B₀ ↥B :=
  letI := inclAlgebra B₀ B hle
  (faithfulSMul_iff_algebraMap_injective ↥B₀ ↥B).mpr (Subalgebra.inclusion_injective hle)

theorem isGaloisGroup (G : Subgroup (K ≃ₐ[k] K)) (B B₀ : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ B ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (hfrac : ∀ f : K, ∃ g h' : ↥B, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K)) :
    letI := subalgAction G B h
    letI := inclAlgebra B₀ B (fun f hf => ((hB₀ f).mp hf).1)
    IsGaloisGroup ↥G ↥B₀ ↥B := by
  letI := subalgAction G B h
  letI := inclAlgebra B₀ B (fun f hf => ((hB₀ f).mp hf).1)
  refine ⟨⟨fun {σ τ} hστ => ?_⟩, ⟨fun τ b₀ b => ?_⟩, ⟨fun b hb => ?_⟩⟩
  ·
    apply Subtype.ext
    apply AlgEquiv.ext
    intro f
    obtain ⟨g, h', hh0, hfg⟩ := hfrac f
    have eg : (σ : K ≃ₐ[k] K) (g : K) = (τ : K ≃ₐ[k] K) (g : K) := congrArg Subtype.val (hστ g)
    have eh : (σ : K ≃ₐ[k] K) (h' : K) = (τ : K ≃ₐ[k] K) (h' : K) := congrArg Subtype.val (hστ h')
    have hσh : (σ : K ≃ₐ[k] K) (h' : K) ≠ 0 := (map_ne_zero_iff _ (σ : K ≃ₐ[k] K).injective).mpr hh0
    have e1 : (σ : K ≃ₐ[k] K) f * (σ : K ≃ₐ[k] K) (h' : K) = (σ : K ≃ₐ[k] K) (g : K) := by rw [← map_mul, hfg]
    have e2 : (τ : K ≃ₐ[k] K) f * (τ : K ≃ₐ[k] K) (h' : K) = (τ : K ≃ₐ[k] K) (g : K) := by rw [← map_mul, hfg]
    rw [← mul_left_inj' hσh, e1, eg, eh, ← e2]
  ·
    apply Subtype.ext
    change (τ : K ≃ₐ[k] K) ((b₀ : K) * (b : K)) = (b₀ : K) * (τ : K ≃ₐ[k] K) (b : K)
    rw [map_mul, ((hB₀ b₀).mp b₀.2).2 τ τ.2]
  ·
    refine ⟨⟨(b : K), (hB₀ b).mpr ⟨b.2, fun τ hτ => ?_⟩⟩, Subtype.ext rfl⟩
    exact congrArg Subtype.val (hb ⟨τ, hτ⟩)

theorem smulCommClass (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    [Algebra R k] [IsScalarTower R k K] :
    letI := subalgAction G B h
    SMulCommClass ↥G R ↥B := by
  letI := subalgAction G B h
  refine ⟨fun τ r b => Subtype.ext ?_⟩
  change (τ : K ≃ₐ[k] K) ((r • b : ↥B) : K) = ((r • (τ • b) : ↥B) : K)
  rw [Subalgebra.coe_smul, Subalgebra.coe_smul, Algebra.smul_def, Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply R k K, AlgEquiv.commutes]
  rfl

end Action
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"

end C3Kit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"

theorem C3aux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h
    rfl
    rfl
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

namespace C3Kit4

theorem exists_invariant_fraction {k K : Type*} [Field k] [Field K] [Algebra k K] {R : Type*} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) [Finite ↥G] (B B₀ : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ B ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (hfrac : ∀ f : K, ∃ g h' : ↥B, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K))
    (f : K) (hf : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f) :
    ∃ g h' : ↥B₀, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K) := by
  classical
  haveI : Fintype ↥G := Fintype.ofFinite _
  obtain ⟨g, h', hh0, hfg⟩ := hfrac f

  let N : K := ∏ σ : ↥G, (σ : K ≃ₐ[k] K) (h' : K)
  have hNB : N ∈ B := Subalgebra.prod_mem B (fun σ _ => h σ σ.2 _ h'.2)
  have hN0 : N ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro σ _
    exact (map_ne_zero_iff _ (σ : K ≃ₐ[k] K).injective).mpr hh0
  have hNinv : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ N = N := by
    intro τ hτ
    simp only [N, map_prod]
    simp_rw [← AlgEquiv.mul_apply]
    exact Fintype.prod_equiv (Equiv.mulLeft ⟨τ, hτ⟩) _ _ (fun σ => rfl)

  let P : K := ∏ σ ∈ (Finset.univ : Finset ↥G).erase 1, (σ : K ≃ₐ[k] K) (h' : K)
  have hPB : P ∈ B := Subalgebra.prod_mem B (fun σ _ => h σ σ.2 _ h'.2)
  have hNP : N = (h' : K) * P := by
    simp only [N, P]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ↥G) _ (Finset.mem_univ (1 : ↥G))]
    rfl
  have hfN : f * N = (g : K) * P := by rw [hNP, ← mul_assoc, hfg]
  have hfNB : f * N ∈ B := by rw [hfN]; exact B.mul_mem g.2 hPB
  have hfNinv : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (f * N) = f * N := by
    intro τ hτ; rw [map_mul, hf τ hτ, hNinv τ hτ]
  exact ⟨⟨f * N, (hB₀ _).mpr ⟨hfNB, hfNinv⟩⟩, ⟨N, (hB₀ _).mpr ⟨hNB, hNinv⟩⟩, hN0, rfl⟩

end C3Kit4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"

namespace C3GlueKit
open IsLocalRing

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {O : Type*} [CommRing O] [Algebra O K]

theorem prime_and_loc_of_invariants
    (G : Subgroup (K ≃ₐ[k] K)) (Bt B₀ : Subalgebra O K) (Wt : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ Bt → f ∈ Wt)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (π : O) (hπm : (⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ : ↥Wt) ∈ maximalIdeal ↥Wt)
    (hπne : algebraMap O K π ≠ 0)
    (hGO : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (algebraMap O K π) = algebraMap O K π)
    (P : (K ≃ₐ[k] K) → Prop) (hPG : ∀ τ, P τ → τ ∈ G)
    (hR5c : ∀ b : ↥Bt, (∀ τ : K ≃ₐ[k] K, P τ → ∀ hb : τ (b : K) ∈ Bt,
        (⟨τ (b : K), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) → algebraMap O ↥Bt π ∣ b)
    (K₀ : IntermediateField k K) (hK₀B₀ : ∀ f : K, f ∈ B₀ → f ∈ K₀)
    (hK₀G : ∀ f : K, f ∈ K₀ → ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (W₀ : ValuationSubring ↥K₀) (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ((f : K)) ∈ Wt)
    (hloc : ∀ f : K, (∀ g : ↥G, g • f = f) →
      (f ∈ Wt ↔ ∃ g h : K, g ∈ Bt.toSubring ∧ h ∈ Bt.toSubring ∧ (∀ σ : ↥G, σ • g = g) ∧ (∀ σ : ↥G, σ • h = h) ∧
        (∀ hh : h ∈ Wt, (⟨h, hh⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) ∧ f * h = g)) :
    (∀ b : ↥B₀, ((⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ : ↥Wt) ∈ maximalIdeal ↥Wt ↔ algebraMap O ↥B₀ π ∣ b)) ∧
    Prime (algebraMap O ↥B₀ π) ∧
    (∀ f : ↥K₀, f ∈ W₀ ↔ ∃ g h : ↥B₀, ¬ (algebraMap O ↥B₀ π ∣ h) ∧ (f : K) * (h : K) = (g : K)) := by
  have hcoeπ : ((algebraMap O ↥B₀ π : ↥B₀) : K) = algebraMap O K π := Subalgebra.coe_algebraMap B₀ π
  have KEY : ∀ b : ↥B₀, ((⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ : ↥Wt) ∈ maximalIdeal ↥Wt ↔ algebraMap O ↥B₀ π ∣ b) := by
    intro b
    obtain ⟨hbBt, hbfix⟩ := (hB₀ _).mp b.2
    constructor
    · intro hm
      have hprem : ∀ τ : K ≃ₐ[k] K, P τ → ∀ hb : τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K) ∈ Bt,
          (⟨τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt := by
        intro τ hP hb
        have e : τ (b : K) = (b : K) := hbfix τ (hPG τ hP)
        have : (⟨τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K), hBW _ hb⟩ : ↥Wt) = ⟨(b : K), hBW _ hbBt⟩ := Subtype.ext e
        rw [this]; exact hm
      obtain ⟨c, hc⟩ := hR5c ⟨(b : K), hbBt⟩ hprem
      have hcK : (b : K) = algebraMap O K π * (c : K) := by
        have := congrArg (fun z : ↥Bt => (z : K)) hc
        simpa [Subalgebra.coe_algebraMap] using this
      have hcfix : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (c : K) = (c : K) := by
        intro τ hτ
        have h1 := hbfix τ hτ
        rw [hcK, map_mul, hGO τ hτ] at h1
        exact mul_left_cancel₀ hπne h1
      have hcB₀ : (c : K) ∈ B₀ := (hB₀ _).mpr ⟨c.2, hcfix⟩
      refine ⟨⟨(c : K), hcB₀⟩, Subtype.ext ?_⟩
      rw [Subalgebra.coe_mul, hcoeπ]; exact hcK
    · rintro ⟨c, hc⟩
      have hcK : (b : K) = algebraMap O K π * (c : K) := by
        have := congrArg (fun z : ↥B₀ => (z : K)) hc
        rw [Subalgebra.coe_mul, hcoeπ] at this; exact this
      have hcW : (c : K) ∈ Wt := hBW _ ((hB₀ _).mp c.2).1
      have : (⟨(b : K), hBW _ hbBt⟩ : ↥Wt) = ⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ * ⟨(c : K), hcW⟩ :=
        Subtype.ext hcK
      rw [this]
      exact Ideal.mul_mem_right _ _ hπm
  refine ⟨KEY, ?_, ?_⟩
  ·
    have hmprime : (maximalIdeal ↥Wt).IsPrime := Ideal.IsMaximal.isPrime inferInstance
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      apply hπne
      have := congrArg (fun z : ↥B₀ => (z : K)) h0
      rw [hcoeπ] at this; simpa using this
    · intro hu
      have hu' : IsUnit ((⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ : ↥Wt)) := by
        obtain ⟨u, hu⟩ := hu
        have hval : ((u : ↥B₀) : K) = algebraMap O K π := by rw [hu, hcoeπ]
        have hinv : ((u⁻¹ : (↥B₀)ˣ) : ↥B₀) * (u : ↥B₀) = 1 := u.inv_mul
        refine isUnit_iff_exists_inv'.mpr ⟨⟨((u⁻¹ : (↥B₀)ˣ) : ↥B₀), hBW _ ((hB₀ _).mp ((u⁻¹ : (↥B₀)ˣ) : ↥B₀).2).1⟩, Subtype.ext ?_⟩
        have := congrArg (fun z : ↥B₀ => (z : K)) hinv
        rw [Subalgebra.coe_mul, hval, Subalgebra.coe_one] at this
        exact this
      exact (mem_maximalIdeal _ |>.mp hπm) hu'
    · intro a b hab
      rw [← KEY] at hab ⊢; rw [← KEY]
      have : (⟨((a * b : ↥B₀) : K), hBW _ ((hB₀ _).mp (a * b).2).1⟩ : ↥Wt) =
          ⟨(a : K), hBW _ ((hB₀ _).mp a.2).1⟩ * ⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ := Subtype.ext (Subalgebra.coe_mul B₀ a b)
      rw [this] at hab
      exact hmprime.mem_or_mem hab
  ·
    intro f
    rw [hW₀, hloc (f : K) (fun g => hK₀G _ f.2 g g.2)]
    constructor
    · rintro ⟨g, h, hg, hh, hgfix, hhfix, hunit, hfh⟩
      have hgB₀ : g ∈ B₀ := (hB₀ _).mpr ⟨Subalgebra.mem_toSubring.mp hg, fun τ hτ => hgfix ⟨τ, hτ⟩⟩
      have hhB₀ : h ∈ B₀ := (hB₀ _).mpr ⟨Subalgebra.mem_toSubring.mp hh, fun τ hτ => hhfix ⟨τ, hτ⟩⟩
      refine ⟨⟨g, hgB₀⟩, ⟨h, hhB₀⟩, fun hd => ?_, hfh⟩
      have hm := (KEY ⟨h, hhB₀⟩).mpr hd
      exact hunit _ hm
    · rintro ⟨g, h, hnd, hfh⟩
      refine ⟨(g : K), (h : K), Subalgebra.mem_toSubring.mpr ((hB₀ _).mp g.2).1, Subalgebra.mem_toSubring.mpr ((hB₀ _).mp h.2).1, fun σ => ((hB₀ _).mp g.2).2 σ σ.2,
        fun σ => ((hB₀ _).mp h.2).2 σ σ.2, fun hh hm => hnd ((KEY h).mp ?_), hfh⟩
      have : (⟨(h : K), hh⟩ : ↥Wt) = ⟨(h : K), hBW _ ((hB₀ _).mp h.2).1⟩ := rfl
      rw [← this]; exact hm

end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"

namespace C3GlueKit
section kitW
open IsLocalRing

theorem mem_iff_map_mem_of_pow_eq_one {k K : Type*} [Field k] [Field K] [Algebra k K]
    {S : Type*} [SetLike S K] (B : S) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g)
    (μ : K ≃ₐ[k] K) (n : ℕ) (hn : 0 < n) (hμn : μ ^ n = 1)
    (hμB : ∀ f : K, f ∈ B → μ f ∈ B)
    (hμP : ∀ (f : K) (hf : f ∈ B), (⟨f, hBW f hf⟩ : ↥W) ∈ maximalIdeal ↥W → (⟨μ f, hBW _ (hμB f hf)⟩ : ↥W) ∈ maximalIdeal ↥W)
    (f : K) : f ∈ W ↔ μ f ∈ W := by

  have hμmB : ∀ (m : ℕ) (f : K), f ∈ B → (μ ^ m) f ∈ B := by
    intro m; induction m with
    | zero => intro f hf; simpa using hf
    | succ m ih => intro f hf; rw [pow_succ, AlgEquiv.mul_apply]; exact ih _ (hμB f hf)
  have hμmP : ∀ (m : ℕ) (f : K) (hf : f ∈ B), (⟨f, hBW f hf⟩ : ↥W) ∈ maximalIdeal ↥W →
      (⟨(μ ^ m) f, hBW _ (hμmB m f hf)⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro m; induction m with
    | zero => intro f hf h; simpa using h
    | succ m ih =>
      intro f hf h
      have h1 := ih _ (hμB f hf) (hμP f hf h)
      have e : (μ ^ (m + 1)) f = (μ ^ m) (μ f) := by rw [pow_succ, AlgEquiv.mul_apply]
      have : (⟨(μ ^ (m + 1)) f, hBW _ (hμmB (m + 1) f hf)⟩ : ↥W) = ⟨(μ ^ m) (μ f), hBW _ (hμmB m _ (hμB f hf))⟩ := Subtype.ext e
      rw [this]; exact h1

  have hμP' : ∀ (h : K) (hh : h ∈ B), (⟨μ h, hBW _ (hμB h hh)⟩ : ↥W) ∈ maximalIdeal ↥W → (⟨h, hBW h hh⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro h hh hm
    have h1 := hμmP (n - 1) (μ h) (hμB h hh) hm
    have e : (μ ^ (n - 1)) (μ h) = h := by
      rw [← AlgEquiv.mul_apply, ← pow_succ, Nat.sub_add_cancel hn, hμn, AlgEquiv.one_apply]
    have : (⟨(μ ^ (n - 1)) (μ h), hBW _ (hμmB (n - 1) _ (hμB h hh))⟩ : ↥W) = ⟨h, hBW h hh⟩ := Subtype.ext e
    rw [← this]; exact h1

  have fwd : ∀ f : K, f ∈ W → μ f ∈ W := by
    intro f hf
    obtain ⟨g, h, hg, hh, hunit, hfh⟩ := (hloc f).mp hf
    refine (hloc (μ f)).mpr ⟨μ g, μ h, hμB g hg, hμB h hh, fun hh' hm => hunit (hBW h hh) (hμP' h hh ?_), by rw [← map_mul, hfh]⟩
    have : (⟨μ h, hh'⟩ : ↥W) = ⟨μ h, hBW _ (hμB h hh)⟩ := rfl
    rw [← this]; exact hm
  refine ⟨fwd f, fun hμf => ?_⟩
  have h1 : (μ ^ (n - 1)) (μ f) ∈ W := by
    have : ∀ (m : ℕ) (x : K), x ∈ W → (μ ^ m) x ∈ W := by
      intro m; induction m with
      | zero => intro x hx; simpa using hx
      | succ m ih => intro x hx; rw [pow_succ, AlgEquiv.mul_apply]; exact ih _ (fwd x hx)
    exact this _ _ hμf
  rwa [← AlgEquiv.mul_apply, ← pow_succ, Nat.sub_add_cancel hn, hμn, AlgEquiv.one_apply] at h1

theorem exists_prime_pullback {k K : Type*} [Field k] [Field K] [Algebra k K] {O : Type*} [CommRing O] [Algebra O K]
    (Bt : Subalgebra O K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ Bt → f ∈ W)
    (τ : K ≃ₐ[k] K) (hτB : ∀ f : K, f ∈ Bt → τ f ∈ Bt) :
    ∃ Q : Ideal ↥Bt, Q.IsPrime ∧
      ∀ b : ↥Bt, b ∈ Q ↔ (⟨τ (b : K), hBW _ (hτB _ b.2)⟩ : ↥W) ∈ maximalIdeal ↥W := by
  let φ : ↥Bt →+* ↥W :=
    { toFun := fun b => ⟨τ (b : K), hBW _ (hτB _ b.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨(maximalIdeal ↥W).comap φ, Ideal.comap_isPrime φ (maximalIdeal ↥W), fun b => ?_⟩
  rw [Ideal.mem_comap]; exact Iff.rfl

end kitW
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"

namespace C3GlueKit
section kitK4
open IsLocalRing

theorem mem_maximalIdeal_of_restrict {k E : Type*} [Field k] [Field E] [Algebra k E]
    (K₀ : IntermediateField k E) (Wt : ValuationSubring E) (W₀ : ValuationSubring ↥K₀)
    (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ((f : E)) ∈ Wt)
    (x : ↥W₀) (hx : (⟨((x : ↥K₀) : E), (hW₀ _).mp x.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) :
    x ∈ maximalIdeal ↥W₀ := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  obtain ⟨u, hu⟩ := hu
  have hinv : ((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) = 1 := u.inv_mul
  refine isUnit_iff_exists_inv'.mpr ⟨⟨(((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀), (hW₀ _).mp ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2⟩, Subtype.ext ?_⟩
  have h1 := congrArg (fun z : ↥W₀ => (((z : ↥K₀)) : E)) hinv
  show (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀) : E)) * ((x : ↥K₀) : E) = 1
  rw [← hu]
  have h2 : (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) : ↥W₀) : ↥K₀) : E) =
      (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀) : E)) * ((((u : ↥W₀)) : ↥K₀) : E) := rfl
  rw [← h2, h1]; rfl

end kitK4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.C3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed.S3GlueKit"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups Pointwise

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option maxHeartbeats 0 in

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (M' : ℕ)
    [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (π₀ : ↥k₀)
    (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (ℓ : ℕ)
    (ζ₀ : ↥k₀)
    (ϖt : ↥k₀)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (Ab : ValuationSubring ↥Kb)
    (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab)
    (ℓ' : ℕ)
    [Fact ℓ'.Prime]
    (ξ : ↥k₀)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ)
    [Fact (jℓ ≠ 0)]
    (ϖt' : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ))
    (Bt : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (Wt : ValuationSubring ↥Kℓ)
    (hBW : ∀ f : ↥Kℓ, f ∈ Bt → f ∈ Wt)
    (n : ℕ)
    (γ₀ : SL(2, ℤ))
    (τ₀ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (m : ℕ)
    (ζc : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (ℱ : ModularCurve.FullLevel.RigidDescentHyps q M' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ℓ' ξ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends)
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ})
    (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (hK₀ : K₀ = IntermediateField.fixedField G)
    (B₀ : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hB₀ : ∀ f : ↥Kℓ, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f)
    (W₀' : ValuationSubring ↥K₀)
    (hW₀' : ∀ f : ↥K₀, f ∈ W₀' ↔ ((f : ↥Kℓ)) ∈ Wt)
    :
        IsIntegrallyClosed (↥B₀ ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩}) := by
  have hℱ := ℱ
  obtain ⟨hq, hqM', hA, hW, hR₀, hdvr, hunif, hhens, hres, hκ, hℓ, hℓ3, hℓq, hℓM', hζ₀, hϖtA, hϖt, hKb, hϖb, hϖb0, hℓ'3, hℓ'q, hℓ'M, htame, hξ, hKℓ, hjℓ, hϖt', hy, hϖy, hss, hover, hOrbit, hS1, hn1, hnq, hγ₀Γ, hγ₀Γ0, hτ₀, hτ₀W, hm1, hm, hζc, hζcprim, hjC, ha₀y, hR7, hR9, hR10, hn⟩ := hℱ
  classical
  haveI hmne : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩

  have hObt1 := C3aux_exists_emb k₀ (q * ℓ') ξ hξ
  obtain ⟨ι, hι'⟩ := hObt1
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')) :=
    ⟨ι, by rw [hι']; simp only [Nat.cast_mul]⟩
  have hObt2 := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  obtain ⟨huniq, hmul, hone⟩ := hObt2
  obtain ⟨Gfull, hGfin, hGmem⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  have hex := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ

  have hGle : G ≤ Gfull := by
    rw [hG, Subgroup.closure_le]
    rintro τ ⟨γ, -, hγ0, hτ⟩
    exact (hGmem τ).mpr ⟨γ, hγ0, hτ⟩
  haveI hGfinite : Finite ↥G := by
    haveI := hGfin
    exact Finite.of_injective (Subgroup.inclusion hGle) (Subgroup.inclusion_injective hGle)
  have hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ := by
    intro τ hτ
    rw [hG] at hτ
    refine Subgroup.closure_induction (p := fun τ _ => ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
        γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ) ?_ ?_ ?_ ?_ hτ
    · intro τ h; exact h
    · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [inv_one]; exact hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _)⟩
    · rintro τ σ - - ⟨γ, hγq, hγ0, hτ⟩ ⟨δ, hδq, hδ0, hσ⟩
      refine ⟨γ * δ, Subgroup.mul_mem _ hγq hδq, Subgroup.mul_mem _ hγ0 hδ0, ?_⟩
      rw [mul_inv_rev]
      exact hmul γ⁻¹ δ⁻¹ (Subgroup.inv_mem _ hγ0) (Subgroup.inv_mem _ hδ0) τ σ hτ hσ
    · rintro τ - ⟨γ, hγq, hγ0, hτ⟩
      have hObt3 := hex γ⁻¹ (Subgroup.inv_mem _ hγ0)
      obtain ⟨σ, hσ⟩ := hObt3
      rw [inv_inv] at hσ

      have h1 : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') (γ * γ⁻¹) Kℓ (τ * σ) := hmul γ⁻¹ γ (Subgroup.inv_mem _ hγ0) hγ0 τ σ hτ hσ
      rw [mul_inv_cancel] at h1
      have h2 : τ * σ = 1 := huniq 1 (Subgroup.one_mem _) _ _ h1 (hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _))
      have h3 : τ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
      refine ⟨γ⁻¹, Subgroup.inv_mem _ hγq, Subgroup.inv_mem _ hγ0, ?_⟩
      rw [inv_inv, h3]; exact hσ

  obtain ⟨hR1a, hR1b, hR2a, hR2b, hR2c, hR3a, hR3b, hR3c, hR3d, hR3e, hR46, hR5a, hR5b, hR5c⟩ := hS1
  have hGBt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt := by
    intro τ hτ f hf
    have hObt4 := hGatt τ hτ
    obtain ⟨γ, -, hγ0, hτ'⟩ := hObt4
    exact hR5a γ hγ0 τ hτ' f hf

  have hB₀le : B₀ ≤ Bt := fun f hf => ((hB₀ f).mp hf).1
  letI instAct : MulSemiringAction ↥G ↥Bt := C3Kit.subalgAction G Bt hGBt
  letI instAlg : Algebra ↥B₀ ↥Bt := C3Kit.inclAlgebra B₀ Bt hB₀le
  haveI instIST : IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ↥Bt := C3Kit.inclAlgebra_isScalarTower B₀ Bt hB₀le
  haveI instFS : FaithfulSMul ↥B₀ ↥Bt := C3Kit.inclAlgebra_faithfulSMul B₀ Bt hB₀le
  haveI instGal : IsGaloisGroup ↥G ↥B₀ ↥Bt := C3Kit.isGaloisGroup G Bt B₀ hGBt hB₀ hR1b
  haveI instSCC : SMulCommClass ↥G ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := C3Kit.smulCommClass G Bt hGBt
  haveI : Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := hR2b
  haveI hdvr0 : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := hdvr

  have hGunit : IsUnit ((Nat.card ↥G : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    have hObt5 := ModularCurve.FullLevel.AuxLevel.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ G hG
    obtain ⟨-, hGdvd⟩ := hObt5
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hGdvd) htame

  have hC1 := IsGaloisGroup.finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
    ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ↥Bt ↥G hGunit
  obtain ⟨hB₀ft, hB₀fp, hBtfin, hB₀normal, hB₀flat, hB₀fib, hB₀smooth⟩ := hC1

  have hObtE := C3GlueKit.exists_residueField_equiv (K := ↥k₀) (L := AlgebraicClosure ℚ) A (fun a ha => hκ a ha)
  obtain ⟨e, he⟩ := hObtE
  haveI hresI : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := hres
  haveI hκalg : IsAlgClosed (ResidueField ↥A) := IsAlgClosed.of_ringEquiv _ _ e
  have hqp : q.Prime := Fact.out
  have hqA : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    have hq' : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
    rw [← ValuationSubring.coe_mem_nonunits_iff, hq']; exact hA
  haveI hchar : CharP (ResidueField ↥A) q := by
    have h0 : ((q : ℕ) : ResidueField ↥A) = 0 := by
      rw [← map_natCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff]; exact hqA
    exact (CharP.charP_iff_prime_eq_zero hqp).mpr h0
  letI instZ : Algebra (ZMod q) (ResidueField ↥A) := ZMod.algebra (ResidueField ↥A) q
  letI inst : Algebra (GaloisField q 2) (ResidueField ↥A) :=
    (IsAlgClosed.lift : GaloisField q 2 →ₐ[ZMod q] ResidueField ↥A).toRingHom.toAlgebra
  letI inst₀ : Algebra (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :=
    ((e.symm : ResidueField ↥A →+* ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).comp (algebraMap (GaloisField q 2) (ResidueField ↥A))).toAlgebra

  have hObtR := hR46 inst₀
  obtain ⟨ρ0, hρ0surj, hρ0ker, -, -⟩ := hObtR
  have hkerprime : (RingHom.ker ρ0).IsPrime := by
    have hObtQ := C3GlueKit.exists_prime_pullback (k := ↥k₀) Bt Wt hBW 1 (fun f hf => by simpa using hf)
    obtain ⟨Q, hQ, hQmem⟩ := hObtQ
    have : RingHom.ker ρ0 = Q := by
      ext b; rw [RingHom.mem_ker, hρ0ker, hQmem]; exact Iff.rfl
    rw [this]; exact hQ
  haveI : (RingHom.ker ρ0).IsPrime := hkerprime
  haveI hdom₀ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) :=
    MulEquiv.isDomain (↥Bt ⧸ RingHom.ker ρ0) (RingHom.quotientKerEquivOfSurjective hρ0surj).symm.toMulEquiv
  haveI hdomκ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A)) :=
    MulEquiv.isDomain (DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (C3GlueKit.BC.bcEquiv q e).symm.toMulEquiv

  have hObtM := ModularCurve.FullLevel.AuxLevel.exists_quotField_ringHom_invariants_of_rigidChart_framed q M' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ℓ' ξ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends ℱ G hG K₀ hK₀ B₀ hB₀ W₀' hW₀' inst hdomκ
  obtain ⟨Cs, ρ, -, hker, -, -, hrange, -⟩ := hObtM

  letI actR : MulSemiringAction ↥Cs (DrinfeldCurve.CoordRing q (ResidueField ↥A)) :=
    MulSemiringAction.compHom _ ((DrinfeldCurve.muAction q (ResidueField ↥A)).comp Cs.subtype)
  have hact : ∀ (ζ : ↥Cs) (a : DrinfeldCurve.CoordRing q (ResidueField ↥A)),
      ζ • a = DrinfeldCurve.muAction q (ResidueField ↥A) (ζ : ↥(rootsOfUnity (q + 1) (GaloisField q 2))) a := fun _ _ => rfl
  let T : Subring (DrinfeldCurve.CoordRing q (ResidueField ↥A)) :=
    { carrier := {a | ∀ ζ : ↥Cs, ζ • a = a}
      mul_mem' := fun {a b} ha hb ζ => by rw [smul_mul', ha ζ, hb ζ]
      one_mem' := fun ζ => smul_one ζ
      add_mem' := fun {a b} ha hb ζ => by rw [smul_add, ha ζ, hb ζ]
      zero_mem' := fun ζ => smul_zero ζ
      neg_mem' := fun {a} ha ζ => by rw [smul_neg, ha ζ] }
  have hTmem : ∀ a, a ∈ T ↔ ∀ ζ : ↥Cs, ζ • a = a := fun a => Iff.rfl
  letI algT : Algebra ↥T (DrinfeldCurve.CoordRing q (ResidueField ↥A)) := T.subtype.toAlgebra
  haveI : FaithfulSMul ↥T (DrinfeldCurve.CoordRing q (ResidueField ↥A)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsGaloisGroup ↥Cs ↥T (DrinfeldCurve.CoordRing q (ResidueField ↥A)) := by
    refine ⟨⟨fun {σ τ} hστ => ?_⟩, ⟨fun ζ t a => ?_⟩, ⟨fun a ha => ⟨⟨a, ha⟩, rfl⟩⟩⟩
    · apply Subtype.ext
      apply C3GlueKit.Scal.sc_injective_on_hAction q (ResidueField ↥A)
      intro a
      have h1 := hστ a
      rw [hact, hact, DrinfeldCurve.muAction_eq_hAction, DrinfeldCurve.muAction_eq_hAction] at h1
      exact h1
    · show ζ • ((t : DrinfeldCurve.CoordRing q (ResidueField ↥A)) * a) = (t : DrinfeldCurve.CoordRing q (ResidueField ↥A)) * ζ • a
      rw [smul_mul', t.2 ζ]
  haveI := DrinfeldCurve.isDedekindDomain_coordRing q (ResidueField ↥A)
  have hTic : IsIntegrallyClosed ↥T :=
    IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed ↥Cs (A := ↥T) (B := DrinfeldCurve.CoordRing q (ResidueField ↥A))

  have hF := DrinfeldCurve.algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField q (ResidueField ↥A) Cs
  have hTq : ∀ t : ↥T, algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) (t : DrinfeldCurve.CoordRing q (ResidueField ↥A)) ∈
      DrinfeldCurve.quotField q (ResidueField ↥A) Cs := fun t => (hF.1 _).mpr (fun ζ => t.2 ζ)
  let g0 : ↥T →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) :=
    ((algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))).comp T.subtype).codRestrict
      (DrinfeldCurve.quotField q (ResidueField ↥A) Cs).toSubring (fun t => hTq t)
  have hg0 : ∀ t : ↥T, ((g0 t : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
      algebraMap _ _ (t : DrinfeldCurve.CoordRing q (ResidueField ↥A)) := fun t => rfl
  have hg0range : ∀ t : ↥T, g0 t ∈ ρ.range := fun t => (hrange _).mpr ⟨(t : DrinfeldCurve.CoordRing q (ResidueField ↥A)), (hg0 t).symm⟩
  let g : ↥T →+* ↥ρ.range := g0.codRestrict ρ.range hg0range
  have hginj : Function.Injective g := by
    intro s t hst
    have h1 : ((g0 s : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) = ((g0 t : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : _) :=
      congrArg (fun z : ↥ρ.range => ((z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) hst
    rw [hg0, hg0] at h1
    exact Subtype.ext (IsFractionRing.injective _ _ h1)
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨a, ha⟩ := (hrange (z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs))).mp z.2
    have haq : algebraMap _ (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) a ∈ DrinfeldCurve.quotField q (ResidueField ↥A) Cs := by
      rw [ha]; exact (z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)).2
    have haT : a ∈ T := fun ζ => (hF.1 a).mp haq ζ
    refine ⟨⟨a, haT⟩, Subtype.ext (Subtype.ext ?_)⟩
    show ((g0 ⟨a, haT⟩ : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) = _
    rw [hg0]; exact ha
  let eT : ↥T ≃+* (↥B₀ ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩}) :=
    (RingEquiv.ofBijective g ⟨hginj, hgsurj⟩).trans ((RingHom.quotientKerEquivRange ρ).symm.trans (Ideal.quotEquivOfEq hker))
  exact IsIntegrallyClosed.of_equiv eT

end S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed (solution)

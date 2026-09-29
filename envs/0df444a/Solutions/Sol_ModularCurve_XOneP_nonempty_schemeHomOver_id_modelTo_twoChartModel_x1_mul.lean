-- Prove2me | solution 1 for ModularCurve.XOneP.nonempty_schemeHomOver_id_modelTo_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/691e2639-b174-56db-a2c6-479f7aaa4319

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_nonempty_schemeHomOver_id_toBase_of_algHom
import Theorems.Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_nonempty_schemeHomOver_id_modelTo_twoChartModel_x1_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

noncomputable section

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

namespace CuspCore

section Good

variable (L : Type) [Field L]

def Good (R : Subring L) (z : LaurentSeries L) : Prop :=
  ∃ pz : PowerSeries L, HahnSeries.ofPowerSeries ℤ L pz = z ∧ PowerSeries.constantCoeff pz ∈ R

variable {L}

theorem good_add {R : Subring L} {z w : LaurentSeries L} (hz : Good L R z) (hw : Good L R w) : Good L R (z + w) := by
  obtain ⟨pz, rfl, hz⟩ := hz
  obtain ⟨pw, rfl, hw⟩ := hw
  exact ⟨pz + pw, map_add _ _ _, by rw [map_add]; exact R.add_mem hz hw⟩

theorem good_mul {R : Subring L} {z w : LaurentSeries L} (hz : Good L R z) (hw : Good L R w) : Good L R (z * w) := by
  obtain ⟨pz, rfl, hz⟩ := hz
  obtain ⟨pw, rfl, hw⟩ := hw
  exact ⟨pz * pw, map_mul _ _ _, by rw [map_mul]; exact R.mul_mem hz hw⟩

theorem good_C {R : Subring L} {x : L} (hx : x ∈ R) : Good L R (HahnSeries.ofPowerSeries ℤ L (PowerSeries.C x)) :=
  ⟨PowerSeries.C x, rfl, by simpa using hx⟩

theorem good_one (R : Subring L) : Good L R 1 :=
  ⟨1, map_one _, by rw [map_one]; exact R.one_mem⟩

theorem good_zero (R : Subring L) : Good L R 0 :=
  ⟨0, map_zero _, by rw [map_zero]; exact R.zero_mem⟩

theorem algebraMap_laurent (x : L) :
    algebraMap L (LaurentSeries L) x = HahnSeries.ofPowerSeries ℤ L (PowerSeries.C x) := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]

theorem algebraMap_powerSeries_laurent :
    algebraMap (PowerSeries L) (LaurentSeries L) = HahnSeries.ofPowerSeries ℤ L := by
  refine RingHom.ext fun f => ?_
  rw [HahnSeries.algebraMap_apply']
  simp

end Good

theorem exists_powerSeries_eq_and_constantCoeff_mem
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (hjinv : ∃ pj : PowerSeries L, HahnSeries.ofPowerSeries ℤ L pj = ((j⁻¹ : ↥K) : LaurentSeries L) ∧
      PowerSeries.constantCoeff pj = 0)
    (y : ↥K) (hy : y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) :
    ∃ py : PowerSeries L, HahnSeries.ofPowerSeries ℤ L py = (y : LaurentSeries L) ∧
      PowerSeries.constantCoeff py ∈ (algebraMap A L).range := by
  classical
  have hinj : Function.Injective (HahnSeries.ofPowerSeries ℤ L) := HahnSeries.ofPowerSeries_injective
  set R : Subring L := (algebraMap A L).range with hR

  let S : Subalgebra A ↥K :=
    { carrier := {x | Good L R (x : LaurentSeries L)}
      mul_mem' := fun {a b} ha hb => by
        show Good L R ((a * b : ↥K) : LaurentSeries L)
        rw [MulMemClass.coe_mul]; exact good_mul ha hb
      one_mem' := by
        show Good L R ((1 : ↥K) : LaurentSeries L)
        rw [OneMemClass.coe_one]; exact good_one R
      add_mem' := fun {a b} ha hb => by
        show Good L R ((a + b : ↥K) : LaurentSeries L)
        rw [AddMemClass.coe_add]; exact good_add ha hb
      zero_mem' := by
        show Good L R ((0 : ↥K) : LaurentSeries L)
        rw [ZeroMemClass.coe_zero]; exact good_zero R
      algebraMap_mem' := fun a => by
        show Good L R ((algebraMap A ↥K a : ↥K) : LaurentSeries L)
        have h : ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a) := by
          rw [IsScalarTower.algebraMap_apply A L ↥K]; rfl
        rw [h, algebraMap_laurent]
        exact good_C ⟨a, rfl⟩ }
  have hjS : (j⁻¹ : ↥K) ∈ S := by
    obtain ⟨pj, hpj, hpj0⟩ := hjinv
    show Good L R _
    exact ⟨pj, hpj, by rw [hpj0]; exact R.zero_mem⟩
  set B : Subalgebra A ↥K := Algebra.adjoin A {(j⁻¹ : ↥K)} with hB
  have hBS : B ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjS)
  have hgoodB : ∀ b : ↥B, Good L R (((b : ↥K)) : LaurentSeries L) := fun b => hBS b.2

  choose ψf hψf hψc using hgoodB
  let ψ : ↥B →+* PowerSeries L :=
    { toFun := ψf
      map_one' := hinj (by rw [hψf, map_one]; simp)
      map_mul' := fun a b => hinj (by rw [map_mul, hψf, hψf, hψf]; simp)
      map_zero' := hinj (by rw [hψf, map_zero]; simp)
      map_add' := fun a b => hinj (by rw [map_add, hψf, hψf, hψf]; simp) }
  have hψ : ∀ b : ↥B, HahnSeries.ofPowerSeries ℤ L (ψ b) = ((b : ↥K) : LaurentSeries L) := fun b => hψf b

  let θ : ↥B →+* LaurentSeries L := (K.val : ↥K →ₐ[L] LaurentSeries L).toRingHom.comp (algebraMap ↥B ↥K)
  have hθ : (HahnSeries.ofPowerSeries ℤ L).comp ψ = θ := by
    ext b
    rw [RingHom.comp_apply, hψ]
    rfl

  have hyint : IsIntegral ↥B y := hy
  obtain ⟨p, hpm, hpy⟩ := hyint
  have hroot : (p.map ψ).eval₂ (HahnSeries.ofPowerSeries ℤ L) ((y : ↥K) : LaurentSeries L) = 0 := by
    rw [Polynomial.eval₂_map, hθ]
    have h := Polynomial.hom_eval₂ p (algebraMap ↥B ↥K) (K.val : ↥K →ₐ[L] LaurentSeries L).toRingHom y
    rw [hpy, map_zero] at h
    exact h.symm
  have hint' : IsIntegral (PowerSeries L) ((y : ↥K) : LaurentSeries L) := by
    refine ⟨p.map ψ, hpm.map ψ, ?_⟩
    rw [algebraMap_powerSeries_laurent]
    exact hroot
  obtain ⟨py, hpy'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hpy : HahnSeries.ofPowerSeries ℤ L py = ((y : ↥K) : LaurentSeries L) := by
    rw [← hpy', algebraMap_powerSeries_laurent]
  refine ⟨py, hpy, ?_⟩

  have heval : (p.map ψ).eval py = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_hom, hpy, hroot]
  set cc : PowerSeries L →+* L := PowerSeries.constantCoeff with hcc
  have hc : ((p.map ψ).map cc).eval (cc py) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, heval, map_zero]
  have hQm : ((p.map ψ).map cc).Monic := (hpm.map ψ).map cc
  have hQlifts : (p.map ψ).map cc ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact RingHom.mem_range.mp (hψc (p.coeff n))
  obtain ⟨Q₀, hQ₀, -, hQ₀m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hQlifts hQm
  have hcint : IsIntegral A (cc py) := ⟨Q₀, hQ₀m, by rw [Polynomial.eval₂_eq_eval_map, hQ₀, hc]⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
  exact ⟨a, ha⟩

end CuspCore

end

namespace CuspAsm

open ModularCurve HahnSeries

section JInv

variable (L : Type) [Field L] [CharZero L]

noncomputable def jNumInv : PowerSeries ℤ := jNum.invOfUnit 1

theorem jNum_mul_jNumInv : jNum * jNumInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNum]; rfl)

noncomputable def jInvSeries : PowerSeries L := (PowerSeries.X * jNumInv).map (Int.castRingHom L)

theorem constantCoeff_jInvSeries : PowerSeries.constantCoeff (jInvSeries L) = 0 := by
  rw [jInvSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_X_mul,
    map_zero]

theorem coeffEmb_jq : coeffEmb L jq = jqModC L := by
  show (jq).map (algebraMap ℚ L) = jqModC L
  rw [← jqModC_rat]
  exact map_jqModC _

theorem jqModC_mul_ofPowerSeries_jInvSeries : jqModC L * ofPowerSeries ℤ L (jInvSeries L) = 1 := by
  have hj : jqModC L = HahnSeries.single (-1 : ℤ) (1 : L) * intSeriesC L jNum := rfl
  rw [jInvSeries, map_mul (PowerSeries.map (Int.castRingHom L)), PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, hj,
    mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
    show HahnSeries.single (0 : ℤ) (1 : L) = 1 from rfl, one_mul, intSeriesC, ← map_mul,
    ← map_mul (PowerSeries.map (Int.castRingHom L)), jNum_mul_jNumInv, map_one, map_one]

theorem coeffEmb_jq_inv : (coeffEmb L jq)⁻¹ = ofPowerSeries ℤ L (jInvSeries L) := by
  rw [coeffEmb_jq]
  exact inv_eq_of_mul_eq_one_right (jqModC_mul_ofPowerSeries_jInvSeries L)

end JInv

section Phi

variable (L : Type) [Field L] [CharZero L]
  (K : IntermediateField L (LaurentSeries L))
  (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
  [Algebra A ↥K] [IsScalarTower A L ↥K]
  (j : ↥K) [Fact (j ≠ 0)]
  (hjinv : ∃ pj : PowerSeries L, HahnSeries.ofPowerSeries ℤ L pj = ((j⁻¹ : ↥K) : LaurentSeries L) ∧
    PowerSeries.constantCoeff pj = 0)

open AlgebraicCurve.TwoChartIntegralModel

noncomputable def ser (y : ↥(chartAlgInf A (↥K) j)) : PowerSeries L :=
  Classical.choose (CuspCore.exists_powerSeries_eq_and_constantCoeff_mem L K A j hjinv y.1 y.2)

theorem ofPowerSeries_ser (y : ↥(chartAlgInf A (↥K) j)) :
    HahnSeries.ofPowerSeries ℤ L (ser L K A j hjinv y) = (((y : ↥K)) : LaurentSeries L) :=
  (Classical.choose_spec (CuspCore.exists_powerSeries_eq_and_constantCoeff_mem L K A j hjinv y.1 y.2)).1

theorem constantCoeff_ser_mem (y : ↥(chartAlgInf A (↥K) j)) :
    PowerSeries.constantCoeff (ser L K A j hjinv y) ∈ (algebraMap A L).range :=
  (Classical.choose_spec (CuspCore.exists_powerSeries_eq_and_constantCoeff_mem L K A j hjinv y.1 y.2)).2

noncomputable def cval (y : ↥(chartAlgInf A (↥K) j)) : A :=
  Classical.choose (RingHom.mem_range.mp (constantCoeff_ser_mem L K A j hjinv y))

theorem algebraMap_cval (y : ↥(chartAlgInf A (↥K) j)) :
    algebraMap A L (cval L K A j hjinv y) = PowerSeries.constantCoeff (ser L K A j hjinv y) :=
  Classical.choose_spec (RingHom.mem_range.mp (constantCoeff_ser_mem L K A j hjinv y))

theorem ser_mul (y z : ↥(chartAlgInf A (↥K) j)) :
    ser L K A j hjinv (y * z) = ser L K A j hjinv y * ser L K A j hjinv z := by
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L))
  rw [map_mul, ofPowerSeries_ser, ofPowerSeries_ser, ofPowerSeries_ser, Subalgebra.coe_mul, IntermediateField.coe_mul]

theorem ser_add (y z : ↥(chartAlgInf A (↥K) j)) :
    ser L K A j hjinv (y + z) = ser L K A j hjinv y + ser L K A j hjinv z := by
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L))
  rw [map_add, ofPowerSeries_ser, ofPowerSeries_ser, ofPowerSeries_ser, Subalgebra.coe_add, IntermediateField.coe_add]

theorem ser_one : ser L K A j hjinv 1 = 1 := by
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L))
  rw [map_one, ofPowerSeries_ser, Subalgebra.coe_one, IntermediateField.coe_one]

theorem ser_zero : ser L K A j hjinv 0 = 0 := by
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L))
  rw [map_zero, ofPowerSeries_ser, Subalgebra.coe_zero, IntermediateField.coe_zero]

theorem ser_algebraMap (a : A) : ser L K A j hjinv (algebraMap A _ a) = PowerSeries.C (algebraMap A L a) := by
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L))
  rw [ofPowerSeries_ser, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L (↥K) a]
  change algebraMap L (LaurentSeries L) (algebraMap A L a) = _
  rw [HahnSeries.algebraMap_apply']
  rfl

theorem cval_injective_aux {a b : A} (h : algebraMap A L a = algebraMap A L b) : a = b :=
  IsFractionRing.injective A L h

theorem cval_mul (y z : ↥(chartAlgInf A (↥K) j)) :
    cval L K A j hjinv (y * z) = cval L K A j hjinv y * cval L K A j hjinv z := by
  apply cval_injective_aux L A
  rw [map_mul, algebraMap_cval, algebraMap_cval, algebraMap_cval, ser_mul, map_mul]

theorem cval_add (y z : ↥(chartAlgInf A (↥K) j)) :
    cval L K A j hjinv (y + z) = cval L K A j hjinv y + cval L K A j hjinv z := by
  apply cval_injective_aux L A
  rw [map_add, algebraMap_cval, algebraMap_cval, algebraMap_cval, ser_add, map_add]

theorem cval_one : cval L K A j hjinv 1 = 1 := by
  apply cval_injective_aux L A
  rw [map_one, algebraMap_cval, ser_one, map_one]

theorem cval_zero : cval L K A j hjinv 0 = 0 := by
  apply cval_injective_aux L A
  rw [map_zero, algebraMap_cval, ser_zero, map_zero]

theorem cval_algebraMap (a : A) : cval L K A j hjinv (algebraMap A _ a) = a := by
  apply cval_injective_aux L A
  rw [algebraMap_cval, ser_algebraMap, PowerSeries.constantCoeff_C]

noncomputable def φ : ↥(chartAlgInf A (↥K) j) →ₐ[A] A where
  toFun := cval L K A j hjinv
  map_one' := cval_one L K A j hjinv
  map_mul' := cval_mul L K A j hjinv
  map_zero' := cval_zero L K A j hjinv
  map_add' := cval_add L K A j hjinv
  commutes' := cval_algebraMap L K A j hjinv

end Phi

end CuspAsm

open CuspAsm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) := by

  have hjinv : ∃ pj : PowerSeries L, HahnSeries.ofPowerSeries ℤ L pj = ((j⁻¹ : ↥K) : LaurentSeries L) ∧
      PowerSeries.constantCoeff pj = 0 := by
    refine ⟨jInvSeries L, ?_, constantCoeff_jInvSeries L⟩
    rw [IntermediateField.coe_inv, hj, coeffEmb_jq_inv]

  obtain ⟨s⟩ := AlgebraicCurve.TwoChartIntegralModel.nonempty_schemeHomOver_id_toBase_of_algHom A (↥K) j
    (CuspAsm.φ L K A j hjinv)
  obtain ⟨e, he, -, -⟩ := ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo A (↥K) j
  refine ⟨⟨s.1 ≫ e.inv, ?_⟩⟩
  rw [← he, Category.assoc, e.inv_hom_id_assoc]
  exact s.2

end S_ModularCurve_XOneP_nonempty_schemeHomOver_id_modelTo_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_nonempty_schemeHomOver_id_modelTo_twoChartModel_x1_mul (solution)

-- Prove2me | solution 1 for ModularCurve.exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/15ecde59-f441-5d11-add4-169c648ba426

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularCurve AlgebraicCurve Polynomial
open scoped MatrixGroups ModularForm

namespace RegKBody

section Generic

variable {κ F : Type*} [Field κ] [Field F] [Algebra κ F]

theorem ord_pow' (y : Place κ F) (f : F) (n : ℕ) : y.ord (f ^ n) = (n : ℤ) * y.ord f := by
  rw [← zpow_natCast]; exact y.ord_zpow f n

theorem ord_nonneg_of_mem (y : Place κ F) {z : F} (hz : z ∈ y.toValuationSubring) : 0 ≤ y.ord z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hle : y.adicValuation z ≤ 1 := by
    rw [show z = ((⟨z, hz⟩ : y.toValuationSubring) : F) from rfl, y.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have h := (WithZero.log_le_log (y.adicValuation_ne_zero hz0) one_ne_zero).mpr hle
  rw [WithZero.log_one] at h
  simp only [Place.ord]
  omega

theorem mem_of_ord_nonneg (y : Place κ F) {z : F} (h : 0 ≤ y.ord z) : z ∈ y.toValuationSubring := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (↥y.toValuationSubring)
  obtain ⟨u, hu⟩ := y.exists_unit_mul_zpow hz0 hπ
  rw [hu, show y.ord z = ((y.ord z).toNat : ℤ) by omega, zpow_natCast]
  exact mul_mem (u : y.toValuationSubring).2 (pow_mem π.2 _)

theorem ord_nonneg_of_eval₂_eq_zero (y : Place κ F) {g z : F} (P : Polynomial (Polynomial κ)) (hP : P.Monic)
    (hroot : P.eval₂ (eval₂RingHom (algebraMap κ F) g) z = 0) (hg : 0 ≤ y.ord g) : 0 ≤ y.ord z := by
  have hgO : g ∈ y.toValuationSubring := mem_of_ord_nonneg y hg
  set f : Polynomial κ →+* ↥y.toValuationSubring := eval₂RingHom (algebraMap κ _) ⟨g, hgO⟩ with hf_def
  have hf : (algebraMap (↥y.toValuationSubring) F).comp f = eval₂RingHom (algebraMap κ F) g := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hf_def, coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, eval₂_C,
        ← IsScalarTower.algebraMap_apply]
    · rw [RingHom.comp_apply, hf_def, coe_eval₂RingHom, eval₂_X, coe_eval₂RingHom, eval₂_X]
      rfl
  have hint : IsIntegral (↥y.toValuationSubring) z :=
    ⟨P.map f, hP.map f, by rw [Polynomial.eval₂_map, hf]; exact hroot⟩
  obtain ⟨zO, hzO⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥y.toValuationSubring) (K := F)).mp hint
  rw [← hzO]
  exact ord_nonneg_of_mem y zO.2

theorem eval₂_eq_zero_of_injective {E : Type*} [Field E] [Algebra κ E] (ι : F →ₐ[κ] E)
    (hι : Function.Injective ι) {g z : F} {gE zE : E} (hg : ι g = gE) (hz : ι z = zE)
    {P : Polynomial (Polynomial κ)} (h : P.eval₂ (eval₂RingHom (algebraMap κ E) gE) zE = 0) :
    P.eval₂ (eval₂RingHom (algebraMap κ F) g) z = 0 := by
  apply hι
  have hcomp : (ι : F →+* E).comp (eval₂RingHom (algebraMap κ F) g) = eval₂RingHom (algebraMap κ E) gE := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, eval₂_C, RingHom.coe_coe,
        AlgHom.commutes]
    · rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, coe_eval₂RingHom, eval₂_X, RingHom.coe_coe, hg]
  rw [map_zero, show ι (P.eval₂ (eval₂RingHom (algebraMap κ F) g) z) =
      (ι : F →+* E) (P.eval₂ (eval₂RingHom (algebraMap κ F) g) z) from rfl, Polynomial.hom_eval₂, hcomp,
    RingHom.coe_coe, hz]
  exact h

theorem mul_min_ord_le (y : Place κ F) {J T : F} (hJ : J ≠ 0) (k : ℕ)
    {P₁ : Polynomial (Polynomial κ)} (hP₁ : P₁.Monic) (h₁ : P₁.eval₂ (eval₂RingHom (algebraMap κ F) J) T = 0)
    {P₂ : Polynomial (Polynomial κ)} (hP₂ : P₂.Monic)
    (h₂ : P₂.eval₂ (eval₂RingHom (algebraMap κ F) J⁻¹) (T * J⁻¹ ^ k) = 0) :
    (k : ℤ) * min 0 (y.ord J) ≤ y.ord T := by
  rcases le_or_gt 0 (y.ord J) with hJ0 | hJ0
  · rw [min_eq_left hJ0, mul_zero]
    exact ord_nonneg_of_eval₂_eq_zero y P₁ hP₁ h₁ hJ0
  · rw [min_eq_right hJ0.le]
    rcases eq_or_ne T 0 with rfl | hT
    · rw [Place.ord_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hJ0.le
    · have hg : 0 ≤ y.ord J⁻¹ := by rw [y.ord_inv]; omega
      have h := ord_nonneg_of_eval₂_eq_zero y P₂ hP₂ h₂ hg
      rw [y.ord_mul hT (pow_ne_zero _ (inv_ne_zero hJ)), ord_pow', y.ord_inv] at h
      linarith

end Generic

section PIntegers

variable (p : ℕ) [Fact p.Prime]

def Ap : Subring ℚ := (PadicInt.subring p).comap (Rat.castHom ℚ_[p])

theorem mem_Ap_iff {x : ℚ} : x ∈ Ap p ↔ ‖(x : ℚ_[p])‖ ≤ 1 := Iff.rfl

def toPadicInt : ↥(Ap p) →+* ℤ_[p] where
  toFun x := ⟨((x : ℚ) : ℚ_[p]), (mem_Ap_iff p).mp x.2⟩
  map_one' := PadicInt.ext (by simp)
  map_mul' x y := PadicInt.ext (by simp)
  map_zero' := PadicInt.ext (by simp)
  map_add' x y := PadicInt.ext (by simp)

variable (κ : Type*) [Field κ] [CharP κ p]

def red : ↥(Ap p) →+* κ := (ZMod.castHom (dvd_refl p) κ).comp (PadicInt.toZMod.comp (toPadicInt p))

end PIntegers

section Reduction

open ModularCurve.CharPReduction

variable (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p]

theorem laurentMap_int_mem (z : LaurentSeries ℤ) :
    laurentMap (Int.castRingHom ℚ) z ∈ integralCoeffs (Ap p) := fun n => by
  rw [laurentMap_coeff, eq_intCast]
  exact intCast_mem _ _

def ψ : LaurentSeries ℤ →+* ↥(integralCoeffs (Ap p)) :=
  (laurentMap (Int.castRingHom ℚ)).codRestrict _ (laurentMap_int_mem p)

theorem coe_ψ (z : LaurentSeries ℤ) :
    ((ψ p z : ↥(integralCoeffs (Ap p))) : LaurentSeries ℚ) = laurentMap (Int.castRingHom ℚ) z := rfl

theorem coeffRed_ψ (z : LaurentSeries ℤ) :
    coeffRed (Ap p) (red p κ) (ψ p z) = laurentMap (Int.castRingHom κ) z := by
  ext n
  rw [coeffRed_coeff, laurentMap_coeff, eq_intCast]
  have h : (⟨((ψ p z : ↥(integralCoeffs (Ap p))) : LaurentSeries ℚ).coeff n, (ψ p z).2 n⟩ : ↥(Ap p)) =
      ((z.coeff n : ℤ) : ↥(Ap p)) := by
    apply Subtype.ext
    show (laurentMap (Int.castRingHom ℚ) z).coeff n = (((z.coeff n : ℤ) : ↥(Ap p)) : ℚ)
    rw [laurentMap_coeff, eq_intCast]
    simp
  rw [h, map_intCast]

theorem const_mem (a : ↥(Ap p)) : algebraMap ℚ (LaurentSeries ℚ) (a : ℚ) ∈ integralCoeffs (Ap p) := fun n => by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  split_ifs
  · exact a.2
  · exact zero_mem _

def constA : ↥(Ap p) →+* ↥(integralCoeffs (Ap p)) :=
  ((algebraMap ℚ (LaurentSeries ℚ)).comp (Ap p).subtype).codRestrict _ (const_mem p)

theorem coe_constA (a : ↥(Ap p)) :
    ((constA p a : ↥(integralCoeffs (Ap p))) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) (a : ℚ) := rfl

theorem coeffRed_constA (a : ↥(Ap p)) :
    coeffRed (Ap p) (red p κ) (constA p a) = algebraMap κ (LaurentSeries κ) (red p κ a) := by
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  have hval : ((constA p a : ↥(integralCoeffs (Ap p))) : LaurentSeries ℚ).coeff n =
      if n = 0 then (a : ℚ) else 0 := by
    rw [coe_constA, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
    split_ifs <;> rfl
  by_cases hn : n = 0
  · have h : (⟨((constA p a : ↥(integralCoeffs (Ap p))) : LaurentSeries ℚ).coeff n, (constA p a).2 n⟩ :
        ↥(Ap p)) = a := by
      apply Subtype.ext
      show ((constA p a : ↥(integralCoeffs (Ap p))) : LaurentSeries ℚ).coeff n = (a : ℚ)
      rw [hval, if_pos hn]
    rw [h, if_pos hn]
  · have h : (⟨((constA p a : ↥(integralCoeffs (Ap p))) : LaurentSeries ℚ).coeff n, (constA p a).2 n⟩ :
        ↥(Ap p)) = 0 := by
      apply Subtype.ext
      show ((constA p a : ↥(integralCoeffs (Ap p))) : LaurentSeries ℚ).coeff n = ((0 : ↥(Ap p)) : ℚ)
      rw [hval, if_neg hn]
      rfl
    rw [h, map_zero, if_neg hn]

theorem reduce {P : Polynomial (Polynomial ↥(Ap p))} {z t : LaurentSeries ℤ}
    (h0 : P.eval₂ (eval₂RingHom ((algebraMap ℚ (LaurentSeries ℚ)).comp (Ap p).subtype)
      (laurentMap (Int.castRingHom ℚ) z)) (laurentMap (Int.castRingHom ℚ) t) = 0) :
    (P.map (mapRingHom (red p κ))).eval₂ (eval₂RingHom (algebraMap κ (LaurentSeries κ))
      (laurentMap (Int.castRingHom κ) z)) (laurentMap (Int.castRingHom κ) t) = 0 := by
  set φ' : Polynomial ↥(Ap p) →+* ↥(integralCoeffs (Ap p)) := eval₂RingHom (constA p) (ψ p z) with hφ'_def
  have hφ : (integralCoeffs (Ap p)).subtype.comp φ' =
      eval₂RingHom ((algebraMap ℚ (LaurentSeries ℚ)).comp (Ap p).subtype) (laurentMap (Int.castRingHom ℚ) z) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hφ'_def, coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, eval₂_C, Subring.coe_subtype,
        coe_constA, RingHom.comp_apply, Subring.coe_subtype]
    · rw [RingHom.comp_apply, hφ'_def, coe_eval₂RingHom, eval₂_X, coe_eval₂RingHom, eval₂_X, Subring.coe_subtype,
        coe_ψ]
  rw [← hφ, show laurentMap (Int.castRingHom ℚ) t = (integralCoeffs (Ap p)).subtype (ψ p t) from rfl,
    ← Polynomial.hom_eval₂] at h0
  have h1 : P.eval₂ φ' (ψ p t) = 0 := Subtype.ext h0
  have h2 := congrArg (coeffRed (Ap p) (red p κ)) h1
  rw [Polynomial.hom_eval₂, map_zero, coeffRed_ψ] at h2
  have hρφ : (coeffRed (Ap p) (red p κ)).comp φ' =
      (eval₂RingHom (algebraMap κ (LaurentSeries κ)) (laurentMap (Int.castRingHom κ) z)).comp
        (mapRingHom (red p κ)) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hφ'_def, coe_eval₂RingHom, eval₂_C, coeffRed_constA, RingHom.comp_apply,
        coe_mapRingHom, map_C, coe_eval₂RingHom, eval₂_C]
    · rw [RingHom.comp_apply, hφ'_def, coe_eval₂RingHom, eval₂_X, coeffRed_ψ, RingHom.comp_apply,
        coe_mapRingHom, map_X, coe_eval₂RingHom, eval₂_X]
  rw [hρφ, ← Polynomial.eval₂_map] at h2
  exact h2

end Reduction

section IntModels

variable (K : Type*) [Field K]

theorem laurentMap_ofPowerSeries_int (q : PowerSeries ℤ) :
    laurentMap (Int.castRingHom K) (HahnSeries.ofPowerSeries ℤ ℤ q) = intSeriesC K q := by
  rw [laurentMap_ofPowerSeries]; rfl

theorem intSeriesC_pow (q : PowerSeries ℤ) (n : ℕ) : intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  induction n with
  | zero => simp [intSeriesC]
  | succ n ih => rw [pow_succ, intSeriesC_mul, ih, pow_succ]

theorem intSeriesC_X : intSeriesC K PowerSeries.X = HahnSeries.single 1 1 := by
  rw [intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem laurentMap_jqInt_eq_jqModC : laurentMap (Int.castRingHom K) jqInt = jqModC K := by
  rw [jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]
  rfl

def deltaInvInt : LaurentSeries ℤ :=
  HahnSeries.single (-1) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

theorem intSeriesC_delta_mul_deltaInv :
    intSeriesC K (PowerSeries.X * dedekindEtaUnit) * laurentMap (Int.castRingHom K) deltaInvInt = 1 := by
  rw [deltaInvInt, map_mul, laurentMap_single, map_one, laurentMap_ofPowerSeries_int, intSeriesC_mul,
    intSeriesC_X]
  calc HahnSeries.single (1 : ℤ) (1 : K) * intSeriesC K dedekindEtaUnit *
        (HahnSeries.single (-1 : ℤ) (1 : K) * intSeriesC K dedekindEtaUnitInv)
      = (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.single (-1 : ℤ) (1 : K)) *
          (intSeriesC K dedekindEtaUnit * intSeriesC K dedekindEtaUnitInv) := by ring
    _ = 1 := by
        rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, ← intSeriesC_mul, dedekindEtaUnit_mul_inv,
          intSeriesC_one, mul_one]
        rfl

theorem intSeriesC_delta_ne_zero : intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 :=
  left_ne_zero_of_mul_eq_one (intSeriesC_delta_mul_deltaInv K)

def TInt (pg : PowerSeries ℤ) (k : ℕ) : LaurentSeries ℤ :=
  HahnSeries.ofPowerSeries ℤ ℤ (pg ^ 12) * deltaInvInt ^ k

theorem laurentMap_TInt (pg : PowerSeries ℤ) (k : ℕ) :
    laurentMap (Int.castRingHom K) (TInt pg k) =
      intSeriesC K (pg ^ 12) / intSeriesC K ((PowerSeries.X * dedekindEtaUnit) ^ k) := by
  have h := intSeriesC_delta_mul_deltaInv K
  rw [eq_div_iff (by rw [intSeriesC_pow]; exact pow_ne_zero _ (intSeriesC_delta_ne_zero K)), TInt, map_mul,
    laurentMap_ofPowerSeries_int, map_pow (laurentMap (Int.castRingHom K)) deltaInvInt k, intSeriesC_pow,
    intSeriesC_pow, mul_assoc, ← mul_pow, mul_comm (laurentMap _ deltaInvInt), h, one_pow, mul_one]

def jNumInv : PowerSeries ℤ := jNum.invOfUnit 1

theorem jNum_mul_jNumInv : jNum * jNumInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNum]; rfl)

def jqInvInt : LaurentSeries ℤ := HahnSeries.single 1 1 * HahnSeries.ofPowerSeries ℤ ℤ jNumInv

theorem jqModC_mul_laurentMap_jqInvInt : jqModC K * laurentMap (Int.castRingHom K) jqInvInt = 1 := by
  rw [← laurentMap_jqInt_eq_jqModC, ← map_mul, jqInt, jqInvInt, mul_mul_mul_comm, HahnSeries.single_mul_single,
    neg_add_cancel, mul_one, show HahnSeries.single (0 : ℤ) (1 : ℤ) = 1 from rfl, one_mul, ← map_mul,
    jNum_mul_jNumInv, map_one, map_one]

theorem laurentMap_jqInvInt : laurentMap (Int.castRingHom K) jqInvInt = (jqModC K)⁻¹ :=
  eq_inv_of_mul_eq_one_right (jqModC_mul_laurentMap_jqInvInt K)

def E4Inv : PowerSeries ℤ := eisenstein4.invOfUnit 1

theorem eisenstein4_mul_E4Inv : eisenstein4 * E4Inv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_eisenstein4]; rfl)

theorem intSeriesC_eisenstein4_mul : intSeriesC K eisenstein4 * intSeriesC K E4Inv = 1 := by
  rw [← intSeriesC_mul, eisenstein4_mul_E4Inv, intSeriesC_one]

theorem intSeriesC_eisenstein4_ne_zero : intSeriesC K eisenstein4 ≠ 0 :=
  left_ne_zero_of_mul_eq_one (intSeriesC_eisenstein4_mul K)

def TInfInt (pg : PowerSeries ℤ) (k : ℕ) : LaurentSeries ℤ :=
  HahnSeries.ofPowerSeries ℤ ℤ (pg ^ 12) * HahnSeries.ofPowerSeries ℤ ℤ E4Inv ^ (3 * k)

theorem laurentMap_TInfInt (pg : PowerSeries ℤ) (k : ℕ) :
    laurentMap (Int.castRingHom K) (TInfInt pg k) = intSeriesC K (pg ^ 12) / intSeriesC K (eisenstein4 ^ (3 * k)) := by
  have h := intSeriesC_eisenstein4_mul K
  rw [eq_div_iff (by rw [intSeriesC_pow]; exact pow_ne_zero _ (intSeriesC_eisenstein4_ne_zero K)), TInfInt, map_mul,
    laurentMap_ofPowerSeries_int, map_pow (laurentMap (Int.castRingHom K)) (HahnSeries.ofPowerSeries ℤ ℤ E4Inv) (3 * k),
    laurentMap_ofPowerSeries_int, intSeriesC_pow, intSeriesC_pow, mul_assoc, ← mul_pow,
    mul_comm (intSeriesC K E4Inv), h, one_pow, mul_one]

theorem jqModC_mul_delta : jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K eisenstein4 ^ 3 := by
  have hj : jqModC K = HahnSeries.single (-1 : ℤ) (1 : K) * intSeriesC K jNum := rfl
  calc jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit)
      = (HahnSeries.single (-1 : ℤ) (1 : K) * HahnSeries.single (1 : ℤ) (1 : K)) *
          (intSeriesC K jNum * intSeriesC K dedekindEtaUnit) := by
        rw [hj, intSeriesC_mul, intSeriesC_X]; ring
    _ = intSeriesC K (jNum * dedekindEtaUnit) := by
        rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, ← intSeriesC_mul]
        rw [show (HahnSeries.single (0 : ℤ) (1 : K)) = 1 from rfl, one_mul]
    _ = intSeriesC K eisenstein4 ^ 3 := by
        rw [jNum, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, intSeriesC_pow]

theorem div_delta_pow_mul_jqModC_inv_pow (pg : PowerSeries ℤ) (k : ℕ) :
    intSeriesC K (pg ^ 12) / intSeriesC K ((PowerSeries.X * dedekindEtaUnit) ^ k) * (jqModC K)⁻¹ ^ k =
      intSeriesC K (pg ^ 12) / intSeriesC K (eisenstein4 ^ (3 * k)) := by
  have hD := intSeriesC_delta_ne_zero K
  have hE := intSeriesC_eisenstein4_ne_zero K
  have hjinv : (jqModC K)⁻¹ = intSeriesC K (PowerSeries.X * dedekindEtaUnit) * (intSeriesC K eisenstein4 ^ 3)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, jqModC_mul_delta, mul_inv_cancel₀ (pow_ne_zero _ hE)]
  simp only [intSeriesC_pow]
  rw [hjinv, mul_pow (intSeriesC K (PowerSeries.X * dedekindEtaUnit)) ((intSeriesC K eisenstein4 ^ 3)⁻¹) k,
    inv_pow, ← pow_mul, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
    ← mul_assoc ((intSeriesC K (PowerSeries.X * dedekindEtaUnit) ^ k)⁻¹),
    inv_mul_cancel₀ (pow_ne_zero _ hD), one_mul]

end IntModels

section Forms

open ModularForm UpperHalfPlane

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods {Δ' : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ') :
    (1 : ℝ) ∈ (Δ' : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

variable (M : ℕ)

theorem isIntegralQExp_pow {w : ℤ} (f : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w)
    (pf : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (n : ℕ) : IsIntegralQExp (f.pow n) (pf ^ n) := by
  unfold IsIntegralQExp at hf ⊢
  rw [map_pow, hf, ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods (T_mem_Gamma1 M))]

theorem isIntegralQExp_mcast {a b : ℤ} (hab : a = b)
    (f : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) a) (pf : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) : IsIntegralQExp (ModularForm.mcast hab f) pf := by
  unfold IsIntegralQExp at hf ⊢
  rw [coe_mcast]; exact hf

noncomputable def deltaForm : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ _) (ModularFormClass.modularForm (CuspForm.discriminant))

theorem isIntegralQExp_deltaForm : IsIntegralQExp (deltaForm M) (PowerSeries.X * dedekindEtaUnit) := by
  unfold IsIntegralQExp
  exact (ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit).symm

end Forms

theorem solution_of_chartInt
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]
    (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (k : ℕ) (g : ModularForm (Gamma1 M) (k : ℤ)) (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC κ pg ≠ 0)
    (H_fin : (Polynomial.eval₂RingHom ((algebraMap ℚ (LaurentSeries ℚ)).comp (Ap p).subtype) ModularCurve.jq).IsIntegralElem
      (intSeriesC ℚ (pg ^ 12) / intSeriesC ℚ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k)))
    (H_inf : (Polynomial.eval₂RingHom ((algebraMap ℚ (LaurentSeries ℚ)).comp (Ap p).subtype) ModularCurve.jq⁻¹).IsIntegralElem
      (intSeriesC ℚ (pg ^ 12) / intSeriesC ℚ (ModularCurve.eisenstein4 ^ (3 * k)))) :
    ∃ T : ↥(ModularCurve.x1FunctionFieldC κ M),
      (T : LaurentSeries κ) =
        intSeriesC κ (pg ^ 12) / intSeriesC κ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k) ∧
      ∀ y : Place κ ↥(ModularCurve.x1FunctionFieldC κ M), (k : ℤ) * min 0 (y.ord J) ≤ y.ord T := by

  have hwt : ((12 : ℕ) : ℤ) * (k : ℤ) = 12 * (k : ℤ) := by norm_num
  have hwt' : ((k : ℕ) : ℤ) * 12 = 12 * (k : ℤ) := by ring
  have hG : IsIntegralQExp (ModularForm.mcast hwt (g.pow 12)) (pg ^ 12) :=
    isIntegralQExp_mcast M hwt _ _ (isIntegralQExp_pow M g pg hg 12)
  have hD : IsIntegralQExp (ModularForm.mcast hwt' ((deltaForm M).pow k)) ((PowerSeries.X * dedekindEtaUnit) ^ k) :=
    isIntegralQExp_mcast M hwt' _ _ (isIntegralQExp_pow M (deltaForm M) _ (isIntegralQExp_deltaForm M) k)
  have hDk : intSeriesC κ ((PowerSeries.X * dedekindEtaUnit) ^ k) ≠ 0 := by
    rw [intSeriesC_pow]; exact pow_ne_zero _ (intSeriesC_delta_ne_zero κ)
  have hTmem : intSeriesC κ (pg ^ 12) / intSeriesC κ ((PowerSeries.X * dedekindEtaUnit) ^ k) ∈
      ModularCurve.x1FunctionFieldC κ M := by
    rw [x1FunctionFieldC]
    exact div_mem_qExpFunctionFieldC _ _ hG hD hDk
  refine ⟨⟨_, hTmem⟩, rfl, fun y => ?_⟩

  have hj : jqModC κ ≠ 0 := left_ne_zero_of_mul_eq_one (jqModC_mul_laurentMap_jqInvInt κ)
  have hJ0 : J ≠ 0 := fun h => hj (by rw [← hJ, h]; rfl)
  let ι : ↥(ModularCurve.x1FunctionFieldC κ M) →ₐ[κ] LaurentSeries κ := (ModularCurve.x1FunctionFieldC κ M).val
  have hι : Function.Injective ι := (ModularCurve.x1FunctionFieldC κ M).val.injective

  obtain ⟨P₁, hP₁m, hP₁⟩ := H_fin
  rw [← laurentMap_jqInt, ← laurentMap_TInt] at hP₁
  have r₁ := reduce p κ hP₁
  rw [laurentMap_jqInt_eq_jqModC, laurentMap_TInt, ← hJ] at r₁
  have h₁ := eval₂_eq_zero_of_injective ι hι (g := J) (z := ⟨_, hTmem⟩) rfl rfl r₁

  obtain ⟨P₂, hP₂m, hP₂⟩ := H_inf
  rw [← jqModC_rat, ← laurentMap_jqInvInt, ← laurentMap_TInfInt] at hP₂
  have r₂ := reduce p κ hP₂
  rw [laurentMap_jqInvInt, laurentMap_TInfInt, ← div_delta_pow_mul_jqModC_inv_pow κ pg k, ← hJ] at r₂
  have h₂ := eval₂_eq_zero_of_injective ι hι (g := J⁻¹) (z := ⟨_, hTmem⟩ * J⁻¹ ^ k)
    (by rw [map_inv₀]; rfl) (by rw [map_mul, map_pow, map_inv₀]; rfl) r₂

  exact mul_min_ord_le y hJ0 k (hP₁m.map _) h₁ (hP₂m.map _) h₂

theorem closure_inv_le_Ap (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) :
    Subring.closure ({((M : ℚ))⁻¹} : Set ℚ) ≤ Ap p := by
  have hp : p.Prime := Fact.out
  rw [Subring.closure_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_Ap_iff, Rat.cast_inv, Rat.cast_natCast,
    norm_inv, Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM), inv_one]

theorem isIntegralElem_of_le {S T : Subring ℚ} (hST : S ≤ T) {x y : LaurentSeries ℚ}
    (h : (Polynomial.eval₂RingHom ((algebraMap ℚ (LaurentSeries ℚ)).comp S.subtype) x).IsIntegralElem y) :
    (Polynomial.eval₂RingHom ((algebraMap ℚ (LaurentSeries ℚ)).comp T.subtype) x).IsIntegralElem y := by
  obtain ⟨P, hPm, hP0⟩ := h
  refine ⟨P.map (Polynomial.mapRingHom (Subring.inclusion hST)), hPm.map _, ?_⟩
  have hcomp : (Polynomial.eval₂RingHom ((algebraMap ℚ (LaurentSeries ℚ)).comp T.subtype) x).comp
      (Polynomial.mapRingHom (Subring.inclusion hST)) =
      Polynomial.eval₂RingHom ((algebraMap ℚ (LaurentSeries ℚ)).comp S.subtype) x := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [Polynomial.eval₂_map, hcomp]
  exact hP0

end RegKBody

open RegKBody in
theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]
    (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (k : ℕ) (g : ModularForm (Gamma1 M) (k : ℤ)) (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC κ pg ≠ 0) :
    ∃ T : ↥(ModularCurve.x1FunctionFieldC κ M),
      (T : LaurentSeries κ) =
        intSeriesC κ (pg ^ 12) / intSeriesC κ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k) ∧
      ∀ y : Place κ ↥(ModularCurve.x1FunctionFieldC κ M), (k : ℤ) * min 0 (y.ord J) ≤ y.ord T :=
  solution_of_chartInt p κ M hpM J hJ k g pg hg hg0
    (isIntegralElem_of_le (closure_inv_le_Ap p M hpM)
      (ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1 M k g pg hg).1)
    (isIntegralElem_of_le (closure_inv_le_Ap p M hpM)
      (ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1 M k g pg hg).2)

end
end S_ModularCurve_exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC (solution)

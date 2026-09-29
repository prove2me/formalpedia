-- Prove2me | solution 1 for ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1d90a969-4dd9-5782-a1ca-ff9240953c7c

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_slot_algHom_modularFunctionFieldFullC_of_ord_neg
import Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist
import Theorems.Thm_ModularCurve_coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_ModularCurve_order_qExpand
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd HahnSeries.ramScale_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve IntermediateField HahnSeries CongruenceSubgroup CohCarrier AlgebraicCurve
open scoped MatrixGroups ModularForm

namespace XHCuspLoc

section Laurent

variable {K : Type*} [Field K]

theorem order_qTwist (v : Kˣ) (f : LaurentSeries K) : (qTwist v f).order = f.order := by
  by_cases hf : f = 0
  · rw [hf, map_zero]
  have h1 : ∀ (u : Kˣ) (g : LaurentSeries K), g ≠ 0 → g.order ≤ (qTwist u g).order := by
    intro u g hg
    have hne : qTwist u g ≠ 0 := (map_ne_zero_iff _ (qTwist_injective u)).mpr hg
    refine HahnSeries.order_le_of_coeff_ne_zero ?_
    intro h0
    apply hne
    apply HahnSeries.coeff_order_eq_zero.mp
    rw [qTwist_coeff, h0, mul_zero]
  refine le_antisymm ?_ (h1 v f hf)
  have h2 := h1 v⁻¹ (qTwist v f) ((map_ne_zero_iff _ (qTwist_injective v)).mpr hf)
  rwa [qTwist_qTwist, inv_mul_cancel, qTwist_one_apply] at h2

variable (K) in

def qTwistAlg (v : Kˣ) : LaurentSeries K →ₐ[K] LaurentSeries K :=
  { qTwist v with
    commutes' := fun c => by
      show qTwist v (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
      rw [algebraMap_laurentSeries_eq_single, qTwist_single, zpow_zero, Units.val_one, one_mul] }

@[scoped simp] theorem qTwistAlg_apply (v : Kˣ) (f : LaurentSeries K) : qTwistAlg K v f = qTwist v f := rfl

end Laurent

section SlotArith

open Matrix.SpecialLinearGroup ModularGroup

variable (M : ℕ)

def IsSlotData (g : SL(2, ℤ)) (a : ℕ) (b : ℤ) : Prop :=
  (a : ℤ) ∣ g 1 0 ∧ (a : ℤ) ∣ (M : ℤ) ∧ g 1 0 * b ≡ g 1 1 * a [ZMOD M]

variable {M}

theorem isCoprime_row (g : SL(2, ℤ)) : IsCoprime (g 1 0) (g 1 1) := by
  have h := Matrix.det_fin_two g.1
  rw [g.det_coe] at h
  exact ⟨-(g 0 1), g 0 0, by linear_combination -h⟩

theorem IsSlotData.natCast_eq_gcd {g : SL(2, ℤ)} {a : ℕ} {b : ℤ} (h : IsSlotData M g a b) :
    (a : ℤ) = Int.gcd (g 1 0) M := by
  obtain ⟨hac, haM, hb⟩ := h
  have h1 : (a : ℤ) ∣ (Int.gcd (g 1 0) M : ℤ) := Int.natCast_dvd_natCast.mpr (Int.dvd_gcd hac haM)
  have h2 : (Int.gcd (g 1 0) M : ℤ) ∣ (a : ℤ) := by
    have hδc : (Int.gcd (g 1 0) M : ℤ) ∣ g 1 0 := Int.gcd_dvd_left _ _
    have hδM : (Int.gcd (g 1 0) M : ℤ) ∣ (M : ℤ) := Int.gcd_dvd_right _ _
    have hδda : (Int.gcd (g 1 0) M : ℤ) ∣ g 1 1 * a := by
      have h3 : (M : ℤ) ∣ g 1 1 * a - g 1 0 * b := hb.dvd
      have h4 : (Int.gcd (g 1 0) M : ℤ) ∣ g 1 1 * a - g 1 0 * b := hδM.trans h3
      have h5 : (Int.gcd (g 1 0) M : ℤ) ∣ g 1 0 * b := hδc.mul_right _
      simpa using h4.add h5
    have hcop : IsCoprime (Int.gcd (g 1 0) M : ℤ) (g 1 1) :=
      (isCoprime_row g).of_isCoprime_of_dvd_left hδc
    exact hcop.dvd_of_dvd_mul_left hδda
  exact Int.dvd_antisymm (by positivity) (by positivity) h1 h2

theorem IsSlotData.gcd_pos {g : SL(2, ℤ)} {a : ℕ} {b : ℤ} [NeZero a] (h : IsSlotData M g a b) :
    0 < Int.gcd (g 1 0) M := by
  have := h.natCast_eq_gcd
  have ha : (0 : ℤ) < a := by exact_mod_cast NeZero.pos a
  omega

theorem IsSlotData.gamma0_mul {g : SL(2, ℤ)} {a : ℕ} {b : ℤ} (h : IsSlotData M g a b)
    (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ Gamma0 M) : IsSlotData M (γ₀ * g) a b := by
  obtain ⟨hac, haM, hb⟩ := h
  have hM0 : (M : ℤ) ∣ γ₀ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ₀)
  have e10 : (γ₀ * g) 1 0 = γ₀ 1 0 * g 0 0 + γ₀ 1 1 * g 1 0 := by
    simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (γ₀ * g) 1 1 = γ₀ 1 0 * g 0 1 + γ₀ 1 1 * g 1 1 := by
    simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, haM, ?_⟩
  · rw [e10]
    exact ((haM.trans hM0).mul_right _).add (hac.mul_left _)
  · rw [e10, e11, Int.modEq_iff_dvd]
    obtain ⟨t, ht⟩ := hb.dvd
    obtain ⟨s, hs⟩ := hM0
    exact ⟨s * (g 0 1 * a - g 0 0 * b) + γ₀ 1 1 * t, by linear_combination (γ₀ 1 1) * ht +
      (g 0 1 * (a : ℤ) - g 0 0 * b) * hs⟩

theorem IsSlotData.mul_T_zpow {g : SL(2, ℤ)} {a : ℕ} {b : ℤ} (h : IsSlotData M g a b) (k : ℤ) :
    IsSlotData M (g * T ^ k) a (b + k * a) := by
  obtain ⟨hac, haM, hb⟩ := h
  have e10 : (g * T ^ k) 1 0 = g 1 0 := by
    simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_T_zpow]
  have e11 : (g * T ^ k) 1 1 = g 1 0 * k + g 1 1 := by
    simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_T_zpow]
  refine ⟨by rw [e10]; exact hac, haM, ?_⟩
  rw [e10, e11, Int.modEq_iff_dvd]
  obtain ⟨t, ht⟩ := hb.dvd
  exact ⟨t, by linear_combination ht⟩

theorem IsSlotData.neg {g : SL(2, ℤ)} {a : ℕ} {b : ℤ} (h : IsSlotData M g a b) :
    IsSlotData M (-g) a b := by
  obtain ⟨hac, haM, hb⟩ := h
  have e10 : (-g) 1 0 = -(g 1 0) := by simp [coe_neg]
  have e11 : (-g) 1 1 = -(g 1 1) := by simp [coe_neg]
  refine ⟨by rw [e10]; exact hac.neg_right, haM, ?_⟩
  rw [e10, e11, neg_mul, neg_mul]
  exact hb.neg

theorem IsSlotData.unique {g : SL(2, ℤ)} {a a' : ℕ} {b b' : ℤ} [NeZero a]
    (h : IsSlotData M g a b) (h' : IsSlotData M g a' b') :
    a = a' ∧ ((M / a : ℕ) : ℤ) ∣ b' - b := by
  have haa : a = a' := by
    have := h.natCast_eq_gcd.trans h'.natCast_eq_gcd.symm
    exact_mod_cast this
  subst haa
  refine ⟨rfl, ?_⟩
  obtain ⟨hac, haM, hb⟩ := h
  obtain ⟨-, -, hb'⟩ := h'
  have hpos : 0 < Int.gcd (g 1 0) M := IsSlotData.gcd_pos (M := M) ⟨hac, haM, hb⟩
  have hgcd : (a : ℤ) = Int.gcd (g 1 0) M := IsSlotData.natCast_eq_gcd (M := M) ⟨hac, haM, hb⟩

  have hM : (M : ℤ) ∣ g 1 0 * (b' - b) := by
    have h1 : (M : ℤ) ∣ g 1 1 * a - g 1 0 * b := hb.dvd
    have h2 : (M : ℤ) ∣ g 1 1 * a - g 1 0 * b' := hb'.dvd
    have := h1.sub h2
    have e : g 1 1 * (a : ℤ) - g 1 0 * b - (g 1 1 * a - g 1 0 * b') = g 1 0 * (b' - b) := by ring
    rwa [e] at this

  set c' : ℤ := g 1 0 / (a : ℤ) with hc'
  set M' : ℤ := (M : ℤ) / (a : ℤ) with hM'
  have hcc : g 1 0 = (a : ℤ) * c' := (Int.mul_ediv_cancel' hac).symm
  have hMM : (M : ℤ) = (a : ℤ) * M' := (Int.mul_ediv_cancel' haM).symm
  have hcop : Int.gcd c' M' = 1 := by
    have := Int.gcd_div_gcd_div_gcd hpos
    rwa [← hgcd] at this
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne a
  have hM'dvd : M' ∣ c' * (b' - b) := by
    rw [hcc, hMM, mul_assoc] at hM
    exact (mul_dvd_mul_iff_left ha0).mp hM
  have hcop' : IsCoprime M' c' := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hcop
  have hres : M' ∣ b' - b := hcop'.dvd_of_dvd_mul_left hM'dvd
  have hcast : ((M / a : ℕ) : ℤ) = M' := by rw [hM', Int.natCast_div]
  rwa [hcast]

theorem exists_eq_T_zpow_or_of_mem {t : SL(2, ℤ)}
    (ht : t ∈ Subgroup.zpowers T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    ∃ k : ℤ, t = T ^ k ∨ t = -(T ^ k) := by

  let C' : Subgroup SL(2, ℤ) :=
    { carrier := {t | ∃ k : ℤ, t = T ^ k ∨ t = -(T ^ k)}
      mul_mem' := by
        rintro x y ⟨k, hk⟩ ⟨m, hm⟩
        refine ⟨k + m, ?_⟩
        rcases hk with rfl | rfl <;> rcases hm with rfl | rfl
        · left; rw [zpow_add]
        · right; rw [mul_neg, zpow_add]
        · right; rw [neg_mul, zpow_add]
        · left; rw [neg_mul_neg, zpow_add]
      one_mem' := ⟨0, Or.inl (zpow_zero _).symm⟩
      inv_mem' := by
        rintro x ⟨k, hk⟩
        refine ⟨-k, ?_⟩
        rcases hk with rfl | rfl
        · left; rw [zpow_neg]
        · right; rw [inv_neg, zpow_neg] }
  have hle : Subgroup.zpowers T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ C' := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨1, Or.inl (zpow_one _).symm⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨0, Or.inr (by rw [zpow_zero])⟩
  exact hle ht

theorem IsSlotData.transport {g g' : SL(2, ℤ)} {a : ℕ} {b : ℤ} (h : IsSlotData M g a b)
    (hgg' : DoubleCoset.mk (Gamma0 M) (Subgroup.zpowers T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) g =
      DoubleCoset.mk (Gamma0 M) (Subgroup.zpowers T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) g') :
    ∃ k : ℤ, IsSlotData M g' a (b + k * a) := by
  rw [DoubleCoset.eq] at hgg'
  obtain ⟨γ₀, hγ₀, t, ht, rfl⟩ := hgg'
  obtain ⟨k, hk⟩ := exists_eq_T_zpow_or_of_mem ht
  refine ⟨k, ?_⟩
  rcases hk with rfl | rfl
  · exact (h.gamma0_mul γ₀ hγ₀).mul_T_zpow k
  · rw [mul_neg]
    exact ((h.gamma0_mul γ₀ hγ₀).mul_T_zpow k).neg

theorem IsSlotData.dvd_sub_of_mk_eq {g g' : SL(2, ℤ)} {a a' : ℕ} {b b' : ℤ} [NeZero a]
    (h : IsSlotData M g a b) (h' : IsSlotData M g' a' b')
    (hgg' : DoubleCoset.mk (Gamma0 M) (Subgroup.zpowers T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) g =
      DoubleCoset.mk (Gamma0 M) (Subgroup.zpowers T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) g') :
    a = a' ∧ ((Nat.gcd a (M / a) : ℕ) : ℤ) ∣ b' - b := by
  obtain ⟨k, hk⟩ := h.transport hgg'
  obtain ⟨haa, hdvd⟩ := hk.unique h'
  refine ⟨haa, ?_⟩
  have h1 : ((Nat.gcd a (M / a) : ℕ) : ℤ) ∣ ((M / a : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  have h2 : ((Nat.gcd a (M / a) : ℕ) : ℤ) ∣ (a : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have h3 : ((Nat.gcd a (M / a) : ℕ) : ℤ) ∣ b' - (b + k * a) := h1.trans hdvd
  have h4 : ((Nat.gcd a (M / a) : ℕ) : ℤ) ∣ k * a := h2.mul_left k
  have := h3.add h4
  have e : b' - (b + k * (a : ℤ)) + k * a = b' - b := by ring
  rwa [e] at this

theorem exists_isSlotData (a : ℕ) [NeZero a] (haM : a ∣ M) (b : ℕ)
    (hb : Nat.Coprime b (Nat.gcd a (M / a))) :
    ∃ g : SL(2, ℤ), IsSlotData M g a b := by
  set g₀ : ℕ := Nat.gcd a (M / a) with hg₀
  have hg₀a : g₀ ∣ a := Nat.gcd_dvd_left _ _

  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hg₀a (ZMod.unitOfCoprime b hb)
  set x : ℕ := (u : ZMod a).val with hx
  have hxu : ((x : ℕ) : ZMod a) = (u : ZMod a) := ZMod.natCast_zmod_val _
  have hxunit : IsUnit ((x : ℕ) : ZMod a) := by rw [hxu]; exact Units.isUnit u
  have hxcop : Nat.Coprime x a := (ZMod.isUnit_iff_coprime x a).mp hxunit
  have hxb : ((x : ℕ) : ZMod g₀) = ((b : ℕ) : ZMod g₀) := by
    have h1 : ((ZMod.unitsMap hg₀a u : (ZMod g₀)ˣ) : ZMod g₀) = ((b : ℕ) : ZMod g₀) := by
      rw [hu]; exact ZMod.coe_unitOfCoprime b hb
    rw [← h1, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ← hxu, map_natCast]
  have hxbmod : (g₀ : ℤ) ∣ (x : ℤ) - (b : ℤ) := by
    have := (ZMod.natCast_eq_natCast_iff' x b g₀).mp hxb
    have h2 : (x : ℤ) % (g₀ : ℤ) = (b : ℤ) % (g₀ : ℤ) := by exact_mod_cast this
    exact Int.ModEq.dvd h2.symm
  obtain ⟨s, hs⟩ := hxbmod

  have hbez : (g₀ : ℤ) = (a : ℤ) * Nat.gcdA a (M / a) + ((M / a : ℕ) : ℤ) * Nat.gcdB a (M / a) :=
    Nat.gcd_eq_gcd_ab a (M / a)
  set d : ℤ := (x : ℤ) - (a : ℤ) * (Nat.gcdA a (M / a) * s) with hd
  have hd' : d = (b : ℤ) + ((M / a : ℕ) : ℤ) * (Nat.gcdB a (M / a) * s) := by
    rw [hd]; linear_combination hs + s * hbez
  have hcop : IsCoprime (a : ℤ) d := by
    have h1 : IsCoprime (x : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.mpr hxcop
    have h2 : IsCoprime ((x : ℤ) + (a : ℤ) * (-(Nat.gcdA a (M / a) * s))) (a : ℤ) :=
      h1.add_mul_left_left _
    have e : (x : ℤ) + (a : ℤ) * (-(Nat.gcdA a (M / a) * s)) = d := by rw [hd]; ring
    rw [e] at h2
    exact h2.symm
  obtain ⟨p, r, hpr⟩ := hcop

  refine ⟨⟨!![r, -p; (a : ℤ), d], by rw [Matrix.det_fin_two_of]; linear_combination hpr⟩, ?_, ?_, ?_⟩
  · show (a : ℤ) ∣ (!![r, -p; (a : ℤ), d] : Matrix (Fin 2) (Fin 2) ℤ) 1 0
    simp
  · exact Int.natCast_dvd_natCast.mpr haM
  · show (!![r, -p; (a : ℤ), d] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (b : ℤ) ≡
      (!![r, -p; (a : ℤ), d] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * a [ZMOD M]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [Int.modEq_iff_dvd, hd']
    have hMa : (M : ℤ) = (a : ℤ) * ((M / a : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' haM).symm
    exact ⟨Nat.gcdB a (M / a) * s, by rw [hMa]; ring⟩

end SlotArith

section Diamond

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {K : Type*} [Field K]

variable (M H K) in

abbrev FbK : Type _ := ↥(qExpFunctionFieldC K (GammaH M H))

variable (M K) in

abbrev FullK : Type _ := ↥(modularFunctionFieldFullC K M)

variable (M K) in

def jFull : FullK M K := ⟨jqModC K, jqModC_mem_full K M⟩

variable (M K) in

def jNFull : FullK M K := ⟨jqNModC K M, jqModCd_mem_full K M (dvd_refl M)⟩

@[scoped simp] theorem coe_jFull : ((jFull M K : FullK M K) : LaurentSeries K) = jqModC K := rfl
@[scoped simp] theorem coe_jNFull : ((jNFull M K : FullK M K) : LaurentSeries K) = jqNModC K M := rfl

variable {ρ : Gamma0 M →* (FbK M H K ≃ₐ[K] FbK M H K)}

theorem rho_eq_one_of_mem (hρ : IsDiamondPullbackModL K M H ρ) (γ : Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ GammaH M H) : ρ γ = 1 := by

  let E : IntermediateField K (FbK M H K) :=
    { carrier := {y | ρ γ y = y}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
      one_mem' := map_one _
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
      zero_mem' := map_zero _
      algebraMap_mem' := fun c => (ρ γ).commutes c
      inv_mem' := fun x hx => by
        simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx] }
  have hE : ∀ z : FbK M H K, z ∈ E ↔ ρ γ z = z := fun z => Iff.rfl
  have hle : qExpFunctionFieldC K (GammaH M H) ≤ IntermediateField.lift E := by
    change IntermediateField.adjoin K (intFormRatiosC K (GammaH M H)) ≤ _
    refine adjoin_le_iff.mpr ?_
    rintro y ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hmem : intSeriesC K pf / intSeriesC K pg ∈ qExpFunctionFieldC K (GammaH M H) :=
      div_mem_qExpFunctionFieldC f g hf hg hg0
    have hfs : (⇑f : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
      rw [ModularForm.SL_slash]
      exact (SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)).symm
    have hgs : (⇑g : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
      rw [ModularForm.SL_slash]
      exact (SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)).symm
    have key := hρ γ k f g f g pf pg pf pg hf hg hf hg hfs hgs hg0 ⟨_, hmem⟩ rfl
    have hfix : ρ γ ⟨_, hmem⟩ = ⟨_, hmem⟩ := Subtype.ext key
    exact (mem_lift (⟨_, hmem⟩ : FbK M H K)).mpr ((hE _).mpr hfix)
  refine AlgEquiv.ext fun x => ?_
  have := hle x.2
  rw [AlgEquiv.one_apply]
  exact (hE x).mp ((mem_lift x).mp this)

theorem rho_comm (hρ : IsDiamondPullbackModL K M H ρ) (γ γ' : Gamma0 M) :
    ρ γ * ρ γ' = ρ γ' * ρ γ := by
  set c : Gamma0 M := γ⁻¹ * γ'⁻¹ * γ * γ' with hc
  have hcH : (c : SL(2, ℤ)) ∈ GammaH M H := by
    rw [mem_GammaH_iff]
    refine ⟨c.2, ?_⟩
    have hu : gamma0Units M ⟨(c : SL(2, ℤ)), c.2⟩ = gamma0Units M c := rfl
    rw [hu, hc, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (gamma0Units M γ)⁻¹,
      inv_mul_cancel_right, inv_mul_cancel]
    exact one_mem H
  have h1 : ρ c = 1 := rho_eq_one_of_mem hρ c hcH
  have e : γ * γ' = γ' * γ * c := by rw [hc]; group
  rw [← map_mul, ← map_mul, e, map_mul, h1, mul_one]

theorem finite_range (hρ : IsDiamondPullbackModL K M H ρ) : Finite ρ.range := by
  have hker : (GammaH M H).subgroupOf (Gamma0 M) ≤ ρ.ker := by
    intro γ hγ
    rw [MonoidHom.mem_ker]
    exact rho_eq_one_of_mem hρ γ (Subgroup.mem_subgroupOf.mp hγ)
  haveI : (GammaH M H).FiniteIndex := by
    refine @Subgroup.finiteIndex_of_le _ _ (Gamma1 M) _ ?_ (Gamma1_le_GammaH M H)
    infer_instance
  haveI : ((GammaH M H).subgroupOf (Gamma0 M)).FiniteIndex := by
    refine ⟨fun h0 => ?_⟩
    have := Subgroup.relIndex_mul_index (GammaH_le_Gamma0 (M := M) H)
    rw [Subgroup.relIndex, h0, zero_mul] at this
    exact Subgroup.FiniteIndex.index_ne_zero this.symm
  haveI : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hker
  have e := QuotientGroup.quotientKerEquivRange ρ
  haveI : Finite (Gamma0 M ⧸ ρ.ker) := Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_equiv _ e.toEquiv

end Diamond

section Charts

variable {K : Type*} [Field K]

theorem mem_iff_order_nonneg {F : Type*} [Field F] [Algebra K F] (θ : F →ₐ[K] LaurentSeries K)
    (w : Place K F) (γ : ℤ) (hγ : 0 < γ) (hw : ∀ x, w.ord x * γ = (θ x).order) (x : F) :
    x ∈ w.toValuationSubring ↔ 0 ≤ (θ x).order := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [Place.mem_iff_ord_nonneg w hx, ← hw x]
  constructor
  · intro h; positivity
  · intro h
    by_contra hneg
    push Not at hneg
    have : w.ord x * γ < 0 := mul_neg_of_neg_of_pos hneg hγ
    omega

theorem place_eq_of_order_eq {F : Type*} [Field F] [Algebra K F] (θ θ' : F →ₐ[K] LaurentSeries K)
    (w w' : Place K F) (γ γ' : ℤ) (hγ : 0 < γ) (hγ' : 0 < γ')
    (hw : ∀ x, w.ord x * γ = (θ x).order) (hw' : ∀ x, w'.ord x * γ' = (θ' x).order)
    (h : ∀ x, (θ' x).order = (θ x).order) : w = w' := by
  apply Place.ext
  ext x
  rw [mem_iff_order_nonneg θ w γ hγ hw, mem_iff_order_nonneg θ' w' γ' hγ' hw', h]

variable {M : ℕ} [NeZero M]

def IsChart (ζ : Kˣ) (a : ℕ) [NeZero a] (b : ℤ) (θ : FullK M K →ₐ[K] LaurentSeries K) : Prop :=
  θ (jFull M K) = qExpand K M (jqModC K) ∧
  θ (jNFull M K) = qExpand K (a * a) (qTwist (ζ ^ (b * (a : ℤ))) (jqModC K))

theorem algHom_ext_full {ℓ : ℕ} [CharP K ℓ] (hℓM : ¬ ℓ ∣ M) {L : Type*} [Field L] [Algebra K L]
    (φ ψ : FullK M K →ₐ[K] L) (h1 : φ (jFull M K) = ψ (jFull M K))
    (h2 : φ (jNFull M K) = ψ (jNFull M K)) : φ = ψ := by
  let E : IntermediateField K (FullK M K) :=
    { carrier := {y | φ y = ψ y}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
      zero_mem' := by simp
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, AlgHom.commutes]
      inv_mem' := fun x hx => by
        simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx] }
  have hE : ∀ z : FullK M K, z ∈ E ↔ φ z = ψ z := fun z => Iff.rfl
  have hle : modularFunctionFieldC K M ≤ IntermediateField.lift E := by
    rw [modularFunctionFieldC, adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact (mem_lift (jFull M K)).mpr ((hE _).mpr h1)
    · exact (mem_lift (jNFull M K)).mpr ((hE _).mpr h2)
  refine AlgHom.ext fun x => ?_
  have hx : (x : LaurentSeries K) ∈ modularFunctionFieldC K M := by
    rw [modularFunctionFieldC_eq_modularFunctionFieldFullC K ℓ M hℓM]; exact x.2
  exact (hE x).mp ((mem_lift x).mp (hle hx))

theorem order_eq_of_isChart {ℓ : ℕ} [CharP K ℓ] (hℓM : ¬ ℓ ∣ M) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) {a : ℕ} [NeZero a] (haM : a ∣ M) {b b' : ℤ}
    {θ θ' : FullK M K →ₐ[K] LaurentSeries K} (h : IsChart ζ a b θ) (h' : IsChart ζ a b' θ')
    (hbb : ((Nat.gcd a (M / a) : ℕ) : ℤ) ∣ b' - b) (x : FullK M K) :
    (θ' x).order = (θ x).order := by
  have hζu : IsPrimitiveRoot ζ M := IsPrimitiveRoot.coe_units_iff.mp hζ

  obtain ⟨s, hs⟩ := hbb
  have hbez : ((Nat.gcd a (M / a) : ℕ) : ℤ) =
      (a : ℤ) * Nat.gcdA a (M / a) + ((M / a : ℕ) : ℤ) * Nat.gcdB a (M / a) :=
    Nat.gcd_eq_gcd_ab a (M / a)
  set t : ℤ := Nat.gcdA a (M / a) * s with ht
  have hMa : (M : ℤ) = (a : ℤ) * ((M / a : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' haM).symm

  have hkey : (M : ℤ) ∣ t * a * a + b * a - b' * a := by
    refine ⟨-(Nat.gcdB a (M / a) * s), ?_⟩
    rw [hMa]
    linear_combination (-(a : ℤ)) * hs - (a : ℤ) * s * hbez

  have e1 : (qTwistAlg K (ζ ^ t)).comp θ = θ' := by
    refine algHom_ext_full hℓM _ _ ?_ ?_
    · rw [AlgHom.comp_apply, qTwistAlg_apply, h.1, h'.1, qTwist_qExpand,
        ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζu.pow_eq_one, one_zpow, qTwist_one_apply]
    · rw [AlgHom.comp_apply, qTwistAlg_apply, h.2, h'.2, qTwist_qExpand, qTwist_qTwist]
      congr 2
      rw [← zpow_mul, ← zpow_add]
      congr 1
      rw [← mul_inv_eq_one, ← zpow_neg, ← zpow_add, hζu.zpow_eq_one_iff_dvd]
      have e : t * ((a * a : ℕ) : ℤ) + b * (a : ℤ) + -(b' * (a : ℤ)) = t * a * a + b * a - b' * a := by
        push_cast; ring
      rw [e]; exact hkey
  rw [← e1, AlgHom.comp_apply, qTwistAlg_apply, order_qTwist]

end Charts

section Galois

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]
  {K : Type*} [Field K] [IsAlgClosed K] [CharP K ℓ]
  {ρ : Gamma0 M →* (FbK M H K ≃ₐ[K] FbK M H K)}

def incl (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (GammaH M H)) :
    FullK M K →ₐ[K] FbK M H K :=
  IntermediateField.inclusion hle

@[scoped simp] theorem coe_incl (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (GammaH M H))
    (u : FullK M K) : ((incl (H := H) hle u : FbK M H K) : LaurentSeries K) = u :=
  IntermediateField.coe_inclusion hle u

theorem incl_toRingHom (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (GammaH M H)) :
    (incl (H := H) hle).toRingHom = (IntermediateField.inclusion hle).toRingHom := rfl

def Gr (ρ : Gamma0 M →* (FbK M H K ≃ₐ[K] FbK M H K)) : Subgroup (FbK M H K ≃ₐ[K] FbK M H K) := ρ.range

def Fix (ρ : Gamma0 M →* (FbK M H K ≃ₐ[K] FbK M H K)) : Subfield (FbK M H K) :=
  FixedPoints.subfield (Gr ρ) (FbK M H K)

theorem mem_Fix_iff (u : FbK M H K) : u ∈ Fix ρ ↔ ∀ γ : Gamma0 M, ρ γ u = u := by
  change (∀ g : Gr ρ, g • u = u) ↔ _
  constructor
  · intro h γ
    exact h ⟨ρ γ, γ, rfl⟩
  · rintro h ⟨g, γ, rfl⟩
    exact h γ

theorem coe_mem_full_of_mem_Fix (hℓM : ¬ ℓ ∣ M) (hρ : IsDiamondPullbackModL K M H ρ)
    (hfix : ∀ (γ : Gamma0 M) (x : FbK M H K),
      (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x)
    (u : FbK M H K) (hu : u ∈ Fix ρ) : (u : LaurentSeries K) ∈ modularFunctionFieldFullC K M :=
  ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq M H hℓM K
    ρ hρ hfix u ((mem_Fix_iff u).mp hu)

def psi (hℓM : ¬ ℓ ∣ M) (hρ : IsDiamondPullbackModL K M H ρ)
    (hfix : ∀ (γ : Gamma0 M) (x : FbK M H K),
      (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x)
    (u : Fix ρ) : FullK M K :=
  ⟨((u : FbK M H K) : LaurentSeries K), coe_mem_full_of_mem_Fix hℓM hρ hfix u u.2⟩

theorem incl_psi (hℓM : ¬ ℓ ∣ M) (hρ : IsDiamondPullbackModL K M H ρ)
    (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (GammaH M H))
    (hfix : ∀ (γ : Gamma0 M) (x : FbK M H K),
      (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x)
    (u : Fix ρ) : incl (H := H) hle (psi hℓM hρ hfix u) = (u : FbK M H K) :=
  Subtype.ext (by rw [coe_incl]; rfl)

theorem ofAlgAut_smul_place (τ : FbK M H K ≃ₐ[K] FbK M H K) (R : Place K (FbK M H K)) :
    SemilinearAut.ofAlgAut τ • R = τ • R := by
  apply Place.ext
  ext u
  rw [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, SemilinearAut.ofAlgAut_smul,
    AlgEquiv.smul_def]

set_option maxHeartbeats 3200000 in

theorem exists_smul_eq_of_comap_eq (hℓM : ¬ ℓ ∣ M) (hρ : IsDiamondPullbackModL K M H ρ)
    (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (GammaH M H))
    (hfix : ∀ (γ : Gamma0 M) (x : FbK M H K),
      (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x)
    (Q Q' : Place K (FbK M H K))
    (h : Q.toValuationSubring.comap (incl (H := H) hle).toRingHom =
      Q'.toValuationSubring.comap (incl (H := H) hle).toRingHom) :
    ∃ γ : Gamma0 M, ρ γ • Q = Q' := by
  haveI : Finite (Gr ρ) := finite_range hρ

  letI : Algebra K (Fix ρ) :=
    ((algebraMap K (FbK M H K)).codRestrict (Fix ρ) fun c => by
      rw [mem_Fix_iff]
      intro γ
      exact (ρ γ).commutes c).toAlgebra
  haveI : IsScalarTower K (Fix ρ) (FbK M H K) := IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI : IsGalois (Fix ρ) (FbK M H K) := IsGalois.of_fixed_field (FbK M H K) (Gr ρ)
  have key : ∀ (R : Place K (FbK M H K)) (u : Fix ρ),
      u ∈ (R.restrict (Fix ρ)).toValuationSubring ↔
        psi hℓM hρ hfix u ∈ R.toValuationSubring.comap (incl (H := H) hle).toRingHom := by
    intro R u
    rw [Place.mem_restrict_iff, ValuationSubring.mem_comap]
    change (u : FbK M H K) ∈ R.toValuationSubring ↔ (incl (H := H) hle) (psi hℓM hρ hfix u) ∈ _
    rw [incl_psi]
  haveI : FiniteDimensional (Fix ρ) (FbK M H K) :=
    show FiniteDimensional (FixedPoints.subfield (Gr ρ) (FbK M H K)) (FbK M H K) from inferInstance
  have hF : Q'.restrict (Fix ρ) = Q.restrict (Fix ρ) := by
    apply Place.ext
    ext u
    rw [key, key, h]
  obtain ⟨σ, hσ⟩ := AlgebraicCurve.Place.exists_algEquiv_smul_eq_of_restrict_eq (K := K)
    (F' := Fix ρ) (M := FbK M H K) Q Q' hF

  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (Gr ρ) (FbK M H K) σ
  obtain ⟨γ, hγ⟩ := g.2
  refine ⟨γ, ?_⟩
  have hres : σ.restrictScalars K = ρ γ := by
    refine AlgEquiv.ext fun x => ?_
    rw [AlgEquiv.restrictScalars_apply, ← hg, MulSemiringAction.toAlgAut_apply, hγ]
    rfl
  rw [← hres, ← ofAlgAut_smul_place]
  exact hσ

end Galois

section Main

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]
  {K : Type*} [Field K] [IsAlgClosed K] [CharP K ℓ]

abbrev DC (M : ℕ) : Type :=
  DoubleCoset.Quotient (Gamma0 M : Set SL(2, ℤ))
    ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))

structure Datum (ζ : Kˣ) (P : Place K (FullK M K)) where
  a : ℕ
  b : ℕ
  ne : NeZero a
  dvd : a ∣ M
  θ : FullK M K →ₐ[K] LaurentSeries K
  chart : @IsChart K _ M _ ζ a ne b θ
  ord : ∀ x, P.ord x * ((a * Nat.gcd a (M / a) : ℕ) : ℤ) = (θ x).order
  g : SL(2, ℤ)
  slot : IsSlotData M g a b

theorem nonempty_datum (hMK : (M : K) ≠ 0) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (P : Place K (FullK M K)) (hP : P.ord (jFull M K) < 0) : Nonempty (Datum ζ P) := by
  obtain ⟨a, b, haM, hb, hg, hne, θ, h1, h2, hord⟩ :=
    ModularCurve.exists_slot_algHom_modularFunctionFieldFullC_of_ord_neg K M hMK ζ hζ P hP
  haveI := hne
  have hcop : Nat.Coprime b (Nat.gcd a (M / a)) := by
    rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_assoc, Nat.gcd_comm b a]
    exact hg
  obtain ⟨g, hslot⟩ := exists_isSlotData (M := M) a haM b hcop
  refine ⟨⟨a, b, hne, haM, θ, ⟨h1, ?_⟩, hord, g, hslot⟩⟩
  rw [show ((b : ℤ) * (a : ℤ)) = ((b * a : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  exact h2

def datum (hMK : (M : K) ≠ 0) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (P : Place K (FullK M K)) (hP : P.ord (jFull M K) < 0) : Datum ζ P :=
  Classical.choice (nonempty_datum hMK ζ hζ P hP)

theorem Datum.factor_pos {ζ : Kˣ} {P : Place K (FullK M K)} (D : Datum ζ P) :
    (0 : ℤ) < ((D.a * Nat.gcd D.a (M / D.a) : ℕ) : ℤ) := by
  haveI := D.ne
  have h1 : 0 < M / D.a := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) D.dvd) (NeZero.pos D.a)
  have h2 : 0 < Nat.gcd D.a (M / D.a) := Nat.gcd_pos_of_pos_left _ (NeZero.pos D.a)
  exact_mod_cast Nat.mul_pos (NeZero.pos D.a) h2

theorem place_eq_of_datum (hℓM : ¬ ℓ ∣ M) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) M)
    {P P' : Place K (FullK M K)} (D : Datum ζ P) (D' : Datum ζ P')
    (ha : D.a = D'.a) (hb : ((Nat.gcd D.a (M / D.a) : ℕ) : ℤ) ∣ (D'.b : ℤ) - D.b) : P = P' := by
  haveI := D.ne
  obtain ⟨a, b, ne, dvd, θ, chart, ord, g, slot⟩ := D
  obtain ⟨a', b', ne', dvd', θ', chart', ord', g', slot'⟩ := D'
  dsimp only at ha hb
  subst ha
  refine place_eq_of_order_eq θ θ' P P' _ _ (Datum.factor_pos ⟨a, b, ne, dvd, θ, chart, ord, g, slot⟩)
    (Datum.factor_pos ⟨a, b', ne', dvd', θ', chart', ord', g', slot'⟩) ord ord' ?_
  intro x
  exact order_eq_of_isChart hℓM ζ hζ dvd chart chart' hb x

variable (ρ : Gamma0 M →* (FbK M H K ≃ₐ[K] FbK M H K))

def iota (hMK : (M : K) ≠ 0) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (P : {P : Place K (FullK M K) // P.ord (jFull M K) < 0}) : DC M :=
  DoubleCoset.mk (Gamma0 M) (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1))
    (datum hMK ζ hζ P.1 P.2).g

theorem iota_injective (hℓM : ¬ ℓ ∣ M) (hMK : (M : K) ≠ 0) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) :
    Function.Injective (iota (M := M) (K := K) hMK ζ hζ) := by
  intro P P' h
  set D := datum hMK ζ hζ P.1 P.2
  set D' := datum hMK ζ hζ P'.1 P'.2
  haveI := D.ne
  obtain ⟨ha, hb⟩ := IsSlotData.dvd_sub_of_mk_eq (M := M) D.slot D'.slot h
  exact Subtype.ext (place_eq_of_datum hℓM hζ D D' ha hb)

theorem stabilizer_clause (hℓM : ¬ ℓ ∣ M) (hMK : (M : K) ≠ 0) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (hρ : IsDiamondPullbackModL K M H ρ)
    (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (GammaH M H))
    (hfix : ∀ (γ : Gamma0 M) (x : FbK M H K),
      (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x)
    (P : {P : Place K (FullK M K) // P.ord (jFull M K) < 0}) (g : SL(2, ℤ))
    (hg : iota (M := M) (K := K) hMK ζ hζ P =
      DoubleCoset.mk (Gamma0 M) (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1)) g)
    (γ : Gamma0 M)
    (hγ : g⁻¹ * (γ : SL(2, ℤ)) * g ∈ Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1))
    (Q : Place K (FbK M H K))
    (hQ : Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
      P.1.toValuationSubring) :
    ρ γ • Q = Q := by
  set D := datum hMK ζ hζ P.1 P.2 with hD
  haveI := D.ne

  obtain ⟨k, hslot⟩ := IsSlotData.transport (M := M) D.slot hg
  obtain ⟨hac, haM', hbc⟩ := hslot

  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ :=
    ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist
      M H hℓM K ζ hζ ρ hρ g D.a ((D.b : ℤ) + k * D.a) hac D.dvd hbc

  have hchart : IsChart ζ D.a ((D.b : ℤ) + k * D.a) (Θ.comp (incl (H := H) hle)) := by
    refine ⟨?_, ?_⟩
    · rw [AlgHom.comp_apply]
      exact hΘ1 _ (coe_incl hle _)
    · rw [AlgHom.comp_apply]
      exact hΘ2 _ (coe_incl hle _)
  have hordeq : ∀ x, (Θ (incl (H := H) hle x)).order = (D.θ x).order := by
    intro x
    have h2 : ((Nat.gcd D.a (M / D.a) : ℕ) : ℤ) ∣ (D.a : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
    have := order_eq_of_isChart hℓM ζ hζ D.dvd D.chart hchart
      (by rw [add_sub_cancel_left]; exact h2.mul_left k) x
    rwa [AlgHom.comp_apply] at this

  have hne : ∃ x : FbK M H K, (Θ x).order ≠ 0 := by
    refine ⟨incl (H := H) hle (jFull M K), ?_⟩
    rw [hordeq, D.chart.1, order_qExpand, order_jqModC]
    simp [NeZero.ne M]
  obtain ⟨Q₀, γ₀, hγ₀, hQ₀⟩ := Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K Θ hne
  have hγ₀' : (0 : ℤ) < (γ₀ : ℤ) := by exact_mod_cast hγ₀

  have hQ₀P : Q₀.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
      P.1.toValuationSubring := by
    ext x
    rw [ValuationSubring.mem_comap, mem_iff_order_nonneg D.θ P.1 _ D.factor_pos D.ord x]
    change incl (H := H) hle x ∈ Q₀.toValuationSubring ↔ _
    rw [mem_iff_order_nonneg Θ Q₀ γ₀ hγ₀' hQ₀, hordeq]

  obtain ⟨m, hm⟩ := exists_eq_T_zpow_or_of_mem hγ
  have hΘγ : ∀ x, (Θ (ρ γ⁻¹ x)).order = (Θ x).order := by
    intro x
    rw [hΘ3 γ m hm x, order_qTwist]
  have hfixQ₀ : ρ γ • Q₀ = Q₀ := by
    apply Place.ext
    ext x
    rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, ← map_inv, mem_iff_order_nonneg Θ Q₀ γ₀ hγ₀' hQ₀,
      mem_iff_order_nonneg Θ Q₀ γ₀ hγ₀' hQ₀, hΘγ]

  obtain ⟨γ', hγ'⟩ := exists_smul_eq_of_comap_eq hℓM hρ hle hfix Q₀ Q (by
    rw [incl_toRingHom, hQ₀P, hQ])
  rw [← hγ', ← mul_smul, rho_comm hρ, mul_smul, hfixQ₀]

theorem main (hℓM : ¬ ℓ ∣ M)
    (hρ : IsDiamondPullbackModL K M H ρ)
    (hle : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (GammaH M H))
    (hfix : ∀ (γ : Gamma0 M) (x : FbK M H K),
      (x : LaurentSeries K) ∈ modularFunctionFieldFullC K M → ρ γ x = x) :
    ∃ ι : {P : Place K (FullK M K) // P.ord (jFull M K) < 0} → DC M,
        Function.Injective ι ∧
        ∀ P (g : SL(2, ℤ)),
          ι P = DoubleCoset.mk (Gamma0 M) (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1)) g →
          ∀ γ : Gamma0 M,
            g⁻¹ * (γ : SL(2, ℤ)) * g ∈ Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) →
            ∀ Q : Place K (FbK M H K),
              Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
                P.1.toValuationSubring →
              ρ γ • Q = Q := by
  have hMK : (M : K) ≠ 0 := fun h => hℓM ((CharP.cast_eq_zero_iff K ℓ M).mp h)
  haveI : NeZero (M : K) := ⟨hMK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
  set ζ : Kˣ := (hz.isUnit (NeZero.ne M)).unit with hζdef
  have hζ : IsPrimitiveRoot (ζ : K) M := by
    rw [hζdef, IsUnit.unit_spec]
    exact hz
  exact ⟨iota hMK ζ hζ, iota_injective hℓM hMK ζ hζ,
    fun P g hg γ hγ Q hQ => stabilizer_clause ρ hℓM hMK ζ hζ hρ hle hfix P g hg γ hγ Q hQ⟩

end Main

end XHCuspLoc
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg.XHCuspLoc"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg.XHCuspLoc"

open scoped MatrixGroups

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (hle : ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hfix : ∀ (γ : CongruenceSubgroup.Gamma0 M)
      (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldFullC K M → ρ γ x = x) :
    ∃ ι : {P : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldFullC K M) //
              P.ord (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K M⟩ :
                ModularCurve.modularFunctionFieldFullC K M) < 0} →
            DoubleCoset.Quotient
              (CongruenceSubgroup.Gamma0 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
              ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
                  Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
                Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
        Function.Injective ι ∧
        ∀ P (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
          ι P = DoubleCoset.mk (CongruenceSubgroup.Gamma0 M)
            (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1)) g →
          ∀ γ : CongruenceSubgroup.Gamma0 M,
            g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g ∈
              Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) →
            ∀ Q : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
              Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
                P.1.toValuationSubring →
              ρ γ • Q = Q :=
  XHCuspLoc.main ρ hℓM hρ hle hfix

end S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg
end P2MW
export P2MW.S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg (solution)

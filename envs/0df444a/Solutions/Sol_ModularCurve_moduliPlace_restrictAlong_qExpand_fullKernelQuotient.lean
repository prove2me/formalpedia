-- Prove2me | solution 1 for ModularCurve.moduliPlace_restrictAlong_qExpand_fullKernelQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a9062d1a-9b01-523d-ac78-2809797d1619

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Theorems.Thm_ModularCurve_ModuliPoint_mk_eq_mk_iff_step
import Theorems.Thm_WeierstrassCurve_exists_fullKernelHom
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom
import Theorems.Thm_WeierstrassCurve_heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_variableChange_vcInvFun
import Theorems.Thm_WeierstrassCurve_heq_fullKernelHom_vcInvFun
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_zmultiples_eq_fullKernelQuotient_j
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace P2MKcDegenC7

p2m_open "AlgebraicCurve ModularCurve WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine IsLocalRing"

universe u

section GroupTheory

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem addOrderOf_div_nsmul {g : G} {N e : ℕ} (hg : addOrderOf g = N) (hN : N ≠ 0) (he : e ∣ N) :
    addOrderOf ((N / e) • g) = e := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he (Nat.pos_of_ne_zero hN)
  have hq : 0 < N / e := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) he) he0
  rw [addOrderOf_nsmul' _ hq.ne', hg, Nat.gcd_eq_right (Nat.div_dvd_of_dvd he), Nat.div_div_self he hN]

theorem addOrderOf_apply_eq (φ : G →+ H) (g : G) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hg : addOrderOf g = m * n) (hker : φ.ker = AddSubgroup.zmultiples (m • g)) :
    addOrderOf (φ g) = m := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← map_nsmul, ← AddMonoidHom.mem_ker, hker]
    exact AddSubgroup.mem_zmultiples _
  · have h0 : addOrderOf (φ g) • g ∈ φ.ker := by
      rw [AddMonoidHom.mem_ker, map_nsmul, addOrderOf_nsmul_eq_zero]
    rw [hker, AddSubgroup.mem_zmultiples_iff] at h0
    obtain ⟨z, hz⟩ := h0
    have h1 : ((addOrderOf (φ g) : ℤ) - z * m) • g = 0 := by
      rw [sub_zsmul, natCast_zsmul, mul_zsmul, natCast_zsmul, hz]
      simp
    have h2 : (addOrderOf g : ℤ) ∣ (addOrderOf (φ g) : ℤ) - z * m :=
      addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
    rw [hg] at h2
    have h3 : (m : ℤ) ∣ ((m * n : ℕ) : ℤ) := ⟨n, by push_cast; ring⟩
    have h4 := h3.trans h2
    have h5 : (m : ℤ) ∣ z * m := dvd_mul_left _ _
    have h6 := dvd_add h4 h5
    rw [sub_add_cancel] at h6
    exact Int.natCast_dvd_natCast.mp h6

theorem exists_generator_of_isAddCyclic {G : Type*} [AddGroup G] (C : AddSubgroup G) {n : ℕ}
    (hC : IsAddCyclic C ∧ Nat.card C = n) :
    ∃ g : G, addOrderOf g = n ∧ AddSubgroup.zmultiples g = C := by
  haveI := hC.1
  obtain ⟨⟨g, hg⟩, hgen⟩ := IsAddCyclic.exists_generator (α := C)
  have hC' : AddSubgroup.zmultiples g = C := by
    refine le_antisymm (AddSubgroup.zmultiples_le.mpr hg) fun x hx => ?_
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen ⟨x, hx⟩)
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨z, ?_⟩
    have := congrArg Subtype.val hz
    simpa using this
  refine ⟨g, ?_, hC'⟩
  rw [← Nat.card_zmultiples, hC', hC.2]

theorem zmultiples_eq_zmultiples_nsmul {g Q : G} {M s : ℕ} (hM : M ≠ 0) (hs : s ≠ 0)
    (hg : addOrderOf g = M * s) (hQ : Q ∈ AddSubgroup.zmultiples g) (hQs : addOrderOf Q = s) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (M • g) := by
  have hordMg : addOrderOf (M • g) = s := by
    have h := addOrderOf_div_nsmul hg (Nat.mul_ne_zero hM hs) (dvd_mul_left s M)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)] at h
  haveI : Finite (AddSubgroup.zmultiples (M • g)) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zmultiples, hordMg]
    exact hs
  apply AddSubgroup.eq_of_le_of_card_ge
  ·
    obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hQ
    have h1 : ((s : ℤ) * z) • g = 0 := by
      rw [mul_zsmul, natCast_zsmul, ← hQs, addOrderOf_nsmul_eq_zero]
    have h2 : (addOrderOf g : ℤ) ∣ (s : ℤ) * z := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
    rw [hg] at h2
    obtain ⟨w, hw⟩ := h2
    have hz : z = M * w := by
      have h3 : (s : ℤ) * z = s * (M * w) := by rw [hw]; push_cast; ring
      exact mul_left_cancel₀ (by exact_mod_cast hs) h3
    refine AddSubgroup.zmultiples_le.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨w, ?_⟩)
    rw [hz, mul_comm, mul_zsmul, natCast_zsmul]
  · rw [Nat.card_zmultiples, Nat.card_zmultiples, hordMg, hQs]

theorem zmultiples_nsmul_eq_of_coprime {R : G} {k : ℕ} (hk : k.Coprime (addOrderOf R)) :
    AddSubgroup.zmultiples (k • R) = AddSubgroup.zmultiples R := by
  refine le_antisymm (AddSubgroup.zmultiples_le.mpr (AddSubgroup.nsmul_mem_zmultiples R k)) ?_
  obtain ⟨m, hm⟩ := exists_nsmul_eq_self_of_coprime (x := R) hk
  refine AddSubgroup.zmultiples_le.mpr ?_
  have h := AddSubgroup.nsmul_mem_zmultiples (k • R) m
  rwa [hm] at h

theorem zmultiples_apply_eq (φ : G →+ H) (g : G) (C'' : AddSubgroup H) {m : ℕ} (hm : m ≠ 0)
    (hord : addOrderOf (φ g) = m) (hC'' : IsAddCyclic C'' ∧ Nat.card C'' = m)
    (hle : ∀ T ∈ AddSubgroup.zmultiples g, φ T ∈ C'') :
    AddSubgroup.zmultiples (φ g) = C'' := by
  haveI : Finite C'' := Nat.finite_of_card_ne_zero (by rw [hC''.2]; exact hm)
  apply AddSubgroup.eq_of_le_of_card_ge
  · exact AddSubgroup.zmultiples_le.mpr (hle g (AddSubgroup.mem_zmultiples g))
  · rw [hC''.2, Nat.card_zmultiples, hord]

end GroupTheory

section TSpec

variable {F : Type*} [Field F] [DecidableEq F]

def tsum {W : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ) (P : W.toAffine.Point) : F × F :=
  (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
      ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
   P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
      ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))

structure TSpec {W W' : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ)
    (φ : W.toAffine.Point →+ W'.toAffine.Point) : Prop where
  ker : φ.ker = AddSubgroup.zmultiples Q
  coords : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q → (φ P).coordsOrZero = tsum Q N P

variable {W W' : WeierstrassCurve F}

theorem TSpec.apply_eq_zero_iff {Q : W.toAffine.Point} {N : ℕ} {φ : W.toAffine.Point →+ W'.toAffine.Point}
    (h : TSpec Q N φ) (P : W.toAffine.Point) : φ P = 0 ↔ P ∈ AddSubgroup.zmultiples Q := by
  rw [← AddMonoidHom.mem_ker, h.ker]

theorem TSpec.apply_ne_zero {Q : W.toAffine.Point} {N : ℕ} {φ : W.toAffine.Point →+ W'.toAffine.Point}
    (h : TSpec Q N φ) {P : W.toAffine.Point} (hP : P ∉ AddSubgroup.zmultiples Q) : φ P ≠ 0 :=
  fun h0 => hP ((h.apply_eq_zero_iff P).mp h0)

theorem image_nsmul_Icc_eq {Q Q' : W.toAffine.Point} {N : ℕ} (hQ : addOrderOf Q = N)
    (hQ' : addOrderOf Q' = N) (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    (Finset.Icc 1 (N - 1)).image (fun k => k • Q) = (Finset.Icc 1 (N - 1)).image (fun k => k • Q') := by

  have key : ∀ {Q Q' : W.toAffine.Point}, addOrderOf Q = N → addOrderOf Q' = N →
      AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' →
      ∀ R, R ∈ (Finset.Icc 1 (N - 1)).image (fun k => k • Q) →
        R ∈ (Finset.Icc 1 (N - 1)).image (fun k => k • Q') := by
    intro Q Q' hQ hQ' h R hR
    simp only [Finset.mem_image, Finset.mem_Icc] at hR ⊢
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hR
    have hN : N ≠ 0 := by omega
    have hkQ : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
    have hmem : k • Q ∈ AddSubgroup.zmultiples Q' := h ▸ AddSubgroup.nsmul_mem_zmultiples Q k
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    set a : ℕ := (z % (N : ℤ)).toNat with ha
    have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN
    have ham : (a : ℤ) = z % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hNz)
    have haQ : a • Q' = k • Q := by
      rw [← hz, ← natCast_zsmul, ham, ← hQ', mod_addOrderOf_zsmul]
    have ha_lt : a < N := by
      have := Int.emod_lt_of_pos z (show (0 : ℤ) < N by omega)
      omega
    have ha0 : a ≠ 0 := by
      rintro h0
      rw [h0, zero_nsmul] at haQ
      exact hkQ haQ.symm
    exact ⟨a, ⟨by omega, by omega⟩, haQ⟩
  ext R
  exact ⟨key hQ hQ' h R, key hQ' hQ h.symm R⟩

theorem injOn_nsmul_Icc {Q : W.toAffine.Point} {N : ℕ} (hQ : addOrderOf Q = N) :
    Set.InjOn (fun k => k • Q) (Finset.Icc 1 (N - 1) : Set ℕ) := by
  intro k hk k' hk' hkk'
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  exact nsmul_injOn_Iio_addOrderOf (by rw [Set.mem_Iio, hQ]; omega)
    (by rw [Set.mem_Iio, hQ]; omega) hkk'

theorem sum_Icc_nsmul_eq {β : Type*} [AddCommMonoid β] {Q Q' : W.toAffine.Point} {N : ℕ}
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') (f : W.toAffine.Point → β) :
    ∑ k ∈ Finset.Icc 1 (N - 1), f (k • Q) = ∑ k ∈ Finset.Icc 1 (N - 1), f (k • Q') := by
  rw [← Finset.sum_image (f := f) (injOn_nsmul_Icc hQ),
    ← Finset.sum_image (f := f) (injOn_nsmul_Icc hQ'), image_nsmul_Icc_eq hQ hQ' h]

theorem oddOrderSummingSet_eq_image_image (Q : W.toAffine.Point) (n : ℕ) :
    W.oddOrderSummingSet Q n =
      ((Finset.Icc 1 n).image (fun k => k • Q)).image (fun P => P.coordsOrZero) := by
  rw [oddOrderSummingSet, Finset.image_image]
  rfl

theorem fullKernelQuotient_eq_of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ}
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.fullKernelQuotient Q N = W.fullKernelQuotient Q' N := by
  rw [fullKernelQuotient, fullKernelQuotient, oddOrderSummingSet_eq_image_image,
    oddOrderSummingSet_eq_image_image, image_nsmul_Icc_eq hQ hQ' h]

theorem tsum_eq_of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ}
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') (P : W.toAffine.Point) :
    tsum Q N P = tsum Q' N P := by
  simp only [tsum]
  rw [sum_Icc_nsmul_eq hQ hQ' h (fun R => (P + R).coordsOrZero.1 - R.coordsOrZero.1),
    sum_Icc_nsmul_eq hQ hQ' h (fun R => (P + R).coordsOrZero.2 - R.coordsOrZero.2)]

theorem TSpec.of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ}
    {φ : W.toAffine.Point →+ W'.toAffine.Point} (hφ : TSpec Q N φ)
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') : TSpec Q' N φ where
  ker := by rw [hφ.ker, h]
  coords P hP := by
    rw [hφ.coords P (by rwa [h]), tsum_eq_of_zmultiples_eq hQ hQ' h]

end TSpec

section Cast

variable {F : Type*} [Field F] [DecidableEq F]

def castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_rfl {W₁ : WeierstrassCurve F} (P : W₁.toAffine.Point) : castPt rfl P = P := rfl

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (P₂ : W₂.toAffine.Point) : castPt e P = P₂ ↔ HEq P P₂ := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

theorem heq_castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) :=
  (castPt_eq_iff_heq e P _).mp rfl

theorem coordsOrZero_castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    (castPt e P).coordsOrZero = P.coordsOrZero := by
  subst e; rfl

theorem castPt_castPt {W₁ W₂ W₃ : WeierstrassCurve F} (e : W₁ = W₂) (e' : W₂ = W₃)
    (P : W₁.toAffine.Point) : castPt e' (castPt e P) = castPt (e.trans e') P := by
  subst e; subst e'; rfl

theorem castPt_symm_castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    castPt e.symm (castPt e P) = P := by
  subst e; rfl

theorem addOrderOf_castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    addOrderOf (castPt e P) = addOrderOf P := by
  subst e; rfl

theorem fullKernelQuotient_castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (Q : W₁.toAffine.Point)
    (N : ℕ) : W₂.fullKernelQuotient (castPt e Q) N = W₁.fullKernelQuotient Q N := by
  subst e; rfl

theorem cyclicQuotientJ_zmultiples_castPt {V₁ V₂ : WeierstrassCurve F} (e : V₁ = V₂)
    (R : V₁.toAffine.Point) (N : ℕ) :
    V₂.cyclicQuotientJ (AddSubgroup.zmultiples (castPt e R)) N =
      V₁.cyclicQuotientJ (AddSubgroup.zmultiples R) N := by
  subst e; rfl

theorem vcInvFun_castPt (γ : VariableChange F) {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂)
    (P : W₁.toAffine.Point) :
    Point.vcInvFun γ W₂.toAffine (castPt e P) =
      castPt (congrArg (fun W : WeierstrassCurve F => γ • W) e) (Point.vcInvFun γ W₁.toAffine P) := by
  subst e; rfl

theorem nsmul_vcInvFun (γ : VariableChange F) (W : WeierstrassCurve F) (Q : W.toAffine.Point) (k : ℕ) :
    k • Point.vcInvFun γ W.toAffine Q = Point.vcInvFun γ W.toAffine (k • Q) := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, succ_nsmul, Point.vcInvFun_add]

def vcInvHom (γ : VariableChange F) (W : WeierstrassCurve F) :
    W.toAffine.Point →+ (γ • W).toAffine.Point :=
  AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine)

theorem vcInvFun_injective (γ : VariableChange F) (W : WeierstrassCurve F) :
    Function.Injective (Point.vcInvFun γ W.toAffine) :=
  (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective

theorem addOrderOf_vcInvFun (γ : VariableChange F) (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    addOrderOf (Point.vcInvFun γ W.toAffine P) = addOrderOf P :=
  addOrderOf_injective (vcInvHom γ W) (vcInvFun_injective γ W) P

end Cast

section BaseChange

variable {F : Type*} {F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  (f : F →+* F')

theorem coordsOrZero_mapPoint {W : WeierstrassCurve F} (P : W.toAffine.Point) :
    (mapPoint f P).coordsOrZero = (f P.coordsOrZero.1, f P.coordsOrZero.2) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [mapPoint]
  · rfl

theorem mapPoint_castPt {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    mapPoint f (castPt e P) =
      castPt (congrArg (fun W : WeierstrassCurve F => W.map f) e) (mapPoint f P) := by
  subst e; rfl

theorem map_veluGx (W : WeierstrassCurve F) (x y : F) :
    (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [veluGx, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
    map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem map_veluGy (W : WeierstrassCurve F) (x y : F) :
    (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp only [veluGy, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_add, map_mul, map_neg,
    map_ofNat]

theorem map_veluQuotientOfSums (W : WeierstrassCurve F) (t w : F) :
    (W.veluQuotientOfSums t w).map f = (W.map f).veluQuotientOfSums (f t) (f w) := by
  ext
  · rfl
  · rfl
  · rfl
  · simp only [WeierstrassCurve.map_a₄, veluQuotientOfSums_a₄, map_sub, map_mul, map_ofNat]
  · simp only [WeierstrassCurve.map_a₆, veluQuotientOfSums_a₆, WeierstrassCurve.map_b₂, map_sub,
      map_mul, map_ofNat]

theorem injOn_coords_nsmul {W : WeierstrassCurve F} {Q : W.toAffine.Point} {N : ℕ}
    (hQ : addOrderOf Q = N) :
    Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 (N - 1) : Set ℕ) := by
  intro k hk k' hk' h
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  have hne : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have hne' : k' • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  exact injOn_nsmul_Icc hQ (by simp [hk]) (by simp [hk']) (eq_of_coordsOrZero_eq hne hne' h)

theorem map_fullKernelQuotient (W : WeierstrassCurve F) {Q : W.toAffine.Point} {N : ℕ}
    (hQ : addOrderOf Q = N) {Q' : (W.map f).toAffine.Point} (hQ' : mapPoint f Q = Q') :
    (W.fullKernelQuotient Q N).map f = (W.map f).fullKernelQuotient Q' N := by
  subst hQ'
  have hQf : addOrderOf (mapPoint f Q) = N := (addOrderOf_mapPoint f Q).trans hQ
  rw [fullKernelQuotient, fullKernelQuotient, map_veluQuotientOfSums, oddOrderSummingSet,
    oddOrderSummingSet, Finset.sum_image (injOn_coords_nsmul hQ),
    Finset.sum_image (injOn_coords_nsmul hQ), Finset.sum_image (injOn_coords_nsmul hQf),
    Finset.sum_image (injOn_coords_nsmul hQf), map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mapPoint_nsmul, coordsOrZero_mapPoint, map_veluGx]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mapPoint_nsmul, coordsOrZero_mapPoint, map_veluGx, map_veluGy, map_sub, map_mul, map_mul]

theorem tsum_mapPoint {W : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ) (P : W.toAffine.Point) :
    tsum (mapPoint f Q) N (mapPoint f P) = (f (tsum Q N P).1, f (tsum Q N P).2) := by
  simp only [tsum, map_add, map_sum, map_sub, ← mapPoint_nsmul, ← mapPoint_add, coordsOrZero_mapPoint]

theorem TSpec.mapPoint_apply {W : WeierstrassCurve F} {Q : W.toAffine.Point} {N : ℕ}
    (hQ : addOrderOf Q = N)
    {φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point} (hφ : TSpec Q N φ)
    {Q' : (W.map f).toAffine.Point} (hQ' : mapPoint f Q = Q')
    {φ' : (W.map f).toAffine.Point →+ ((W.map f).fullKernelQuotient Q' N).toAffine.Point}
    (hφ' : TSpec Q' N φ') (P : W.toAffine.Point) :
    φ' (mapPoint f P) = castPt (map_fullKernelQuotient f W hQ hQ') (mapPoint f (φ P)) := by
  subst hQ'
  by_cases hP : P ∈ AddSubgroup.zmultiples Q
  · have h1 : φ P = 0 := (hφ.apply_eq_zero_iff P).mpr hP
    have h2 : φ' (mapPoint f P) = 0 := by
      rw [hφ'.apply_eq_zero_iff]
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
      rw [show mapPoint f (z • Q) = z • mapPoint f Q from map_zsmul (mapPointHom f) z Q]
      exact AddSubgroup.zsmul_mem_zmultiples _ z
    rw [h1, h2, mapPoint_zero, map_zero]
  · have hP' : mapPoint f P ∉ AddSubgroup.zmultiples (mapPoint f Q) := by
      intro hmem
      obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      rw [show z • mapPoint f Q = mapPoint f (z • Q) from (map_zsmul (mapPointHom f) z Q).symm] at hz
      exact hP (AddSubgroup.mem_zmultiples_iff.mpr ⟨z, mapPoint_injective f hz⟩)
    apply eq_of_coordsOrZero_eq (hφ'.apply_ne_zero hP')
    · intro h0
      exact hφ.apply_ne_zero hP (mapPoint_injective f
        ((castPt _).injective (h0.trans (by rw [mapPoint_zero, map_zero]))))
    rw [hφ'.coords _ hP', coordsOrZero_castPt, coordsOrZero_mapPoint, hφ.coords P hP, tsum_mapPoint]

end BaseChange

section Transport

variable {F : Type*} [Field F] [DecidableEq F]

theorem TSpec.castPt_apply_eq {W W₁' W₂' : WeierstrassCurve F} {Q : W.toAffine.Point} {N : ℕ}
    (e : W₁' = W₂') {φ₁ : W.toAffine.Point →+ W₁'.toAffine.Point}
    {φ₂ : W.toAffine.Point →+ W₂'.toAffine.Point} (h₁ : TSpec Q N φ₁) (h₂ : TSpec Q N φ₂)
    (P : W.toAffine.Point) : castPt e (φ₁ P) = φ₂ P := by
  subst e
  rw [castPt_rfl]
  by_cases hP : P ∈ AddSubgroup.zmultiples Q
  · rw [(h₁.apply_eq_zero_iff P).mpr hP, (h₂.apply_eq_zero_iff P).mpr hP]
  · exact eq_of_coordsOrZero_eq (h₁.apply_ne_zero hP) (h₂.apply_ne_zero hP)
      ((h₁.coords P hP).trans (h₂.coords P hP).symm)

theorem step_transport {M s : ℕ} (hM : M ≠ 0) (hs : s ≠ 0)
    (X₀ : WeierstrassCurve F) (gr : X₀.toAffine.Point) (hgr : addOrderOf gr = M * s)
    (γ : VariableChange F) (E : WeierstrassCurve F) (e₀ : γ • X₀ = E)
    (k : ℕ) (hk : k.Coprime (M * s)) (g₀ : E.toAffine.Point)
    (hg₀ : g₀ = castPt e₀ (k • Point.vcInvFun γ X₀.toAffine gr))
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = s)
    (hQg : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (M • g₀))
    (φ : E.toAffine.Point →+ (E.fullKernelQuotient Q s).toAffine.Point) (hφ : TSpec Q s φ)
    (φ₂ : X₀.toAffine.Point →+ (X₀.fullKernelQuotient (M • gr) s).toAffine.Point)
    (hφ₂ : TSpec (M • gr) s φ₂)
    (X₁ : WeierstrassCurve F) (e₂ : X₀.fullKernelQuotient (M • gr) s = X₁)
    (y₁ : X₁.toAffine.Point) (hy₁ : y₁ = castPt e₂ (φ₂ gr)) :
    ∃ e₁ : γ • X₁ = E.fullKernelQuotient Q s, HEq (φ g₀) (k • Point.vcInvFun γ X₁.toAffine y₁) := by
  subst e₂ hy₁ e₀ hg₀
  rw [castPt_rfl] at hQg ⊢
  rw [castPt_rfl]
  set T : (γ • X₀).toAffine.Point := Point.vcInvFun γ X₀.toAffine gr with hT

  have hMs : M * s ≠ 0 := Nat.mul_ne_zero hM hs
  have hordT : addOrderOf T = M * s := (addOrderOf_vcInvFun γ X₀ gr).trans hgr
  have hordMgr : addOrderOf (M • gr) = s := by
    have h := addOrderOf_div_nsmul hgr hMs (dvd_mul_left s M)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)] at h
  have hordMT : addOrderOf (M • T) = s := by
    have h := addOrderOf_div_nsmul hordT hMs (dvd_mul_left s M)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)] at h

  have hMT : Point.vcInvFun γ X₀.toAffine (M • gr) = M • T := (nsmul_vcInvFun γ X₀ gr M).symm
  have hQT : AddSubgroup.zmultiples Q =
      AddSubgroup.zmultiples (Point.vcInvFun γ X₀.toAffine (M • gr)) := by
    rw [hQg, hMT, smul_smul, mul_comm, ← smul_smul]
    exact zmultiples_nsmul_eq_of_coprime
      (hordMT ▸ Nat.Coprime.coprime_dvd_right (dvd_mul_left s M) hk)
  have hordQ' : addOrderOf (Point.vcInvFun γ X₀.toAffine (M • gr)) = s := by rw [hMT, hordMT]

  have hcurve : (γ • X₀).fullKernelQuotient Q s =
      (γ • X₀).fullKernelQuotient (Point.vcInvFun γ X₀.toAffine (M • gr)) s :=
    fullKernelQuotient_eq_of_zmultiples_eq hQ hordQ' hQT
  have hφ' : TSpec (Point.vcInvFun γ X₀.toAffine (M • gr)) s φ := hφ.of_zmultiples_eq hQ hordQ' hQT
  set φ₃ : (γ • X₀).toAffine.Point →+
      ((γ • X₀).fullKernelQuotient (Point.vcInvFun γ X₀.toAffine (M • gr)) s).toAffine.Point :=
    (castPt hcurve).toAddMonoidHom.comp φ with hφ₃
  have hφ₃spec : TSpec (Point.vcInvFun γ X₀.toAffine (M • gr)) s φ₃ :=
    { ker := by
        rw [← hφ'.ker]
        ext P
        simp only [AddMonoidHom.mem_ker, hφ₃, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
          Function.comp_apply, EmbeddingLike.map_eq_zero_iff]
      coords := fun P hP => by
        simp only [hφ₃, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
          coordsOrZero_castPt]
        exact hφ'.coords P hP }

  have hVC := WeierstrassCurve.fullKernelQuotient_variableChange_vcInvFun X₀ γ (M • gr) hordMgr
  have hHom := WeierstrassCurve.heq_fullKernelHom_vcInvFun X₀ γ (M • gr) hordMgr φ₂ hφ₂.ker
    hφ₂.coords φ₃ hφ₃spec.ker hφ₃spec.coords gr
  refine ⟨by rw [hcurve, hVC], ?_⟩

  rw [map_nsmul]
  have h1 : φ T = castPt hcurve.symm (φ₃ T) := by
    simp only [hφ₃, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
      castPt_symm_castPt]
  rw [h1, ← map_nsmul]
  have h2 : HEq (k • φ₃ T)
      (k • Point.vcInvFun γ (X₀.fullKernelQuotient (M • gr) s).toAffine (φ₂ gr)) :=
    Point.heq_nsmul (V := ((γ • X₀).fullKernelQuotient (Point.vcInvFun γ X₀.toAffine (M • gr)) s).toAffine)
      (V' := (γ • X₀.fullKernelQuotient (M • gr) s).toAffine) (congrArg WeierstrassCurve.toAffine hVC.symm)
      k hHom.symm |>.symm
  exact HEq.trans (heq_castPt hcurve.symm (k • φ₃ T)).symm h2

end Transport

section Pins

variable {L : Type u} [Field L] [DecidableEq L] [IsAlgClosed L]

theorem natCast_ne_zero_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : (b : L) ≠ 0) : (a : L) ≠ 0 := by
  obtain ⟨c, rfl⟩ := hab
  intro h
  apply hb
  rw [Nat.cast_mul, h, zero_mul]

theorem j_congr {V₁ V₂ : WeierstrassCurve L} (h : V₁ = V₂) (i₁ : V₁.IsElliptic) (i₂ : V₂.IsElliptic) :
    @WeierstrassCurve.j L _ V₁ i₁ = @WeierstrassCurve.j L _ V₂ i₂ := by
  subst h
  rfl

theorem pin_identity (V : WeierstrassCurve L) [V.IsElliptic] {s d : ℕ} (hs : s ≠ 0) (hd0 : d ≠ 0)
    (hdsL : ((d * s : ℕ) : L) ≠ 0) (R : V.toAffine.Point) (hordR : addOrderOf R = d * s)
    (Φ : V.toAffine.Point →+ (V.fullKernelQuotient (d • R) s).toAffine.Point)
    (hΦ : TSpec (d • R) s Φ) :
    V.cyclicQuotientJ (AddSubgroup.zmultiples R) (d * s) =
      (V.fullKernelQuotient (d • R) s).cyclicQuotientJ (AddSubgroup.zmultiples (Φ R)) d := by
  haveI : NeZero d := ⟨hd0⟩
  haveI : NeZero s := ⟨hs⟩
  haveI : NeZero (d * s) := ⟨Nat.mul_ne_zero hd0 hs⟩
  haveI : NeZero (s * d) := ⟨Nat.mul_ne_zero hs hd0⟩

  have hordR' : addOrderOf R = s * d := by rw [hordR, Nat.mul_comm]
  have horddR : addOrderOf (d • R) = s := by
    have h1 := addOrderOf_div_nsmul hordR (Nat.mul_ne_zero hd0 hs) (dvd_mul_left s d)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)] at h1
  have hsL : (s : L) ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_left s d) hdsL
  have hdL : (d : L) ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_right d s) hdsL

  have hΔ₁ : (V.fullKernelQuotient R (d * s)).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero (d * s) V hdsL R hordR
  rw [WeierstrassCurve.cyclicQuotientJ_zmultiples_eq_fullKernelQuotient_j hdsL V R hordR hΔ₁]

  have hΔE' : (V.fullKernelQuotient (d • R) s).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero s V hsL (d • R) horddR
  haveI hE' : (V.fullKernelQuotient (d • R) s).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔE'⟩
  have hordΦR : addOrderOf (Φ R) = d := addOrderOf_apply_eq Φ R hd0 hs hordR hΦ.ker
  have hΔ₂ : ((V.fullKernelQuotient (d • R) s).fullKernelQuotient (Φ R) d).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero d _ hdL (Φ R) hordΦR
  rw [WeierstrassCurve.cyclicQuotientJ_zmultiples_eq_fullKernelQuotient_j hdL _ (Φ R) hordΦR hΔ₂]

  have hsdL : ((s * d : ℕ) : L) ≠ 0 := by rwa [Nat.mul_comm] at hdsL
  have hTower := WeierstrassCurve.fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
    V hsdL R hordR' Φ hΦ.ker hΦ.coords
  have hcomm : V.fullKernelQuotient R (s * d) = V.fullKernelQuotient R (d * s) := by rw [Nat.mul_comm]
  exact (j_congr (hTower.trans hcomm) _ _).symm

end Pins

section Main

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]

theorem beta_jqNFull (β : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s))
    (hβ : ∀ f : modularFunctionFieldFullC K M,
      ((β f : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) =
        qExpand K s (f : LaurentSeries K))
    (d : ℕ) [NeZero d] (hd : d ∣ M) [NeZero (d * s)] :
    β (jqNFull K M d hd) = jqNFull K (M * s) (d * s) (Nat.mul_dvd_mul_right hd s) := by
  haveI : NeZero (s * d) := ⟨by rw [Nat.mul_comm]; exact NeZero.ne (d * s)⟩
  apply Subtype.ext
  rw [hβ, coe_jqNFull, coe_jqNFull, jqNModC, jqNModC, qExpand_qExpand,
    qExpand_congr (Nat.mul_comm s d)]

variable {K M s}

theorem isModuliPlaceOf_restrictAlong (hMs : ((M * s : ℕ) : K) ≠ 0)
    (β : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s))
    (hβ : ∀ f : modularFunctionFieldFullC K M,
      ((β f : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) =
        qExpand K s (f : LaurentSeries K))
    (hb : β.toRingHom.IsIntegral)
    (E : WeierstrassCurve K) [hE : E.IsElliptic] (g₀ : E.toAffine.Point) (hg₀ : addOrderOf g₀ = M * s)
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = s)
    (hQg : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (M • g₀))
    (hΔ : (E.fullKernelQuotient Q s).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.fullKernelQuotient Q s).toAffine.Point) (hφ : TSpec Q s φ)
    (hordφ : addOrderOf (φ g₀) = M)
    (v : Place K (modularFunctionFieldFullC K (M * s)))
    (hv : IsModuliPlaceOf K (M * s) (Quot.mk _ (⟨E, hE, g₀, hg₀⟩ : Gamma0Pair (M * s) K)) v) :
    IsModuliPlaceOf K M
      (Quot.mk _ (⟨E.fullKernelQuotient Q s, ⟨isUnit_iff_ne_zero.mpr hΔ⟩, φ g₀, hordφ⟩ :
        Gamma0Pair M K))
      (v.restrictAlong β hb) := by
  obtain ⟨Ω, iF, iD, iA, D, hD⟩ := hv
  letI := Classical.decEq (ResidueField D.W.toValuationSubring)
  have hM : M ≠ 0 := NeZero.ne M
  have hs : s ≠ 0 := NeZero.ne s
  have hMs0 : M * s ≠ 0 := Nat.mul_ne_zero hM hs

  have hsK : (s : K) ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_left s M) hMs
  have hsΩ : (s : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero _).mpr hsK
  have hsκ : (s : ResidueField D.W.toValuationSubring) ≠ 0 := by
    intro h0
    apply hsK
    have := congrArg D.res h0
    rwa [map_natCast, map_zero] at this

  obtain ⟨hordgb, hx⟩ := D.reduction
  set gen := D.gen with hgen
  set P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point := M • gen with hPdef
  have hordP : addOrderOf P = s := by
    have h1 := addOrderOf_div_nsmul D.addOrderOf_gen hMs0 (dvd_mul_left s M)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)] at h1
  have hredP : reduceHom D.map_Δ_ne_zero P = M • reduceHom D.map_Δ_ne_zero gen := map_nsmul _ _ _
  have hordPb : addOrderOf (reduceHom D.map_Δ_ne_zero P) = s := by
    rw [hredP]
    have h1 := addOrderOf_div_nsmul hordgb hMs0 (dvd_mul_left s M)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)] at h1

  obtain ⟨W', hW'L, hW'k, -⟩ :=
    WeierstrassCurve.exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom
      D.map_Δ_ne_zero s P hordPb
  have hΔk : ((D.curve.map (residue D.W.toValuationSubring)).fullKernelQuotient (reduceHom D.map_Δ_ne_zero P) s).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero s _ hsκ _ hordPb
  have hΔW' : (W'.map (residue D.W.toValuationSubring)).Δ ≠ 0 := by rw [hW'k]; exact hΔk

  obtain ⟨Φ, hΦker, hΦc⟩ := WeierstrassCurve.exists_fullKernelHom (D.curve.map D.W.toValuationSubring.subtype) hsΩ P hordP
  have hΦ : TSpec P s Φ := ⟨hΦker, hΦc⟩
  obtain ⟨φk, hφkker, hφkc⟩ := WeierstrassCurve.exists_fullKernelHom (D.curve.map (residue D.W.toValuationSubring)) hsκ
    (reduceHom D.map_Δ_ne_zero P) hordPb
  have hφk : TSpec (reduceHom D.map_Δ_ne_zero P) s φk := ⟨hφkker, hφkc⟩

  set gen' : (W'.map D.W.toValuationSubring.subtype).toAffine.Point := castPt hW'L.symm (Φ gen) with hgen'
  have hred : reduceHom hΔW' gen' = castPt hW'k.symm (φk (reduceHom D.map_Δ_ne_zero gen)) := by
    have hheq := WeierstrassCurve.heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient
      D.map_Δ_ne_zero s P hordPb W' hW'L hW'k hΔW' Φ hΦ.ker hΦ.coords φk hφk.ker hφk.coords gen gen'
      (heq_castPt hW'L.symm (Φ gen)).symm
    rw [← castPt_eq_iff_heq hW'k] at hheq
    rw [← hheq, castPt_symm_castPt]
  have hordΦgen : addOrderOf (Φ gen) = M := addOrderOf_apply_eq Φ gen hM hs D.addOrderOf_gen hΦ.ker
  have hordgen' : addOrderOf gen' = M := by rw [hgen', addOrderOf_castPt, hordΦgen]
  have hordφkgb : addOrderOf (φk (reduceHom D.map_Δ_ne_zero gen)) = M :=
    addOrderOf_apply_eq φk _ hM hs hordgb (by rw [hφk.ker, hredP])
  have hordred : addOrderOf (reduceHom hΔW' gen') = M := by rw [hred, addOrderOf_castPt, hordφkgb]

  have hclass : ModuliPoint.map D.res
      (Quot.mk _ (⟨W'.map (residue D.W.toValuationSubring), ⟨isUnit_iff_ne_zero.mpr hΔW'⟩, reduceHom hΔW' gen', hordred⟩ :
        Gamma0Pair M (ResidueField D.W.toValuationSubring))) =
      Quot.mk _ (⟨E.fullKernelQuotient Q s, ⟨isUnit_iff_ne_zero.mpr hΔ⟩, φ g₀, hordφ⟩ :
        Gamma0Pair M K) := by

    rw [ModuliPoint.map_mk] at hx ⊢
    obtain ⟨γ, e₀, k, hk, hheq⟩ := (ModuliPoint.mk_eq_mk_iff_step _ _).mp hx
    simp only [Gamma0Pair.map_toCurve, Gamma0Pair.map_gen] at e₀ hheq

    set X₀ : WeierstrassCurve K := (D.curve.map (residue D.W.toValuationSubring)).map D.res with hX₀
    set gr : X₀.toAffine.Point := mapPoint D.res (reduceHom D.map_Δ_ne_zero gen) with hgr
    have hordgr : addOrderOf gr = M * s := (addOrderOf_mapPoint D.res _).trans hordgb
    have hg₀ : g₀ = castPt e₀ (k • Point.vcInvFun γ X₀.toAffine gr) :=
      ((castPt_eq_iff_heq e₀ _ _).mpr hheq.symm).symm

    have hordMgr : addOrderOf (M • gr) = s := by
      have h1 := addOrderOf_div_nsmul hordgr hMs0 (dvd_mul_left s M)
      rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)] at h1
    obtain ⟨φ₂, hφ₂ker, hφ₂c⟩ := WeierstrassCurve.exists_fullKernelHom X₀ hsK (M • gr) hordMgr
    have hφ₂ : TSpec (M • gr) s φ₂ := ⟨hφ₂ker, hφ₂c⟩

    have hPres : mapPoint D.res (reduceHom D.map_Δ_ne_zero P) = M • gr := by
      rw [hredP, mapPoint_nsmul]
    have hBC := hφk.mapPoint_apply D.res hordPb hPres hφ₂ (reduceHom D.map_Δ_ne_zero gen)

    have e₂ : X₀.fullKernelQuotient (M • gr) s = (W'.map (residue D.W.toValuationSubring)).map D.res :=
      (map_fullKernelQuotient D.res _ hordPb hPres).symm.trans (congrArg (fun W => W.map D.res) hW'k.symm)
    have hy₁ : mapPoint D.res (reduceHom hΔW' gen') = castPt e₂ (φ₂ gr) := by
      rw [hred, mapPoint_castPt, ← castPt_symm_castPt (map_fullKernelQuotient D.res _ hordPb hPres)
        (mapPoint D.res (φk (reduceHom D.map_Δ_ne_zero gen))), ← hBC, castPt_castPt]
    obtain ⟨e₁, hstep⟩ := step_transport hM hs X₀ gr hordgr γ E e₀ k hk g₀ hg₀ Q hQ hQg φ hφ φ₂ hφ₂
      ((W'.map (residue D.W.toValuationSubring)).map D.res) e₂ (mapPoint D.res (reduceHom hΔW' gen')) hy₁
    exact (ModuliPoint.mk_eq_mk_iff_step _ _).mpr
      ⟨γ, e₁, k, Nat.Coprime.coprime_dvd_right (dvd_mul_right M s) hk, hstep⟩

  refine ⟨Ω, iF, iD, iA,
    { W := D.W
      curve := W'
      map_Δ_ne_zero := hΔW'
      gen := gen'
      addOrderOf_gen := hordgen'
      res := D.res
      res_algebraMap := D.res_algebraMap
      reduction := ⟨hordred, hclass⟩
      emb := D.emb.comp β
      emb_jqNFull := ?_ }, ?_⟩
  ·
    intro Ω' _ _ _ _ d _ hd
    haveI : NeZero (d * s) := ⟨Nat.mul_ne_zero (NeZero.ne d) hs⟩
    set ι : Ω →+* Ω' := algebraMap Ω Ω' with hι
    have hMsΩ' : ((M * s : ℕ) : Ω') ≠ 0 := by
      rw [← map_natCast ι, map_ne_zero, ← map_natCast (algebraMap K Ω), map_ne_zero]
      exact hMs
    have hsΩ' : (s : Ω') ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_left s M) hMsΩ'

    rw [AlgHom.comp_apply, beta_jqNFull K M s β hβ d hd, D.emb_jqNFull Ω' (d * s), mapPoint_nsmul]

    set V : WeierstrassCurve Ω' := (D.curve.map D.W.toValuationSubring.subtype).map ι with hV
    set gι : V.toAffine.Point := mapPoint ι gen with hgι
    have hordgι : addOrderOf gι = M * s := (addOrderOf_mapPoint ι gen).trans D.addOrderOf_gen
    have hPι : mapPoint ι P = d • ((M / d) • gι) := by
      rw [hPdef, mapPoint_nsmul, smul_smul, Nat.mul_div_cancel' hd]
    have horddh : addOrderOf (d • ((M / d) • gι)) = s := by
      rw [← hPι, addOrderOf_mapPoint, hordP]
    obtain ⟨Φι, hΦιker, hΦιc⟩ := WeierstrassCurve.exists_fullKernelHom V hsΩ' _ horddh
    have hΦι : TSpec (d • ((M / d) • gι)) s Φι := ⟨hΦιker, hΦιc⟩
    have hBC := hΦ.mapPoint_apply ι hordP hPι hΦι gen

    have e₄ : V.fullKernelQuotient (d • ((M / d) • gι)) s = (W'.map D.W.toValuationSubring.subtype).map ι :=
      (map_fullKernelQuotient ι _ hordP hPι).symm.trans (congrArg (fun W => W.map ι) hW'L.symm)
    have h4 : mapPoint ι ((M / d) • gen') = castPt e₄ ((M / d) • Φι gι) := by
      rw [mapPoint_nsmul, map_nsmul, hgen', mapPoint_castPt,
        ← castPt_symm_castPt (map_fullKernelQuotient ι _ hordP hPι) (mapPoint ι (Φ gen)), ← hBC,
        castPt_castPt]
    rw [h4, cyclicQuotientJ_zmultiples_castPt e₄, ← map_nsmul,
      Nat.mul_div_mul_right _ _ (Nat.pos_of_ne_zero hs)]
    have hordR : addOrderOf ((M / d) • gι) = d * s := by
      rw [← Nat.mul_div_mul_right M d (Nat.pos_of_ne_zero hs)]
      exact addOrderOf_div_nsmul hordgι hMs0 (Nat.mul_dvd_mul_right hd s)
    have hdsΩ' : ((d * s : ℕ) : Ω') ≠ 0 := natCast_ne_zero_of_dvd (Nat.mul_dvd_mul_right hd s) hMsΩ'
    exact pin_identity V hs (NeZero.ne d) hdsΩ' ((M / d) • gι) hordR Φι hΦι
  ·
    show (v.restrictAlong β hb).toValuationSubring =
      D.W.toValuationSubring.comap (D.emb.comp β).toRingHom
    ext f
    show β f ∈ v.toValuationSubring ↔ _
    rw [hD]
    rfl

end Main

end P2MKcDegenC7

end

p2m_open "AlgebraicCurve ModularCurve WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine P2MW.S_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient.P2MKcDegenC7"

universe u in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]
    (hMs : ((M * s : ℕ) : K) ≠ 0)
    (huniq : ∀ (x : ModuliPoint M K) (v v' : Place K (modularFunctionFieldFullC K M)),
      IsModuliPlaceOf K M x v → IsModuliPlaceOf K M x v' → v = v')
    (hex : ∀ x : ModuliPoint (M * s) K, ∃ v, IsModuliPlaceOf K (M * s) x v)
    (β : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s))
    (hβ : ∀ f : modularFunctionFieldFullC K M,
      ((β f : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) =
        qExpand K s (f : LaurentSeries K))
    (hb : β.toRingHom.IsIntegral)
    (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) (hC : IsAddCyclic C ∧ Nat.card C = M * s)
    (Q : E.toAffine.Point) (hQC : Q ∈ C) (hQ : addOrderOf Q = s)
    (hΔ : (E.fullKernelQuotient Q s).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.fullKernelQuotient Q s).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : E.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (s - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (s - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (C'' : AddSubgroup (E.fullKernelQuotient Q s).toAffine.Point)
    (hC'' : IsAddCyclic C'' ∧ Nat.card C'' = M) (hCC'' : ∀ T ∈ C, φ T ∈ C'') :
    (moduliPlace K (M * s) E C).restrictAlong β hb =
      moduliPlace K M (E.fullKernelQuotient Q s) C'' := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  haveI hE₁ : (E.fullKernelQuotient Q s).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  obtain ⟨g₀, hg₀, rfl⟩ := exists_generator_of_isAddCyclic C hC
  obtain ⟨g₁, hg₁, rfl⟩ := exists_generator_of_isAddCyclic C'' hC''
  have hQg : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (M • g₀) :=
    zmultiples_eq_zmultiples_nsmul (NeZero.ne M) (NeZero.ne s) hg₀ hQC hQ
  have hφspec : TSpec Q s φ := ⟨hφker, hφ⟩
  have hordφ : addOrderOf (φ g₀) = M :=
    addOrderOf_apply_eq φ g₀ (NeZero.ne M) (NeZero.ne s) hg₀ (by rw [hφker, hQg])
  have himg : AddSubgroup.zmultiples (φ g₀) = AddSubgroup.zmultiples g₁ :=
    zmultiples_apply_eq φ g₀ _ (NeZero.ne M) hordφ hC'' hCC''

  rw [moduliPlace_zmultiples K (M * s) E g₀ hg₀, moduliPlace_zmultiples K M _ g₁ hg₁,
    ModuliPoint.mk_eq_mk_of_zmultiples_eq hg₁ hordφ himg.symm]
  have hv := isModuliPlaceOf_moduliPlaceOfPoint K (M * s) (hex (Quot.mk _ ⟨E, ‹_›, g₀, hg₀⟩))
  have hres := isModuliPlaceOf_restrictAlong hMs β hβ hb E g₀ hg₀ Q hQ hQg hΔ φ hφspec hordφ _ hv
  exact (moduliPlaceOfPoint_eq_of_forall_eq K M (huniq _) hres).symm

end S_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient
end P2MW
export P2MW.S_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient (solution)

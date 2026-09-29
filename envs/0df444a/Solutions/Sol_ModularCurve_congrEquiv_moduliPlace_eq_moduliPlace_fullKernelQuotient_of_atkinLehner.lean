-- Prove2me | solution 1 for ModularCurve.congrEquiv_moduliPlace_eq_moduliPlace_fullKernelQuotient_of_atkinLehner
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9ae03672-a624-5d0b-97d7-7e5014db8e4b

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
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
import Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_congrEquiv_moduliPlace_eq_moduliPlace_fullKernelQuotient_of_atkinLehner
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace P2MKcAtkinLehnerB

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
  · obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hQ
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

theorem zmultiples_eq_of_mem_of_addOrderOf_eq {x y : G} {n : ℕ} (hn : n ≠ 0)
    (hx : addOrderOf x = n) (hy : addOrderOf y = n) (hmem : x ∈ AddSubgroup.zmultiples y) :
    AddSubgroup.zmultiples x = AddSubgroup.zmultiples y := by
  haveI : Finite (AddSubgroup.zmultiples y) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hy]; exact hn)
  exact AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr hmem)
    (by rw [Nat.card_zmultiples, Nat.card_zmultiples, hx, hy])

theorem addOrderOf_eq_of_prime {w : G} {q : ℕ} (hq : q.Prime) (hqw : q • w = 0) (hw : w ≠ 0) :
    addOrderOf w = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact addOrderOf_eq_prime hqw hw

theorem addOrderOf_add_eq_mul {u w : G} {N q : ℕ} (hu : addOrderOf u = N) (hw : addOrderOf w = q)
    (hcop : Nat.Coprime N q) : addOrderOf (u + w) = N * q := by
  rw [(AddCommute.all u w).addOrderOf_add_eq_mul_addOrderOf_of_coprime (by rw [hu, hw]; exact hcop),
    hu, hw]

theorem mem_zmultiples_add_of_coprime {N q : ℕ} (hcop : Nat.Coprime N q)
    {u w : G} (hu : N • u = 0) (hw : q • w = 0) :
    u ∈ AddSubgroup.zmultiples (u + w) ∧ w ∈ AddSubgroup.zmultiples (u + w) := by
  obtain ⟨α, β, hαβ⟩ : IsCoprime (N : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hu' : (N : ℤ) • u = 0 := by rw [natCast_zsmul]; exact hu
  have hw' : (q : ℤ) • w = 0 := by rw [natCast_zsmul]; exact hw
  have hu1 : (β * (q : ℤ)) • u = u := by
    have h1 : (α * (N : ℤ) + β * (q : ℤ)) • u = u := by rw [hαβ, one_smul]
    rwa [add_smul, mul_smul α, hu', smul_zero, zero_add] at h1
  have hw1 : (α * (N : ℤ)) • w = w := by
    have h1 : (α * (N : ℤ) + β * (q : ℤ)) • w = w := by rw [hαβ, one_smul]
    rwa [add_smul, mul_smul β, hw', smul_zero, add_zero] at h1
  constructor
  · refine AddSubgroup.mem_zmultiples_iff.mpr ⟨β * q, ?_⟩
    rw [smul_add, hu1, mul_smul, hw', smul_zero, add_zero]
  · refine AddSubgroup.mem_zmultiples_iff.mpr ⟨α * N, ?_⟩
    rw [smul_add, hw1, mul_smul, hu', smul_zero, zero_add]

theorem exists_torsion_not_mem_of_card {q : ℕ} (hq : 1 < q) (P : G) (hP : addOrderOf P = q)
    (hcard : Nat.card {x : G // q • x = 0} = q ^ 2) :
    ∃ t : G, q • t = 0 ∧ t ∉ AddSubgroup.zmultiples P := by
  by_contra hcon
  have hcon' : ∀ t : G, q • t = 0 → t ∈ AddSubgroup.zmultiples P := by
    intro t ht
    by_contra h
    exact hcon ⟨t, ht, h⟩
  haveI : Finite (AddSubgroup.zmultiples P) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zmultiples, hP]; omega
  have hle : Nat.card {x : G // q • x = 0} ≤ Nat.card (AddSubgroup.zmultiples P) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨x.1, hcon' x.1 x.2⟩ : AddSubgroup.zmultiples P)) ?_
    intro x x' h
    exact Subtype.ext (congrArg (fun s : AddSubgroup.zmultiples P => (s : G)) h)
  rw [hcard, Nat.card_zmultiples, hP, pow_two] at hle
  have h3 : q * q ≤ q * 1 := by simpa using hle
  have h4 : q ≤ 1 := Nat.le_of_mul_le_mul_left h3 (by omega)
  omega

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

theorem vcInvHom_apply (γ : VariableChange F) (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    vcInvHom γ W P = Point.vcInvFun γ W.toAffine P := rfl

theorem vcInvFun_injective (γ : VariableChange F) (W : WeierstrassCurve F) :
    Function.Injective (Point.vcInvFun γ W.toAffine) :=
  (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective

theorem addOrderOf_vcInvFun (γ : VariableChange F) (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    addOrderOf (Point.vcInvFun γ W.toAffine P) = addOrderOf P :=
  addOrderOf_injective (vcInvHom γ W) (vcInvFun_injective γ W) P

theorem zsmul_vcInvFun (γ : VariableChange F) (W : WeierstrassCurve F) (Q : W.toAffine.Point) (k : ℤ) :
    k • Point.vcInvFun γ W.toAffine Q = Point.vcInvFun γ W.toAffine (k • Q) :=
  (map_zsmul (vcInvHom γ W) k Q).symm

theorem mem_zmultiples_vcInvFun_iff (γ : VariableChange F) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) (R : (γ • W).toAffine.Point) :
    R ∈ AddSubgroup.zmultiples (Point.vcInvFun γ W.toAffine P) ↔
      Point.vcFun γ W.toAffine R ∈ AddSubgroup.zmultiples P := by
  rw [← vcInvHom_apply, ← AddMonoidHom.map_zmultiples, AddSubgroup.mem_map]
  constructor
  · rintro ⟨R', hR', hRQ⟩
    rw [vcInvHom_apply] at hRQ
    rw [← hRQ, Point.vcFun_rightInverse R']
    exact hR'
  · intro h
    refine ⟨_, h, ?_⟩
    rw [vcInvHom_apply, Point.vcFun_leftInverse R]

theorem cyclicQuotientJ_zmultiples_vcInvFun (γ : VariableChange F) (V : WeierstrassCurve F)
    (P : V.toAffine.Point) (n : ℕ) (hn : (n : F) ≠ 0) :
    (γ • V).cyclicQuotientJ (AddSubgroup.zmultiples (Point.vcInvFun γ V.toAffine P)) n =
      V.cyclicQuotientJ (AddSubgroup.zmultiples P) n :=
  WeierstrassCurve.cyclicQuotientJ_variableChange_eq γ V _ _
    (fun R => mem_zmultiples_vcInvFun_iff γ V P R) n hn

theorem equivOfVariableChangeEq_symm_apply (γ : VariableChange F) (W : WeierstrassCurve F)
    {V' : WeierstrassCurve F} (h : γ • W = V') (P : W.toAffine.Point) :
    (Point.equivOfVariableChangeEq (C := γ) (W := W.toAffine) (V := V'.toAffine) h).symm P =
      castPt h (Point.vcInvFun γ W.toAffine P) := by
  subst h; rfl

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

theorem not_mem_zmultiples_mapPoint {W : WeierstrassCurve F} {t P : W.toAffine.Point}
    (ht : t ∉ AddSubgroup.zmultiples P) :
    mapPoint f t ∉ AddSubgroup.zmultiples (mapPoint f P) := by
  intro hmem
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  rw [show z • mapPoint f P = mapPoint f (z • P) from (map_zsmul (mapPointHom f) z P).symm] at hz
  exact ht (AddSubgroup.mem_zmultiples_iff.mpr ⟨z, mapPoint_injective f hz⟩)

end BaseChange

section Transport

variable {F : Type*} [Field F] [DecidableEq F]

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
    (X : X₀.toAffine.Point) (y₁ : X₁.toAffine.Point) (hy₁ : y₁ = castPt e₂ (φ₂ X)) :
    ∃ e₁ : γ • X₁ = E.fullKernelQuotient Q s,
      HEq (φ (castPt e₀ (k • Point.vcInvFun γ X₀.toAffine X))) (k • Point.vcInvFun γ X₁.toAffine y₁) := by
  subst e₂ hy₁ e₀ hg₀
  rw [castPt_rfl] at hQg ⊢
  rw [castPt_rfl]
  set T : (γ • X₀).toAffine.Point := Point.vcInvFun γ X₀.toAffine gr with hT
  set TX : (γ • X₀).toAffine.Point := Point.vcInvFun γ X₀.toAffine X with hTX
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
    hφ₂.coords φ₃ hφ₃spec.ker hφ₃spec.coords X
  refine ⟨by rw [hcurve, hVC], ?_⟩
  rw [map_nsmul]
  have h1 : φ TX = castPt hcurve.symm (φ₃ TX) := by
    simp only [hφ₃, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
      castPt_symm_castPt]
  rw [h1]
  have h2 : HEq (k • φ₃ TX)
      (k • Point.vcInvFun γ (X₀.fullKernelQuotient (M • gr) s).toAffine (φ₂ X)) :=
    ModularCurve.Point.heq_nsmul
      (V := ((γ • X₀).fullKernelQuotient (Point.vcInvFun γ X₀.toAffine (M • gr)) s).toAffine)
      (V' := (γ • X₀.fullKernelQuotient (M • gr) s).toAffine) (congrArg WeierstrassCurve.toAffine hVC.symm)
      k hHom.symm |>.symm
  have h3 : k • castPt hcurve.symm (φ₃ TX) = castPt hcurve.symm (k • φ₃ TX) := (map_nsmul _ _ _).symm
  rw [h3]
  exact HEq.trans (heq_castPt hcurve.symm (k • φ₃ TX)).symm h2

end Transport

section Torsion

variable {L : Type u} [Field L] [DecidableEq L] [IsAlgClosed L]

theorem natCast_ne_zero_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : (b : L) ≠ 0) : (a : L) ≠ 0 := by
  obtain ⟨c, rfl⟩ := hab
  intro h
  apply hb
  rw [Nat.cast_mul, h, zero_mul]

theorem torsion_mem_sup (V : WeierstrassCurve L) [V.IsElliptic] {q : ℕ} (hq : q.Prime)
    (hqL : (q : L) ≠ 0) (P₀ : V.toAffine.Point) (hP₀ : addOrderOf P₀ = q) (t : V.toAffine.Point)
    (ht : q • t = 0) (htP : t ∉ AddSubgroup.zmultiples P₀) (T : V.toAffine.Point) (hT : q • T = 0) :
    ∃ i j : ℤ, T = i • P₀ + j • t := by
  haveI : Fact q.Prime := ⟨hq⟩
  set Tq : AddSubgroup V.toAffine.Point :=
    (Submodule.torsionBy ℤ V.toAffine.Point (q : ℤ)).toAddSubgroup with hTq
  have hmemTq : ∀ P : V.toAffine.Point, P ∈ Tq ↔ q • P = 0 := by
    intro P
    rw [hTq, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, ← natCast_zsmul]
  have hcardTq : Nat.card Tq = q ^ 2 := by
    rw [hTq]
    exact WeierstrassCurve.card_torsion_of_isAlgClosed (K := L) V hqL
  haveI hfin : Finite Tq := Nat.finite_of_card_ne_zero (by rw [hcardTq]; exact pow_ne_zero 2 hq.ne_zero)
  have hqQ : q • P₀ = 0 := by rw [← hP₀]; exact addOrderOf_nsmul_eq_zero P₀
  set H : AddSubgroup V.toAffine.Point := AddSubgroup.zmultiples P₀ ⊔ AddSubgroup.zmultiples t with hH
  have hHle : H ≤ Tq := by
    rw [hH, sup_le_iff]
    constructor
    · rw [AddSubgroup.zmultiples_le]; exact (hmemTq P₀).mpr hqQ
    · rw [AddSubgroup.zmultiples_le]; exact (hmemTq t).mpr ht
  haveI : Finite H := Finite.of_injective (AddSubgroup.inclusion hHle) (AddSubgroup.inclusion_injective hHle)
  have hdvd : Nat.card H ∣ q ^ 2 := hcardTq ▸ AddSubgroup.card_dvd_of_le hHle
  obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  have hQle : AddSubgroup.zmultiples P₀ ≤ H := le_sup_left
  have hcardQ : Nat.card (AddSubgroup.zmultiples P₀) = q := by rw [Nat.card_zmultiples, hP₀]
  have hk2 : k = 2 := by
    interval_cases k
    · exfalso
      have hq1 : q ∣ 1 := by
        have := AddSubgroup.card_dvd_of_le hQle
        rwa [hcardQ, hkH, pow_zero] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp hq1)
    · exfalso
      rw [pow_one] at hkH
      have heq : AddSubgroup.zmultiples P₀ = H :=
        AddSubgroup.eq_of_le_of_card_ge hQle (by rw [hkH, hcardQ])
      have htH : t ∈ H := (le_sup_right : AddSubgroup.zmultiples t ≤ H) (AddSubgroup.mem_zmultiples t)
      rw [← heq] at htH
      exact htP htH
    · rfl
  rw [hk2] at hkH
  have hHeq : H = Tq := AddSubgroup.eq_of_le_of_card_ge hHle (by rw [hkH, hcardTq])
  have hTH : T ∈ H := by rw [hHeq]; exact (hmemTq T).mpr hT
  rw [hH] at hTH
  obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hTH
  obtain ⟨i, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  exact ⟨i, j, hyz.symm⟩

end Torsion

section Pins

variable {L : Type u} [Field L] [DecidableEq L] [IsAlgClosed L]

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

theorem pin_identity_dual (V : WeierstrassCurve L) [V.IsElliptic] {q d : ℕ} (hq0 : q ≠ 0) (hd0 : d ≠ 0)
    (hdqL : ((d * q : ℕ) : L) ≠ 0) (P₀ : V.toAffine.Point) (hP₀ : addOrderOf P₀ = q)
    (Φ : V.toAffine.Point →+ (V.fullKernelQuotient P₀ q).toAffine.Point) (hΦ : TSpec P₀ q Φ)
    (X : V.toAffine.Point) (hordΦX : addOrderOf (Φ X) = d * q)
    (hgen : ∀ Y : V.toAffine.Point, q • Y = 0 → Φ Y ∈ AddSubgroup.zmultiples (d • Φ X)) :
    (V.fullKernelQuotient P₀ q).cyclicQuotientJ (AddSubgroup.zmultiples (Φ X)) (d * q) =
      V.cyclicQuotientJ (AddSubgroup.zmultiples (q • X)) d := by
  haveI : NeZero q := ⟨hq0⟩
  haveI : NeZero d := ⟨hd0⟩
  have hqL : (q : L) ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_left q d) hdqL
  have hdL : (d : L) ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_right d q) hdqL

  have hΔ' : (V.fullKernelQuotient P₀ q).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero q V hqL P₀ hP₀
  haveI hV' : (V.fullKernelQuotient P₀ q).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩

  have hordd : addOrderOf (d • Φ X) = q := by
    have h1 := addOrderOf_div_nsmul hordΦX (Nat.mul_ne_zero hd0 hq0) (dvd_mul_left q d)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hq0)] at h1
  obtain ⟨Φ', hΦ'ker, hΦ'c⟩ :=
    WeierstrassCurve.exists_fullKernelHom (V.fullKernelQuotient P₀ q) hqL (d • Φ X) hordd
  have hΦ' : TSpec (d • Φ X) q Φ' := ⟨hΦ'ker, hΦ'c⟩

  rw [pin_identity (V.fullKernelQuotient P₀ q) hq0 hd0 hdqL (Φ X) hordΦX Φ' hΦ']

  have hΔ'' : ((V.fullKernelQuotient P₀ q).fullKernelQuotient (d • Φ X) q).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero q _ hqL (d • Φ X) hordd
  obtain ⟨C, hC, hbid⟩ :=
    WeierstrassCurve.exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul
      hqL V P₀ hP₀ hΔ' Φ hΦ.ker hΦ.coords (d • Φ X) hordd hgen hΔ'' Φ' hΦ'.ker hΦ'.coords

  have hpt : Φ' (Φ X) = castPt hC (Point.vcInvFun C V.toAffine (q • X)) := by
    have h := hbid X
    rw [natCast_zsmul] at h
    rw [← equivOfVariableChangeEq_symm_apply C V hC (q • X), ← h, Equiv.symm_apply_apply]
  rw [hpt, cyclicQuotientJ_zmultiples_castPt hC, cyclicQuotientJ_zmultiples_vcInvFun C V (q • X) d hdL]

theorem pin_first (V : WeierstrassCurve L) [V.IsElliptic] {N q e : ℕ} [NeZero N] [NeZero q] [NeZero e]
    (hcop : Nat.Coprime N q) (hNqL : ((N * q : ℕ) : L) ≠ 0) (heN : e ∣ N)
    (g t P₀ : V.toAffine.Point) (hg : addOrderOf g = N * q) (hqt : q • t = 0)
    (hP₀ : P₀ = e • ((N / e) • g))
    (Φ : V.toAffine.Point →+ (V.fullKernelQuotient P₀ q).toAffine.Point) (hΦ : TSpec P₀ q Φ) :
    V.cyclicQuotientJ (AddSubgroup.zmultiples ((N * q / (e * q)) • g)) (e * q) =
      (V.fullKernelQuotient P₀ q).cyclicQuotientJ
        (AddSubgroup.zmultiples (Φ ((N * q / e) • (g + t)))) e := by
  subst hP₀
  have hq : q ≠ 0 := NeZero.ne q
  have he0 : e ≠ 0 := NeZero.ne e
  have hNq0 : N * q ≠ 0 := Nat.mul_ne_zero (NeZero.ne N) hq
  have hdiv : N * q / e = N / e * q := (Nat.div_mul_right_comm heN q).symm
  have hpt : (N * q / e) • (g + t) = q • ((N / e) • g) := by
    rw [hdiv, smul_add, ← smul_smul, ← smul_smul, hqt, smul_zero, add_zero, smul_comm]
  rw [hpt, map_nsmul, Nat.mul_div_mul_right _ _ (Nat.pos_of_ne_zero hq)]
  have hordR : addOrderOf ((N / e) • g) = e * q := by
    rw [← Nat.mul_div_mul_right N e (Nat.pos_of_ne_zero hq)]
    exact addOrderOf_div_nsmul hg hNq0 (Nat.mul_dvd_mul_right heN q)
  have hordΦR : addOrderOf (Φ ((N / e) • g)) = e := addOrderOf_apply_eq Φ _ he0 hq hordR hΦ.ker
  have hcopq : q.Coprime (addOrderOf (Φ ((N / e) • g))) := by
    rw [hordΦR]; exact (Nat.Coprime.coprime_dvd_left heN hcop).symm
  rw [zmultiples_nsmul_eq_of_coprime hcopq]
  have hdsL : ((e * q : ℕ) : L) ≠ 0 := natCast_ne_zero_of_dvd (Nat.mul_dvd_mul_right heN q) hNqL
  exact pin_identity V hq he0 hdsL ((N / e) • g) hordR Φ hΦ

theorem pin_second (V : WeierstrassCurve L) [V.IsElliptic] {N q d : ℕ} [NeZero N] [NeZero q] [NeZero d]
    (hqp : q.Prime) (hcop : Nat.Coprime N q) (hNqL : ((N * q : ℕ) : L) ≠ 0) (hdN : d ∣ N)
    (g t P₀ : V.toAffine.Point) (hg : addOrderOf g = N * q) (hqt : q • t = 0)
    (htP : t ∉ AddSubgroup.zmultiples (N • g)) (hP₀ : P₀ = N • g)
    (Φ : V.toAffine.Point →+ (V.fullKernelQuotient P₀ q).toAffine.Point) (hΦ : TSpec P₀ q Φ) :
    V.cyclicQuotientJ (AddSubgroup.zmultiples ((N * q / d) • g)) d =
      (V.fullKernelQuotient P₀ q).cyclicQuotientJ
        (AddSubgroup.zmultiples (Φ ((N * q / (q * d)) • (g + t)))) (q * d) := by
  subst hP₀
  have hN : N ≠ 0 := NeZero.ne N
  have hq : q ≠ 0 := NeZero.ne q
  have hd0 : d ≠ 0 := NeZero.ne d
  have hNq0 : N * q ≠ 0 := Nat.mul_ne_zero hN hq
  have hqL : (q : L) ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_left q N) hNqL
  have hdqL : ((d * q : ℕ) : L) ≠ 0 := natCast_ne_zero_of_dvd (Nat.mul_dvd_mul_right hdN q) hNqL
  have hordNg : addOrderOf (N • g) = q := by
    have h1 := addOrderOf_div_nsmul hg hNq0 (dvd_mul_left q N)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hq)] at h1
  have hdiv : N * q / (q * d) = N / d := by
    rw [Nat.mul_comm q d, Nat.mul_div_mul_right _ _ (Nat.pos_of_ne_zero hq)]
  rw [hdiv]
  set X : V.toAffine.Point := (N / d) • (g + t) with hX

  have hordΦg : addOrderOf (Φ g) = N := addOrderOf_apply_eq Φ g hN hq hg hΦ.ker
  have hΦt0 : Φ t ≠ 0 := hΦ.apply_ne_zero htP
  have hqΦt : q • Φ t = 0 := by rw [← map_nsmul, hqt, map_zero]
  have hordΦt : addOrderOf (Φ t) = q := addOrderOf_eq_of_prime hqp hqΦt hΦt0
  have hordΦX : addOrderOf (Φ X) = d * q := by
    rw [hX, map_nsmul, map_add, smul_add]
    have h1 : addOrderOf ((N / d) • Φ g) = d := addOrderOf_div_nsmul hordΦg hN hdN
    have h2 : addOrderOf ((N / d) • Φ t) = q := by
      have hcopd : Nat.Coprime (N / d) q := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdN) hcop
      rw [Nat.Coprime.addOrderOf_nsmul (hordΦt.symm ▸ hcopd.symm), hordΦt]
    exact addOrderOf_add_eq_mul h1 h2 (Nat.Coprime.coprime_dvd_left hdN hcop)
  have hqX : q • X = (N * q / d) • g := by
    rw [hX, smul_add, smul_add, smul_comm q (N / d) t, hqt, smul_zero, add_zero, smul_smul,
      Nat.mul_comm q (N / d), ← Nat.div_mul_right_comm hdN q]

  have hΦP : Φ (N • g) = 0 := (hΦ.apply_eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples _)
  have hdX : d • Φ X = Φ (N • t) := by
    rw [hX, ← map_nsmul, smul_smul, Nat.mul_div_cancel' hdN, smul_add, map_add, hΦP, zero_add]
  have hgen : ∀ Y : V.toAffine.Point, q • Y = 0 → Φ Y ∈ AddSubgroup.zmultiples (d • Φ X) := by
    intro Y hY
    obtain ⟨i, j, rfl⟩ := torsion_mem_sup V hqp hqL (N • g) hordNg t hqt htP Y hY
    rw [hdX, map_add, map_zsmul, map_zsmul, hΦP, smul_zero, zero_add, map_nsmul]
    have hsub : AddSubgroup.zmultiples (N • Φ t) = AddSubgroup.zmultiples (Φ t) :=
      zmultiples_nsmul_eq_of_coprime (hordΦt.symm ▸ hcop)
    rw [hsub]
    exact AddSubgroup.zsmul_mem_zmultiples _ _
  rw [Nat.mul_comm q d, pin_identity_dual V hq hd0 hdqL (N • g) hordNg Φ hΦ X hordΦX hgen, hqX]

end Pins

section Main

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (N q : ℕ) [NeZero N] [NeZero q]

theorem jqNFull_eq_mk (L : ℕ) (d : ℕ) [NeZero d] (hd : d ∣ L)
    (h : qExpand K d (jqModC K) ∈ modularFunctionFieldFullC K L) :
    jqNFull K L d hd = ⟨qExpand K d (jqModC K), h⟩ := rfl

variable (τ : modularFunctionFieldFullC K (N * q) ≃ₐ[K] modularFunctionFieldFullC K (N * q))
  (hτ : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
    τ ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * q) (Dvd.dvd.mul_right hd q)⟩
        = ⟨qExpand K (d * q) (jqModC K), jqModCd_mem_full K (N * q) (Nat.mul_dvd_mul_right hd q)⟩
      ∧ τ ⟨qExpand K (d * q) (jqModC K), jqModCd_mem_full K (N * q) (Nat.mul_dvd_mul_right hd q)⟩
        = ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * q) (Dvd.dvd.mul_right hd q)⟩)

include hτ

theorem tau_symm_jqNFull_of_dvd (d : ℕ) [NeZero d] (hd : d ∣ N) [NeZero (d * q)]
    (h₁ : d ∣ N * q) :
    τ.symm (jqNFull K (N * q) d h₁) = jqNFull K (N * q) (d * q) (Nat.mul_dvd_mul_right hd q) := by
  rw [AlgEquiv.symm_apply_eq]
  exact ((hτ d inferInstance hd).2).symm

theorem tau_symm_jqNFull_of_eq_mul (e d : ℕ) [NeZero e] [NeZero d] (he : e = q * d) (hd : d ∣ N)
    (h₁ : e ∣ N * q) :
    τ.symm (jqNFull K (N * q) e h₁) = jqNFull K (N * q) d (Dvd.dvd.mul_right hd q) := by
  subst he
  rw [AlgEquiv.symm_apply_eq]
  have h := (hτ d inferInstance hd).1
  have hd' : jqNFull K (N * q) d (Dvd.dvd.mul_right hd q) =
      ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * q) (Dvd.dvd.mul_right hd q)⟩ := rfl
  rw [hd', h]
  apply Subtype.ext
  show qExpand K (q * d) (jqModC K) = qExpand K (d * q) (jqModC K)
  rw [qExpand_congr (Nat.mul_comm q d)]

set_option maxHeartbeats 1600000 in
variable {K N q} in

theorem isModuliPlaceOf_congr (hqp : q.Prime) (hqN : ¬ q ∣ N) (hNq : ((N * q : ℕ) : K) ≠ 0)
    (E : WeierstrassCurve K) [hE : E.IsElliptic] (g₀ : E.toAffine.Point) (hg₀ : addOrderOf g₀ = N * q)
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = q)
    (hQg : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (N • g₀))
    (hΔ : (E.fullKernelQuotient Q q).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.fullKernelQuotient Q q).toAffine.Point) (hφ : TSpec Q q φ)
    (g₁ : (E.fullKernelQuotient Q q).toAffine.Point) (hg₁ : addOrderOf g₁ = N * q)
    (hCC'' : φ g₀ ∈ AddSubgroup.zmultiples g₁)
    (hqC'' : ∀ T : E.toAffine.Point, q • T = 0 → φ T ∈ AddSubgroup.zmultiples g₁)
    {Ω : Type u} [iF : Field Ω] [iD : DecidableEq Ω] [iA : Algebra K Ω]
    (D : ModuliTestDatum K (N * q) (Quot.mk _ (⟨E, hE, g₀, hg₀⟩ : Gamma0Pair (N * q) K)) Ω)
    (hcardq : Nat.card {P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point // q • P = 0}
        = q ^ 2)
    (hinj : ∀ [DecidableEq (ResidueField D.W.toValuationSubring)]
      (P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point),
        q • P = 0 → reduceHom D.map_Δ_ne_zero P = 0 → P = 0) :
    IsModuliPlaceOf K (N * q)
      (Quot.mk _ (⟨E.fullKernelQuotient Q q, ⟨isUnit_iff_ne_zero.mpr hΔ⟩, g₁, hg₁⟩ :
        Gamma0Pair (N * q) K))
      (Place.congrEquiv τ.toRingEquiv (fun c => τ.commutes c) D.place) := by
  letI := Classical.decEq (ResidueField D.W.toValuationSubring)
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne q)⟩
  have hN : N ≠ 0 := NeZero.ne N
  have hq : q ≠ 0 := NeZero.ne q
  have hNq0 : N * q ≠ 0 := Nat.mul_ne_zero hN hq
  have hcop : Nat.Coprime N q := ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqN).symm

  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_left q N) hNq
  have hqΩ : (q : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero _).mpr hqK
  have hqκ : (q : ResidueField D.W.toValuationSubring) ≠ 0 := by
    intro h0
    apply hqK
    have := congrArg D.res h0
    rwa [map_natCast, map_zero] at this

  obtain ⟨hordgb, hx⟩ := D.reduction
  set gen := D.gen with hgen
  set P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point := N • gen with hPdef
  have hordP : addOrderOf P = q := by
    have h1 := addOrderOf_div_nsmul D.addOrderOf_gen hNq0 (dvd_mul_left q N)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hq)] at h1
  have hredP : reduceHom D.map_Δ_ne_zero P = N • reduceHom D.map_Δ_ne_zero gen := map_nsmul _ _ _
  have hordPb : addOrderOf (reduceHom D.map_Δ_ne_zero P) = q := by
    rw [hredP]
    have h1 := addOrderOf_div_nsmul hordgb hNq0 (dvd_mul_left q N)
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hq)] at h1

  obtain ⟨t, htq, htP⟩ := exists_torsion_not_mem_of_card hqp.one_lt P hordP hcardq
  have htbq : q • reduceHom D.map_Δ_ne_zero t = 0 := by rw [← map_nsmul, htq, map_zero]
  have htbP : reduceHom D.map_Δ_ne_zero t ∉ AddSubgroup.zmultiples (reduceHom D.map_Δ_ne_zero P) := by
    intro hmem
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have h0 : reduceHom D.map_Δ_ne_zero (t - z • P) = 0 := by rw [map_sub, map_zsmul, hz, sub_self]
    have hqt : q • (t - z • P) = 0 := by
      have hqP : q • P = 0 := by
        have h := addOrderOf_nsmul_eq_zero P
        rwa [hordP] at h
      rw [nsmul_sub, htq, smul_comm, hqP, smul_zero, sub_zero]
    have := hinj (t - z • P) hqt h0
    rw [sub_eq_zero] at this
    exact htP (this ▸ AddSubgroup.zsmul_mem_zmultiples P z)

  obtain ⟨W', hW'L, hW'k, -⟩ :=
    WeierstrassCurve.exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom
      D.map_Δ_ne_zero q P hordPb
  have hΔk : ((D.curve.map (residue D.W.toValuationSubring)).fullKernelQuotient
      (reduceHom D.map_Δ_ne_zero P) q).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero q _ hqκ _ hordPb
  have hΔW' : (W'.map (residue D.W.toValuationSubring)).Δ ≠ 0 := by rw [hW'k]; exact hΔk

  obtain ⟨Φ, hΦker, hΦc⟩ :=
    WeierstrassCurve.exists_fullKernelHom (D.curve.map D.W.toValuationSubring.subtype) hqΩ P hordP
  have hΦ : TSpec P q Φ := ⟨hΦker, hΦc⟩
  obtain ⟨φk, hφkker, hφkc⟩ := WeierstrassCurve.exists_fullKernelHom
    (D.curve.map (residue D.W.toValuationSubring)) hqκ (reduceHom D.map_Δ_ne_zero P) hordPb
  have hφk : TSpec (reduceHom D.map_Δ_ne_zero P) q φk := ⟨hφkker, hφkc⟩

  set gen' : (W'.map D.W.toValuationSubring.subtype).toAffine.Point :=
    castPt hW'L.symm (Φ (gen + t)) with hgen'
  have hred : reduceHom hΔW' gen' =
      castPt hW'k.symm (φk (reduceHom D.map_Δ_ne_zero (gen + t))) := by
    have hheq := WeierstrassCurve.heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient
      D.map_Δ_ne_zero q P hordPb W' hW'L hW'k hΔW' Φ hΦ.ker hΦ.coords φk hφk.ker hφk.coords
      (gen + t) gen' (heq_castPt hW'L.symm (Φ (gen + t))).symm
    rw [← castPt_eq_iff_heq hW'k] at hheq
    rw [← hheq, castPt_symm_castPt]

  have hordΦgen : addOrderOf (Φ gen) = N := addOrderOf_apply_eq Φ gen hN hq D.addOrderOf_gen hΦ.ker
  have hΦt0 : Φ t ≠ 0 := hΦ.apply_ne_zero htP
  have hqΦt : q • Φ t = 0 := by rw [← map_nsmul, htq, map_zero]
  have hordΦt : addOrderOf (Φ t) = q := addOrderOf_eq_of_prime hqp hqΦt hΦt0
  have hordsum : addOrderOf (Φ (gen + t)) = N * q := by
    rw [map_add]; exact addOrderOf_add_eq_mul hordΦgen hordΦt hcop
  have hordgen' : addOrderOf gen' = N * q := by rw [hgen', addOrderOf_castPt, hordsum]

  have hordφkgb : addOrderOf (φk (reduceHom D.map_Δ_ne_zero gen)) = N :=
    addOrderOf_apply_eq φk _ hN hq hordgb (by rw [hφk.ker, hredP])
  have hφkt0 : φk (reduceHom D.map_Δ_ne_zero t) ≠ 0 := hφk.apply_ne_zero htbP
  have hqφkt : q • φk (reduceHom D.map_Δ_ne_zero t) = 0 := by rw [← map_nsmul, htbq, map_zero]
  have hordφkt : addOrderOf (φk (reduceHom D.map_Δ_ne_zero t)) = q :=
    addOrderOf_eq_of_prime hqp hqφkt hφkt0
  have hordred : addOrderOf (reduceHom hΔW' gen') = N * q := by
    rw [hred, addOrderOf_castPt, map_add, map_add]
    exact addOrderOf_add_eq_mul hordφkgb hordφkt hcop

  have hordφ : addOrderOf (φ g₀) = N := addOrderOf_apply_eq φ g₀ hN hq hg₀ (by rw [hφ.ker, hQg])
  have hφQ0 : ∀ T : E.toAffine.Point, T ∈ AddSubgroup.zmultiples (N • g₀) → φ T = 0 := fun T hT =>
    (hφ.apply_eq_zero_iff T).mpr (hQg ▸ hT)

  have hclass : ModuliPoint.map D.res
      (Quot.mk _ (⟨W'.map (residue D.W.toValuationSubring), ⟨isUnit_iff_ne_zero.mpr hΔW'⟩,
        reduceHom hΔW' gen', hordred⟩ : Gamma0Pair (N * q) (ResidueField D.W.toValuationSubring))) =
      Quot.mk _ (⟨E.fullKernelQuotient Q q, ⟨isUnit_iff_ne_zero.mpr hΔ⟩, g₁, hg₁⟩ :
        Gamma0Pair (N * q) K) := by

    rw [ModuliPoint.map_mk] at hx ⊢
    obtain ⟨γ, e₀, k, hk, hheq⟩ := (ModuliPoint.mk_eq_mk_iff_step _ _).mp hx
    simp only [Gamma0Pair.map_toCurve, Gamma0Pair.map_gen] at e₀ hheq

    set X₀ : WeierstrassCurve K := (D.curve.map (residue D.W.toValuationSubring)).map D.res with hX₀
    set gr : X₀.toAffine.Point := mapPoint D.res (reduceHom D.map_Δ_ne_zero gen) with hgr
    set tr : X₀.toAffine.Point := mapPoint D.res (reduceHom D.map_Δ_ne_zero t) with htr
    have hordgr : addOrderOf gr = N * q := (addOrderOf_mapPoint D.res _).trans hordgb
    have hg₀' : g₀ = castPt e₀ (k • Point.vcInvFun γ X₀.toAffine gr) :=
      ((castPt_eq_iff_heq e₀ _ _).mpr hheq.symm).symm
    have hqtr : q • tr = 0 := by rw [htr, ← mapPoint_nsmul, htbq, mapPoint_zero]
    have hPres : mapPoint D.res (reduceHom D.map_Δ_ne_zero P) = N • gr := by
      rw [hredP, mapPoint_nsmul]
    have htrP : tr ∉ AddSubgroup.zmultiples (N • gr) := by
      rw [← hPres]; exact not_mem_zmultiples_mapPoint D.res htbP

    have hordNgr : addOrderOf (N • gr) = q := by
      have h1 := addOrderOf_div_nsmul hordgr hNq0 (dvd_mul_left q N)
      rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hq)] at h1
    obtain ⟨φ₂, hφ₂ker, hφ₂c⟩ := WeierstrassCurve.exists_fullKernelHom X₀ hqK (N • gr) hordNgr
    have hφ₂ : TSpec (N • gr) q φ₂ := ⟨hφ₂ker, hφ₂c⟩

    have hBC := hφk.mapPoint_apply D.res hordPb hPres hφ₂ (reduceHom D.map_Δ_ne_zero (gen + t))

    have e₂ : X₀.fullKernelQuotient (N • gr) q = (W'.map (residue D.W.toValuationSubring)).map D.res :=
      (map_fullKernelQuotient D.res _ hordPb hPres).symm.trans (congrArg (fun W => W.map D.res) hW'k.symm)
    have hsum : mapPoint D.res (reduceHom D.map_Δ_ne_zero (gen + t)) = gr + tr := by
      rw [map_add, mapPoint_add]
    have hy₁ : mapPoint D.res (reduceHom hΔW' gen') = castPt e₂ (φ₂ (gr + tr)) := by
      rw [hred, mapPoint_castPt, ← castPt_symm_castPt (map_fullKernelQuotient D.res _ hordPb hPres)
        (mapPoint D.res (φk (reduceHom D.map_Δ_ne_zero (gen + t)))), ← hBC, hsum, castPt_castPt]

    obtain ⟨e₁, hstep⟩ := step_transport hN hq X₀ gr hordgr γ E e₀ k hk g₀ hg₀' Q hQ hQg φ hφ φ₂ hφ₂
      ((W'.map (residue D.W.toValuationSubring)).map D.res) e₂ (gr + tr)
      (mapPoint D.res (reduceHom hΔW' gen')) hy₁
    set t₀ : E.toAffine.Point := castPt e₀ (Point.vcInvFun γ X₀.toAffine tr) with ht₀
    have hZ : castPt e₀ (k • Point.vcInvFun γ X₀.toAffine (gr + tr)) = g₀ + k • t₀ := by
      rw [hg₀', ht₀, Point.vcInvFun_add, smul_add, map_add, map_nsmul, map_nsmul]
    rw [hZ] at hstep

    have hqt₀ : q • t₀ = 0 := by
      rw [ht₀, ← map_nsmul, nsmul_vcInvFun, hqtr, Point.vcInvFun_zero, map_zero]
    have ht₀Q : t₀ ∉ AddSubgroup.zmultiples (N • g₀) := by
      intro hmem
      apply htrP
      obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem

      have h1 : Point.vcInvFun γ X₀.toAffine tr =
          Point.vcInvFun γ X₀.toAffine ((z * k) • (N • gr)) := by
        apply (castPt e₀).injective
        rw [← ht₀, ← hz, hg₀']
        rw [← map_nsmul, ← map_zsmul, nsmul_vcInvFun, nsmul_vcInvFun, zsmul_vcInvFun]
        congr 2
        rw [mul_zsmul, natCast_zsmul, smul_comm N k gr]
      rw [vcInvFun_injective γ X₀ h1]
      exact AddSubgroup.zsmul_mem_zmultiples _ _

    have hφkt₀ : φ (k • t₀) ≠ 0 := by
      intro h0
      have hmem : k • t₀ ∈ AddSubgroup.zmultiples (N • g₀) := hQg ▸ (hφ.apply_eq_zero_iff _).mp h0

      have hordt₀ : addOrderOf t₀ = q := by
        refine addOrderOf_eq_of_prime hqp hqt₀ ?_
        rintro h00
        exact ht₀Q (h00 ▸ zero_mem _)
      have hkq : k.Coprime (addOrderOf t₀) := hordt₀ ▸ Nat.Coprime.coprime_dvd_right (dvd_mul_left q N) hk
      have heq : AddSubgroup.zmultiples (k • t₀) = AddSubgroup.zmultiples t₀ :=
        zmultiples_nsmul_eq_of_coprime hkq
      have : t₀ ∈ AddSubgroup.zmultiples (N • g₀) := by
        have h2 : AddSubgroup.zmultiples (k • t₀) ≤ AddSubgroup.zmultiples (N • g₀) :=
          AddSubgroup.zmultiples_le.mpr hmem
        rw [heq] at h2
        exact h2 (AddSubgroup.mem_zmultiples t₀)
      exact ht₀Q this
    have hqφkt₀ : q • φ (k • t₀) = 0 := by rw [← map_nsmul, smul_comm, hqt₀, smul_zero, map_zero]
    have hordφZ : addOrderOf (φ (g₀ + k • t₀)) = N * q := by
      rw [map_add]
      exact addOrderOf_add_eq_mul hordφ (addOrderOf_eq_of_prime hqp hqφkt₀ hφkt₀) hcop
    have hZmem : φ (g₀ + k • t₀) ∈ AddSubgroup.zmultiples g₁ := by
      rw [map_add, map_nsmul]
      exact add_mem hCC'' (AddSubgroup.nsmul_mem _ (hqC'' t₀ hqt₀) k)
    have hZgen : AddSubgroup.zmultiples (φ (g₀ + k • t₀)) = AddSubgroup.zmultiples g₁ :=
      zmultiples_eq_of_mem_of_addOrderOf_eq hNq0 hordφZ hg₁ hZmem

    haveI hE₁ : (E.fullKernelQuotient Q q).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    rw [← ModuliPoint.mk_eq_mk_of_zmultiples_eq hordφZ hg₁ hZgen]
    exact (ModuliPoint.mk_eq_mk_iff_step _ _).mpr ⟨γ, e₁, k, hk, hstep⟩

  refine ⟨Ω, iF, iD, iA,
    { W := D.W
      curve := W'
      map_Δ_ne_zero := hΔW'
      gen := gen'
      addOrderOf_gen := hordgen'
      res := D.res
      res_algebraMap := D.res_algebraMap
      reduction := ⟨hordred, hclass⟩
      emb := D.emb.comp τ.symm.toAlgHom
      emb_jqNFull := ?_ }, ?_⟩
  ·
    intro Ω' _ _ _ _ e _ he
    set ι : Ω →+* Ω' := algebraMap Ω Ω' with hι
    have hNqΩ' : ((N * q : ℕ) : Ω') ≠ 0 := by
      rw [← map_natCast ι, map_ne_zero, ← map_natCast (algebraMap K Ω), map_ne_zero]
      exact hNq
    have hqΩ' : (q : Ω') ≠ 0 := natCast_ne_zero_of_dvd (dvd_mul_left q N) hNqΩ'

    set V : WeierstrassCurve Ω' := (D.curve.map D.W.toValuationSubring.subtype).map ι with hV
    set gι : V.toAffine.Point := mapPoint ι gen with hgι
    set tι : V.toAffine.Point := mapPoint ι t with htι
    have hordgι : addOrderOf gι = N * q := (addOrderOf_mapPoint ι gen).trans D.addOrderOf_gen
    have hqtι : q • tι = 0 := by rw [htι, ← mapPoint_nsmul, htq, mapPoint_zero]
    have hPι0 : mapPoint ι P = N • gι := by rw [hPdef, mapPoint_nsmul]
    have htιP : tι ∉ AddSubgroup.zmultiples (N • gι) := by
      rw [← hPι0]; exact not_mem_zmultiples_mapPoint ι htP
    haveI hVell : V.IsElliptic := by rw [hV]; infer_instance
    have hordPι : addOrderOf (mapPoint ι P) = q := (addOrderOf_mapPoint ι P).trans hordP
    obtain ⟨Φι, hΦιker, hΦιc⟩ := WeierstrassCurve.exists_fullKernelHom V hqΩ' _ hordPι
    have hΦι : TSpec (mapPoint ι P) q Φι := ⟨hΦιker, hΦιc⟩
    have hBC := hΦ.mapPoint_apply ι hordP rfl hΦι (gen + t)
    have e₄ : V.fullKernelQuotient (mapPoint ι P) q = (W'.map D.W.toValuationSubring.subtype).map ι :=
      (map_fullKernelQuotient ι _ hordP rfl).symm.trans (congrArg (fun W => W.map ι) hW'L.symm)

    have h4 : ∀ m : ℕ, mapPoint ι (m • gen') = castPt e₄ (Φι (m • (gι + tι))) := by
      intro m
      rw [mapPoint_nsmul, hgen', mapPoint_castPt,
        ← castPt_symm_castPt (map_fullKernelQuotient ι _ hordP rfl) (mapPoint ι (Φ (gen + t))),
        ← hBC, castPt_castPt, ← map_nsmul, ← map_nsmul, mapPoint_add]
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom]
    by_cases hqe : q ∣ e
    ·
      obtain ⟨d, hed⟩ := hqe
      have hdN : d ∣ N := by
        have h1 : q * d ∣ q * N := by rw [← hed, Nat.mul_comm q N]; exact he
        exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hq) h1
      have hd0 : d ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hdN)
      haveI : NeZero d := ⟨hd0⟩
      rw [tau_symm_jqNFull_of_eq_mul K N q τ hτ e d hed hdN he, D.emb_jqNFull Ω' d, mapPoint_nsmul]
      subst hed
      rw [h4, cyclicQuotientJ_zmultiples_castPt e₄]
      exact pin_second V hqp hcop hNqΩ' hdN gι tι (mapPoint ι P) hordgι hqtι htιP hPι0 Φι hΦι
    ·
      have hdN : e ∣ N := by
        have hcope : Nat.Coprime e q := (Nat.Prime.coprime_iff_not_dvd hqp).mpr hqe |>.symm
        exact hcope.dvd_of_dvd_mul_right he
      haveI : NeZero (e * q) := ⟨Nat.mul_ne_zero (NeZero.ne e) hq⟩
      have hPι : mapPoint ι P = e • ((N / e) • gι) := by
        rw [hPι0, smul_smul, Nat.mul_div_cancel' hdN]
      rw [tau_symm_jqNFull_of_dvd K N q τ hτ e hdN he, D.emb_jqNFull Ω' (e * q), mapPoint_nsmul, h4,
        cyclicQuotientJ_zmultiples_castPt e₄]
      exact pin_first V hcop hNqΩ' hdN gι tι (mapPoint ι P) hordgι hqtι hPι Φι hΦι
  ·
    show (Place.congrEquiv τ.toRingEquiv (fun c => τ.commutes c) D.place).toValuationSubring =
      D.W.toValuationSubring.comap (D.emb.comp τ.symm.toAlgHom).toRingHom
    ext f
    exact Iff.rfl

end Main

end P2MKcAtkinLehnerB

end

p2m_open "AlgebraicCurve ModularCurve WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine P2MW.S_ModularCurve_congrEquiv_moduliPlace_eq_moduliPlace_fullKernelQuotient_of_atkinLehner.P2MKcAtkinLehnerB"

universe u in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (hNq : ((N * q : ℕ) : K) ≠ 0)
    (huniq : ∀ (x : ModuliPoint (N * q) K) (v v' : Place K (modularFunctionFieldFullC K (N * q))),
      IsModuliPlaceOf K (N * q) x v → IsModuliPlaceOf K (N * q) x v' → v = v')
    (hexT : ∀ x : ModuliPoint (N * q) K,
      ∃ (Ω : Type u) (_ : Field Ω) (_ : DecidableEq Ω) (_ : Algebra K Ω)
        (D : ModuliTestDatum K (N * q) x Ω),
        Nat.card {P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point // q • P = 0}
            = q ^ 2 ∧
        ∀ [DecidableEq (IsLocalRing.ResidueField D.W.toValuationSubring)]
          (P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point),
          q • P = 0 → reduceHom D.map_Δ_ne_zero P = 0 → P = 0)
    (τ : modularFunctionFieldFullC K (N * q) ≃ₐ[K] modularFunctionFieldFullC K (N * q))
    (hτ : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
      τ ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * q) (Dvd.dvd.mul_right hd q)⟩
          = ⟨qExpand K (d * q) (jqModC K), jqModCd_mem_full K (N * q) (Nat.mul_dvd_mul_right hd q)⟩
        ∧ τ ⟨qExpand K (d * q) (jqModC K), jqModCd_mem_full K (N * q) (Nat.mul_dvd_mul_right hd q)⟩
          = ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * q) (Dvd.dvd.mul_right hd q)⟩)
    (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) (hC : IsAddCyclic C ∧ Nat.card C = N * q)
    (Q : E.toAffine.Point) (hQC : Q ∈ C) (hQ : addOrderOf Q = q)
    (hΔ : (E.fullKernelQuotient Q q).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.fullKernelQuotient Q q).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : E.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (q - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (q - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (C'' : AddSubgroup (E.fullKernelQuotient Q q).toAffine.Point)
    (hC'' : IsAddCyclic C'' ∧ Nat.card C'' = N * q) (hCC'' : ∀ T ∈ C, φ T ∈ C'')
    (hqC'' : ∀ T : E.toAffine.Point, q • T = 0 → φ T ∈ C'') :
    Place.congrEquiv τ.toRingEquiv (fun c => τ.commutes c) (moduliPlace K (N * q) E C) =
      moduliPlace K (N * q) (E.fullKernelQuotient Q q) C'' := by
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne q)⟩
  haveI hE₁ : (E.fullKernelQuotient Q q).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  obtain ⟨g₀, hg₀, rfl⟩ := exists_generator_of_isAddCyclic C hC
  obtain ⟨g₁, hg₁, rfl⟩ := exists_generator_of_isAddCyclic C'' hC''
  have hQg : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (N • g₀) :=
    zmultiples_eq_zmultiples_nsmul (NeZero.ne N) (NeZero.ne q) hg₀ hQC hQ
  have hφspec : TSpec Q q φ := ⟨hφker, hφ⟩

  rw [moduliPlace_zmultiples K (N * q) E g₀ hg₀, moduliPlace_zmultiples K (N * q) _ g₁ hg₁]
  obtain ⟨Ω, _, _, _, D, hcard, hinj⟩ := hexT (Quot.mk _ ⟨E, ‹_›, g₀, hg₀⟩)
  rw [ModuliTestDatum.moduliPlaceOfPoint_eq_place K (N * q) (huniq _) D]
  have hres := isModuliPlaceOf_congr τ hτ hq hqN hNq E g₀ hg₀ Q hQ hQg hΔ φ hφspec g₁ hg₁
    (hCC'' g₀ (AddSubgroup.mem_zmultiples g₀)) hqC'' D hcard (fun P => hinj P)
  exact (moduliPlaceOfPoint_eq_of_forall_eq K (N * q) (huniq _) hres).symm

end S_ModularCurve_congrEquiv_moduliPlace_eq_moduliPlace_fullKernelQuotient_of_atkinLehner
end P2MW
export P2MW.S_ModularCurve_congrEquiv_moduliPlace_eq_moduliPlace_fullKernelQuotient_of_atkinLehner (solution)

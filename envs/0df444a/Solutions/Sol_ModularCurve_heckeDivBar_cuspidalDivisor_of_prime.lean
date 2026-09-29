-- Prove2me | solution 1 for ModularCurve.heckeDivBar_cuspidalDivisor_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/26c019aa-01c7-5eea-84e5-50fe71287b6c

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_heckeBetaBar_coeffEmb
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_order_qExpand
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
import Theorems.Thm_ModularCurve_isCusp_cuspZeroBar
import Theorems.Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_towerInclBar_finiteAlong
import Theorems.Thm_ModularCurve_towerSubstBar_finiteAlong
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_ModularCurve_heckeDivBar_cuspidalDivisor
import Theorems.Thm_ModularCurve_deg_cuspInftyBar
import Theorems.Thm_ModularCurve_deg_cuspZeroBar
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.FieldTheory.Relrank
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFull_prime
import Theorems.Thm_ModularCurve_relfinrank_full_mul_prime
import Mathlib.FieldTheory.Perfect
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_of_prime
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~mem_restrictAlong_iff IntermediateField"

namespace PLSol

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem deg_restrictAlong_mul_inertiaDegAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

theorem isIntegral_of_finiteAlong (φ : F →ₐ[K] F') (h : FiniteAlong K φ) : φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := h
  intro x
  exact Algebra.IsIntegral.isIntegral (R := F) x

theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    0 < w.ramificationIndexAlong φ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos

theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] (v : Place K F) (hv : v.deg ≠ 0) : v.deg = 1 := by
  haveI : Module.Finite K v.ResidueField := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hv)
  have e : K ≃ₗ[K] v.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField) (IsAlgClosed.algebraMap_bijective_of_isIntegral)
  unfold Place.deg
  rw [← e.finrank_eq, Module.finrank_self]

end Generic

section Level

local notation "𝕂" => AlgebraicClosure ℚ

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hl : Fact ℓ.Prime]

scoped instance : NeZero p := ⟨hp.out.ne_zero⟩

abbrev alpha' : modularFunctionFieldBar ℓ →ₐ[𝕂] modularFunctionFieldBar (p * ℓ) :=
  towerInclBar 𝕂 (Dvd.intro_left p rfl)

abbrev beta' : modularFunctionFieldBar ℓ →ₐ[𝕂] modularFunctionFieldBar (p * ℓ) :=
  towerSubstBar 𝕂 ℓ p (dvd_of_eq (Nat.mul_comm ℓ p))

theorem alpha'_integral : (alpha' p ℓ).toRingHom.IsIntegral :=
  isIntegral_of_finiteAlong _ (towerInclBar_finiteAlong 𝕂 _)

theorem beta'_integral : (beta' p ℓ).toRingHom.IsIntegral :=
  isIntegral_of_finiteAlong _ (towerSubstBar_finiteAlong 𝕂 p _)

abbrev jb (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (jq_mem_full N)⟩

abbrev jdb (N d : ℕ) [NeZero N] [NeZero d] (hd : d ∣ N) : modularFunctionFieldBar N :=
  ⟨coeffEmb 𝕂 (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange 𝕂 (jqd_mem_full N hd)⟩

omit hp hl in
theorem hdl : ℓ ∣ p * ℓ := Dvd.intro_left p rfl
omit hp hl in
theorem hdp : p ∣ p * ℓ := Dvd.intro ℓ rfl

theorem alpha_jb : heckeAlphaBar 𝕂 p ℓ (jb p) = jb (p * ℓ) := Subtype.ext (coe_heckeAlphaBar p ℓ (jb p))

theorem beta_jb : heckeBetaBar 𝕂 p ℓ (jb p) = jdb (p * ℓ) ℓ (hdl p ℓ) :=
  Subtype.ext (heckeBetaBar_coeffEmb p ℓ (jq_mem_full p))

theorem alpha_jdb : heckeAlphaBar 𝕂 p ℓ (jdb p p dvd_rfl) = jdb (p * ℓ) p (hdp p ℓ) :=
  Subtype.ext (coe_heckeAlphaBar p ℓ _)

theorem beta_jdb : heckeBetaBar 𝕂 p ℓ (jdb p p dvd_rfl) = jdb (p * ℓ) (p * ℓ) dvd_rfl := by
  apply Subtype.ext
  rw [Subtype.coe_mk, heckeBetaBar_coeffEmb p ℓ (jqd_mem_full p dvd_rfl), qExpand_qExpand,
    qExpand_congr (Nat.mul_comm ℓ p) jq]

theorem alpha'_jb : alpha' p ℓ (jb ℓ) = jb (p * ℓ) := Subtype.ext (coe_towerInclBar 𝕂 _ _)

theorem alpha'_jdb : alpha' p ℓ (jdb ℓ ℓ dvd_rfl) = jdb (p * ℓ) ℓ (hdl p ℓ) := Subtype.ext (coe_towerInclBar 𝕂 _ _)

theorem beta'_jb : beta' p ℓ (jb ℓ) = jdb (p * ℓ) p (hdp p ℓ) := by
  apply Subtype.ext
  rw [coe_towerSubstBar, Subtype.coe_mk, ← coeffEmb_qExpand]

theorem beta'_jdb : beta' p ℓ (jdb ℓ ℓ dvd_rfl) = jdb (p * ℓ) (p * ℓ) dvd_rfl := by
  apply Subtype.ext
  rw [coe_towerSubstBar, Subtype.coe_mk, ← coeffEmb_qExpand, qExpand_qExpand]

theorem ord_inf_jb (N : ℕ) [NeZero N] : (cuspInftyBar N).ord (jb N) = -1 := ord_cuspInftyBar_coeffEmb_jq N
theorem ord_inf_jdb (N : ℕ) [NeZero N] : (cuspInftyBar N).ord (jdb N N dvd_rfl) = -N :=
  ord_cuspInftyBar_coeffEmb_qExpand N N dvd_rfl
theorem ord_zero_jb (N : ℕ) [Fact N.Prime] : (cuspZeroBar N).ord (jb N) = -N :=
  ord_cuspZeroBar_coeffEmb_jq N (isFrickeAutFull_frickeInvolutionFull_prime N)
theorem ord_zero_jdb (N : ℕ) [Fact N.Prime] : (cuspZeroBar N).ord (jdb N N dvd_rfl) = -1 := by
  have h := ord_cuspZeroBar_coeffEmb_qExpand N (isFrickeAutFull_frickeInvolutionFull_prime N) 1 N (one_mul N)
  simpa using h

theorem zero_ne_inf (N : ℕ) [hN : Fact N.Prime] : cuspZeroBar N ≠ cuspInftyBar N :=
  cuspZeroBar_ne_cuspInftyBar N (isFrickeAutFull_frickeInvolutionFull_prime N) hN.out.one_lt

theorem isIntegral_adjoin_of_eval₂ (M : ℕ) [NeZero M] (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    (x y : LaurentSeries ℚ) (hx : x ∈ modularFunctionFieldFull M) (hy : y ∈ modularFunctionFieldFull M)
    (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    IsIntegral (Algebra.adjoin 𝕂 {(⟨coeffEmb 𝕂 x, coeffEmb_mem_laurentBaseChange 𝕂 hx⟩ : modularFunctionFieldBar M)})
      (⟨coeffEmb 𝕂 y, coeffEmb_mem_laurentBaseChange 𝕂 hy⟩ : modularFunctionFieldBar M) := by
  set X' : modularFunctionFieldBar M := ⟨coeffEmb 𝕂 x, coeffEmb_mem_laurentBaseChange 𝕂 hx⟩ with hX'
  set Y' : modularFunctionFieldBar M := ⟨coeffEmb 𝕂 y, coeffEmb_mem_laurentBaseChange 𝕂 hy⟩ with hY'
  let φ : Polynomial ℤ →+* Algebra.adjoin 𝕂 ({X'} : Set (modularFunctionFieldBar M)) :=
    (Polynomial.aeval (R := ℤ) (⟨X', Algebra.self_mem_adjoin_singleton 𝕂 X'⟩ :
      Algebra.adjoin 𝕂 ({X'} : Set (modularFunctionFieldBar M)))).toRingHom
  refine ⟨Φ.map φ, hΦ.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap (Algebra.adjoin 𝕂 ({X'} : Set (modularFunctionFieldBar M))) (modularFunctionFieldBar M)).comp φ
      = (Polynomial.aeval (R := ℤ) X').toRingHom := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [φ]
  rw [hcomp]
  apply Subtype.val_injective
  show ((Φ.eval₂ (Polynomial.aeval (R := ℤ) X').toRingHom Y' : modularFunctionFieldBar M) : LaurentSeries 𝕂) = ((0 : modularFunctionFieldBar M) : LaurentSeries 𝕂)
  rw [show (((Φ.eval₂ (Polynomial.aeval (R := ℤ) X').toRingHom Y') : modularFunctionFieldBar M) : LaurentSeries 𝕂)
      = algebraMap (modularFunctionFieldBar M) (LaurentSeries 𝕂) (Φ.eval₂ (Polynomial.aeval (R := ℤ) X').toRingHom Y') from rfl,
    Polynomial.hom_eval₂]
  have hc2 : (algebraMap (modularFunctionFieldBar M) (LaurentSeries 𝕂)).comp (Polynomial.aeval (R := ℤ) X').toRingHom
      = (coeffEmb 𝕂).comp (Polynomial.aeval (R := ℤ) x).toRingHom := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
    rfl
  rw [hc2, show algebraMap (modularFunctionFieldBar M) (LaurentSeries 𝕂) Y' = coeffEmb 𝕂 y from rfl,
    ← Polynomial.hom_eval₂, h, map_zero]
  rfl

theorem mem_iff_mem_of_prime (M N : ℕ) [NeZero M] [Fact N.Prime] (hN : N ∣ M)
    (W : Place 𝕂 (modularFunctionFieldBar M)) :
    jb M ∈ W.toValuationSubring ↔ jdb M N hN ∈ W.toValuationSubring := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm N
  constructor
  · intro h
    refine W.mem_toValuationSubring_of_isIntegral_adjoin h ?_
    exact isIntegral_adjoin_of_eval₂ M data.Φ data.monic jq (qExpand ℚ N jq) (jq_mem_full M) (jqd_mem_full M hN)
      data.eval_eq_zero
  · intro h
    refine W.mem_toValuationSubring_of_isIntegral_adjoin h ?_
    refine isIntegral_adjoin_of_eval₂ M data.Φ data.monic (qExpand ℚ N jq) jq (jqd_mem_full M hN) (jq_mem_full M) ?_
    have h0 := data.eval_eq_zero
    rw [show evalAtJ = (Polynomial.aeval (R := ℤ) jq).toRingHom from rfl, hsymm jq (jqN N)] at h0
    exact h0

end Level

section AB

local notation "𝕂" => AlgebraicClosure ℚ

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hl : Fact ℓ.Prime]

omit hp hl in
theorem absurd_sq_eq_one {c : ℕ} (hc : 0 < c) (hp2 : 2 ≤ p) (h : p * p * c = c) : False := by
  have h1 : p * p = 1 := Nat.eq_of_mul_eq_mul_right hc (by simpa using h)
  nlinarith

omit hp hl in
theorem absurd_sq_eq_sq {c : ℕ} (hc : 0 < c) (hne : p ≠ ℓ) (h : p * p * c = ℓ * ℓ * c) : False := by
  have h1 : p * p = ℓ * ℓ := Nat.eq_of_mul_eq_mul_right hc h
  exact hne (Nat.mul_self_inj.mp h1)

theorem not_ell_dvd_p (hpl : p ≠ ℓ) : ¬ ℓ ∣ p := fun h =>
  hpl ((Nat.prime_dvd_prime_iff_eq hl.out hp.out).mp h).symm

theorem finrankAlong_beta (hpl : p ≠ ℓ) : finrankAlong 𝕂 (heckeBetaBar 𝕂 p ℓ) = ℓ + 1 := by
  rw [finrankAlong_heckeBetaBar, if_neg (not_ell_dvd_p p ℓ hpl)]

theorem budget_beta (hpl : p ≠ ℓ) (hβ : HeckeBetaBarIntegral 𝕂 p ℓ) (v : Place 𝕂 (modularFunctionFieldBar p))
    (S : Finset (Place 𝕂 (modularFunctionFieldBar (p * ℓ))))
    (hS : ∀ w ∈ S, w.restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ = v) :
    ∑ w ∈ S, (w.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) : ℤ) * (w.inertiaDegAlong (heckeBetaBar 𝕂 p ℓ) hβ : ℤ)
      ≤ ℓ + 1 := by
  letI := algebraAlong (heckeBetaBar 𝕂 p ℓ)
  haveI := isScalarTower_along (heckeBetaBar 𝕂 p ℓ)
  haveI := isIntegral_along (heckeBetaBar 𝕂 p ℓ) hβ
  haveI : FiniteDimensional (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) :=
    finiteAlong_heckeBetaBar_of_prime 𝕂 p ℓ
  haveI : Algebra.IsSeparable (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have h := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank (F := modularFunctionFieldBar p) v S hS
  have hfin : (Module.finrank (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) : ℤ) = ℓ + 1 := by
    have := finrankAlong_beta p ℓ hpl
    unfold finrankAlong at this
    exact_mod_cast this
  rw [hfin] at h
  exact h

theorem inertiaDegAlong_beta_pos (hβ : HeckeBetaBarIntegral 𝕂 p ℓ) (w : Place 𝕂 (modularFunctionFieldBar (p * ℓ))) :
    0 < w.inertiaDegAlong (heckeBetaBar 𝕂 p ℓ) hβ := by
  letI := algebraAlong (heckeBetaBar 𝕂 p ℓ)
  haveI := isScalarTower_along (heckeBetaBar 𝕂 p ℓ)
  haveI := isIntegral_along (heckeBetaBar 𝕂 p ℓ) hβ
  haveI : FiniteDimensional (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) :=
    finiteAlong_heckeBetaBar_of_prime 𝕂 p ℓ
  haveI : Algebra.IsSeparable (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Place.inertiaDeg_pos (F := modularFunctionFieldBar p) w

theorem inf_restrictAlong_alpha (hα : HeckeAlphaBarIntegral 𝕂 p ℓ) :
    (cuspInftyBar (p * ℓ)).restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα = cuspInftyBar p := by
  ext f
  rw [mem_restrictAlong_iff]
  show 0 ≤ ((heckeAlphaBar 𝕂 p ℓ f : modularFunctionFieldBar (p * ℓ)) : LaurentSeries 𝕂).order ↔ 0 ≤ (f : LaurentSeries 𝕂).order
  rw [coe_heckeAlphaBar]

theorem inf_restrictAlong_beta (hβ : HeckeBetaBarIntegral 𝕂 p ℓ) :
    (cuspInftyBar (p * ℓ)).restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ = cuspInftyBar p := by
  ext f
  rw [mem_restrictAlong_iff]
  show 0 ≤ ((heckeBetaBar 𝕂 p ℓ f : modularFunctionFieldBar (p * ℓ)) : LaurentSeries 𝕂).order ↔ 0 ≤ (f : LaurentSeries 𝕂).order
  rw [coe_heckeBetaBar, order_qExpand]
  constructor
  · intro h
    rcases lt_or_ge (f : LaurentSeries 𝕂).order 0 with hlt | hge
    · have : (ℓ : ℤ) * (f : LaurentSeries 𝕂).order < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hl.out.pos) hlt
      omega
    · exact hge
  · intro h; positivity

theorem e_beta_inf (hβ : HeckeBetaBarIntegral 𝕂 p ℓ) :
    (cuspInftyBar (p * ℓ)).ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) = ℓ := by
  have h := Place.ord_restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ (cuspInftyBar (p * ℓ)) (jb p)
  rw [inf_restrictAlong_beta p ℓ hβ, beta_jb, ord_inf_jb] at h
  have h2 : (cuspInftyBar (p * ℓ)).ord (jdb (p * ℓ) ℓ (hdl p ℓ)) = -ℓ := ord_cuspInftyBar_coeffEmb_qExpand (p * ℓ) ℓ (hdl p ℓ)
  rw [h2] at h
  have : ((cuspInftyBar (p * ℓ)).ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) : ℤ) = ℓ := by linarith
  exact_mod_cast this

theorem restrictAlong_alpha_of_beta_inf (hpl : p ≠ ℓ) (hα : HeckeAlphaBarIntegral 𝕂 p ℓ) (hβ : HeckeBetaBarIntegral 𝕂 p ℓ)
    (W : Place 𝕂 (modularFunctionFieldBar (p * ℓ)))
    (hW : W.restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ = cuspInftyBar p) :
    W.restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα = cuspInftyBar p := by
  have hEb := ramificationIndexAlong_pos (heckeBetaBar 𝕂 p ℓ) hβ W
  have hEa := ramificationIndexAlong_pos (heckeAlphaBar 𝕂 p ℓ) hα W
  have hE' := ramificationIndexAlong_pos (alpha' p ℓ) (alpha'_integral p ℓ) W
  set Eb := W.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) with hEb_def
  set Ea := W.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) with hEa_def
  set E' := W.ramificationIndexAlong (alpha' p ℓ) with hE'_def

  have hJl : W.ord (jdb (p * ℓ) ℓ (hdl p ℓ)) = -(Eb : ℤ) := by
    have h := Place.ord_restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ W (jb p)
    rw [beta_jb, hW, ord_inf_jb] at h
    linarith
  have hJl_nm : jdb (p * ℓ) ℓ (hdl p ℓ) ∉ W.toValuationSubring := by
    intro hmem
    have hne0 : jdb (p * ℓ) ℓ (hdl p ℓ) ≠ 0 := fun h => by
      have h0 : W.ord (jdb (p * ℓ) ℓ (hdl p ℓ)) = 0 := by rw [h, Place.ord_zero]
      omega
    have h0 := (W.mem_iff_ord_nonneg hne0).mp hmem
    omega
  have hJ_nm : jb (p * ℓ) ∉ W.toValuationSubring := fun h => hJl_nm ((mem_iff_mem_of_prime (p * ℓ) ℓ (hdl p ℓ) W).mp h)
  have hcusp : IsCusp (jb p) (W.restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα) := by
    rw [isCusp_iff, mem_restrictAlong_iff, alpha_jb]; exact hJ_nm
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar p _ hcusp with h | h
  · exact h
  exfalso

  have hJ : W.ord (jb (p * ℓ)) = -(p : ℤ) * Ea := by
    have h1 := Place.ord_restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα W (jb p)
    rw [alpha_jb, h, ord_zero_jb] at h1
    linarith
  have hcusp' : IsCusp (jb ℓ) (W.restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ)) := by
    rw [isCusp_iff, mem_restrictAlong_iff, alpha'_jb]; exact hJ_nm
  have hne : W ≠ cuspInftyBar (p * ℓ) := by
    rintro rfl
    rw [inf_restrictAlong_alpha p ℓ hα] at h
    exact zero_ne_inf p h.symm
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar ℓ _ hcusp' with h' | h'
  ·
    have a1 := Place.ord_restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) W (jb ℓ)
    rw [alpha'_jb, h', ord_inf_jb] at a1
    have a2 := Place.ord_restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) W (jdb ℓ ℓ dvd_rfl)
    rw [alpha'_jdb, h', ord_inf_jdb] at a2

    have k1 : (E' : ℤ) = p * Ea := by linarith
    have k2 : (Eb : ℤ) = ℓ * E' := by linarith
    have bud := budget_beta p ℓ hpl hβ (cuspInftyBar p) {W} (by simpa using hW)
    rw [Finset.sum_singleton] at bud
    have hf := inertiaDegAlong_beta_pos p ℓ hβ W
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    have hl2 : (2 : ℤ) ≤ ℓ := by exact_mod_cast hl.out.two_le
    have k3 : (2 : ℤ) ≤ E' := by nlinarith
    have k4 : 2 * (ℓ : ℤ) ≤ Eb := by nlinarith
    have k5 : (Eb : ℤ) ≤ ℓ + 1 := by nlinarith
    linarith
  ·
    have a1 := Place.ord_restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) W (jb ℓ)
    rw [alpha'_jb, h', ord_zero_jb] at a1
    have a2 := Place.ord_restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) W (jdb ℓ ℓ dvd_rfl)
    rw [alpha'_jdb, h', ord_zero_jdb] at a2
    have k1 : (p : ℤ) * Ea = ℓ * E' := by linarith
    have k2 : (Eb : ℤ) = E' := by linarith

    have k1n : p * Ea = ℓ * Eb := by exact_mod_cast (k2 ▸ k1)
    have hdvd : p ∣ Eb := (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp.out hl.out).mpr hpl) ⟨Ea, by linarith⟩)
    have k3 : p ≤ Eb := Nat.le_of_dvd hEb hdvd
    classical
    have bud := budget_beta p ℓ hpl hβ (cuspInftyBar p) {cuspInftyBar (p * ℓ), W} (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact inf_restrictAlong_beta p ℓ hβ
      · rw [Finset.mem_singleton.mp hw]; exact hW)
    rw [Finset.sum_pair (Ne.symm hne), e_beta_inf p ℓ hβ] at bud
    have hf1 := inertiaDegAlong_beta_pos p ℓ hβ (cuspInftyBar (p * ℓ))
    have hf2 := inertiaDegAlong_beta_pos p ℓ hβ W
    have hp2 : 2 ≤ p := hp.out.two_le
    have : (Eb : ℤ) * (W.inertiaDegAlong (heckeBetaBar 𝕂 p ℓ) hβ : ℤ) ≤ 1 := by nlinarith
    nlinarith

end AB

section B

local notation "𝕂" => AlgebraicClosure ℚ

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hl : Fact ℓ.Prime]

theorem restrictAlong_alpha_of_beta_zero (hpl : p ≠ ℓ) (hα : HeckeAlphaBarIntegral 𝕂 p ℓ) (hβ : HeckeBetaBarIntegral 𝕂 p ℓ)
    (V : Place 𝕂 (modularFunctionFieldBar (p * ℓ)))
    (hV : V.restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ = cuspZeroBar p) :
    V.restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα = cuspZeroBar p := by
  have hEb := ramificationIndexAlong_pos (heckeBetaBar 𝕂 p ℓ) hβ V
  have hEa := ramificationIndexAlong_pos (heckeAlphaBar 𝕂 p ℓ) hα V
  have hE' := ramificationIndexAlong_pos (alpha' p ℓ) (alpha'_integral p ℓ) V
  have hE'' := ramificationIndexAlong_pos (beta' p ℓ) (beta'_integral p ℓ) V
  set Eb := V.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) with hEb_def
  set Ea := V.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) with hEa_def
  set E' := V.ramificationIndexAlong (alpha' p ℓ) with hE'_def
  set E'' := V.ramificationIndexAlong (beta' p ℓ) with hE''_def

  have hJl : V.ord (jdb (p * ℓ) ℓ (hdl p ℓ)) = -((p : ℤ) * Eb) := by
    have h := Place.ord_restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ V (jb p)
    rw [beta_jb, hV, ord_zero_jb] at h
    linarith only [h]
  have hJpl : V.ord (jdb (p * ℓ) (p * ℓ) dvd_rfl) = -(Eb : ℤ) := by
    have h := Place.ord_restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ V (jdb p p dvd_rfl)
    rw [beta_jdb, hV, ord_zero_jdb] at h
    linarith only [h]
  have hJl_nm : jdb (p * ℓ) ℓ (hdl p ℓ) ∉ V.toValuationSubring := by
    intro hmem
    have hpos : (0 : ℤ) < p * Eb := mul_pos (by exact_mod_cast hp.out.pos) (by exact_mod_cast hEb)
    have hne0 : jdb (p * ℓ) ℓ (hdl p ℓ) ≠ 0 := fun h => by
      have h0 : V.ord (jdb (p * ℓ) ℓ (hdl p ℓ)) = 0 := by rw [h, Place.ord_zero]
      omega
    have h0 := (V.mem_iff_ord_nonneg hne0).mp hmem
    omega
  have hJ_nm : jb (p * ℓ) ∉ V.toValuationSubring := fun h => hJl_nm ((mem_iff_mem_of_prime (p * ℓ) ℓ (hdl p ℓ) V).mp h)
  have hJp_nm : jdb (p * ℓ) p (hdp p ℓ) ∉ V.toValuationSubring := fun h =>
    hJ_nm ((mem_iff_mem_of_prime (p * ℓ) p (hdp p ℓ) V).mpr h)
  have hcusp : IsCusp (jb p) (V.restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα) := by
    rw [isCusp_iff, mem_restrictAlong_iff, alpha_jb]; exact hJ_nm
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar p _ hcusp with h | h
  swap
  · exact h
  exfalso

  have hJ : V.ord (jb (p * ℓ)) = -(Ea : ℤ) := by
    have h1 := Place.ord_restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα V (jb p)
    rw [alpha_jb, h, ord_inf_jb] at h1
    linarith only [h1]
  have hJp : V.ord (jdb (p * ℓ) p (hdp p ℓ)) = -((p : ℤ) * Ea) := by
    have h1 := Place.ord_restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα V (jdb p p dvd_rfl)
    rw [alpha_jdb, h, ord_inf_jdb] at h1
    linarith only [h1]
  have hcusp' : IsCusp (jb ℓ) (V.restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ)) := by
    rw [isCusp_iff, mem_restrictAlong_iff, alpha'_jb]; exact hJ_nm
  have hcusp'' : IsCusp (jb ℓ) (V.restrictAlong (beta' p ℓ) (beta'_integral p ℓ)) := by
    rw [isCusp_iff, mem_restrictAlong_iff, beta'_jb]; exact hJp_nm
  have a1 := Place.ord_restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) V (jb ℓ)
  have a2 := Place.ord_restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) V (jdb ℓ ℓ dvd_rfl)
  rw [alpha'_jb] at a1
  rw [alpha'_jdb] at a2
  have b1 := Place.ord_restrictAlong (beta' p ℓ) (beta'_integral p ℓ) V (jb ℓ)
  have b2 := Place.ord_restrictAlong (beta' p ℓ) (beta'_integral p ℓ) V (jdb ℓ ℓ dvd_rfl)
  rw [beta'_jb] at b1
  rw [beta'_jdb] at b2
  have hp2 : 2 ≤ p := hp.out.two_le
  have hl2 : 2 ≤ ℓ := hl.out.two_le
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar ℓ _ hcusp' with h' | h' <;>
    rcases eq_cuspInftyBar_or_eq_cuspZeroBar ℓ _ hcusp'' with h'' | h''
  ·
    rw [h', ord_inf_jb] at a1
    rw [h', ord_inf_jdb] at a2
    rw [h'', ord_inf_jb] at b1
    rw [h'', ord_inf_jdb] at b2
    have k1 : (E' : ℤ) = Ea := by linarith only [a1, hJ]
    have k2 : (p : ℤ) * Eb = ℓ * E' := by linarith only [a2, hJl]
    have k3 : (E'' : ℤ) = p * Ea := by linarith only [b1, hJp]
    have k4 : (Eb : ℤ) = ℓ * E'' := by linarith only [b2, hJpl]
    have k5 : p * p * (ℓ * Ea) = ℓ * Ea := by
      have : (p : ℤ) * p * (ℓ * Ea) = ℓ * Ea := by linear_combination (ℓ : ℤ) * k1 + k2 - (p * ℓ : ℤ) * k3 - (p : ℤ) * k4
      exact_mod_cast this
    exact absurd_sq_eq_one p (mul_pos hl.out.pos hEa) hp2 k5
  ·
    rw [h', ord_inf_jb] at a1
    rw [h', ord_inf_jdb] at a2
    rw [h'', ord_zero_jb] at b1
    rw [h'', ord_zero_jdb] at b2
    have k1 : (E' : ℤ) = Ea := by linarith only [a1, hJ]
    have k2 : (p : ℤ) * Eb = ℓ * E' := by linarith only [a2, hJl]
    have k3 : (p : ℤ) * Ea = ℓ * E'' := by linarith only [b1, hJp]
    have k4 : (Eb : ℤ) = E'' := by linarith only [b2, hJpl]
    rw [k1] at k2
    rw [← k4] at k3
    have k5 : p * p * (Ea * Eb) = ℓ * ℓ * (Ea * Eb) := by
      have : (p : ℤ) * p * (Ea * Eb) = ℓ * ℓ * (Ea * Eb) := by linear_combination (p * Ea : ℤ) * k2 + (ℓ * Ea : ℤ) * k3
      exact_mod_cast this
    exact absurd_sq_eq_sq p ℓ (mul_pos hEa hEb) hpl k5
  ·
    rw [h', ord_zero_jb] at a1
    rw [h', ord_zero_jdb] at a2
    rw [h'', ord_inf_jb] at b1
    rw [h'', ord_inf_jdb] at b2
    have k1 : (Ea : ℤ) = ℓ * E' := by linarith only [a1, hJ]
    have k2 : (p : ℤ) * Eb = E' := by linarith only [a2, hJl]
    have k3 : (E'' : ℤ) = p * Ea := by linarith only [b1, hJp]
    have k4 : (Eb : ℤ) = ℓ * E'' := by linarith only [b2, hJpl]
    have k5 : (p * ℓ) * (p * ℓ) * Eb = Eb := by
      have : ((p : ℤ) * ℓ) * (p * ℓ) * Eb = Eb := by linear_combination (-(ℓ * p : ℤ)) * k1 + (ℓ * ℓ * p : ℤ) * k2 - (ℓ : ℤ) * k3 - k4
      exact_mod_cast this
    exact absurd_sq_eq_one (p * ℓ) hEb (le_trans hp2 (Nat.le_mul_of_pos_right p hl.out.pos)) k5
  ·
    rw [h', ord_zero_jb] at a1
    rw [h', ord_zero_jdb] at a2
    rw [h'', ord_zero_jb] at b1
    rw [h'', ord_zero_jdb] at b2
    have k1 : (Ea : ℤ) = ℓ * E' := by linarith only [a1, hJ]
    have k2 : (p : ℤ) * Eb = E' := by linarith only [a2, hJl]
    have k3 : (p : ℤ) * Ea = ℓ * E'' := by linarith only [b1, hJp]
    have k4 : (Eb : ℤ) = E'' := by linarith only [b2, hJpl]
    have k5 : p * p * (ℓ * Eb) = ℓ * Eb := by
      have : (p : ℤ) * p * (ℓ * Eb) = ℓ * Eb := by linear_combination (-(ℓ : ℤ)) * k4 + k3 - (p : ℤ) * k1 + (p * ℓ : ℤ) * k2
      exact_mod_cast this
    exact absurd_sq_eq_one p (mul_pos hl.out.pos hEb) hp2 k5

end B

section Deg

local notation "𝕂" => AlgebraicClosure ℚ

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hl : Fact ℓ.Prime]

theorem deg_eq_one_of_beta (hβ : HeckeBetaBarIntegral 𝕂 p ℓ) (W : Place 𝕂 (modularFunctionFieldBar (p * ℓ)))
    (hW : (W.restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ).deg = 1) : W.deg = 1 := by
  have h := deg_restrictAlong_mul_inertiaDegAlong (K := 𝕂) (heckeBetaBar 𝕂 p ℓ) hβ W
  rw [hW, one_mul] at h
  have hf := inertiaDegAlong_beta_pos p ℓ hβ W
  exact deg_eq_one_of_isAlgClosed W (by omega)

theorem f_beta_eq_one (hβ : HeckeBetaBarIntegral 𝕂 p ℓ) (W : Place 𝕂 (modularFunctionFieldBar (p * ℓ)))
    (hW : (W.restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ).deg = 1) : W.inertiaDegAlong (heckeBetaBar 𝕂 p ℓ) hβ = 1 := by
  have h := deg_restrictAlong_mul_inertiaDegAlong (K := 𝕂) (heckeBetaBar 𝕂 p ℓ) hβ W
  rwa [hW, one_mul, deg_eq_one_of_beta p ℓ hβ W hW] at h

theorem f_alpha_eq_one (hα : HeckeAlphaBarIntegral 𝕂 p ℓ) (hβ : HeckeBetaBarIntegral 𝕂 p ℓ)
    (W : Place 𝕂 (modularFunctionFieldBar (p * ℓ)))
    (hWβ : (W.restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ).deg = 1) (hWα : (W.restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα).deg = 1) :
    W.inertiaDegAlong (heckeAlphaBar 𝕂 p ℓ) hα = 1 := by
  have h := deg_restrictAlong_mul_inertiaDegAlong (K := 𝕂) (heckeAlphaBar 𝕂 p ℓ) hα W
  rwa [hWα, one_mul, deg_eq_one_of_beta p ℓ hβ W hWβ] at h

theorem sum_e_beta (hpl : p ≠ ℓ) (hβ : HeckeBetaBarIntegral 𝕂 p ℓ) [HasPrincipalDivisors 𝕂 (modularFunctionFieldBar (p * ℓ))]
    (v : Place 𝕂 (modularFunctionFieldBar p)) (hv : v.deg = 1) :
    ∑ W ∈ Place.fiberAlong (heckeBetaBar 𝕂 p ℓ) hβ v, W.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) = ℓ + 1 := by
  have h := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong (heckeBetaBar 𝕂 p ℓ) hβ
    (finiteAlong_heckeBetaBar_of_prime 𝕂 p ℓ) (separableAlong_of_charZero (heckeBetaBar 𝕂 p ℓ) hβ) v
  rw [finrankAlong_beta p ℓ hpl] at h
  have h' : ∀ W ∈ Place.fiberAlong (heckeBetaBar 𝕂 p ℓ) hβ v,
      (W.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) : ℤ) * (W.inertiaDegAlong (heckeBetaBar 𝕂 p ℓ) hβ : ℤ)
        = (W.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) : ℤ) := by
    intro W hW
    rw [f_beta_eq_one p ℓ hβ W (by rw [Place.mem_fiberAlong.mp hW, hv]), Nat.cast_one, mul_one]
  rw [Finset.sum_congr rfl h'] at h
  exact_mod_cast h

theorem bar_le_bar : modularFunctionFieldBar p ≤ modularFunctionFieldBar (p * ℓ) := by
  show laurentBaseChange 𝕂 (modularFunctionFieldFull p) ≤ laurentBaseChange 𝕂 (modularFunctionFieldFull (p * ℓ))
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange 𝕂 (full_degeneracy_le (dvd_mul_right p ℓ) hy)

theorem adjoin_jbar_le (N : ℕ) [NeZero N] :
    IntermediateField.adjoin 𝕂 ({coeffEmb 𝕂 jq} : Set (LaurentSeries 𝕂)) ≤ modularFunctionFieldBar N :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (coeffEmb_mem_laurentBaseChange 𝕂 (jq_mem_full N)))

theorem adjoin_jq_le (N : ℕ) [NeZero N] :
    IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ modularFunctionFieldFull N :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_full N))

theorem relfinrank_bar (hpl : p ≠ ℓ) :
    IntermediateField.relfinrank (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) = ℓ + 1 := by
  have htower := IntermediateField.relfinrank_mul_relfinrank (adjoin_jbar_le p) (bar_le_bar p ℓ)
  have h1 : IntermediateField.relfinrank (IntermediateField.adjoin 𝕂 ({coeffEmb 𝕂 jq} : Set (LaurentSeries 𝕂)))
      (modularFunctionFieldBar p) = p + 1 := by
    show IntermediateField.relfinrank _ (laurentBaseChange 𝕂 (modularFunctionFieldFull p)) = _
    rw [relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_modularFunctionFieldFull_prime]
  have h2 : IntermediateField.relfinrank (IntermediateField.adjoin 𝕂 ({coeffEmb 𝕂 jq} : Set (LaurentSeries 𝕂)))
      (modularFunctionFieldBar (p * ℓ)) = (p + 1) * (ℓ + 1) := by
    show IntermediateField.relfinrank _ (laurentBaseChange 𝕂 (modularFunctionFieldFull (p * ℓ))) = _
    rw [relfinrank_laurentBaseChange_modularFunctionFieldFull,
      ← IntermediateField.relfinrank_mul_relfinrank (adjoin_jq_le p) (full_degeneracy_le (dvd_mul_right p ℓ)),
      relfinrank_modularFunctionFieldFull_prime, relfinrank_full_mul_prime p hp.out.squarefree hl.out (not_ell_dvd_p p ℓ hpl)]
  rw [h1, h2] at htower
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos p) htower

theorem finrankAlong_alpha (hpl : p ≠ ℓ) : finrankAlong 𝕂 (heckeAlphaBar 𝕂 p ℓ) = ℓ + 1 := by
  refine Eq.trans ?_ (relfinrank_bar p ℓ hpl)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (bar_le_bar p ℓ)]
  unfold finrankAlong
  letI := algebraAlong (heckeAlphaBar 𝕂 p ℓ)
  let e : modularFunctionFieldBar (p * ℓ) ≃ₗ[modularFunctionFieldBar p]
      IntermediateField.extendScalars (bar_le_bar p ℓ) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.finrank_eq

theorem budget_alpha (hpl : p ≠ ℓ) (hα : HeckeAlphaBarIntegral 𝕂 p ℓ) (hβ : HeckeBetaBarIntegral 𝕂 p ℓ)
    (v : Place 𝕂 (modularFunctionFieldBar p)) (hv : v.deg = 1)
    (S : Finset (Place 𝕂 (modularFunctionFieldBar (p * ℓ))))
    (hS : ∀ w ∈ S, w.restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα = v)
    (hSβ : ∀ w ∈ S, (w.restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ).deg = 1) :
    ∑ w ∈ S, w.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) ≤ ℓ + 1 := by
  letI := algebraAlong (heckeAlphaBar 𝕂 p ℓ)
  haveI := isScalarTower_along (heckeAlphaBar 𝕂 p ℓ)
  haveI := isIntegral_along (heckeAlphaBar 𝕂 p ℓ) hα
  haveI : FiniteDimensional (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) :=
    finiteAlong_heckeAlphaBar_of_prime 𝕂 p ℓ
  haveI : Algebra.IsSeparable (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have h := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank (F := modularFunctionFieldBar p) v S hS
  have hfin : (Module.finrank (modularFunctionFieldBar p) (modularFunctionFieldBar (p * ℓ)) : ℤ) = ℓ + 1 := by
    have := finrankAlong_alpha p ℓ hpl
    unfold finrankAlong at this
    exact_mod_cast this
  rw [hfin] at h
  have h' : ∀ w ∈ S, ((w.ramificationIndex (modularFunctionFieldBar p) : ℕ) : ℤ) * ((Place.inertiaDeg (modularFunctionFieldBar p) w : ℕ) : ℤ)
      = (w.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) : ℤ) := by
    intro w hw
    have : w.inertiaDegAlong (heckeAlphaBar 𝕂 p ℓ) hα = 1 :=
      f_alpha_eq_one p ℓ hα hβ w (hSβ w hw) (by rw [hS w hw, hv])
    show (w.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) : ℤ) * (w.inertiaDegAlong (heckeAlphaBar 𝕂 p ℓ) hα : ℤ) = _
    rw [this, Nat.cast_one, mul_one]
  rw [Finset.sum_congr rfl h'] at h
  exact_mod_cast h

end Deg

section Main

local notation "𝕂" => AlgebraicClosure ℚ

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hl : Fact ℓ.Prime]

theorem type_of_zero (hα : HeckeAlphaBarIntegral 𝕂 p ℓ) (hβ : HeckeBetaBarIntegral 𝕂 p ℓ)
    (V : Place 𝕂 (modularFunctionFieldBar (p * ℓ)))
    (hVβ : V.restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ = cuspZeroBar p)
    (hVα : V.restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα = cuspZeroBar p) :
    (V.restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) = cuspInftyBar ℓ ∧
        V.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) = ℓ * V.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ)) ∨
      (V.restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) = cuspZeroBar ℓ ∧
        V.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) = ℓ * V.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ)) := by
  have hJ : V.ord (jb (p * ℓ)) = -((p : ℤ) * V.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ)) := by
    have h1 := Place.ord_restrictAlong (heckeAlphaBar 𝕂 p ℓ) hα V (jb p)
    rw [alpha_jb, hVα, ord_zero_jb] at h1
    linarith only [h1]
  have hJl : V.ord (jdb (p * ℓ) ℓ (hdl p ℓ)) = -((p : ℤ) * V.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ)) := by
    have h := Place.ord_restrictAlong (heckeBetaBar 𝕂 p ℓ) hβ V (jb p)
    rw [beta_jb, hVβ, ord_zero_jb] at h
    linarith only [h]
  have hJ_nm : jb (p * ℓ) ∉ V.toValuationSubring := by
    have h := isCusp_cuspZeroBar p (isFrickeAutFull_frickeInvolutionFull_prime p)
    rw [← hVα, isCusp_iff, mem_restrictAlong_iff, alpha_jb] at h
    exact h
  have hcusp' : IsCusp (jb ℓ) (V.restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ)) := by
    rw [isCusp_iff, mem_restrictAlong_iff, alpha'_jb]; exact hJ_nm
  have a1 := Place.ord_restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) V (jb ℓ)
  have a2 := Place.ord_restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) V (jdb ℓ ℓ dvd_rfl)
  rw [alpha'_jb] at a1
  rw [alpha'_jdb] at a2
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar ℓ _ hcusp' with h' | h'
  · left
    refine ⟨h', ?_⟩
    rw [h', ord_inf_jb] at a1
    rw [h', ord_inf_jdb] at a2
    have k1 : (V.ramificationIndexAlong (alpha' p ℓ) : ℤ) = p * V.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) := by
      linarith only [a1, hJ]
    have k2 : (p : ℤ) * V.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) = ℓ * V.ramificationIndexAlong (alpha' p ℓ) := by
      linarith only [a2, hJl]
    have k : (p : ℤ) * V.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) = p * (ℓ * V.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ)) := by
      linear_combination k2 + (ℓ : ℤ) * k1
    exact_mod_cast (mul_left_cancel₀ hp0.ne' k)
  · right
    refine ⟨h', ?_⟩
    rw [h', ord_zero_jb] at a1
    rw [h', ord_zero_jdb] at a2
    have k1 : (p : ℤ) * V.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) = ℓ * V.ramificationIndexAlong (alpha' p ℓ) := by
      linarith only [a1, hJ]
    have k2 : (p : ℤ) * V.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ) = V.ramificationIndexAlong (alpha' p ℓ) := by
      linarith only [a2, hJl]
    have k : (p : ℤ) * V.ramificationIndexAlong (heckeAlphaBar 𝕂 p ℓ) = p * (ℓ * V.ramificationIndexAlong (heckeBetaBar 𝕂 p ℓ)) := by
      linear_combination k1 - (ℓ : ℤ) * k2
    exact_mod_cast (mul_left_cancel₀ hp0.ne' k)

theorem eq_singleton_of_sum_eq_one {ι : Type*} (S : Finset ι) (g : ι → ℕ) (hg : ∀ x ∈ S, 1 ≤ g x)
    (h : ∑ x ∈ S, g x = 1) : ∃ a, S = {a} ∧ g a = 1 := by
  have hcard : S.card ≤ 1 :=
    calc S.card = ∑ x ∈ S, 1 := Finset.card_eq_sum_ones S
      _ ≤ ∑ x ∈ S, g x := Finset.sum_le_sum hg
      _ = 1 := h
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at h
  have hc1 : S.card = 1 := le_antisymm hcard (Finset.card_pos.mpr hne)
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
  exact ⟨a, rfl, by simpa using h⟩

end Main

end PLSol
p2m_reactivate "P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_of_prime.PLSol"

end
p2m_reactivate "P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_of_prime.PLSol"

p2m_open "ModularCurve~mem_restrictAlong_iff" in open AlgebraicCurve PLSol in
theorem solution (p ℓ : ℕ) [hp : Fact (Nat.Prime p)] [hl : Fact (Nat.Prime ℓ)] (hpl : p ≠ ℓ) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p ℓ) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * ℓ))] : heckeDivBar hα hβ (cuspidalDivisor p) = (1 + ℓ : ℤ) • cuspidalDivisor p := by
  classical
  have hwp : IsFrickeAutFull p (frickeInvolutionFull p) := isFrickeAutFull_frickeInvolutionFull_prime p
  have hdeg_inf : (cuspInftyBar p).deg = 1 := deg_cuspInftyBar p
  have hdeg_zero : (cuspZeroBar p).deg = 1 := deg_cuspZeroBar p

  have hinf_mem : cuspInftyBar (p * ℓ) ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ (cuspInftyBar p) :=
    Place.mem_fiberAlong.mpr (inf_restrictAlong_beta p ℓ hβ)
  have hsum_inf := sum_e_beta p ℓ hpl hβ (cuspInftyBar p) hdeg_inf
  rw [← Finset.insert_erase hinf_mem, Finset.sum_insert (Finset.notMem_erase _ _), e_beta_inf p ℓ hβ] at hsum_inf
  obtain ⟨W₁, hS, heW₁⟩ := eq_singleton_of_sum_eq_one
    ((Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ (cuspInftyBar p)).erase (cuspInftyBar (p * ℓ)))
    (fun W => W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ))
    (fun W _ => ramificationIndexAlong_pos (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ W) (Nat.add_left_cancel hsum_inf)
  have hW₁mem : W₁ ∈ (Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ (cuspInftyBar p)).erase (cuspInftyBar (p * ℓ)) := by
    rw [hS]; exact Finset.mem_singleton_self _
  have hW₁ne : W₁ ≠ cuspInftyBar (p * ℓ) := (Finset.mem_erase.mp hW₁mem).1
  have hW₁β : W₁.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ = cuspInftyBar p :=
    Place.mem_fiberAlong.mp (Finset.mem_of_mem_erase hW₁mem)
  have hfibInf : ∀ W, W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ (cuspInftyBar p) ↔ W = W₁ ∨ W = cuspInftyBar (p * ℓ) := by
    intro W
    rw [← Finset.insert_erase hinf_mem, hS, Finset.mem_insert, Finset.mem_singleton, or_comm]

  have hF0β : ∀ V ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ (cuspZeroBar p),
      V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ = cuspZeroBar p := fun V hV => Place.mem_fiberAlong.mp hV
  have hF0α : ∀ V ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ (cuspZeroBar p),
      V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ) hα = cuspZeroBar p :=
    fun V hV => restrictAlong_alpha_of_beta_zero p ℓ hpl hα hβ V (hF0β V hV)
  have hsum_zero := sum_e_beta p ℓ hpl hβ (cuspZeroBar p) hdeg_zero
  have hbud := budget_alpha p ℓ hpl hα hβ (cuspZeroBar p) hdeg_zero _ hF0α (fun V hV => by rw [hF0β V hV, hdeg_zero])
  set F0 := Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ (cuspZeroBar p) with hF0
  let P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * ℓ)) → Prop := fun V =>
    V.restrictAlong (alpha' p ℓ) (alpha'_integral p ℓ) = cuspInftyBar ℓ
  have htype := fun V (hV : V ∈ F0) => type_of_zero p ℓ hα hβ V (hF0β V hV) (hF0α V hV)

  have hPe : ∀ V ∈ F0.filter P, V.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) = ℓ * V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ) := by
    intro V hV
    rw [Finset.mem_filter] at hV
    rcases htype V hV.1 with ⟨_, h⟩ | ⟨h0, _⟩
    · exact h
    · exact absurd (hV.2.symm.trans h0) (zero_ne_inf ℓ).symm
  have hNe : ∀ V ∈ F0.filter (fun V => ¬ P V), V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ) = ℓ * V.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) := by
    intro V hV
    rw [Finset.mem_filter] at hV
    rcases htype V hV.1 with ⟨hi, _⟩ | ⟨_, h⟩
    · exact absurd hi hV.2
    · exact h

  have hsplitβ := Finset.sum_filter_add_sum_filter_not F0 P (fun V => V.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ))
  have hsplitα := Finset.sum_filter_add_sum_filter_not F0 P (fun V => V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ))
  rw [hsum_zero] at hsplitβ
  set A := ∑ V ∈ F0.filter P, V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ) with hA
  set Z := ∑ V ∈ F0.filter (fun V => ¬ P V), V.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) with hZ
  have hBinf : ∑ V ∈ F0.filter P, V.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) = ℓ * A := by
    rw [hA, Finset.mul_sum]; exact Finset.sum_congr rfl hPe
  have hAzero : ∑ V ∈ F0.filter (fun V => ¬ P V), V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ) = ℓ * Z := by
    rw [hZ, Finset.mul_sum]; exact Finset.sum_congr rfl hNe
  rw [hBinf] at hsplitβ
  rw [hAzero] at hsplitα
  have hl2 : 2 ≤ ℓ := hl.out.two_le
  have hA1 : A = 1 := by
    rcases Nat.lt_or_ge A 1 with hA0 | hA1
    ·
      exfalso
      have hA0' : A = 0 := by omega
      rw [hA0', mul_zero, zero_add] at hsplitβ
      rw [hA0', zero_add, hsplitβ] at hsplitα
      have : ℓ * (ℓ + 1) ≤ ℓ + 1 := hsplitα ▸ hbud
      nlinarith
    · rcases Nat.lt_or_ge A 2 with hA2 | hA2
      · omega
      · exfalso
        have hZ0 : 0 ≤ Z := Nat.zero_le Z
        nlinarith
  have hZ1 : Z = 1 := by rw [hA1] at hsplitβ; omega

  obtain ⟨V₁, hS₁, heV₁⟩ := eq_singleton_of_sum_eq_one (F0.filter P)
    (fun V => V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ))
    (fun V _ => ramificationIndexAlong_pos (heckeAlphaBar (AlgebraicClosure ℚ) p ℓ) hα V) hA1
  obtain ⟨V₂, hS₂, heV₂⟩ := eq_singleton_of_sum_eq_one (F0.filter (fun V => ¬ P V))
    (fun V => V.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ))
    (fun V _ => ramificationIndexAlong_pos (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ V) hZ1
  have hV₁mem : V₁ ∈ F0.filter P := by rw [hS₁]; exact Finset.mem_singleton_self _
  have hV₂mem : V₂ ∈ F0.filter (fun V => ¬ P V) := by rw [hS₂]; exact Finset.mem_singleton_self _
  have hV₁F0 : V₁ ∈ F0 := (Finset.mem_filter.mp hV₁mem).1
  have hV₂F0 : V₂ ∈ F0 := (Finset.mem_filter.mp hV₂mem).1
  have hV : V₁ ≠ V₂ := by
    intro h
    exact (Finset.mem_filter.mp hV₂mem).2 (h ▸ (Finset.mem_filter.mp hV₁mem).2)
  have heβV₁ : V₁.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) = ℓ := by rw [hPe V₁ hV₁mem, heV₁, mul_one]
  have hfibZero : ∀ V, V ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p ℓ) hβ (cuspZeroBar p) ↔ V = V₁ ∨ V = V₂ := by
    intro V
    show V ∈ F0 ↔ _
    rw [← Finset.filter_union_filter_not_eq P F0, hS₁, hS₂, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_singleton]

  exact heckeDivBar_cuspidalDivisor p ℓ hα hβ W₁ (cuspInftyBar (p * ℓ)) hW₁ne hfibInf heW₁ (e_beta_inf p ℓ hβ)
    (restrictAlong_alpha_of_beta_inf p ℓ hpl hα hβ W₁ hW₁β) (inf_restrictAlong_alpha p ℓ hα)
    (f_alpha_eq_one p ℓ hα hβ W₁ (by rw [hW₁β, hdeg_inf])
      (by rw [restrictAlong_alpha_of_beta_inf p ℓ hpl hα hβ W₁ hW₁β, hdeg_inf]))
    (f_alpha_eq_one p ℓ hα hβ (cuspInftyBar (p * ℓ)) (by rw [inf_restrictAlong_beta p ℓ hβ, hdeg_inf])
      (by rw [inf_restrictAlong_alpha p ℓ hα, hdeg_inf]))
    V₁ V₂ hV hfibZero heβV₁ heV₂ (hF0α V₁ hV₁F0) (hF0α V₂ hV₂F0)
    (f_alpha_eq_one p ℓ hα hβ V₁ (by rw [hF0β V₁ hV₁F0, hdeg_zero]) (by rw [hF0α V₁ hV₁F0, hdeg_zero]))
    (f_alpha_eq_one p ℓ hα hβ V₂ (by rw [hF0β V₂ hV₂F0, hdeg_zero]) (by rw [hF0α V₂ hV₂F0, hdeg_zero]))

end S_ModularCurve_heckeDivBar_cuspidalDivisor_of_prime
end P2MW
export P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_of_prime (solution)

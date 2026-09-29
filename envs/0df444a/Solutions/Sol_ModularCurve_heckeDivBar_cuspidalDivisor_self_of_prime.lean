-- Prove2me | solution 1 for ModularCurve.heckeDivBar_cuspidalDivisor_self_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/928ab0b2-111d-5f5b-8d9f-4f32020e3954

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_modularFunctionFieldFull_algHom_ext
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_heckeBetaBar_coeffEmb
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Relrank
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFull_prime
import Theorems.Thm_ModularCurve_relfinrank_full_sq
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Mathlib.Algebra.Algebra.Rat
import Theorems.Thm_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_sum
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_sq
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_ModularCurve_frickeInvolutionFull_apply_apply
import Theorems.Thm_ModularCurve_deg_cuspZeroBar
import Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Mathlib.FieldTheory.Perfect
import Theorems.Thm_ModularCurve_order_qExpand
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_deg_cuspInftyBar
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_prime
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~mem_restrictAlong_iff IntermediateField"

namespace FibreSol

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem mem_smul_iff (σ : F' ≃ₐ[K] F') (w : Place K F') (x : F') :
    x ∈ (σ • w).toValuationSubring ↔ σ.symm x ∈ w.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem deg_restrictAlong_mul_inertiaDegAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

variable (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
  (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x))
include h

theorem sq_symm (x : F) : σ.symm (α x) = β (τ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, ← h, AlgEquiv.apply_symm_apply]

theorem smul_restrictAlong (W : Place K F') :
    (σ • W).restrictAlong α hα = τ • (W.restrictAlong β hβ) := by
  ext f
  rw [mem_restrictAlong_iff, mem_smul_iff, sq_symm α β σ τ h,
    show f ∈ (τ • W.restrictAlong β hβ).toValuationSubring ↔ τ.symm f ∈ (W.restrictAlong β hβ).toValuationSubring from by
      rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]; rfl,
    mem_restrictAlong_iff]

theorem ramificationIndexAlong_smul (W : Place K F') :
    (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β := by
  show sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (σ • W).ord (α f) = n}
    = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (β f) = n}
  congr 1
  ext n
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hn⟩
    refine ⟨τ.symm f, by simpa using hf, ?_⟩
    rw [← hn, ← sq_symm α β σ τ h f, ← Place.ord_smul σ W (σ.symm (α f)), AlgEquiv.apply_symm_apply]
  · rintro ⟨g, hg, hn⟩
    refine ⟨τ g, by simpa using hg, ?_⟩
    rw [← hn, h g, Place.ord_smul]

theorem inertiaDegAlong_smul (W : Place K F') (hdeg : (W.restrictAlong β hβ).deg = 1) :
    (σ • W).inertiaDegAlong α hα = W.inertiaDegAlong β hβ := by
  have h1 := deg_restrictAlong_mul_inertiaDegAlong (K := K) α hα (σ • W)
  have h2 := deg_restrictAlong_mul_inertiaDegAlong (K := K) β hβ W
  rw [smul_restrictAlong α β hα hβ σ τ h, Place.deg_smul, hdeg, one_mul, Place.deg_smul] at h1
  rw [hdeg, one_mul] at h2
  rw [h1, h2]

end Generic

section GenericDeg

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem finrankAlong_eq_of_sq (α β : F →ₐ[K] F') (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F)
    (h : ∀ x, α (τ x) = σ (β x)) : finrankAlong K β = finrankAlong K α := by
  unfold finrankAlong
  exact @Algebra.finrank_eq_of_equiv_equiv F F' _ _ (algebraAlong β) F F' _ _ (algebraAlong α)
    τ.toRingEquiv σ.toRingEquiv (by ext x; exact h x)

theorem algHom_ext_baseChange {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    {A : Type*} [DivisionRing A] [Algebra L A] {f g : laurentBaseChange L F₀ →ₐ[L] A}
    (hfg : ∀ x : F₀, f ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L x.2⟩ = g ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L x.2⟩) :
    f = g := by
  ext ⟨y, hy⟩
  change y ∈ IntermediateField.adjoin L (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) at hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hyS =>
      obtain ⟨x, hx, rfl⟩ := hyS
      exact hfg ⟨x, hx⟩
  | algebraMap r =>
      have hr : (⟨algebraMap L (LaurentSeries L) r, (laurentBaseChange L F₀).algebraMap_mem r⟩ : laurentBaseChange L F₀)
          = algebraMap L (laurentBaseChange L F₀) r := Subtype.ext rfl
      rw [hr, f.commutes, g.commutes]
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) = g (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

end GenericDeg

section LevelSq

local notation "𝕂" => AlgebraicClosure ℚ

variable (p : ℕ) [hp : Fact p.Prime]

scoped instance : NeZero p := ⟨hp.out.ne_zero⟩

def betaQRingHom : modularFunctionFieldFull p →+* modularFunctionFieldFull (p * p) where
  toFun x := ⟨qExpand ℚ p x, full_degeneracy_map_le (N := p) p ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand ℚ p))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand ℚ p) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand ℚ p))
  map_add' _ _ := Subtype.ext (map_add (qExpand ℚ p) _ _)

def betaQ : modularFunctionFieldFull p →ₐ[ℚ] modularFunctionFieldFull (p * p) := (betaQRingHom p).toRatAlgHom

theorem coe_betaQ (x : modularFunctionFieldFull p) : (betaQ p x : LaurentSeries ℚ) = qExpand ℚ p x := rfl

theorem coe_fricke_sq (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) (x : modularFunctionFieldFull p) :
    ((frickeInvolutionFull p x : modularFunctionFieldFull p) : LaurentSeries ℚ)
      = ((frickeInvolutionFull (p * p) (betaQ p x) : modularFunctionFieldFull (p * p)) : LaurentSeries ℚ) := by
  have h1 : IsFrickeAutFull p (frickeInvolutionFull p) := isFrickeAutFull_frickeInvolutionFull_prime p
  let f : modularFunctionFieldFull p →ₐ[ℚ] LaurentSeries ℚ :=
    ((algebraMap (modularFunctionFieldFull p) (LaurentSeries ℚ)).comp
      (frickeInvolutionFull p).toRingEquiv.toRingHom).toRatAlgHom
  let g : modularFunctionFieldFull p →ₐ[ℚ] LaurentSeries ℚ :=
    ((algebraMap (modularFunctionFieldFull (p * p)) (LaurentSeries ℚ)).comp
      ((frickeInvolutionFull (p * p)).toRingEquiv.toRingHom.comp (betaQRingHom p))).toRatAlgHom
  suffices hfg : f = g from congrArg (fun φ => φ x) hfg
  refine modularFunctionFieldFull_algHom_ext (fun d hne hd => ?_)
  haveI := hne
  show ((frickeInvolutionFull p ⟨qExpand ℚ d jq, _⟩ : modularFunctionFieldFull p) : LaurentSeries ℚ)
    = ((frickeInvolutionFull (p * p) (betaQ p ⟨qExpand ℚ d jq, jqd_mem_full p hd⟩) : modularFunctionFieldFull (p * p)) : LaurentSeries ℚ)
  have hb : betaQ p ⟨qExpand ℚ d jq, jqd_mem_full p hd⟩
      = ⟨qExpand ℚ (p * d) jq, jqd_mem_full (p * p) (mul_dvd_mul_left p hd)⟩ :=
    Subtype.ext (qExpand_qExpand d p jq)
  rw [hb]
  rcases (Nat.dvd_prime hp.out).mp hd with rfl | rfl
  · rw [h1 1 p (one_mul p) inferInstance inferInstance,
      h2 (p * 1) p (by ring) inferInstance inferInstance]
  · rw [h1 d 1 (mul_one d) inferInstance inferInstance,
      h2 (d * d) 1 (mul_one _) inferInstance inferInstance]

theorem alpha_fricke_eq_fricke_beta (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) (x : modularFunctionFieldBar p) :
    heckeAlphaBar 𝕂 p p (frickeInvolutionBar p x) = frickeInvolutionBar (p * p) (heckeBetaBar 𝕂 p p x) := by
  set f : modularFunctionFieldBar p →ₐ[𝕂] modularFunctionFieldBar (p * p) :=
    (heckeAlphaBar 𝕂 p p).comp (frickeInvolutionBar p).toAlgHom
  set g : modularFunctionFieldBar p →ₐ[𝕂] modularFunctionFieldBar (p * p) :=
    (frickeInvolutionBar (p * p)).toAlgHom.comp (heckeBetaBar 𝕂 p p)
  suffices hfg : f = g from congrArg (fun φ => φ x) hfg
  refine algHom_ext_baseChange (modularFunctionFieldFull p) (fun y => ?_)
  apply Subtype.ext
  show ((heckeAlphaBar 𝕂 p p (frickeInvolutionBar p ⟨coeffEmb 𝕂 y, _⟩) : modularFunctionFieldBar (p * p)) : LaurentSeries 𝕂)
    = ((frickeInvolutionBar (p * p) (heckeBetaBar 𝕂 p p ⟨coeffEmb 𝕂 y, _⟩) : modularFunctionFieldBar (p * p)) : LaurentSeries 𝕂)
  rw [coe_heckeAlphaBar, frickeInvolutionBar_def, coe_geomAut_coeffEmb]
  have hb : heckeBetaBar 𝕂 p p ⟨coeffEmb 𝕂 (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange 𝕂 y.2⟩
      = ⟨coeffEmb 𝕂 ((betaQ p y : modularFunctionFieldFull (p * p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange 𝕂 (betaQ p y).2⟩ :=
    Subtype.ext (heckeBetaBar_coeffEmb p p y.2)
  rw [hb, frickeInvolutionBar_def, coe_geomAut_coeffEmb, coe_fricke_sq p h2 y]

end LevelSq

section Degrees

local notation "𝕂" => AlgebraicClosure ℚ

variable (p : ℕ) [hp : Fact p.Prime]

theorem bar_le_bar : modularFunctionFieldBar p ≤ modularFunctionFieldBar (p * p) := by
  show laurentBaseChange 𝕂 (modularFunctionFieldFull p) ≤ laurentBaseChange 𝕂 (modularFunctionFieldFull (p * p))
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange 𝕂 (full_degeneracy_le (dvd_mul_right p p) hy)

theorem adjoin_jbar_le (N : ℕ) [NeZero N] :
    IntermediateField.adjoin 𝕂 ({coeffEmb 𝕂 jq} : Set (LaurentSeries 𝕂)) ≤ modularFunctionFieldBar N :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
    (coeffEmb_mem_laurentBaseChange 𝕂 (jq_mem_full N)))

theorem relfinrank_bar_sq : IntermediateField.relfinrank (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) = p := by
  have htower := IntermediateField.relfinrank_mul_relfinrank (adjoin_jbar_le p) (bar_le_bar p)
  have h1 : IntermediateField.relfinrank (IntermediateField.adjoin 𝕂 ({coeffEmb 𝕂 jq} : Set (LaurentSeries 𝕂)))
      (modularFunctionFieldBar p) = p + 1 := by
    show IntermediateField.relfinrank _ (laurentBaseChange 𝕂 (modularFunctionFieldFull p)) = _
    rw [relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_modularFunctionFieldFull_prime]
  have h2 : IntermediateField.relfinrank (IntermediateField.adjoin 𝕂 ({coeffEmb 𝕂 jq} : Set (LaurentSeries 𝕂)))
      (modularFunctionFieldBar (p * p)) = (p + 1) * p := by
    show IntermediateField.relfinrank _ (laurentBaseChange 𝕂 (modularFunctionFieldFull (p * p))) = _
    rw [relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_full_sq, ← sq,
      dedekindPsi_prime_pow p 2 hp.out two_ne_zero]
    ring
  rw [h1, h2] at htower
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos p) htower

theorem finrankAlong_alpha : finrankAlong 𝕂 (heckeAlphaBar 𝕂 p p) = p := by
  refine Eq.trans ?_ (relfinrank_bar_sq p)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (bar_le_bar p)]
  unfold finrankAlong
  letI := algebraAlong (heckeAlphaBar 𝕂 p p)
  let e : modularFunctionFieldBar (p * p) ≃ₗ[modularFunctionFieldBar p]
      IntermediateField.extendScalars (bar_le_bar p) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.finrank_eq

theorem finrankAlong_beta (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) :
    finrankAlong 𝕂 (heckeBetaBar 𝕂 p p) = p := by
  rw [finrankAlong_eq_of_sq (heckeAlphaBar 𝕂 p p) (heckeBetaBar 𝕂 p p) (frickeInvolutionBar (p * p))
    (frickeInvolutionBar p) (alpha_fricke_eq_fricke_beta p h2), finrankAlong_alpha]

end Degrees

section Cusps

local notation "𝕂" => AlgebraicClosure ℚ

variable (p : ℕ) [hp : Fact p.Prime]

abbrev jb (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (jq_mem_full N)⟩

theorem mem_inf_iff (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) :
    f ∈ (cuspInftyBar N).toValuationSubring ↔ 0 ≤ (f : LaurentSeries 𝕂).order := Iff.rfl

theorem inf_restrictAlong_alpha (hα : HeckeAlphaBarIntegral 𝕂 p p) :
    (cuspInftyBar (p * p)).restrictAlong (heckeAlphaBar 𝕂 p p) hα = cuspInftyBar p := by
  ext f
  rw [mem_restrictAlong_iff, mem_inf_iff, mem_inf_iff, coe_heckeAlphaBar]

theorem inf_restrictAlong_beta (hβ : HeckeBetaBarIntegral 𝕂 p p) :
    (cuspInftyBar (p * p)).restrictAlong (heckeBetaBar 𝕂 p p) hβ = cuspInftyBar p := by
  ext f
  rw [mem_restrictAlong_iff, mem_inf_iff, mem_inf_iff, coe_heckeBetaBar, order_qExpand]
  constructor
  · intro h
    rcases lt_or_ge (f : LaurentSeries 𝕂).order 0 with hlt | hge
    · have : (p : ℤ) * (f : LaurentSeries 𝕂).order < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hp.out.pos) hlt
      omega
    · exact hge
  · intro h; positivity

theorem alpha_jb : heckeAlphaBar 𝕂 p p (jb p) = jb (p * p) := Subtype.ext (coe_heckeAlphaBar p p (jb p))

theorem beta_jb : heckeBetaBar 𝕂 p p (jb p)
    = ⟨coeffEmb 𝕂 (qExpand ℚ p jq), coeffEmb_mem_laurentBaseChange 𝕂 (jqd_mem_full (p * p) (Dvd.intro p rfl))⟩ :=
  Subtype.ext (heckeBetaBar_coeffEmb p p (jq_mem_full p))

theorem e_alpha_inf (hα : HeckeAlphaBarIntegral 𝕂 p p) : (cuspInftyBar (p * p)).ramificationIndexAlong (heckeAlphaBar 𝕂 p p) = 1 := by
  have h := Place.ord_restrictAlong (heckeAlphaBar 𝕂 p p) hα (cuspInftyBar (p * p)) (jb p)
  rw [inf_restrictAlong_alpha p hα, alpha_jb, ord_cuspInftyBar_coeffEmb_jq, ord_cuspInftyBar_coeffEmb_jq] at h
  have : ((cuspInftyBar (p * p)).ramificationIndexAlong (heckeAlphaBar 𝕂 p p) : ℤ) = 1 := by linarith
  exact_mod_cast this

theorem e_beta_inf (hβ : HeckeBetaBarIntegral 𝕂 p p) : (cuspInftyBar (p * p)).ramificationIndexAlong (heckeBetaBar 𝕂 p p) = p := by
  have h := Place.ord_restrictAlong (heckeBetaBar 𝕂 p p) hβ (cuspInftyBar (p * p)) (jb p)
  rw [inf_restrictAlong_beta p hβ, beta_jb, ord_cuspInftyBar_coeffEmb_qExpand (p * p) p (Dvd.intro p rfl),
    ord_cuspInftyBar_coeffEmb_jq] at h
  have : ((cuspInftyBar (p * p)).ramificationIndexAlong (heckeBetaBar 𝕂 p p) : ℤ) = p := by linarith
  exact_mod_cast this

theorem f_alpha_inf (hα : HeckeAlphaBarIntegral 𝕂 p p) : (cuspInftyBar (p * p)).inertiaDegAlong (heckeAlphaBar 𝕂 p p) hα = 1 := by
  have h := deg_restrictAlong_mul_inertiaDegAlong (K := 𝕂) (heckeAlphaBar 𝕂 p p) hα (cuspInftyBar (p * p))
  rwa [inf_restrictAlong_alpha p hα, deg_cuspInftyBar, deg_cuspInftyBar, one_mul] at h

theorem f_beta_inf (hβ : HeckeBetaBarIntegral 𝕂 p p) : (cuspInftyBar (p * p)).inertiaDegAlong (heckeBetaBar 𝕂 p p) hβ = 1 := by
  have h := deg_restrictAlong_mul_inertiaDegAlong (K := 𝕂) (heckeBetaBar 𝕂 p p) hβ (cuspInftyBar (p * p))
  rwa [inf_restrictAlong_beta p hβ, deg_cuspInftyBar, deg_cuspInftyBar, one_mul] at h

theorem finite_along_beta (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) :
    letI := algebraAlong (heckeBetaBar 𝕂 p p)
    FiniteDimensional (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) := by
  letI := algebraAlong (heckeBetaBar 𝕂 p p)
  have h : 0 < Module.finrank (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) := by
    have := finrankAlong_beta p h2
    unfold finrankAlong at this
    rw [this]; exact hp.out.pos
  exact Module.finite_of_finrank_pos h

theorem finite_along_alpha :
    letI := algebraAlong (heckeAlphaBar 𝕂 p p)
    FiniteDimensional (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) := by
  letI := algebraAlong (heckeAlphaBar 𝕂 p p)
  have h : 0 < Module.finrank (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) := by
    have := finrankAlong_alpha p
    unfold finrankAlong at this
    rw [this]; exact hp.out.pos
  exact Module.finite_of_finrank_pos h

theorem restrictAlong_beta_eq_inf_iff (hβ : HeckeBetaBarIntegral 𝕂 p p) (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p)))
    (W : Place 𝕂 (modularFunctionFieldBar (p * p))) :
    W.restrictAlong (heckeBetaBar 𝕂 p p) hβ = cuspInftyBar p ↔ W = cuspInftyBar (p * p) := by
  classical
  refine ⟨fun hW => ?_, fun hW => hW ▸ inf_restrictAlong_beta p hβ⟩
  by_contra hne
  letI := algebraAlong (heckeBetaBar 𝕂 p p)
  haveI := isScalarTower_along (heckeBetaBar 𝕂 p p)
  haveI := isIntegral_along (heckeBetaBar 𝕂 p p) hβ
  haveI := finite_along_beta p h2
  haveI : Algebra.IsSeparable (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank (F := modularFunctionFieldBar p)
    (cuspInftyBar p) ({cuspInftyBar (p * p), W} : Finset _) (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact inf_restrictAlong_beta p hβ
      · rw [Finset.mem_singleton.mp hw]; exact hW)
  rw [Finset.sum_pair (Ne.symm hne)] at hsum
  have hfin : (Module.finrank (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) : ℤ) = p := by
    have := finrankAlong_beta p h2
    unfold finrankAlong at this
    exact_mod_cast this
  have e1 : ((cuspInftyBar (p * p)).ramificationIndex (modularFunctionFieldBar p) : ℤ) = p := by
    exact_mod_cast e_beta_inf p hβ
  have f1 : ((cuspInftyBar (p * p)).inertiaDeg (modularFunctionFieldBar p) : ℤ) = 1 := by
    exact_mod_cast f_beta_inf p hβ
  have ew : (1 : ℤ) ≤ (W.ramificationIndex (modularFunctionFieldBar p) : ℤ) := by
    exact_mod_cast W.ramificationIndex_pos
  have fw : (1 : ℤ) ≤ (W.inertiaDeg (modularFunctionFieldBar p) : ℤ) := by
    exact_mod_cast Place.inertiaDeg_pos (F := modularFunctionFieldBar p) W
  rw [hfin, e1, f1] at hsum
  nlinarith

end Cusps

section Zero

local notation "𝕂" => AlgebraicClosure ℚ

variable (p : ℕ) [hp : Fact p.Prime]

theorem frickeBar_mul_self (N : ℕ) [NeZero N] : frickeInvolutionBar N * frickeInvolutionBar N = 1 := by
  have h : frickeInvolutionFull N * frickeInvolutionFull N = 1 :=
    AlgEquiv.ext fun x => frickeInvolutionFull_apply_apply N x
  rw [frickeInvolutionBar_def, ← map_mul, h, map_one]

theorem frickeBar_smul_smul (N : ℕ) [NeZero N] (P : Place 𝕂 (modularFunctionFieldBar N)) :
    frickeInvolutionBar N • frickeInvolutionBar N • P = P := by
  rw [smul_smul, frickeBar_mul_self, one_smul]

theorem sqT (hα : HeckeAlphaBarIntegral 𝕂 p p) (hβ : HeckeBetaBarIntegral 𝕂 p p)
    (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) (W : Place 𝕂 (modularFunctionFieldBar (p * p))) :
    (frickeInvolutionBar (p * p) • W).restrictAlong (heckeAlphaBar 𝕂 p p) hα
      = frickeInvolutionBar p • W.restrictAlong (heckeBetaBar 𝕂 p p) hβ :=
  smul_restrictAlong _ _ hα hβ _ _ (alpha_fricke_eq_fricke_beta p h2) W

theorem zero_restrictAlong_alpha (hα : HeckeAlphaBarIntegral 𝕂 p p) (hβ : HeckeBetaBarIntegral 𝕂 p p)
    (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) :
    (cuspZeroBar (p * p)).restrictAlong (heckeAlphaBar 𝕂 p p) hα = cuspZeroBar p := by
  rw [cuspZeroBar_def, sqT p hα hβ h2, inf_restrictAlong_beta p hβ, ← cuspZeroBar_def]

theorem zero_restrictAlong_beta (hα : HeckeAlphaBarIntegral 𝕂 p p) (hβ : HeckeBetaBarIntegral 𝕂 p p)
    (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) :
    (cuspZeroBar (p * p)).restrictAlong (heckeBetaBar 𝕂 p p) hβ = cuspZeroBar p := by
  have h := sqT p hα hβ h2 (cuspZeroBar (p * p))
  rw [cuspZeroBar_def (p * p), frickeBar_smul_smul, inf_restrictAlong_alpha p hα] at h
  have h' := congrArg (frickeInvolutionBar p • ·) h
  simp only [frickeBar_smul_smul] at h'
  rw [cuspZeroBar_def (p * p), ← h', ← cuspZeroBar_def]

theorem e_beta_zero (hα : HeckeAlphaBarIntegral 𝕂 p p)
    (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) : (cuspZeroBar (p * p)).ramificationIndexAlong (heckeBetaBar 𝕂 p p) = 1 := by
  have h := ramificationIndexAlong_smul _ _ (frickeInvolutionBar (p * p)) (frickeInvolutionBar p)
    (alpha_fricke_eq_fricke_beta p h2) (cuspZeroBar (p * p))
  rw [cuspZeroBar_def (p * p), frickeBar_smul_smul, e_alpha_inf p hα] at h
  rw [cuspZeroBar_def]; exact h.symm

theorem f_alpha_zero (hα : HeckeAlphaBarIntegral 𝕂 p p) (hβ : HeckeBetaBarIntegral 𝕂 p p)
    (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) :
    (cuspZeroBar (p * p)).inertiaDegAlong (heckeAlphaBar 𝕂 p p) hα = 1 := by
  have h := deg_restrictAlong_mul_inertiaDegAlong (K := 𝕂) (heckeAlphaBar 𝕂 p p) hα (cuspZeroBar (p * p))
  rwa [zero_restrictAlong_alpha p hα hβ h2, deg_cuspZeroBar, deg_cuspZeroBar, one_mul] at h

theorem isIntegral_jb_over_jbp (data : ModularPolynomialData p) (hsymm : EvalSymm data.Φ) :
    IsIntegral (Algebra.adjoin 𝕂 {heckeBetaBar 𝕂 p p (jb p)}) (jb (p * p)) := by
  set x : modularFunctionFieldBar (p * p) := heckeBetaBar 𝕂 p p (jb p) with hx
  let φ : Polynomial ℤ →+* Algebra.adjoin 𝕂 ({x} : Set (modularFunctionFieldBar (p * p))) :=
    (Polynomial.aeval (R := ℤ) (⟨x, Algebra.self_mem_adjoin_singleton 𝕂 x⟩ :
      Algebra.adjoin 𝕂 ({x} : Set (modularFunctionFieldBar (p * p))))).toRingHom
  refine ⟨data.Φ.map φ, data.monic.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap (Algebra.adjoin 𝕂 ({x} : Set (modularFunctionFieldBar (p * p))))
      (modularFunctionFieldBar (p * p))).comp φ = (Polynomial.aeval (R := ℤ) x).toRingHom := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [φ]
  rw [hcomp]
  apply Subtype.val_injective
  show ((data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom (jb (p * p)) : modularFunctionFieldBar (p * p)) :
      LaurentSeries 𝕂) = ((0 : modularFunctionFieldBar (p * p)) : LaurentSeries 𝕂)
  rw [show (((data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom (jb (p * p))) : modularFunctionFieldBar (p * p)) :
        LaurentSeries 𝕂) = algebraMap (modularFunctionFieldBar (p * p)) (LaurentSeries 𝕂)
          (data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom (jb (p * p))) from rfl,
    Polynomial.hom_eval₂]
  have hx' : algebraMap (modularFunctionFieldBar (p * p)) (LaurentSeries 𝕂) x = coeffEmb 𝕂 (jqN p) := by
    show ((heckeBetaBar 𝕂 p p (jb p) : modularFunctionFieldBar (p * p)) : LaurentSeries 𝕂) = _
    rw [beta_jb]; rfl
  have hc2 : (algebraMap (modularFunctionFieldBar (p * p)) (LaurentSeries 𝕂)).comp (Polynomial.aeval (R := ℤ) x).toRingHom
      = (coeffEmb 𝕂).comp (Polynomial.aeval (R := ℤ) (jqN p)).toRingHom := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
    exact hx'
  rw [hc2, show algebraMap (modularFunctionFieldBar (p * p)) (LaurentSeries 𝕂) (jb (p * p)) = coeffEmb 𝕂 jq from rfl,
    ← Polynomial.hom_eval₂, ← hsymm jq (jqN p),
    show (Polynomial.aeval (R := ℤ) jq).toRingHom = evalAtJ from rfl, data.eval_eq_zero, map_zero]
  rfl

theorem mid_restrictAlong_beta (hα : HeckeAlphaBarIntegral 𝕂 p p) (hβ : HeckeBetaBarIntegral 𝕂 p p)
    (h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p))) (M : Place 𝕂 (modularFunctionFieldBar (p * p)))
    (hM : M.restrictAlong (heckeAlphaBar 𝕂 p p) hα = cuspInftyBar p) (hne : M ≠ cuspInftyBar (p * p)) :
    M.restrictAlong (heckeBetaBar 𝕂 p p) hβ = cuspZeroBar p := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm p

  have hj : jb (p * p) ∉ M.toValuationSubring := by
    intro hmem
    have : jb p ∈ (M.restrictAlong (heckeAlphaBar 𝕂 p p) hα).toValuationSubring := by
      rw [mem_restrictAlong_iff, alpha_jb]; exact hmem
    rw [hM] at this
    exact isCusp_cuspInftyBar p this

  have hjp : heckeBetaBar 𝕂 p p (jb p) ∉ M.toValuationSubring := fun hmem =>
    hj (M.mem_toValuationSubring_of_isIntegral_adjoin hmem (isIntegral_jb_over_jbp p data hsymm))
  have hc : IsCusp (jb p) (M.restrictAlong (heckeBetaBar 𝕂 p p) hβ) := by
    rw [isCusp_iff, mem_restrictAlong_iff]; exact hjp
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar p _ hc with h | h
  · exact absurd ((restrictAlong_beta_eq_inf_iff p hβ h2 M).mp h) hne
  · exact h

end Zero

section Discharge

local notation "𝕂" => AlgebraicClosure ℚ

variable (p : ℕ) [hp : Fact p.Prime]

open scoped Classical in

def Mid (hα : HeckeAlphaBarIntegral 𝕂 p p) [HasPrincipalDivisors 𝕂 (modularFunctionFieldBar (p * p))] :
    Finset (Place 𝕂 (modularFunctionFieldBar (p * p))) :=
  (Place.fiberAlong (heckeAlphaBar 𝕂 p p) hα (cuspInftyBar p)).erase (cuspInftyBar (p * p))

open scoped Classical in

def Smid (hα : HeckeAlphaBarIntegral 𝕂 p p) [HasPrincipalDivisors 𝕂 (modularFunctionFieldBar (p * p))] :
    Finset (Place 𝕂 (modularFunctionFieldBar (p * p))) :=
  (Mid p hα).image (frickeInvolutionBar (p * p) • ·)

variable {p} in
theorem mem_Mid_iff (hα : HeckeAlphaBarIntegral 𝕂 p p) [HasPrincipalDivisors 𝕂 (modularFunctionFieldBar (p * p))]
    (M : Place 𝕂 (modularFunctionFieldBar (p * p))) :
    M ∈ Mid p hα ↔ M ≠ cuspInftyBar (p * p) ∧ M.restrictAlong (heckeAlphaBar 𝕂 p p) hα = cuspInftyBar p := by
  classical
  rw [Mid, Finset.mem_erase, Place.mem_fiberAlong]

variable {p} in
theorem mem_Smid_iff (hα : HeckeAlphaBarIntegral 𝕂 p p) [HasPrincipalDivisors 𝕂 (modularFunctionFieldBar (p * p))]
    (V : Place 𝕂 (modularFunctionFieldBar (p * p))) :
    V ∈ Smid p hα ↔ ∃ M ∈ Mid p hα, frickeInvolutionBar (p * p) • M = V := by
  classical
  rw [Smid, Finset.mem_image]

theorem frickeBar_smul_injective (N : ℕ) [NeZero N] :
    Function.Injective (frickeInvolutionBar N • · : Place 𝕂 (modularFunctionFieldBar N) → Place 𝕂 (modularFunctionFieldBar N)) :=
  fun P Q h => by simpa [frickeBar_smul_smul] using congrArg (frickeInvolutionBar N • ·) h

end Discharge

end FibreSol
p2m_reactivate "P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_prime.FibreSol"

end
p2m_reactivate "P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_prime.FibreSol"

p2m_open "ModularCurve~mem_restrictAlong_iff" in open AlgebraicCurve FibreSol in
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))] : heckeDivBar hα hβ (cuspidalDivisor p) = cuspidalDivisor p := by
  classical
  have h2 : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p)) := isFrickeAutFull_frickeInvolutionFull_sq p

  have hMidβ : ∀ M ∈ Mid p hα, M.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ = cuspZeroBar p := fun M hM =>
    mid_restrictAlong_beta p hα hβ h2 M ((mem_Mid_iff hα M).mp hM).2 ((mem_Mid_iff hα M).mp hM).1
  have hSmidα : ∀ V ∈ Smid p hα, V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα = cuspInftyBar p := by
    intro V hV
    obtain ⟨M, hM, rfl⟩ := (mem_Smid_iff hα V).mp hV
    show (frickeInvolutionBar (p * p) • M).restrictAlong _ hα = _
    rw [sqT p hα hβ h2 M, hMidβ M hM, cuspZeroBar_def, frickeBar_smul_smul]
  refine heckeDivBar_cuspidalDivisor_self_of_sum p hα hβ (cuspInftyBar (p * p)) ?_ ?_ (inf_restrictAlong_alpha p hα)
    (cuspZeroBar (p * p)) (Smid p hα) ?_ ?_ ?_ (zero_restrictAlong_alpha p hα hβ h2) ?_ hSmidα

  · intro W'
    rw [Place.mem_fiberAlong]
    exact restrictAlong_beta_eq_inf_iff p hβ h2 W'

  · rw [e_beta_inf p hβ, f_alpha_inf p hα, mul_one]

  · intro hV
    obtain ⟨M, hM, hMV⟩ := (mem_Smid_iff hα _).mp hV
    have hM' : M = cuspInftyBar (p * p) := by
      have := congrArg (frickeInvolutionBar (p * p) • ·) hMV
      simp only [frickeBar_smul_smul] at this
      rw [this, cuspZeroBar_def, frickeBar_smul_smul]
    exact ((mem_Mid_iff hα M).mp hM).1 hM'

  · intro V
    rw [Place.mem_fiberAlong]
    constructor
    · intro hVβ
      by_cases hV : V = cuspZeroBar (p * p)
      · exact Or.inl hV
      · refine Or.inr ((mem_Smid_iff hα V).mpr ⟨frickeInvolutionBar (p * p) • V, (mem_Mid_iff hα _).mpr ⟨?_, ?_⟩, frickeBar_smul_smul _ V⟩)
        · intro hM
          apply hV
          have := congrArg (frickeInvolutionBar (p * p) • ·) hM
          simp only [frickeBar_smul_smul] at this
          rw [this, cuspZeroBar_def]
        · rw [sqT p hα hβ h2 V, hVβ, cuspZeroBar_def, frickeBar_smul_smul]
    · rintro (rfl | hV)
      · exact zero_restrictAlong_beta p hα hβ h2
      · obtain ⟨M, hM, rfl⟩ := (mem_Smid_iff hα V).mp hV
        have h := sqT p hα hβ h2 (frickeInvolutionBar (p * p) • M)
        rw [frickeBar_smul_smul, ((mem_Mid_iff hα M).mp hM).2] at h
        have h' := congrArg (frickeInvolutionBar p • ·) h
        simp only [frickeBar_smul_smul] at h'
        rw [← h', ← cuspZeroBar_def]

  · rw [e_beta_zero p hα h2, f_alpha_zero p hα hβ h2]

  · rw [Smid, Finset.sum_image (fun M _ M' _ h => frickeBar_smul_injective (p * p) h)]

    have hterm : ∀ M ∈ Mid p hα,
        (frickeInvolutionBar (p * p) • M).ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) * (frickeInvolutionBar (p * p) • M).inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα
          = M.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) * M.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα := by
      intro M hM
      have he := ramificationIndexAlong_smul _ _ (frickeInvolutionBar (p * p)) (frickeInvolutionBar p) (alpha_fricke_eq_fricke_beta p h2) (frickeInvolutionBar (p * p) • M)
      rw [frickeBar_smul_smul] at he
      have hdegβ : (M.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ).deg = 1 := by rw [hMidβ M hM, deg_cuspZeroBar]
      have hf := inertiaDegAlong_smul _ _ hα hβ (frickeInvolutionBar (p * p)) (frickeInvolutionBar p) (alpha_fricke_eq_fricke_beta p h2) M hdegβ

      have hfa := deg_restrictAlong_mul_inertiaDegAlong (K := (AlgebraicClosure ℚ)) (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα M
      have hfb := deg_restrictAlong_mul_inertiaDegAlong (K := (AlgebraicClosure ℚ)) (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ M
      rw [((mem_Mid_iff hα M).mp hM).2, deg_cuspInftyBar, one_mul] at hfa
      rw [hdegβ, one_mul] at hfb
      rw [← he, hf, hfb, ← hfa]
    rw [Finset.sum_congr rfl hterm]

    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p)
    haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) p p)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα
    haveI := finite_along_alpha p
    haveI : Algebra.IsSeparable (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    have hsum := Place.sum_ramificationIndex_mul_inertiaDeg (F' := modularFunctionFieldBar (p * p)) (cuspInftyBar p)
    have hfib : Place.fiber (modularFunctionFieldBar (p * p)) (cuspInftyBar p)
        = insert (cuspInftyBar (p * p)) (Mid p hα) := by
      rw [Mid, Finset.insert_erase (Place.mem_fiberAlong.mpr (inf_restrictAlong_alpha p hα))]
      rfl
    have hnot : cuspInftyBar (p * p) ∉ Mid p hα := fun h => ((mem_Mid_iff hα _).mp h).1 rfl
    rw [hfib, Finset.sum_insert hnot] at hsum
    have hfin : (Module.finrank (modularFunctionFieldBar p) (modularFunctionFieldBar (p * p)) : ℤ) = p := by
      have := finrankAlong_alpha p
      unfold finrankAlong at this
      exact_mod_cast this
    have e1 : ((cuspInftyBar (p * p)).ramificationIndex (modularFunctionFieldBar p) : ℤ) = 1 := by
      exact_mod_cast e_alpha_inf p hα
    have f1 : ((cuspInftyBar (p * p)).inertiaDeg (modularFunctionFieldBar p) : ℤ) = 1 := by
      exact_mod_cast f_alpha_inf p hα
    rw [hfin, e1, f1] at hsum
    have hsum' : ((∑ M ∈ Mid p hα, M.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) *
        M.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα : ℕ) : ℤ) = p - 1 := by
      push_cast
      show ∑ M ∈ Mid p hα, ((M.ramificationIndex (modularFunctionFieldBar p) : ℤ) *
        (M.inertiaDeg (modularFunctionFieldBar p) : ℤ)) = p - 1
      linarith
    have hp1 : 1 ≤ p := hp.out.one_le
    omega

end S_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_prime
end P2MW
export P2MW.S_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_prime (solution)

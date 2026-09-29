-- Prove2me | solution 1 for ModularCurve.heckeDivBar_self_add_frickeInvolutionBar_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8e07cd79-a344-54fd-b6bf-2eda4b4a0732

import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
import Theorems.Thm_ModularCurve_heckeRoof_adjoin_range_union_eq_top
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import Theorems.Thm_ModularCurve_towerInclBar_surjective_of_dvd_dvd
import Theorems.Thm_ModularCurve_towerInclBar_finiteAlong
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_heckeAlphaBar_frickeInvolutionBar_sq
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_order_qExpand
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_coeffEmb_injective
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDivBar_self_add_frickeInvolutionBar_smul
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_heckeDivBar_self_add_frickeInvolutionBar_smul.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_heckeDivBar_self_add_frickeInvolutionBar_smul.ModularCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FiniteAlong finrankAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.correspondence Place.ord_restrictAlong Divisor.pushforwardAlong_single Place.restrictAlong_congr Place.fiberAlong Place.mem_fiberAlong Divisor.pullbackAlong_single Place.fiber Place Divisor HasPrincipalDivisors Place.ord_smul Divisor.smul_single Place.fiber_eq_fiberOver Divisor.correspondence_single Place.restrictAlong_restrictAlong Place.smul_restrictAlong"
p2m_open "AlgebraicCurve"

universe uK uF₁ uF uF'

section NormMackey

variable {K : Type uK} {F₁ : Type uF₁} {F : Type uF} {F' : Type uF'}
  [Field K] [Field F₁] [Field F] [Field F'] [Algebra K F₁] [Algebra K F] [Algebra K F']

private noncomputable def normAlong {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) :
    B →* A :=
  letI := algebraAlong φ
  Algebra.norm A

private theorem ringHom_ext_of_adjoin_range_union {R : Type*} [Semiring R]
    (α β : F →ₐ[K] F') (hgen : Algebra.adjoin K (Set.range α ∪ Set.range β) = ⊤)
    (f g : F' →+* R) (hα : ∀ x, f (α x) = g (α x)) (hβ : ∀ x, f (β x) = g (β x)) : f = g := by
  refine RingHom.ext fun y => ?_
  have hy : y ∈ Algebra.adjoin K (Set.range α ∪ Set.range β) := hgen ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact hα x
      · exact hβ x
  | algebraMap k =>
      have h := hα (algebraMap K F k)
      rwa [α.commutes] at h
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

private theorem normAlong_sq_eq_mul_normAlong [CharZero F₁] [CharZero F]
    (ι σ : F₁ →ₐ[K] F) (α β : F →ₐ[K] F') (w : F ≃ₐ[K] F)
    (hsq : ∀ x, α (σ x) = β (ι x)) (hwι : ∀ x, w (ι x) = σ x) (hwσ : ∀ x, w (σ x) = ι x)
    (hne : ∃ g, β (σ g) ≠ α (ι g))
    (hgen : Algebra.adjoin K (Set.range α ∪ Set.range β) = ⊤)
    (hfinι : FiniteAlong K ι) (hfinα : FiniteAlong K α)
    (hdeg : finrankAlong K ι = finrankAlong K α + 1) (t : F) :
    σ (normAlong ι t) = w t * normAlong α (β t) := by
  classical
  letI algι : Algebra F₁ F := algebraAlong ι
  letI algα : Algebra F F' := algebraAlong α
  haveI : Module.Finite F₁ F := hfinι
  haveI : Module.Finite F F' := hfinα
  haveI : Algebra.IsSeparable F₁ F := Algebra.IsSeparable.of_integral F₁ F
  haveI : Algebra.IsSeparable F F' := Algebra.IsSeparable.of_integral F F'

  let Ω := AlgebraicClosure F'
  letI algΩ₁ : Algebra F₁ Ω := ((algebraMap F Ω).comp σ.toRingHom).toAlgebra
  have hE : ∀ x : F, algebraMap F Ω x = algebraMap F' Ω (α x) := fun x =>
    IsScalarTower.algebraMap_apply F F' Ω x
  have hE₁ : ∀ g : F₁, algebraMap F₁ Ω g = algebraMap F Ω (σ g) := fun _ => rfl

  let τ₀ : F →ₐ[F₁] Ω :=
    { (algebraMap F Ω).comp (w : F →+* F) with
      commutes' := fun g => by
        show algebraMap F Ω (w (ι g)) = algebraMap F₁ Ω g
        rw [hwι, hE₁] }

  let τ : (F' →ₐ[F] Ω) → (F →ₐ[F₁] Ω) := fun θ =>
    { (θ : F' →+* Ω).comp (β : F →+* F') with
      commutes' := fun g => by
        show θ (β (ι g)) = algebraMap F₁ Ω g
        rw [← hsq, hE₁]
        exact θ.commutes (σ g) }
  let Φ : Option (F' →ₐ[F] Ω) → (F →ₐ[F₁] Ω) := fun o => o.elim τ₀ τ
  have hΦ_none : ∀ x, Φ none x = algebraMap F Ω (w x) := fun _ => rfl
  have hΦ_some : ∀ θ x, Φ (some θ) x = θ (β x) := fun _ _ => rfl

  have hinj : Function.Injective Φ := by
    rintro (_ | θ) (_ | θ') h
    · rfl
    · exfalso
      obtain ⟨g, hg⟩ := hne
      have h1 : Φ none (σ g) = Φ (some θ') (σ g) := by rw [h]
      rw [hΦ_none, hΦ_some, hwσ, hE] at h1

      have h2 : θ' (α (ι g)) = θ' (β (σ g)) := by
        rw [← h1]
        exact (θ'.commutes (ι g)).trans (hE (ι g))
      exact hg (θ'.toRingHom.injective h2).symm
    · exfalso
      obtain ⟨g, hg⟩ := hne
      have h1 : Φ (some θ) (σ g) = Φ none (σ g) := by rw [h]
      rw [hΦ_none, hΦ_some, hwσ, hE] at h1
      have h2 : θ (β (σ g)) = θ (α (ι g)) := by
        rw [h1]
        exact ((θ.commutes (ι g)).trans (hE (ι g))).symm
      exact hg (θ.toRingHom.injective h2)
    · have hθ : (θ : F' →+* Ω) = (θ' : F' →+* Ω) := by
        refine ringHom_ext_of_adjoin_range_union α β hgen _ _ (fun x => ?_) (fun x => ?_)
        · show θ (algebraMap F F' x) = θ' (algebraMap F F' x)
          rw [θ.commutes, θ'.commutes]
        · have h1 : Φ (some θ) x = Φ (some θ') x := by rw [h]
          rwa [hΦ_some, hΦ_some] at h1
      rw [AlgHom.coe_ringHom_injective hθ]

  have hcard : Fintype.card (Option (F' →ₐ[F] Ω)) = Fintype.card (F →ₐ[F₁] Ω) := by
    rw [Fintype.card_option, AlgHom.card, AlgHom.card]
    exact hdeg.symm
  have hbij : Function.Bijective Φ := (Fintype.bijective_iff_injective_and_card Φ).mpr ⟨hinj, hcard⟩

  have hprod : (∏ τ' : F →ₐ[F₁] Ω, τ' t) = algebraMap F Ω (w t) * ∏ θ : F' →ₐ[F] Ω, θ (β t) := by
    rw [← Fintype.prod_bijective Φ hbij (fun o => Φ o t) (fun τ' => τ' t) (fun _ => rfl),
      Fintype.prod_option]
    rfl
  have key : algebraMap F Ω (σ (normAlong ι t)) = algebraMap F Ω (w t * normAlong α (β t)) := by
    rw [map_mul, ← hE₁]
    show algebraMap F₁ Ω (Algebra.norm F₁ t) = algebraMap F Ω (w t) * algebraMap F Ω (Algebra.norm F (β t))
    rw [Algebra.norm_eq_prod_embeddings F₁ Ω t, Algebra.norm_eq_prod_embeddings F Ω (β t), hprod]
  exact (algebraMap F Ω).injective key

private theorem finrankAlong_eq_of_equiv_equiv {A B A' B' : Type*} [Field A] [Field B]
    [Field A'] [Field B'] [Algebra K A] [Algebra K B] [Algebra K A'] [Algebra K B']
    (φ : A →ₐ[K] B) (φ' : A' →ₐ[K] B') (i : A ≃+* A') (j : B ≃+* B')
    (hc : ∀ a, φ' (i a) = j (φ a)) : finrankAlong K φ = finrankAlong K φ' := by
  letI := algebraAlong φ
  letI := algebraAlong φ'
  exact Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext fun a => hc a)

end NormMackey

end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "towerInclBar coe_towerInclBar towerInclBar_comp_towerInclBar towerSubstBar coe_towerSubstBar heckeAlphaBar_eq_towerInclBar dvd_of_eq_roof heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral heckeDivBar modularFunctionFieldBar qExpand qExpand_one_apply qExpand_qExpand jq modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange frickeInvolutionBar order_jq jq_mem_full heckeRoof_adjoin_range_union_eq_top functionFieldGeneration nonempty_modularPolynomialData_of_squarefree towerInclBar_surjective_of_dvd_dvd towerInclBar_finiteAlong finiteAlong_heckeAlphaBar_of_prime finrankAlong_heckeBetaBar heckeAlphaBar_frickeInvolutionBar_sq frickeInvolutionBar_frickeInvolutionBar isFrickeAutFull_frickeInvolutionFull_prime frickeInvolutionBar_coeffEmb_qExpand order_qExpand coeffEmb_qExpand coeffEmb_injective adjoin_jBar_jNBar_eq_top"
p2m_open "ModularCurve"

section TowerNormIdentity

variable (L : Type*) [Field L] [Algebra ℚ L] (p : ℕ) [Fact p.Prime]

private theorem adjoin_range_heckeAlphaBar_union_range_heckeBetaBar_self :
    Algebra.adjoin L (Set.range (heckeAlphaBar L p p) ∪ Set.range (heckeBetaBar L p p)) = ⊤ := by
  have hM : p * p = 1 * p * p := by rw [one_mul]
  have h1p : 1 * p ∣ p := by rw [one_mul]
  have hp1 : p ∣ 1 * p := by rw [one_mul]
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree p
    (Fact.out : p.Prime).prime.squarefree (Fact.out : p.Prime).one_lt
  have hroof := heckeRoof_adjoin_range_union_eq_top L 1 p p (p * p) hM
    (functionFieldGeneration (p * p)) data
  have he : Function.Surjective (towerInclBar L h1p) :=
    towerInclBar_surjective_of_dvd_dvd L h1p hp1
  have hincl : towerInclBar L (dvd_of_eq_roof 1 p p (p * p) hM).1 =
      (heckeAlphaBar L p p).comp (towerInclBar L h1p) := by
    rw [heckeAlphaBar_eq_towerInclBar]
    exact (towerInclBar_comp_towerInclBar L h1p (dvd_mul_right p p) _).symm
  have hsubst : towerSubstBar L (1 * p) p (dvd_of_eq_roof 1 p p (p * p) hM).2 =
      (heckeBetaBar L p p).comp (towerInclBar L h1p) := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    rw [coe_towerSubstBar, AlgHom.comp_apply, coe_heckeBetaBar, coe_towerInclBar]
  rw [hincl, hsubst, AlgHom.coe_comp, AlgHom.coe_comp, Set.range_comp, Set.range_comp,
    he.range_eq, Set.image_univ, Set.image_univ, Set.union_comm] at hroof
  exact hroof

private theorem finrankAlong_heckeAlphaBar_self :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) p p) = p := by
  rw [← finrankAlong_eq_of_equiv_equiv (heckeBetaBar (AlgebraicClosure ℚ) p p)
    (heckeAlphaBar (AlgebraicClosure ℚ) p p) (frickeInvolutionBar p).toRingEquiv
    (frickeInvolutionBar (p * p)).toRingEquiv (fun a => heckeAlphaBar_frickeInvolutionBar_sq p a),
    finrankAlong_heckeBetaBar (AlgebraicClosure ℚ) p p, if_pos dvd_rfl]

private theorem finrankAlong_towerSubstBar_one :
    finrankAlong L (towerSubstBar L 1 p ((one_mul p).dvd)) = p + 1 := by
  have h1p : 1 * p ∣ p := (one_mul p).dvd
  have hp1 : p ∣ 1 * p := (one_mul p).symm.dvd
  let e : laurentBaseChange L (modularFunctionFieldFull (1 * p)) ≃ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull p) :=
    AlgEquiv.ofBijective (towerInclBar L h1p)
      ⟨(towerInclBar L h1p).toRingHom.injective, towerInclBar_surjective_of_dvd_dvd L h1p hp1⟩
  rw [← finrankAlong_eq_of_equiv_equiv (heckeBetaBar L 1 p) (towerSubstBar L 1 p h1p)
    (RingEquiv.refl _) e.toRingEquiv (fun a => rfl), finrankAlong_heckeBetaBar L 1 p, if_neg]
  exact fun h => (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h)

private theorem finrankAlong_towerInclBar_one_eq
    (hwι : ∀ x, frickeInvolutionBar p (towerInclBar (AlgebraicClosure ℚ) (one_dvd p) x) =
      towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) x) :
    finrankAlong (AlgebraicClosure ℚ) (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) =
      finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) p p) + 1 := by
  rw [finrankAlong_eq_of_equiv_equiv (towerInclBar (AlgebraicClosure ℚ) (one_dvd p))
    (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)) (RingEquiv.refl _)
    (frickeInvolutionBar p).toRingEquiv (fun a => (hwι a).symm),
    finrankAlong_towerSubstBar_one (AlgebraicClosure ℚ) p, finrankAlong_heckeAlphaBar_self p]

private theorem heckeAlphaBar_towerSubstBar_eq_heckeBetaBar_towerInclBar
    (x : laurentBaseChange L (modularFunctionFieldFull 1)) :
    heckeAlphaBar L p p (towerSubstBar L 1 p ((one_mul p).dvd) x) =
      heckeBetaBar L p p (towerInclBar L (one_dvd p) x) :=
  Subtype.ext <| by
    rw [coe_heckeAlphaBar, coe_towerSubstBar, coe_heckeBetaBar, coe_towerInclBar]

private theorem towerSubstBar_normAlong_towerInclBar
    (hwι : ∀ x, frickeInvolutionBar p (towerInclBar (AlgebraicClosure ℚ) (one_dvd p) x) =
      towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) x)
    (hwσ : ∀ x, frickeInvolutionBar p (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) x) =
      towerInclBar (AlgebraicClosure ℚ) (one_dvd p) x)
    (hne : ∃ g, heckeBetaBar (AlgebraicClosure ℚ) p p
        (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) g) ≠
      heckeAlphaBar (AlgebraicClosure ℚ) p p (towerInclBar (AlgebraicClosure ℚ) (one_dvd p) g))
    (t : modularFunctionFieldBar p) :
    towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)
        (normAlong (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) t) =
      frickeInvolutionBar p t *
        normAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) (heckeBetaBar (AlgebraicClosure ℚ) p p t) := by
  haveI : CharZero (modularFunctionFieldBar 1) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  haveI : CharZero (modularFunctionFieldBar p) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  exact normAlong_sq_eq_mul_normAlong _ _ _ _ (frickeInvolutionBar p)
    (heckeAlphaBar_towerSubstBar_eq_heckeBetaBar_towerInclBar (AlgebraicClosure ℚ) p) hwι hwσ hne
    (adjoin_range_heckeAlphaBar_union_range_heckeBetaBar_self (AlgebraicClosure ℚ) p)
    (towerInclBar_finiteAlong (AlgebraicClosure ℚ) (one_dvd p))
    (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) p p)
    (finrankAlong_towerInclBar_one_eq p hwι) t

end TowerNormIdentity

end ModularCurve

set_option autoImplicit false

namespace HaAux2

private theorem frickeInvolutionBar_mul_self (N : ℕ) [NeZero N] :
    frickeInvolutionBar N * frickeInvolutionBar N = 1 :=
  AlgEquiv.ext (frickeInvolutionBar_frickeInvolutionBar N)

private theorem frickeInvolutionBar_inv (N : ℕ) [NeZero N] :
    (frickeInvolutionBar N)⁻¹ = frickeInvolutionBar N :=
  (eq_inv_of_mul_eq_one_right (frickeInvolutionBar_mul_self N)).symm

private theorem frickeInvolutionBar_smul_smul {N : ℕ} [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    frickeInvolutionBar N • (frickeInvolutionBar N • v) = v := by
  rw [← mul_smul, frickeInvolutionBar_mul_self, one_smul]

private theorem qExpand_sq_jq_ne_jq (p : ℕ) [hp : Fact p.Prime] :
    qExpand ℚ (p * p) jq ≠ jq := by
  intro h
  have ho := congrArg HahnSeries.order h
  rw [order_qExpand, order_jq] at ho
  simp only [mul_neg, mul_one, neg_inj] at ho
  have hp2 : (2 : ℕ) ≤ p := hp.out.two_le
  have : (p * p : ℤ) = 1 := by exact_mod_cast ho
  nlinarith [this, (show (2 : ℤ) ≤ p from by exact_mod_cast hp2)]

section F1

variable (p : ℕ) [hp : Fact p.Prime]

private theorem fricke_legs_on_jq
    (h1 : coeffEmb (AlgebraicClosure ℚ) jq
      ∈ laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull 1)) :
    towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) ⟨_, h1⟩
      = frickeInvolutionBar p (towerInclBar (AlgebraicClosure ℚ) (one_dvd p) ⟨_, h1⟩) := by
  set L := AlgebraicClosure ℚ
  apply Subtype.ext
  rw [coe_towerSubstBar, ← coeffEmb_qExpand]

  have hι : towerInclBar L (one_dvd p) ⟨coeffEmb L jq, h1⟩
      = ⟨coeffEmb L (qExpand ℚ 1 jq),
          coeffEmb_mem_laurentBaseChange L (jqd_mem_full p (Dvd.intro p (one_mul p)))⟩ :=
    Subtype.ext ((coe_towerInclBar L (one_dvd p) _).trans
      (congrArg (coeffEmb L) (qExpand_one_apply jq).symm))
  rw [hι, congrArg Subtype.val (frickeInvolutionBar_coeffEmb_qExpand p
    (isFrickeAutFull_frickeInvolutionFull_prime p) 1 p (one_mul p))]

private def algHomEqualizer {L A B : Type*} [Field L] [Field A] [Field B]
    [Algebra L A] [Algebra L B] (φ ψ : A →ₐ[L] B) : IntermediateField L A where
  carrier := {x | φ x = ψ x}
  mul_mem' ha hb := by
    show φ _ = ψ _; rw [map_mul, map_mul, show φ _ = ψ _ from ha, show φ _ = ψ _ from hb]
  one_mem' := by show φ 1 = ψ 1; rw [map_one, map_one]
  add_mem' ha hb := by
    show φ _ = ψ _; rw [map_add, map_add, show φ _ = ψ _ from ha, show φ _ = ψ _ from hb]
  zero_mem' := by show φ 0 = ψ 0; rw [map_zero, map_zero]
  algebraMap_mem' r := by show φ _ = ψ _; rw [AlgHom.commutes, AlgHom.commutes]
  inv_mem' x hx := by show φ _ = ψ _; rw [map_inv₀, map_inv₀, show φ x = ψ x from hx]

private theorem mem_algHomEqualizer {L A B : Type*} [Field L] [Field A] [Field B]
    [Algebra L A] [Algebra L B] {φ ψ : A →ₐ[L] B} {x : A} :
    x ∈ algHomEqualizer φ ψ ↔ φ x = ψ x := Iff.rfl

private theorem towerSubstBar_eq_frickeInvolutionBar_towerInclBar
    (x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull 1)) :
    towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) x
      = frickeInvolutionBar p (towerInclBar (AlgebraicClosure ℚ) (one_dvd p) x) := by
  set L := AlgebraicClosure ℚ
  let σm : laurentBaseChange L (modularFunctionFieldFull 1) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull p) :=
    towerSubstBar L 1 p ((one_mul p).dvd)
  let wι : laurentBaseChange L (modularFunctionFieldFull 1) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull p) :=
    (frickeInvolutionBar p).toAlgHom.comp (towerInclBar L (one_dvd p))
  change x ∈ algHomEqualizer σm wι
  have htop : algHomEqualizer σm wι = ⊤ := by
    rw [← top_le_iff, ← adjoin_jBar_jNBar_eq_top L 1]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro y (rfl | rfl)
    · exact fricke_legs_on_jq p _
    · rw [show (⟨coeffEmb L (qExpand ℚ 1 jq),
            coeffEmb_mem_laurentBaseChange L (jqd_mem_full 1 (dvd_refl 1))⟩
          : laurentBaseChange L (modularFunctionFieldFull 1))
        = ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full 1)⟩ from
        Subtype.ext (congrArg (coeffEmb L) (qExpand_one_apply jq))]
      exact fricke_legs_on_jq p _
  rw [htop]; exact IntermediateField.mem_top

private theorem towerInclBar_eq_frickeInvolutionBar_towerSubstBar
    (x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull 1)) :
    towerInclBar (AlgebraicClosure ℚ) (one_dvd p) x
      = frickeInvolutionBar p (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) x) := by
  rw [towerSubstBar_eq_frickeInvolutionBar_towerInclBar, frickeInvolutionBar_frickeInvolutionBar]

end F1

section F3twin

variable (p : ℕ) [hp : Fact p.Prime]

private theorem exists_heckeBetaBar_towerSubstBar_ne_heckeAlphaBar_towerInclBar :
    ∃ g : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull 1),
      heckeBetaBar (AlgebraicClosure ℚ) p p
          (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) g)
        ≠ heckeAlphaBar (AlgebraicClosure ℚ) p p
          (towerInclBar (AlgebraicClosure ℚ) (one_dvd p) g) := by
  set L := AlgebraicClosure ℚ
  refine ⟨⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full 1)⟩, ?_⟩
  intro h
  have hcoe := congrArg Subtype.val h
  rw [coe_heckeBetaBar, coe_towerSubstBar, coe_heckeAlphaBar, coe_towerInclBar] at hcoe
  rw [qExpand_qExpand, ← coeffEmb_qExpand] at hcoe
  exact qExpand_sq_jq_ne_jq p (coeffEmb_injective L hcoe)

end F3twin

end HaAux2

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FiniteAlong finrankAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.correspondence Place.ord_restrictAlong Divisor.pushforwardAlong_single Place.restrictAlong_congr Place.fiberAlong Place.mem_fiberAlong Divisor.pullbackAlong_single Place.fiber Place Divisor HasPrincipalDivisors Place.ord_smul Divisor.smul_single Place.fiber_eq_fiberOver Divisor.correspondence_single Place.restrictAlong_restrictAlong Place.smul_restrictAlong"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong inertiaDegAlong ord_restrictAlong restrictAlong_congr fiberAlong mem_fiberAlong restrict fiber ext ord ord_mul ord_unit_smul_zpow ord_smul algebraMap_mem' toValuationSubring center integralClosureAt forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos fiberEquiv fiberOver mem_fiberOver fiber_eq_fiberOver restrictAlong_restrictAlong smul_restrictAlong ord_norm_eq_sum_fiberOver"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section SeparatingElement

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

private theorem ord_nonneg_of_mem'' {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    (v : Place K₀ F₀) {f : F₀} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F₀) * ((π : F₀) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem exists_ord_pos_forall_ord_eq_zero (v : Place K F) {w : Place K F'}
    (hw : w.restrict F = v) :
    ∃ t : F', t ≠ 0 ∧ 0 < w.ord t ∧
      ∀ w' : Place K F', w'.restrict F = v → w' ≠ w → w'.ord t = 0 := by
  classical
  set s : Finset (Place K F') := (v.fiberOver F').erase w with hs
  set f : Place K F' → Ideal (integralClosureAt F' v) := fun w' =>
    if h : w'.restrict F = v then (fiberCenter F' v h).asIdeal else ⊥ with hfdef
  obtain ⟨c, hcI, hc0, hcnot⟩ :
      ∃ c : integralClosureAt F' v, c ∈ (fiberCenter F' v hw).asIdeal ∧ c ≠ 0 ∧
        ∀ (w' : Place K F') (h' : w'.restrict F = v), w' ≠ w →
          c ∉ (fiberCenter F' v h').asIdeal := by
    rcases Finset.eq_empty_or_nonempty s with hse | hne
    ·
      obtain ⟨c, hcI, hc0⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (fiberCenter F' v hw).ne_bot
      refine ⟨c, hcI, hc0, fun w' h' hne' _ => ?_⟩
      have hmem : w' ∈ s := by
        rw [hs]
        exact Finset.mem_erase.mpr ⟨hne', (mem_fiberOver _).mpr h'⟩
      rw [hse] at hmem
      exact absurd hmem (Finset.notMem_empty w')
    ·
      have hprime : ∀ w' ∈ s, w' ≠ w → w' ≠ w → (f w').IsPrime := by
        intro w' hw's _ _
        have h' : w'.restrict F = v := (mem_fiberOver _).mp (Finset.mem_of_mem_erase hw's)
        rw [hfdef]
        simpa only [dif_pos h'] using (fiberCenter F' v h').isPrime
      have hnotsub :
          ¬ ((fiberCenter F' v hw).asIdeal : Set (integralClosureAt F' v)) ⊆
            ⋃ w' ∈ (s : Set (Place K F')), (f w' : Set (integralClosureAt F' v)) := by
        intro hsub
        obtain ⟨w'₀, hw'₀s, hle⟩ := (Ideal.subset_union_prime w w hprime).mp hsub
        have h'₀ : w'₀.restrict F = v := (mem_fiberOver _).mp (Finset.mem_of_mem_erase hw'₀s)
        have hfw : f w'₀ = (fiberCenter F' v h'₀).asIdeal := by
          rw [hfdef]; simp only [dif_pos h'₀]
        rw [hfw] at hle
        have hImax : (fiberCenter F' v hw).asIdeal.IsMaximal :=
          Ideal.IsPrime.isMaximal (fiberCenter F' v hw).isPrime (fiberCenter F' v hw).ne_bot
        have hIeq : (fiberCenter F' v hw).asIdeal = (fiberCenter F' v h'₀).asIdeal :=
          hImax.eq_of_le (fiberCenter F' v h'₀).isPrime.ne_top hle
        have hcenter : fiberCenter F' v hw = fiberCenter F' v h'₀ :=
          IsDedekindDomain.HeightOneSpectrum.ext hIeq
        have hsub_eq : (⟨w, hw⟩ : {w' : Place K F' // w'.restrict F = v}) = ⟨w'₀, h'₀⟩ :=
          (fiberEquiv F' v).injective (by simpa using hcenter)
        exact Finset.ne_of_mem_erase hw'₀s (congrArg Subtype.val hsub_eq).symm
      obtain ⟨c, hcI, hcU⟩ := Set.not_subset.mp hnotsub
      have hcnot : ∀ (w' : Place K F') (h' : w'.restrict F = v), w' ≠ w →
          c ∉ (fiberCenter F' v h').asIdeal := by
        intro w' h' hne' hmem
        refine hcU (Set.mem_biUnion (show w' ∈ (s : Set (Place K F')) from ?_) ?_)
        · rw [hs]
          exact_mod_cast Finset.mem_erase.mpr ⟨hne', (mem_fiberOver _).mpr h'⟩
        · rw [hfdef]
          first | exact hmem | exact SetLike.mem_coe.mpr hmem | simpa only [dif_pos h', SetLike.mem_coe] using hmem
      have hc0 : c ≠ 0 := by
        obtain ⟨w'₁, hw'₁⟩ := hne
        have h'₁ : w'₁.restrict F = v := (mem_fiberOver _).mp (Finset.mem_of_mem_erase hw'₁)
        intro hc
        exact hcnot w'₁ h'₁ (Finset.ne_of_mem_erase hw'₁)
          (hc ▸ (fiberCenter F' v h'₁).asIdeal.zero_mem)
      exact ⟨c, hcI, hc0, hcnot⟩
  refine ⟨algebraMap (integralClosureAt F' v) F' c, ?_, ?_, ?_⟩
  · intro h
    exact hc0 ((IsFractionRing.to_map_eq_zero_iff (K := F')).mp h)
  · exact (mem_fiberCenter_iff_ord_pos hw hc0).mp hcI
  · intro w' h' hne
    have h1 : 0 ≤ w'.ord (algebraMap (integralClosureAt F' v) F' c) :=
      ord_nonneg_of_mem'' w' (forall_mem_of_restrict_eq h' c)
    have h2 : ¬ 0 < w'.ord (algebraMap (integralClosureAt F' v) F' c) := fun hpos =>
      hcnot w' h' hne ((mem_fiberCenter_iff_ord_pos h' hc0).mpr hpos)
    omega

end SeparatingElement

section NormRouteAssembly

variable {K F₁ F F' : Type*} [Field K] [Field F₁] [Field F] [Field F']
  [Algebra K F₁] [Algebra K F] [Algebra K F']

private theorem ord_normAlong_eq_sum {A B : Type*} [Field A] [Field B] [Algebra K A]
    [Algebra K B] [CharZero A] [HasPrincipalDivisors K B]
    (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (v : Place K A) {f : B} (hf : f ≠ 0) :
    v.ord (normAlong φ f)
      = ∑ w ∈ Place.fiberAlong φ hφ v, (w.inertiaDegAlong φ hφ : ℤ) * w.ord f := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite A B := hfin
  haveI : Algebra.IsSeparable A B := Algebra.IsSeparable.of_integral A B
  have hfib : Place.fiberAlong φ hφ v = v.fiberOver B := by
    rw [show Place.fiberAlong φ hφ v = Place.fiber B v from rfl, Place.fiber_eq_fiberOver]
  rw [hfib]
  exact v.ord_norm_eq_sum_fiberOver hf

private theorem exists_separating_along {A B : Type*} [Field A] [Field B] [Algebra K A]
    [Algebra K B] [CharZero A]
    (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    {v₁ : Place K A} {v : Place K B} (hv : v.restrictAlong φ hφ = v₁) :
    ∃ t : B, t ≠ 0 ∧ 0 < v.ord t ∧
      ∀ v' : Place K B, v'.restrictAlong φ hφ = v₁ → v' ≠ v → v'.ord t = 0 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite A B := hfin
  haveI : Algebra.IsSeparable A B := Algebra.IsSeparable.of_integral A B
  exact Place.exists_ord_pos_forall_ord_eq_zero v₁ hv

variable (ι σm : F₁ →ₐ[K] F) (α β : F →ₐ[K] F') (w : F ≃ₐ[K] F)

private theorem restrictAlong_smul_left (hσ : σm.toRingHom.IsIntegral)
    (hι : ι.toRingHom.IsIntegral) (hwι : ∀ x, w (ι x) = σm x) (W : Place K F) :
    (w • W).restrictAlong σm hσ = W.restrictAlong ι hι := by
  have h := Place.smul_restrictAlong σm ι hσ hι w 1
    (fun x => by simpa using (hwι x).symm) W
  simpa using h

private theorem restrictAlong_smul_left' (hσ : σm.toRingHom.IsIntegral)
    (hι : ι.toRingHom.IsIntegral) (hwσ : ∀ x, w (σm x) = ι x) (W : Place K F) :
    (w • W).restrictAlong ι hι = W.restrictAlong σm hσ := by
  have h := Place.smul_restrictAlong ι σm hι hσ w 1
    (fun x => by simpa using (hwσ x).symm) W
  simpa using h

private theorem restrictAlong_square (hι : ι.toRingHom.IsIntegral)
    (hσ : σm.toRingHom.IsIntegral) (hα : α.toRingHom.IsIntegral)
    (hβ : β.toRingHom.IsIntegral) (hsq : α.comp σm = β.comp ι) (W : Place K F') :
    (W.restrictAlong β hβ).restrictAlong ι hι
      = (W.restrictAlong α hα).restrictAlong σm hσ := by
  have hβι : (β.comp ι).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hι hβ
  have hασ : (α.comp σm).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hσ hα
  rw [Place.restrictAlong_restrictAlong ι β hι hβ hβι W,
    Place.restrictAlong_restrictAlong σm α hσ hα hασ W,
    Place.restrictAlong_congr hsq hασ hβι W]

private theorem count_identity [CharZero F₁] [CharZero F] [DecidableEq (Place K F)]
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (hι : ι.toRingHom.IsIntegral) (hσ : σm.toRingHom.IsIntegral)
    (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (hfinι : FiniteAlong K ι) (hfinα : FiniteAlong K α)
    (hsq : α.comp σm = β.comp ι) (hw2 : w * w = 1)
    (hwσ : ∀ x, w (σm x) = ι x)
    (hstar : ∀ t : F, σm (normAlong ι t) = w t * normAlong α (β t))
    (v u : Place K F) (hu : u.restrictAlong σm hσ = v.restrictAlong ι hι) :
    (u.ramificationIndexAlong σm : ℤ) * (v.inertiaDegAlong ι hι : ℤ)
      = (if w • v = u then 1 else 0)
        + ∑ W ∈ (Place.fiberAlong α hα u).filter
            (fun W => W.restrictAlong β hβ = v),
            (W.inertiaDegAlong α hα : ℤ) * (W.ramificationIndexAlong β : ℤ) := by
  classical
  obtain ⟨t, ht0, htv, htz⟩ := exists_separating_along ι hι hfinι (rfl :
    v.restrictAlong ι hι = v.restrictAlong ι hι)
  have hβt0 : β t ≠ 0 := fun h =>
    ht0 ((map_eq_zero_iff β.toRingHom (RingHom.injective _)).mp h)
  have hwt0 : w t ≠ 0 := fun h => ht0 (w.injective (h.trans (map_zero w).symm))
  have hN0 : normAlong α (β t) ≠ 0 := by
    letI := algebraAlong α
    haveI := isScalarTower_along α
    haveI := isIntegral_along α hα
    haveI : Module.Finite F F' := hfinα
    exact Algebra.norm_ne_zero_iff.mpr hβt0

  have hE := congrArg u.ord (hstar t)
  rw [Place.ord_restrictAlong σm hσ u (normAlong ι t), hu,
    ord_normAlong_eq_sum ι hι hfinι (v.restrictAlong ι hι) ht0,
    u.ord_mul hwt0 hN0,
    ord_normAlong_eq_sum α hα hfinα u hβt0] at hE

  have hsum1 : ∑ v' ∈ Place.fiberAlong ι hι (v.restrictAlong ι hι),
      (v'.inertiaDegAlong ι hι : ℤ) * v'.ord t
      = (v.inertiaDegAlong ι hι : ℤ) * v.ord t := by
    refine Finset.sum_eq_single v (fun v' hv' hne => ?_) (fun habs => ?_)
    · rw [htz v' (Place.mem_fiberAlong.mp hv') hne, mul_zero]
    · exact absurd (Place.mem_fiberAlong.mpr rfl) habs

  have hword : u.ord (w t) = (w • u).ord t := by
    conv_lhs => rw [show u = w • (w • u) by rw [smul_smul, hw2, one_smul]]
    exact Place.ord_smul w (w • u) t
  have hwu_mem : (w • u).restrictAlong ι hι = v.restrictAlong ι hι := by
    rw [restrictAlong_smul_left' ι σm w hσ hι hwσ u, hu]
  have hword2 : u.ord (w t) = if w • v = u then v.ord t else 0 := by
    rw [hword]
    by_cases hcase : w • u = v
    · have : w • v = u := by rw [← hcase, smul_smul, hw2, one_smul]
      rw [if_pos this, hcase]
    · have : ¬ w • v = u := fun habs => hcase (by rw [← habs, smul_smul, hw2, one_smul])
      rw [if_neg this, htz (w • u) hwu_mem hcase]

  have hsum2 : ∑ W ∈ Place.fiberAlong α hα u,
      (W.inertiaDegAlong α hα : ℤ) * W.ord (β t)
      = (∑ W ∈ (Place.fiberAlong α hα u).filter
          (fun W => W.restrictAlong β hβ = v),
          (W.inertiaDegAlong α hα : ℤ) * (W.ramificationIndexAlong β : ℤ)) * v.ord t := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_filter_add_sum_filter_not (Place.fiberAlong α hα u)
      (fun W => W.restrictAlong β hβ = v)]
    have hz : ∑ W ∈ (Place.fiberAlong α hα u).filter
        (fun W => ¬ W.restrictAlong β hβ = v),
        (W.inertiaDegAlong α hα : ℤ) * W.ord (β t) = 0 := by
      refine Finset.sum_eq_zero fun W hW => ?_
      obtain ⟨hWfib, hWne⟩ := Finset.mem_filter.mp hW
      have hWmem : (W.restrictAlong β hβ).restrictAlong ι hι = v.restrictAlong ι hι := by
        rw [restrictAlong_square ι σm α β hι hσ hα hβ hsq W,
          Place.mem_fiberAlong.mp hWfib, hu]
      rw [Place.ord_restrictAlong β hβ W t, htz _ hWmem hWne, mul_zero, mul_zero]
    have hv' : ∑ W ∈ (Place.fiberAlong α hα u).filter
        (fun W => W.restrictAlong β hβ = v),
        (W.inertiaDegAlong α hα : ℤ) * W.ord (β t)
        = ∑ W ∈ (Place.fiberAlong α hα u).filter
            (fun W => W.restrictAlong β hβ = v),
            (W.inertiaDegAlong α hα : ℤ) * (W.ramificationIndexAlong β : ℤ) * v.ord t := by
      refine Finset.sum_congr rfl fun W hW => ?_
      obtain ⟨_, hWv⟩ := Finset.mem_filter.mp hW
      rw [Place.ord_restrictAlong β hβ W t, hWv, mul_assoc]
    rw [hz, add_zero, hv']
  rw [hsum1, hword2, hsum2] at hE

  refine mul_right_cancel₀ (ne_of_gt htv) ?_
  rw [mul_assoc, add_mul]
  by_cases hcase : w • v = u
  · rw [if_pos hcase] at hE ⊢
    rw [one_mul]
    exact hE
  · rw [if_neg hcase] at hE ⊢
    rw [zero_add] at hE
    rw [zero_mul, zero_add]
    exact hE

private theorem fibre_identification_generic [CharZero F₁] [CharZero F]
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (hι : ι.toRingHom.IsIntegral) (hσ : σm.toRingHom.IsIntegral)
    (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (hfinι : FiniteAlong K ι) (hfinα : FiniteAlong K α)
    (hsq : α.comp σm = β.comp ι) (hw2 : w * w = 1)
    (hwι : ∀ x, w (ι x) = σm x) (hwσ : ∀ x, w (σm x) = ι x)
    (hstar : ∀ t : F, σm (normAlong ι t) = w t * normAlong α (β t))
    (v : Place K F) (n : ℤ) :
    (∑ W ∈ Place.fiberAlong β hβ v,
        Finsupp.single (W.restrictAlong α hα)
          (n * (W.ramificationIndexAlong β : ℤ) * (W.inertiaDegAlong α hα : ℤ)))
      + Finsupp.single (w • v) n
      = ∑ u ∈ Place.fiberAlong σm hσ (v.restrictAlong ι hι),
          Finsupp.single u
            ((n * (v.inertiaDegAlong ι hι : ℤ)) * (u.ramificationIndexAlong σm : ℤ)) := by
  classical
  ext u
  rw [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' (Place.fiberAlong σm hσ (v.restrictAlong ι hι)) u]
  by_cases hu : u.restrictAlong σm hσ = v.restrictAlong ι hι
  · rw [if_pos (Place.mem_fiberAlong.mpr hu)]
    have hcount := count_identity ι σm α β w hι hσ hα hβ hfinι hfinα hsq hw2 hwσ hstar v u hu
    have hsets : (Place.fiberAlong β hβ v).filter
        (fun W => W.restrictAlong α hα = u)
        = (Place.fiberAlong α hα u).filter (fun W => W.restrictAlong β hβ = v) := by
      ext W
      simp only [Finset.mem_filter, Place.mem_fiberAlong]
      exact and_comm
    have hswap : ∑ W ∈ Place.fiberAlong β hβ v,
        (if W.restrictAlong α hα = u then
          n * (W.ramificationIndexAlong β : ℤ) * (W.inertiaDegAlong α hα : ℤ) else 0)
        = n * ∑ W ∈ (Place.fiberAlong α hα u).filter
            (fun W => W.restrictAlong β hβ = v),
            (W.inertiaDegAlong α hα : ℤ) * (W.ramificationIndexAlong β : ℤ) := by
      rw [← Finset.sum_filter, hsets, Finset.mul_sum]
      exact Finset.sum_congr rfl fun W _ => by ring
    rw [hswap]
    have hif : (if w • v = u then n else 0) = n * (if w • v = u then 1 else 0) := by
      split_ifs <;> ring
    rw [hif]
    linear_combination (-n) * hcount
  · rw [if_neg (fun h => hu (Place.mem_fiberAlong.mp h))]
    have hz1 : ∑ W ∈ Place.fiberAlong β hβ v,
        (if W.restrictAlong α hα = u then
          n * (W.ramificationIndexAlong β : ℤ) * (W.inertiaDegAlong α hα : ℤ) else 0)
        = 0 := by
      refine Finset.sum_eq_zero fun W hW => if_neg fun habs => hu ?_
      rw [← habs, ← restrictAlong_square ι σm α β hι hσ hα hβ hsq W,
        Place.mem_fiberAlong.mp hW]
    have hz2 : ¬ w • v = u := fun habs => by
      refine hu ?_
      rw [← habs, restrictAlong_smul_left ι σm w hσ hι hwι v]
    rw [hz1, if_neg hz2, add_zero]

end NormRouteAssembly

end AlgebraicCurve.Place

namespace ModularCurve
p2m_export "ModularCurve" "towerInclBar coe_towerInclBar towerInclBar_comp_towerInclBar towerSubstBar coe_towerSubstBar heckeAlphaBar_eq_towerInclBar dvd_of_eq_roof heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral heckeDivBar modularFunctionFieldBar qExpand qExpand_one_apply qExpand_qExpand jq modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange frickeInvolutionBar order_jq jq_mem_full heckeRoof_adjoin_range_union_eq_top functionFieldGeneration nonempty_modularPolynomialData_of_squarefree towerInclBar_surjective_of_dvd_dvd towerInclBar_finiteAlong finiteAlong_heckeAlphaBar_of_prime finrankAlong_heckeBetaBar heckeAlphaBar_frickeInvolutionBar_sq frickeInvolutionBar_frickeInvolutionBar isFrickeAutFull_frickeInvolutionFull_prime frickeInvolutionBar_coeffEmb_qExpand order_qExpand coeffEmb_qExpand coeffEmb_injective adjoin_jBar_jNBar_eq_top"
p2m_open "ModularCurve"

section Skeleton

variable (p : ℕ) [Fact p.Prime]

private theorem square_commutes :
    (heckeBetaBar (AlgebraicClosure ℚ) p p).comp (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) =
      (heckeAlphaBar (AlgebraicClosure ℚ) p p).comp
        (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)) := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeBetaBar, coe_towerInclBar,
    coe_heckeAlphaBar, coe_towerSubstBar]

private theorem fibre_identification
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    (hι : (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)).toRingHom.IsIntegral)
    (hσ : (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)).toRingHom.IsIntegral)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) (n : ℤ) :
    (∑ W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ v,
        Finsupp.single (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα)
          (n * (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) : ℤ) *
            (W.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα : ℤ)))
      + Finsupp.single (frickeInvolutionBar p • v) n
      = ∑ u ∈ Place.fiberAlong (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)) hσ
            (v.restrictAlong (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) hι),
          Finsupp.single u
            ((n * (v.inertiaDegAlong (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) hι : ℤ)) *
              (u.ramificationIndexAlong
                (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)) : ℤ)) := by

  have hwι : ∀ x, frickeInvolutionBar p (towerInclBar (AlgebraicClosure ℚ) (one_dvd p) x)
      = towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd) x := fun x =>
    (HaAux2.towerSubstBar_eq_frickeInvolutionBar_towerInclBar p x).symm

  have hwσ : ∀ x, frickeInvolutionBar p (towerSubstBar (AlgebraicClosure ℚ) 1 p
      ((one_mul p).dvd) x) = towerInclBar (AlgebraicClosure ℚ) (one_dvd p) x := fun x =>
    (HaAux2.towerInclBar_eq_frickeInvolutionBar_towerSubstBar p x).symm

  have hw2 : frickeInvolutionBar p * frickeInvolutionBar p = 1 :=
    HaAux2.frickeInvolutionBar_mul_self p

  have hfinι : FiniteAlong (AlgebraicClosure ℚ)
      (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) :=
    towerInclBar_finiteAlong (AlgebraicClosure ℚ) (one_dvd p)
  have hfinα : FiniteAlong (AlgebraicClosure ℚ)
      (heckeAlphaBar (AlgebraicClosure ℚ) p p) :=
    finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) p p

  have hstar : ∀ t, towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)
      (normAlong (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) t)
      = frickeInvolutionBar p t
        * normAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p)
            (heckeBetaBar (AlgebraicClosure ℚ) p p t) := fun t =>
    towerSubstBar_normAlong_towerInclBar p hwι hwσ
      (HaAux2.exists_heckeBetaBar_towerSubstBar_ne_heckeAlphaBar_towerInclBar p) t

  haveI : CharZero (modularFunctionFieldBar 1) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1)).injective
  haveI : CharZero (modularFunctionFieldBar p) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).injective
  exact Place.fibre_identification_generic
    (towerInclBar (AlgebraicClosure ℚ) (one_dvd p))
    (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd))
    (heckeAlphaBar (AlgebraicClosure ℚ) p p) (heckeBetaBar (AlgebraicClosure ℚ) p p)
    (frickeInvolutionBar p) hι hσ hα hβ hfinι hfinα (square_commutes p).symm
    hw2 hwι hwσ hstar v n

private theorem perPlace
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    (hι : (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)).toRingHom.IsIntegral)
    (hσ : (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)).toRingHom.IsIntegral)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) (n : ℤ) :
    heckeDivBar hα hβ (Finsupp.single v n) + frickeInvolutionBar p • Finsupp.single v n =
      Divisor.pullbackAlong (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)) hσ
        (Divisor.pushforwardAlong (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) hι
          (Finsupp.single v n)) := by
  rw [show heckeDivBar hα hβ (Finsupp.single v n)
      = Divisor.correspondence (heckeBetaBar (AlgebraicClosure ℚ) p p)
          (heckeAlphaBar (AlgebraicClosure ℚ) p p) hβ hα (Finsupp.single v n) from rfl,
    AlgebraicCurve.Divisor.correspondence_single, Divisor.smul_single,
    Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single]
  exact fibre_identification p hα hβ hι hσ v n

end Skeleton

end ModularCurve

theorem solution (p : ℕ) [Fact p.Prime]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    (hι : (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)).toRingHom.IsIntegral)
    (hσ : (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)).toRingHom.IsIntegral)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) :
    heckeDivBar hα hβ D + frickeInvolutionBar p • D =
      Divisor.pullbackAlong (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)) hσ
        (Divisor.pushforwardAlong (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) hι D) := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, smul_zero, add_zero, map_zero, map_zero]
  | single_add v n D _ _ ih =>
      rw [map_add, smul_add, add_add_add_comm, map_add, map_add, ih,
        ModularCurve.perPlace p hα hβ hι hσ v n]

end S_ModularCurve_heckeDivBar_self_add_frickeInvolutionBar_smul
end P2MW
export P2MW.S_ModularCurve_heckeDivBar_self_add_frickeInvolutionBar_smul (solution)

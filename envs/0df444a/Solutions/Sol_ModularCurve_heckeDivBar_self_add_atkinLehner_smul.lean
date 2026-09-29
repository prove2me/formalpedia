-- Prove2me | solution 1 for ModularCurve.heckeDivBar_self_add_atkinLehner_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7aa77d8b-8663-5fdf-bd3a-fabec30acb14

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
import Theorems.Thm_ModularCurve_order_qExpand
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_coeffEmb_injective
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldFull_algHom_ext
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDivBar_self_add_atkinLehner_smul
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_heckeDivBar_self_add_atkinLehner_smul.AlgebraicCurve ModularCurve"

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

namespace MackeyGeneric

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

end MackeyGeneric

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
          (first | (simp only [dif_pos h']; exact hmem) | exact hmem | simpa only [dif_pos h'] using hmem)
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

namespace MackeyN

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_heckeDivBar_self_add_atkinLehner_smul.AlgebraicCurve ModularCurve"

local notation "Qb" => AlgebraicClosure ℚ

private theorem qExpand_sq_jq_ne_jq (p : ℕ) [hp : Fact p.Prime] :
    qExpand ℚ (p * p) jq ≠ jq := by
  intro h
  have ho := congrArg HahnSeries.order h
  rw [order_qExpand, order_jq] at ho
  simp only [mul_neg, mul_one, neg_inj] at ho
  have hp2 : (2 : ℕ) ≤ p := hp.out.two_le
  have : (p * p : ℤ) = 1 := by exact_mod_cast ho
  nlinarith [this, (show (2 : ℤ) ≤ p from by exact_mod_cast hp2)]

section LevelN
variable (N q : ℕ) [NeZero N] [hq : Fact q.Prime] (hqN : ¬ q ∣ N)

local notation "αN" => heckeAlphaBar (AlgebraicClosure ℚ) N q
local notation "βN" => heckeBetaBar (AlgebraicClosure ℚ) N q
local notation "α₂" => heckeAlphaBar (AlgebraicClosure ℚ) (N * q) q
local notation "β₂" => heckeBetaBar (AlgebraicClosure ℚ) (N * q) q
local notation "σq" => atkinLehnerInvolutionFull N q
local notation "wq" => geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)

include hqN in
theorem isAL : IsAtkinLehnerAutFull N q σq :=
  isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q hq.out hqN)

include hqN in

theorem atkinLehnerInvolutionFull_mul_self : σq * σq = 1 := by
  have hAL := isAL N q hqN
  apply AlgEquiv.coe_algHom_injective
  apply modularFunctionFieldFull_algHom_ext
  intro d hd hdiv
  show σq (σq ⟨qExpand ℚ d jq, jqd_mem_full (N * q) hdiv⟩) = ⟨qExpand ℚ d jq, jqd_mem_full (N * q) hdiv⟩
  by_cases hqd : q ∣ d
  · obtain ⟨d', rfl⟩ := hqd
    have hq0 : 0 < q := hq.out.pos
    have hd'N : d' ∣ N := by
      have : d' * q ∣ N * q := by rw [Nat.mul_comm d' q]; exact hdiv
      exact Nat.dvd_of_mul_dvd_mul_right hq0 this
    haveI : NeZero d' := ⟨fun h => by apply (NeZero.ne (q * d')); rw [h, Nat.mul_zero]⟩
    obtain ⟨h1, h2⟩ := hAL d' inferInstance hd'N
    have e : (⟨qExpand ℚ (q * d') jq, jqd_mem_full (N * q) hdiv⟩ : modularFunctionFieldFull (N * q))
        = ⟨qExpand ℚ (d' * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right hd'N q)⟩ :=
      Subtype.ext (by show qExpand ℚ (q * d') jq = qExpand ℚ (d' * q) jq; simp only [Nat.mul_comm q d'])
    rw [e, h2, h1]
  · have hdN : d ∣ N :=
      (Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hq.out).mpr hqd).symm hdiv)
    obtain ⟨h1, h2⟩ := hAL d hd hdN
    have e : (⟨qExpand ℚ d jq, jqd_mem_full (N * q) hdiv⟩ : modularFunctionFieldFull (N * q))
        = ⟨qExpand ℚ d jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right hdN q)⟩ := rfl
    rw [e, h1, h2]

include hqN in
theorem geomAut_atkinLehner_mul_self : wq * wq = 1 := by
  rw [← map_mul, atkinLehnerInvolutionFull_mul_self N q hqN, map_one]

include hqN in
theorem geomAut_atkinLehner_alpha (x : modularFunctionFieldBar N) : wq (αN x) = βN x :=
  AlgHom.congr_fun (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q σq (isAL N q hqN)).1 x

include hqN in
theorem geomAut_atkinLehner_beta (x : modularFunctionFieldBar N) : wq (βN x) = αN x :=
  AlgHom.congr_fun (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q σq (isAL N q hqN)).2 x

omit hq in

theorem square [NeZero q] : (α₂).comp βN = (β₂).comp αN := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeAlphaBar, coe_heckeBetaBar, coe_heckeBetaBar,
    coe_heckeAlphaBar]

theorem adjoin_range_union : Algebra.adjoin Qb (Set.range α₂ ∪ Set.range β₂) = ⊤ := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree q hq.out.prime.squarefree hq.out.one_lt
  have hroof := heckeRoof_adjoin_range_union_eq_top Qb N q q (N * q * q) rfl
    (functionFieldGeneration (N * q * q)) data
  rw [Set.union_comm]
  have e1 : towerSubstBar Qb (N * q) q (dvd_of_eq_roof N q q (N * q * q) rfl).2 = β₂ := by
    rw [heckeBetaBar_eq_towerSubstBar]
  have e2 : towerInclBar Qb (dvd_of_eq_roof N q q (N * q * q) rfl).1 = α₂ := by
    rw [heckeAlphaBar_eq_towerInclBar]
  rw [e1, e2] at hroof
  exact hroof

theorem finrankAlong_comp {K A B C : Type*} [Field K] [Field A] [Field B] [Field C]
    [Algebra K A] [Algebra K B] [Algebra K C] (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    finrankAlong K (ψ.comp φ) = finrankAlong K φ * finrankAlong K ψ := by
  letI := algebraAlong φ
  letI := algebraAlong ψ
  letI : Algebra A C := algebraAlong (ψ.comp φ)
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  exact (Module.finrank_mul_finrank A B C).symm

include hqN in
theorem finrankAlong_alphaN : finrankAlong Qb αN = q + 1 := by
  have hc : ∀ a : modularFunctionFieldBar N, αN ((RingEquiv.refl _) a) = (wq).toRingEquiv (βN a) :=
    fun a => (geomAut_atkinLehner_beta N q hqN a).symm
  rw [← finrankAlong_eq_of_equiv_equiv (K := Qb) βN αN (RingEquiv.refl _) (wq).toRingEquiv hc,
    finrankAlong_heckeBetaBar Qb N q, if_neg hqN]

include hqN in
theorem finrankAlong_alpha2 : finrankAlong Qb α₂ = q := by
  have h := congrArg (finrankAlong Qb) (square N q)
  rw [finrankAlong_comp, finrankAlong_comp, finrankAlong_alphaN N q hqN, finrankAlong_heckeBetaBar Qb N q,
    if_neg hqN, finrankAlong_heckeBetaBar Qb (N * q) q, if_pos (dvd_mul_left q N)] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos q) h

theorem exists_ne : ∃ g : modularFunctionFieldBar N, β₂ (βN g) ≠ α₂ (αN g) := by
  refine ⟨⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (jq_mem_full N)⟩, ?_⟩
  intro h
  have hcoe := congrArg Subtype.val h
  rw [coe_heckeBetaBar, coe_heckeBetaBar, coe_heckeAlphaBar, coe_heckeAlphaBar] at hcoe
  change qExpand Qb q (qExpand Qb q (coeffEmb Qb jq)) = coeffEmb Qb jq at hcoe
  rw [qExpand_qExpand, ← coeffEmb_qExpand] at hcoe
  exact qExpand_sq_jq_ne_jq q (coeffEmb_injective Qb hcoe)

include hqN in

theorem norm_identity (t : modularFunctionFieldBar (N * q)) :
    βN (normAlong αN t) = wq t * normAlong α₂ (β₂ t) := by
  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap Qb _).injective
  haveI : CharZero (modularFunctionFieldBar (N * q)) :=
    charZero_of_injective_algebraMap (algebraMap Qb _).injective
  refine normAlong_sq_eq_mul_normAlong αN βN α₂ β₂ wq (fun x => AlgHom.congr_fun (square N q) x)
    (geomAut_atkinLehner_alpha N q hqN) (geomAut_atkinLehner_beta N q hqN) (exists_ne N q) (adjoin_range_union N q)
    (finiteAlong_heckeAlphaBar_of_prime Qb N q) (finiteAlong_heckeAlphaBar_of_prime Qb (N * q) q) ?_ t
  rw [finrankAlong_alphaN N q hqN, finrankAlong_alpha2 N q hqN]

end LevelN

end MackeyN

namespace MackeyN

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_heckeDivBar_self_add_atkinLehner_smul.AlgebraicCurve ModularCurve"

section Skeleton
variable (N q : ℕ) [NeZero N] [hq : Fact q.Prime] (hqN : ¬ q ∣ N)

include hqN in

theorem fibre_identification
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * q))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hαN : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβN : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (n : ℤ) :
    (∑ W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) q) hβ v,
        Finsupp.single (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) q) hα)
          (n * (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) q) : ℤ) *
            (W.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) q) hα : ℤ)))
      + Finsupp.single ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)) • v) n
      = ∑ u ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβN
            (v.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαN),
          Finsupp.single u
            ((n * (v.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαN : ℤ)) *
              (u.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ)) := by
  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
  haveI : CharZero (modularFunctionFieldBar (N * q)) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).injective
  exact Place.fibre_identification_generic
    (heckeAlphaBar (AlgebraicClosure ℚ) N q) (heckeBetaBar (AlgebraicClosure ℚ) N q)
    (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) q) (heckeBetaBar (AlgebraicClosure ℚ) (N * q) q)
    (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)) hαN hβN hα hβ
    (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q)
    (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) (N * q) q)
    (square N q) (geomAut_atkinLehner_mul_self N q hqN)
    (geomAut_atkinLehner_alpha N q hqN) (geomAut_atkinLehner_beta N q hqN) (norm_identity N q hqN) v n

include hqN in

theorem perPlace
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * q))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hαN : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβN : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (n : ℤ) :
    heckeDivBar hα hβ (Finsupp.single v n) + (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)) • Finsupp.single v n =
      Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβN
        (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαN (Finsupp.single v n)) := by
  rw [show heckeDivBar hα hβ (Finsupp.single v n)
      = Divisor.correspondence (heckeBetaBar (AlgebraicClosure ℚ) (N * q) q)
          (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) q) hβ hα (Finsupp.single v n) from rfl,
    AlgebraicCurve.Divisor.correspondence_single, Divisor.smul_single,
    Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single]
  exact fibre_identification N q hqN hα hβ hαN hβN v n

end Skeleton

end MackeyN

theorem solution (N q : ℕ) [NeZero N] [Fact q.Prime]
    (hqN : ¬ q ∣ N)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * q))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hαN : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβN : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    heckeDivBar hα hβ D
        + (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)) • D =
      Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβN
        (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαN D) := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, smul_zero, add_zero, map_zero, map_zero]
  | single_add v n D _ _ ih =>
      rw [map_add, smul_add, add_add_add_comm, map_add, map_add, ih,
        MackeyN.perPlace N q hqN hα hβ hαN hβN v n]

end S_ModularCurve_heckeDivBar_self_add_atkinLehner_smul
end P2MW
export P2MW.S_ModularCurve_heckeDivBar_self_add_atkinLehner_smul (solution)

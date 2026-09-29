-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.norm_mem_and_residue_norm_eq_core
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/871be4c8-9593-5446-bca8-c995f331f1a3

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_GaussPencilAdapter
import Theorems.Thm_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_norm_mem_and_residue_norm_eq_core
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped nonZeroDivisors TensorProduct

namespace Module p2m_export "Module" "Flat Injective Free.chooseBasis isTorsionFree_iff_algebraMap_injective free_of_flat_of_isLocalRing finrank_eq_card_basis finrank Free mk IsTorsionFree finrank_baseChange finite_of_finrank_pos finrank_eq_card_chooseBasisIndex finrank_prod Flat.flat_iff_torsion_eq_bot_of_isBezout" end Module
p2m_open_scoped "Module" in

theorem Module.free_of_finite_of_torsion_eq_bot_of_valuationRing {R M : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : Submodule.torsion R M = ⊥) : Module.Free R M := by
  have : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr h
  exact Module.free_of_flat_of_isLocalRing

p2m_open_scoped "Module" in
theorem Module.free_of_finite_of_isTorsionFree_of_valuationRing {R M : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M :=
  Module.free_of_finite_of_torsion_eq_bot_of_valuationRing
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp ‹_›)

namespace GaussPencil

theorem algebraMap_injective_of_tower (V K F : Type*) [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] : Function.Injective (algebraMap V F) := by
  rw [IsScalarTower.algebraMap_eq V K F]
  exact (algebraMap K F).injective.comp (IsFractionRing.injective V K)

theorem isTorsionFree_subalgebra {V F : Type*} [CommRing V] [IsDomain V] [Field F] [Algebra V F]
    (hinj : Function.Injective (algebraMap V F)) (S : Subalgebra V F) :
    Module.IsTorsionFree V S :=
  haveI : Module.IsTorsionFree V F := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  Function.Injective.moduleIsTorsionFree (Subtype.val : S → F) Subtype.val_injective
    (fun _ _ => rfl)

theorem free_subalgebra {V F : Type*} [CommRing V] [IsDomain V] [ValuationRing V] [Field F]
    [Algebra V F] (hinj : Function.Injective (algebraMap V F)) (S : Subalgebra V F)
    [Module.Finite V S] : Module.Free V S :=
  haveI := isTorsionFree_subalgebra hinj S
  Module.free_of_finite_of_isTorsionFree_of_valuationRing

theorem isLocalization_of_span_eq_top {V K F : Type*} [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] (S : Subalgebra V F) (hspan : Submodule.span K (S : Set F) = ⊤) :
    IsLocalization (Algebra.algebraMapSubmonoid S V⁰) F := by
  have hinj := algebraMap_injective_of_tower V K F
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, v, hv, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [← IsScalarTower.algebraMap_apply V S F v]
    exact (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hv)
  · intro z
    have hz : z ∈ Submodule.span K (S : Set F) := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact ⟨(⟨x, hx⟩, 1), by simp⟩
    | zero => exact ⟨(0, 1), by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨⟨a, m⟩, ha⟩ := hx
      obtain ⟨⟨b, n⟩, hb⟩ := hy
      refine ⟨(a * n + b * m, m * n), ?_⟩
      simp only [Submonoid.coe_mul, map_mul, map_add] at ha hb ⊢
      rw [add_mul, ← mul_assoc, ha, mul_comm (algebraMap S F (m : S)) (algebraMap S F (n : S)),
        ← mul_assoc, hb]
    | smul k x _ hx =>
      obtain ⟨⟨a, m⟩, ha⟩ := hx
      obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := V) k
      have hdS : algebraMap V S d ∈ Algebra.algebraMapSubmonoid S V⁰ := ⟨d, hd, rfl⟩
      refine ⟨(algebraMap V S c * a, m * ⟨algebraMap V S d, hdS⟩), ?_⟩
      have hd0 : algebraMap V F d ≠ 0 :=
        (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hd)
      simp only [Submonoid.coe_mul, map_mul] at ha ⊢
      rw [← IsScalarTower.algebraMap_apply V S F d, ← IsScalarTower.algebraMap_apply V S F c,
        Algebra.smul_def, map_div₀, ← IsScalarTower.algebraMap_apply V K F,
        ← IsScalarTower.algebraMap_apply V K F, ← ha]
      field_simp
  · intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

theorem finrank_subalgebra_eq {V K F : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤) :
    Module.finrank V S = Module.finrank K F := by
  haveI := free_subalgebra (algebraMap_injective_of_tower V K F) S
  haveI := isLocalization_of_span_eq_top S hspan
  let b := Module.Free.chooseBasis V S
  rw [Module.finrank_eq_card_chooseBasisIndex,
    Module.finrank_eq_card_basis (b.localizationLocalization K V⁰ F)]

theorem algebraMap_norm_subalgebra_eq {V K F : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤) (s : S) :
    algebraMap V K (Algebra.norm V s) = Algebra.norm K (s : F) := by
  haveI := free_subalgebra (algebraMap_injective_of_tower V K F) S
  haveI := isLocalization_of_span_eq_top S hspan
  exact (Algebra.norm_localization V V⁰ (Rₘ := K) (Sₘ := F) s).symm

end GaussPencil

namespace GaussPencil

theorem norm_one_tmul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (A' : Type*) [CommRing A'] [Algebra A A'] (b : B) :
    Algebra.norm A' ((1 : A') ⊗ₜ[A] b) = algebraMap A A' (Algebra.norm A b) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

theorem norm_prod_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Free R S] [Module.Finite R S] [Module.Free R T]
    [Module.Finite R T] (x : S × T) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have h : Algebra.lmul R (S × T) x
      = LinearMap.prodMap (Algebra.lmul R S x.1) (Algebra.lmul R T x.2) :=
    LinearMap.ext fun _ => rfl
  rw [Algebra.norm_apply, h, LinearMap.det_prodMap, ← Algebra.norm_apply, ← Algebra.norm_apply]

theorem residue_norm_eq_prod_norm_of_surjective {V B : Type*} [CommRing V] [IsLocalRing V]
    [CommRing B] [Algebra V B] [Module.Free V B] [Module.Finite V B]
    {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂]
    [Algebra (IsLocalRing.ResidueField V) κ₁] [Algebra (IsLocalRing.ResidueField V) κ₂]
    [Algebra V κ₁] [Algebra V κ₂] [IsScalarTower V (IsLocalRing.ResidueField V) κ₁]
    [IsScalarTower V (IsLocalRing.ResidueField V) κ₂]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₁]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₂]
    (ρ₁ : B →ₐ[V] κ₁) (ρ₂ : B →ₐ[V] κ₂)
    (hsurj : Function.Surjective fun b : B => (ρ₁ b, ρ₂ b))
    (hdim : Module.finrank (IsLocalRing.ResidueField V) κ₁
      + Module.finrank (IsLocalRing.ResidueField V) κ₂ = Module.finrank V B) (b : B) :
    IsLocalRing.residue V (Algebra.norm V b)
      = Algebra.norm (IsLocalRing.ResidueField V) (ρ₁ b)
          * Algebra.norm (IsLocalRing.ResidueField V) (ρ₂ b) := by
  set κ := IsLocalRing.ResidueField V

  let Φ : κ ⊗[V] B →ₐ[κ] κ₁ × κ₂ :=
    Algebra.TensorProduct.lift (Algebra.ofId κ (κ₁ × κ₂)) (ρ₁.prod ρ₂) fun _ _ => Commute.all _ _
  have hΦ : ∀ x : B, Φ ((1 : κ) ⊗ₜ[V] x) = (ρ₁ x, ρ₂ x) := fun x => by
    simp [Φ, Algebra.TensorProduct.lift_tmul]
  have hΦsurj : Function.Surjective Φ := fun c => by
    obtain ⟨x, hx⟩ := hsurj c
    exact ⟨1 ⊗ₜ x, by rw [hΦ]; exact hx⟩
  have hdim' : Module.finrank κ (κ ⊗[V] B) = Module.finrank κ (κ₁ × κ₂) := by
    rw [Module.finrank_baseChange, Module.finrank_prod, hdim]
  have hΦinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim' (f := Φ.toLinearMap)).mpr
      hΦsurj
  let e : κ ⊗[V] B ≃ₐ[κ] κ₁ × κ₂ := AlgEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  calc IsLocalRing.residue V (Algebra.norm V b)
      = algebraMap V κ (Algebra.norm V b) := rfl
    _ = Algebra.norm κ ((1 : κ) ⊗ₜ[V] b) := (norm_one_tmul κ b).symm
    _ = Algebra.norm κ (e ((1 : κ) ⊗ₜ[V] b)) := (Algebra.norm_eq_of_algEquiv e _).symm
    _ = Algebra.norm κ (ρ₁ b, ρ₂ b) := by rw [AlgEquiv.ofBijective_apply, hΦ]
    _ = Algebra.norm κ (ρ₁ b) * Algebra.norm κ (ρ₂ b) := norm_prod_apply _

end GaussPencil

namespace GaussPencil

theorem residue_norm_subalgebra_eq_prod {V K F : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤)
    {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂]
    [Algebra (IsLocalRing.ResidueField V) κ₁] [Algebra (IsLocalRing.ResidueField V) κ₂]
    [Algebra V κ₁] [Algebra V κ₂] [IsScalarTower V (IsLocalRing.ResidueField V) κ₁]
    [IsScalarTower V (IsLocalRing.ResidueField V) κ₂]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₁]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₂]
    (ρ₁ : S →ₐ[V] κ₁) (ρ₂ : S →ₐ[V] κ₂)
    (hsurj : Function.Surjective fun s : S => (ρ₁ s, ρ₂ s))
    (hdim : Module.finrank (IsLocalRing.ResidueField V) κ₁
      + Module.finrank (IsLocalRing.ResidueField V) κ₂ = Module.finrank K F) (s : S) :
    IsLocalRing.residue V (Algebra.norm V s)
      = Algebra.norm (IsLocalRing.ResidueField V) (ρ₁ s)
          * Algebra.norm (IsLocalRing.ResidueField V) (ρ₂ s) := by
  haveI := free_subalgebra (algebraMap_injective_of_tower V K F) S
  exact residue_norm_eq_prod_norm_of_surjective ρ₁ ρ₂ hsurj
    (hdim.trans (finrank_subalgebra_eq S hspan).symm) s

theorem norm_eq_algebraMap_and_residue_eq_prod {V K F : Type*} [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F]
    [Algebra V F] [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤)
    {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂]
    [Algebra (IsLocalRing.ResidueField V) κ₁] [Algebra (IsLocalRing.ResidueField V) κ₂]
    [Algebra V κ₁] [Algebra V κ₂] [IsScalarTower V (IsLocalRing.ResidueField V) κ₁]
    [IsScalarTower V (IsLocalRing.ResidueField V) κ₂]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₁]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₂]
    (ρ₁ : S →ₐ[V] κ₁) (ρ₂ : S →ₐ[V] κ₂)
    (hsurj : Function.Surjective fun s : S => (ρ₁ s, ρ₂ s))
    (hdim : Module.finrank (IsLocalRing.ResidueField V) κ₁
      + Module.finrank (IsLocalRing.ResidueField V) κ₂ = Module.finrank K F) (s : S) :
    Algebra.norm K (s : F) = algebraMap V K (Algebra.norm V s) ∧
      IsLocalRing.residue V (Algebra.norm V s)
        = Algebra.norm (IsLocalRing.ResidueField V) (ρ₁ s)
            * Algebra.norm (IsLocalRing.ResidueField V) (ρ₂ s) :=
  ⟨(algebraMap_norm_subalgebra_eq S hspan s).symm,
    residue_norm_subalgebra_eq_prod S hspan ρ₁ ρ₂ hsurj hdim s⟩

end GaussPencil

namespace GaussPencil

theorem surjective_prod_of_surjective_of_exists
    {S κ₁ κ₂ : Type*} [CommRing S] [Field κ₁] [Field κ₂]
    (ρ₁ : S →+* κ₁) (ρ₂ : S →+* κ₂) (h₁ : Function.Surjective ρ₁) (h₂ : Function.Surjective ρ₂)
    (e : S) (he₁ : ρ₁ e ≠ 0) (he₂ : ρ₂ e = 0) :
    Function.Surjective fun s => (ρ₁ s, ρ₂ s) := by
  rintro ⟨a, b⟩
  obtain ⟨x, rfl⟩ := h₁ a
  obtain ⟨y, rfl⟩ := h₂ b
  obtain ⟨t, ht⟩ := h₁ (ρ₁ e)⁻¹

  have hu₁ : ρ₁ (t * e) = 1 := by rw [map_mul, ht, inv_mul_cancel₀ he₁]
  have hu₂ : ρ₂ (t * e) = 0 := by rw [map_mul, he₂, mul_zero]
  refine ⟨x * (t * e) + y * (1 - t * e), ?_⟩
  simp only [map_add, map_mul, map_sub, map_one, hu₁, hu₂, Prod.mk.injEq]
  constructor <;> ring

theorem surjective_prod_algHom_of_exists
    {V S κ₁ κ₂ : Type*} [CommRing V] [CommRing S] [Algebra V S] [Field κ₁] [Field κ₂]
    [Algebra V κ₁] [Algebra V κ₂]
    (ρ₁ : S →ₐ[V] κ₁) (ρ₂ : S →ₐ[V] κ₂) (h₁ : Function.Surjective ρ₁) (h₂ : Function.Surjective ρ₂)
    (e : S) (he₁ : ρ₁ e ≠ 0) (he₂ : ρ₂ e = 0) :
    Function.Surjective fun s => (ρ₁ s, ρ₂ s) :=
  surjective_prod_of_surjective_of_exists ρ₁.toRingHom ρ₂.toRingHom h₁ h₂ e he₁ he₂

end GaussPencil

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_norm_mem_and_residue_norm_eq_core.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun PlaceSpecialization.jqFun modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr jq ModularPolynomialData jqd_mem_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence transcendental_jqModC frickeInvolutionBar isFrickeAutFull_frickeInvolutionFull coeffMap_jqModC mem_divisorExpansionsC modularFunctionFieldFullC coeffMap_qExpand PlaceSpecialization.LevelOneProlongationPair.ResOne PlaceSpecialization.LevelOneProlongationPair.ResTwo PlaceSpecialization.LevelOneProlongationPair.ResOne.val PlaceSpecialization.LevelOneProlongationPair.ResTwo.val frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun mk mk.injEq LevelOneProlongationPair.ResOne LevelOneProlongationPair.ResTwo LevelOneProlongationPair.ResOne.val LevelOneProlongationPair.ResTwo.val"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "mem_integers₂_iff residue₂_eq R₂ residue₁_coeffMap redBar mk.injEq mk R₁ gaussBase algebraMap_mem_gaussBase_iff HasGaussTransport gaussOrder self_mem_gaussOrder ResOne ResTwo ResOne.val ResTwo.val ResOne.valEquiv ResTwo.valEquiv resBase₁_algebraMap gaussOrderToIntegers₁ coe_gaussOrderToIntegers₁ rho₁ rho₁_apply resBase₂_algebraMap gaussOrderToIntegers₂ coe_gaussOrderToIntegers₂ rho₂ rho₂_apply"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"

section RFacts

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

theorem coeffMap_subtype_jqModC :
    coeffMap A.subtype (jqModC A) = coeffEmb (AlgebraicClosure ℚ) jq := by
  rw [coeffMap_jqModC, coeffEmb, ← jqModC_rat, coeffMap_jqModC]

theorem coeffMap_subtype_qExpand_jqModC :
    coeffMap A.subtype (qExpand A (1 * q) (jqModC A)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) := by
  rw [coeffMap_qExpand, coeffMap_jqModC, coeffEmb, coeffMap_qExpand, ← jqModC_rat, coeffMap_jqModC]

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jFun_mem_integers₁ : jFun (q := q) ∈ R.R₁.integers ∧
    ∃ h : jFun (q := q) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = jqModC (ResidueField A) := by
  have hy : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (1 * q) := by
    rw [coeffMap_subtype_jqModC]; exact (jFun (q := q)).2
  obtain ⟨h, e⟩ := R.residue₁_coeffMap (jqModC A) hy
  have hj : (⟨coeffMap A.subtype (jqModC A), hy⟩ : modularFunctionFieldBar (1 * q)) = jFun (q := q) :=
    Subtype.ext coeffMap_subtype_jqModC
  obtain ⟨h', e'⟩ : ∃ h' : jFun (q := q) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = coeffMap (IsLocalRing.residue A) (jqModC A) := by
    rw [← hj]; exact ⟨h, e⟩
  exact ⟨h', h', e'.trans (coeffMap_jqModC _)⟩

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jFun_mem_integers₁"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jqFun_mem_integers₁ : jqFun (q := q) ∈ R.R₁.integers ∧
    ∃ h : jqFun (q := q) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) := by
  have hy : coeffMap A.subtype (qExpand A (1 * q) (jqModC A)) ∈ modularFunctionFieldBar (1 * q) := by
    rw [coeffMap_subtype_qExpand_jqModC]; exact (jqFun (q := q)).2
  obtain ⟨h, e⟩ := R.residue₁_coeffMap (qExpand A (1 * q) (jqModC A)) hy
  have hj : (⟨coeffMap A.subtype (qExpand A (1 * q) (jqModC A)), hy⟩ : modularFunctionFieldBar (1 * q))
      = jqFun (q := q) :=
    Subtype.ext coeffMap_subtype_qExpand_jqModC
  obtain ⟨h', e'⟩ : ∃ h' : jqFun (q := q) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = coeffMap (IsLocalRing.residue A) (qExpand A (1 * q) (jqModC A)) := by
    rw [← hj]; exact ⟨h, e⟩
  exact ⟨h', h', e'.trans (by rw [coeffMap_qExpand, coeffMap_jqModC])⟩

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jqFun_mem_integers₁"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jqFun_mem_integers₂ : jqFun (q := q) ∈ R.R₂.integers := by
  rw [R.mem_integers₂_iff]
  have e : frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) :=
    (frickeInvolutionBar_coeffEmb_qExpand (1 * q)
      (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) (1 * q) 1 (mul_one _)).trans
      (Subtype.ext (show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) = coeffEmb (AlgebraicClosure ℚ) jq from
        congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq)))
  rw [e]; exact R.jFun_mem_integers₁.1

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jqFun_mem_integers₂"
include R in
theorem charP_residueField : CharP (ResidueField A) q := RingHom.charP R.redBar R.redBar.injective q

include R in

theorem qExpand_one_mul_jqModC :
    qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) = jqModC (ResidueField A) ^ q := by
  haveI := charP_residueField R
  rw [qExpand_congr (one_mul q)]
  exact qExpand_jqModC_eq_pow_unconditional (ResidueField A)

theorem coe_residue₂_jqFun (h : jqFun (q := q) ∈ R.R₂.integers) :
    ((R.R₂.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) := by
  rw [R.residue₂_eq]
  obtain ⟨h₁, e₁⟩ := R.jFun_mem_integers₁.2
  have hw : frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) :=
    (frickeInvolutionBar_coeffEmb_qExpand (1 * q)
      (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) (1 * q) 1 (mul_one _)).trans
      (Subtype.ext (show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) = coeffEmb (AlgebraicClosure ℚ) jq from
        congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq)))
  obtain ⟨h', e'⟩ : ∃ h' : frickeInvolutionBar (1 * q) (jqFun (q := q)) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = jqModC (ResidueField A) := by
    rw [hw]; exact ⟨h₁, e₁⟩
  exact e'

theorem frickeInvolutionBar_jFun' :
    frickeInvolutionBar (1 * q) (jFun (q := q)) = jqFun (q := q) := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q)
    (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) 1 (1 * q) (one_mul _)
  have e : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩
        : modularFunctionFieldBar (1 * q)) = jFun (q := q) :=
    Subtype.ext (show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) = coeffEmb (AlgebraicClosure ℚ) jq from
      congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [e] at h
  exact h

theorem coe_residue₂_jFun (h : jFun (q := q) ∈ R.R₂.integers) :
    ((R.R₂.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) ^ q := by
  rw [R.residue₂_eq]
  obtain ⟨h₁, e₁⟩ := R.jqFun_mem_integers₁.2
  obtain ⟨h', e'⟩ : ∃ h' : frickeInvolutionBar (1 * q) (jFun (q := q)) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) := by
    rw [frickeInvolutionBar_jFun']; exact ⟨h₁, e₁⟩
  rw [e', qExpand_one_mul_jqModC R]

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jFun_mem_integers₂ : jFun (q := q) ∈ R.R₂.integers := by
  rw [R.mem_integers₂_iff, frickeInvolutionBar_jFun']; exact R.jqFun_mem_integers₁.1

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jFun_mem_integers₂"
end RFacts
section Core

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
  {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
  [Algebra K₁ (modularFunctionFieldBar (1 * q))]
  [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]

variable (R : LevelOneProlongationPair P)

variable [R.HasGaussTransport K₁]

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.gaussOrder_finite {y f : modularFunctionFieldBar (1 * q)}
    (hy : IsIntegral (R.gaussBase K₁) y) (hf : IsIntegral (R.gaussBase K₁) f) :
    Module.Finite (R.gaussBase K₁) (R.gaussOrder K₁ y f) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral ((Set.finite_singleton f).insert _)
    (by rintro x (rfl | rfl); exacts [hy, hf])

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "gaussOrder_finite"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.surjective_of_finite_of_gen_mem_range
    {S : Type*} [CommRing S] [Algebra (R.gaussBase K₁) S]
    {T : Type*} [Field T] [Algebra (R.gaussBase K₁) T] [Algebra (ResidueField (R.gaussBase K₁)) T]
    [IsScalarTower (R.gaussBase K₁) (ResidueField (R.gaussBase K₁)) T]
    (val : T ≃+* modularFunctionFieldFullC (ResidueField A) 1)
    (hval : ∀ a : A, val (algebraMap (R.gaussBase K₁) T ⟨algebraMap (AlgebraicClosure ℚ) K₁ a, (R.algebraMap_mem_gaussBase_iff a).mpr a.2⟩)
      = algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a))
    (hfin : FiniteDimensional (ResidueField (R.gaussBase K₁)) T)
    (ρ : S →ₐ[R.gaussBase K₁] T)
    (hgen : ∃ s : S, ((val (ρ s) : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A)) :
    Function.Surjective ρ := by
  haveI := hfin
  have halg : ∀ c : ResidueField (R.gaussBase K₁), algebraMap (ResidueField (R.gaussBase K₁)) T c ∈ Set.range ρ := by
    intro c
    obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨algebraMap (R.gaussBase K₁) S v, ?_⟩
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (R.gaussBase K₁) (ResidueField (R.gaussBase K₁)) T v]
    rfl
  let Tr : Subalgebra (ResidueField (R.gaussBase K₁)) T :=
    { carrier := Set.range ρ
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, map_mul _ _ _⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, map_add _ _ _⟩
      algebraMap_mem' := halg }
  haveI : Algebra.IsAlgebraic (ResidueField (R.gaussBase K₁)) T := Algebra.IsAlgebraic.of_finite _ _
  have hinv : ∀ y ∈ Tr, y⁻¹ ∈ Tr := fun y hy =>
    Subalgebra.inv_mem_of_algebraic (A := Tr) (x := ⟨y, hy⟩) (Algebra.IsAlgebraic.isAlgebraic _)
  have hmemV : ∀ v : R.gaussBase K₁, algebraMap (R.gaussBase K₁) T v ∈ Tr := fun v =>
    ⟨algebraMap (R.gaussBase K₁) S v, ρ.commutes v⟩
  obtain ⟨s₀, hs₀⟩ := hgen

  suffices key : ∀ (y : LaurentSeries (ResidueField A)) (hy : y ∈ modularFunctionFieldFullC (ResidueField A) 1),
      val.symm ⟨y, hy⟩ ∈ Tr by
    intro x
    obtain ⟨s, hs⟩ := key (val x).1 (val x).2
    refine ⟨s, ?_⟩
    rw [hs]
    show val.symm (val x) = x
    exact val.symm_apply_apply x
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨d, _, hd, rfl⟩ := hx
      obtain rfl : d = 1 := Nat.dvd_one.mp hd
      have e : val.symm ⟨qExpand (ResidueField A) 1 (jqModC (ResidueField A)),
          IntermediateField.subset_adjoin _ _ (mem_divisorExpansionsC (ResidueField A) 1 (dvd_refl 1))⟩ = ρ s₀ := by
        rw [RingEquiv.symm_apply_eq]
        apply Subtype.ext
        show qExpand (ResidueField A) 1 (jqModC (ResidueField A)) = ((val (ρ s₀) : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        rw [hs₀, qExpand_one_apply]
      rw [e]; exact ⟨s₀, rfl⟩
  | algebraMap c =>
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      have e : val.symm ⟨algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A a),
          IntermediateField.algebraMap_mem _ _⟩
          = algebraMap (R.gaussBase K₁) T ⟨algebraMap (AlgebraicClosure ℚ) K₁ a, (R.algebraMap_mem_gaussBase_iff a).mpr a.2⟩ := by
        rw [RingEquiv.symm_apply_eq, hval]; rfl
      rw [e]; exact hmemV _
  | add x y hx hy ihx ihy =>
      have e : val.symm ⟨x + y, add_mem hx hy⟩ = val.symm ⟨x, hx⟩ + val.symm ⟨y, hy⟩ := by
        rw [← map_add]; rfl
      rw [e]; exact Tr.add_mem ihx ihy
  | inv x hx ihx =>
      have e : val.symm ⟨x⁻¹, inv_mem hx⟩ = (val.symm ⟨x, hx⟩)⁻¹ := by
        rw [← map_inv₀]; rfl
      rw [e]; exact hinv _ ihx
  | mul x y hx hy ihx ihy =>
      have e : val.symm ⟨x * y, mul_mem hx hy⟩ = val.symm ⟨x, hx⟩ * val.symm ⟨y, hy⟩ := by
        rw [← map_mul]; rfl
      rw [e]; exact Tr.mul_mem ihx ihy

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "surjective_of_finite_of_gen_mem_range"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.rho₁_surjective {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₁.integers) (hf : f ∈ R.R₁.integers)
    (hfin₁ : FiniteDimensional (ResidueField (R.gaussBase K₁)) R.ResOne)
    (hgen₁ : ∃ s : R.gaussOrder K₁ y f, ((ResOne.val R (R.rho₁ K₁ hy hf s) : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A)) :
    Function.Surjective (R.rho₁ K₁ hy hf) :=
  R.surjective_of_finite_of_gen_mem_range (ResOne.valEquiv R) (fun a => R.resBase₁_algebraMap a) hfin₁ (R.rho₁ K₁ hy hf) hgen₁

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "rho₁_surjective"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.rho₂_surjective {y f : modularFunctionFieldBar (1 * q)} (hy : y ∈ R.R₂.integers) (hf : f ∈ R.R₂.integers)
    (hfin₂ : FiniteDimensional (ResidueField (R.gaussBase K₁)) R.ResTwo)
    (hgen₂ : ∃ s : R.gaussOrder K₁ y f, ((ResTwo.val R (R.rho₂ K₁ hy hf s) : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A)) :
    Function.Surjective (R.rho₂ K₁ hy hf) :=
  R.surjective_of_finite_of_gen_mem_range (ResTwo.valEquiv R) (fun a => R.resBase₂_algebraMap a) hfin₂ (R.rho₂ K₁ hy hf) hgen₂

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "rho₂_surjective"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_halfIdempotent {y f : modularFunctionFieldBar (1 * q)}
    (hy₁ : y ∈ R.R₁.integers) (hf₁ : f ∈ R.R₁.integers) (hy₂ : y ∈ R.R₂.integers) (hf₂ : f ∈ R.R₂.integers)
    (hjS : jFun (q := q) ∈ R.gaussOrder K₁ y f) (hjqS : jqFun (q := q) ∈ R.gaussOrder K₁ y f) :
    ∃ e : R.gaussOrder K₁ y f, R.rho₁ K₁ hy₁ hf₁ e ≠ 0 ∧ R.rho₂ K₁ hy₂ hf₂ e = 0 := by
  let X : R.gaussOrder K₁ y f := ⟨jqFun (q := q), hjqS⟩
  let Y : R.gaussOrder K₁ y f := ⟨jFun (q := q), hjS⟩
  have vX₁ : ((ResOne.val R (R.rho₁ K₁ hy₁ hf₁ X) : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) ^ q := by
    rw [rho₁_apply]
    obtain ⟨h, e⟩ := R.jqFun_mem_integers₁.2
    have : R.gaussOrderToIntegers₁ K₁ hy₁ hf₁ X = ⟨jqFun (q := q), h⟩ := Subtype.ext (R.coe_gaussOrderToIntegers₁ hy₁ hf₁ X)
    rw [this, e, qExpand_one_mul_jqModC R]
  have vY₁ : ((ResOne.val R (R.rho₁ K₁ hy₁ hf₁ Y) : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) := by
    rw [rho₁_apply]
    obtain ⟨h, e⟩ := R.jFun_mem_integers₁.2
    have : R.gaussOrderToIntegers₁ K₁ hy₁ hf₁ Y = ⟨jFun (q := q), h⟩ := Subtype.ext (R.coe_gaussOrderToIntegers₁ hy₁ hf₁ Y)
    rw [this, e]
  have vX₂ : ((ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ X) : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) := by
    rw [rho₂_apply]
    have : R.gaussOrderToIntegers₂ K₁ hy₂ hf₂ X = ⟨jqFun (q := q), R.jqFun_mem_integers₂⟩ := Subtype.ext (R.coe_gaussOrderToIntegers₂ hy₂ hf₂ X)
    rw [this, coe_residue₂_jqFun]
  have vY₂ : ((ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ Y) : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) ^ q := by
    rw [rho₂_apply]
    have : R.gaussOrderToIntegers₂ K₁ hy₂ hf₂ Y = ⟨jFun (q := q), R.jFun_mem_integers₂⟩ := Subtype.ext (R.coe_gaussOrderToIntegers₂ hy₂ hf₂ Y)
    rw [this, coe_residue₂_jFun]
  refine ⟨X ^ q - Y, ?_, ?_⟩
  · intro h0
    have hsplit : ResOne.val R (R.rho₁ K₁ hy₁ hf₁ (X ^ q - Y)) = (ResOne.val R (R.rho₁ K₁ hy₁ hf₁ X)) ^ q - ResOne.val R (R.rho₁ K₁ hy₁ hf₁ Y) := by
      rw [map_sub, map_pow]; rfl
    have h0' : ((ResOne.val R (R.rho₁ K₁ hy₁ hf₁ (X ^ q - Y)) : modularFunctionFieldFullC (ResidueField A) 1) :
        LaurentSeries (ResidueField A)) = 0 := by rw [h0]; rfl
    rw [hsplit, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, vX₁, vY₁, sub_eq_zero, ← pow_mul] at h0'
    apply transcendental_jqModC (ResidueField A)
    refine ⟨Polynomial.X ^ (q * q) - Polynomial.X, ?_, ?_⟩
    · exact FiniteField.X_pow_card_sub_X_ne_zero (ResidueField A)
        (lt_of_lt_of_le (Fact.out : q.Prime).one_lt (Nat.le_mul_self q))
    · simp only [map_sub, map_pow, Polynomial.aeval_X, h0', sub_self]
  · have hsplit : ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ (X ^ q - Y)) = (ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ X)) ^ q - ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ Y) := by
      rw [map_sub, map_pow]; rfl
    show ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ (X ^ q - Y)) = (0 : modularFunctionFieldFullC (ResidueField A) 1)
    rw [hsplit]
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, vX₂, vY₂, sub_self, ZeroMemClass.coe_zero]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "exists_halfIdempotent"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.rho_surjective {y f : modularFunctionFieldBar (1 * q)}
    (hy₁ : y ∈ R.R₁.integers) (hf₁ : f ∈ R.R₁.integers) (hy₂ : y ∈ R.R₂.integers) (hf₂ : f ∈ R.R₂.integers)
    (hjS : jFun (q := q) ∈ R.gaussOrder K₁ y f) (hjqS : jqFun (q := q) ∈ R.gaussOrder K₁ y f)
    (hfin₁ : FiniteDimensional (ResidueField (R.gaussBase K₁)) R.ResOne)
    (hfin₂ : FiniteDimensional (ResidueField (R.gaussBase K₁)) R.ResTwo)
    (hgen₁ : ∃ s : R.gaussOrder K₁ y f, ((ResOne.val R (R.rho₁ K₁ hy₁ hf₁ s) : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (hgen₂ : ∃ s : R.gaussOrder K₁ y f, ((ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ s) : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A)) :
    Function.Surjective fun s : R.gaussOrder K₁ y f => (R.rho₁ K₁ hy₁ hf₁ s, R.rho₂ K₁ hy₂ hf₂ s) := by
  obtain ⟨e, he₁, he₂⟩ := R.exists_halfIdempotent hy₁ hf₁ hy₂ hf₂ hjS hjqS
  exact GaussPencil.surjective_prod_algHom_of_exists (R.rho₁ K₁ hy₁ hf₁) (R.rho₂ K₁ hy₂ hf₂)
    (R.rho₁_surjective hy₁ hf₁ hfin₁ hgen₁) (R.rho₂_surjective hy₂ hf₂ hfin₂ hgen₂) e he₁ he₂

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "rho_surjective"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.norm_mem_and_residue_norm_eq_core_impl
    (y f : modularFunctionFieldBar (1 * q))
    (hy₁ : y ∈ R.R₁.integers) (hf₁ : f ∈ R.R₁.integers) (hy₂ : y ∈ R.R₂.integers) (hf₂ : f ∈ R.R₂.integers)
    (hyint : IsIntegral (R.gaussBase K₁) y) (hfint : IsIntegral (R.gaussBase K₁) f)
    (hjS : jFun (q := q) ∈ R.gaussOrder K₁ y f) (hjqS : jqFun (q := q) ∈ R.gaussOrder K₁ y f)
    (hspan : Submodule.span K₁ (R.gaussOrder K₁ y f : Set (modularFunctionFieldBar (1 * q))) = ⊤)
    (hκ₁ : 0 < Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne)
    (hκ₂ : 0 < Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo)
    (hdeg : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne + Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo
      = Module.finrank K₁ (modularFunctionFieldBar (1 * q)))
    (hgen₁ : ∃ s : R.gaussOrder K₁ y f, ((ResOne.val R (R.rho₁ K₁ hy₁ hf₁ s) : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (hgen₂ : ∃ s : R.gaussOrder K₁ y f, ((ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ s) : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A)) :
    Algebra.norm K₁ f
        = algebraMap (R.gaussBase K₁) K₁ (Algebra.norm (R.gaussBase K₁) (⟨f, R.self_mem_gaussOrder y f⟩ : R.gaussOrder K₁ y f)) ∧
      IsLocalRing.residue (R.gaussBase K₁) (Algebra.norm (R.gaussBase K₁) (⟨f, R.self_mem_gaussOrder y f⟩ : R.gaussOrder K₁ y f))
        = Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₁ K₁ hy₁ hf₁ ⟨f, R.self_mem_gaussOrder y f⟩)
            * Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₂ K₁ hy₂ hf₂ ⟨f, R.self_mem_gaussOrder y f⟩) := by
  haveI := R.gaussOrder_finite hyint hfint
  haveI hfin₁ : FiniteDimensional (ResidueField (R.gaussBase K₁)) R.ResOne := Module.finite_of_finrank_pos hκ₁
  haveI hfin₂ : FiniteDimensional (ResidueField (R.gaussBase K₁)) R.ResTwo := Module.finite_of_finrank_pos hκ₂
  exact GaussPencil.norm_eq_algebraMap_and_residue_eq_prod (R.gaussOrder K₁ y f) hspan
    (R.rho₁ K₁ hy₁ hf₁) (R.rho₂ K₁ hy₂ hf₂) (R.rho_surjective hy₁ hf₁ hy₂ hf₂ hjS hjqS hfin₁ hfin₂ hgen₁ hgen₂) hdeg
    ⟨f, R.self_mem_gaussOrder y f⟩

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "norm_mem_and_residue_norm_eq_core_impl"
end Core

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
    [Algebra K₁ (modularFunctionFieldBar (1 * q))]
    [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]
    (R : P.LevelOneProlongationPair) [R.HasGaussTransport K₁]
    (y f : modularFunctionFieldBar (1 * q))
    (hy₁ : y ∈ R.R₁.integers) (hf₁ : f ∈ R.R₁.integers) (hy₂ : y ∈ R.R₂.integers) (hf₂ : f ∈ R.R₂.integers)
    (hyint : IsIntegral (R.gaussBase K₁) y) (hfint : IsIntegral (R.gaussBase K₁) f)
    (hjS : PlaceSpecialization.jFun (q := q) ∈ R.gaussOrder K₁ y f) (hjqS : PlaceSpecialization.jqFun (q := q) ∈ R.gaussOrder K₁ y f)
    (hspan : Submodule.span K₁ (R.gaussOrder K₁ y f : Set (modularFunctionFieldBar (1 * q))) = ⊤)
    (hκ₁ : 0 < Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne)
    (hκ₂ : 0 < Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo)
    (hdeg : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne + Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo
      = Module.finrank K₁ (modularFunctionFieldBar (1 * q)))
    (hgen₁ : ∃ s : R.gaussOrder K₁ y f, ((ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ResOne.val R (R.rho₁ K₁ hy₁ hf₁ s) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (hgen₂ : ∃ s : R.gaussOrder K₁ y f, ((ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ s) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A)) :
    Algebra.norm K₁ f
        = algebraMap (R.gaussBase K₁) K₁ (Algebra.norm (R.gaussBase K₁) (⟨f, R.self_mem_gaussOrder y f⟩ : R.gaussOrder K₁ y f)) ∧
      IsLocalRing.residue (R.gaussBase K₁) (Algebra.norm (R.gaussBase K₁) (⟨f, R.self_mem_gaussOrder y f⟩ : R.gaussOrder K₁ y f))
        = Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₁ K₁ hy₁ hf₁ ⟨f, R.self_mem_gaussOrder y f⟩)
            * Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₂ K₁ hy₂ hf₂ ⟨f, R.self_mem_gaussOrder y f⟩) :=
  R.norm_mem_and_residue_norm_eq_core_impl y f hy₁ hf₁ hy₂ hf₂ hyint hfint hjS hjqS hspan hκ₁ hκ₂ hdeg hgen₁ hgen₂

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_norm_mem_and_residue_norm_eq_core
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_norm_mem_and_residue_norm_eq_core (solution)

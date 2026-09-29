-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_sum_eq_span_translates_of_isCuspidalAlong_of_isCosetEigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a506766c-23bb-5a79-83de-fb63e6ae0fde

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Submodule
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_eq_span_translates_of_isCuspidalAlong_of_isCosetEigenfunction
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

noncomputable section

section Core

open FLT.SmoothAdmissibleSchurCommutant

namespace IsotypicSpan

universe u v w

section Module

variable {G : Type u} [Group G] {X : Type v} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)

private theorem asModuleEquiv_smul (μ : MonoidAlgebra ℂ G) (y : ρ.asModule) :
    ρ.asModuleEquiv (μ • y) = μ.coeff.sum fun g c => c • ρ g (ρ.asModuleEquiv y) := by
  rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp only [Finsupp.sum, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]

private theorem asModuleEquiv_of_smul (g : G) (y : ρ.asModule) :
    ρ.asModuleEquiv (MonoidAlgebra.of ℂ G g • y) = ρ g (ρ.asModuleEquiv y) := by
  have h := Representation.asModuleEquiv_symm_map_rho ρ g (ρ.asModuleEquiv y)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [← h, LinearEquiv.apply_symm_apply]

private def toX (q : Submodule (MonoidAlgebra ℂ G) ρ.asModule) : Submodule ℂ X :=
  (q.restrictScalars ℂ).map (ρ.asModuleEquiv : ρ.asModule →ₗ[ℂ] X)

private theorem mem_toX {q : Submodule (MonoidAlgebra ℂ G) ρ.asModule} {x : X} :
    x ∈ toX ρ q ↔ ρ.asModuleEquiv.symm x ∈ q := by
  rw [toX, Submodule.mem_map_equiv, Submodule.restrictScalars_mem]

private theorem asModuleEquiv_mem_toX {q : Submodule (MonoidAlgebra ℂ G) ρ.asModule} {y : ρ.asModule} (hy : y ∈ q) :
    ρ.asModuleEquiv y ∈ toX ρ q := by
  rw [mem_toX, LinearEquiv.symm_apply_apply]; exact hy

private theorem toX_mono {q q' : Submodule (MonoidAlgebra ℂ G) ρ.asModule} (h : q ≤ q') : toX ρ q ≤ toX ρ q' :=
  fun _ hx => (mem_toX ρ).mpr (h ((mem_toX ρ).mp hx))

private theorem rho_mem_toX {q : Submodule (MonoidAlgebra ℂ G) ρ.asModule} {x : X} (hx : x ∈ toX ρ q) (g : G) :
    ρ g x ∈ toX ρ q := by
  rw [mem_toX] at hx ⊢
  rw [Representation.asModuleEquiv_symm_map_rho]
  exact Submodule.smul_mem _ _ hx

private theorem toX_span_singleton (y : ρ.asModule) :
    toX ρ (Submodule.span (MonoidAlgebra ℂ G) {y}) =
      Submodule.span ℂ (Set.range fun g => ρ g (ρ.asModuleEquiv y)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_toX, Submodule.mem_span_singleton] at hx
    obtain ⟨μ, hμ⟩ := hx
    have hx' : x = ρ.asModuleEquiv (μ • y) := by rw [hμ, LinearEquiv.apply_symm_apply]
    rw [hx', asModuleEquiv_smul, Finsupp.sum]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, mem_toX, Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)

variable {E : Type w} [AddCommGroup E] [Module ℂ E] (πE : Representation ℂ G E)

set_option backward.isDefEq.respectTransparency false in

private theorem isSimpleModule_of_isIrreducibleRep (h : IsIrreducibleRep πE) :
    IsSimpleModule (MonoidAlgebra ℂ G) πE.asModule := by
  obtain ⟨⟨v, hv⟩, hW⟩ := h
  haveI : Nontrivial E := nontrivial_of_ne v 0 hv
  have hs : IsSimpleOrder πE.invtSubmodule :=
    { eq_bot_or_eq_top := fun p => by
        have hinv : ∀ (g : G) (w : E), w ∈ (p : Submodule ℂ E) → πE g w ∈ (p : Submodule ℂ E) := by
          intro g w hw
          have hp := (Representation.mem_invtSubmodule πE).mp p.2 g
          rw [Module.End.mem_invtSubmodule] at hp
          exact hp hw
        rcases hW (p : Submodule ℂ E) hinv with h0 | h1
        · exact Or.inl (Subtype.ext h0)
        · exact Or.inr (Subtype.ext h1) }
  rw [isSimpleModule_iff]
  exact (OrderIso.isSimpleOrder_iff (Representation.mapSubmodule πE)).mp hs

private theorem isIsotypicOfType_pi (R : Type*) [Ring R] (S : Type*) [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (d : ℕ) : IsIsotypicOfType R (Fin d → S) S := by
  intro m hm
  haveI : Nontrivial m := IsSimpleModule.nontrivial R m
  obtain ⟨⟨x, hxm⟩, hx⟩ := exists_ne (0 : m)
  have hx0 : x ≠ 0 := fun h => hx (Subtype.ext h)
  have hx1 : ¬ ∀ j, x j = 0 := fun h => hx0 (funext h)
  obtain ⟨j, hj⟩ := not_forall.mp hx1
  let p : m →ₗ[R] S := (LinearMap.proj j).comp m.subtype
  have hp0 : p ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h ⟨x, hxm⟩
    simp only [p, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearMap.coe_proj,
      Function.eval, LinearMap.zero_apply] at this
    exact hj this
  have hinj := (LinearMap.injective_or_eq_zero p).resolve_right hp0
  have hsurj := (LinearMap.surjective_or_eq_zero p).resolve_right hp0
  exact ⟨LinearEquiv.ofBijective p ⟨hinj, hsurj⟩⟩

set_option backward.isDefEq.respectTransparency false in

private theorem exists_linearEquiv_fun [IsSimpleModule (MonoidAlgebra ℂ G) πE.asModule] {d : ℕ}
    (e' : Fin d → πE.asModule) (f' : ρ.asModule)
    (hyp : ∀ μ : MonoidAlgebra ℂ G, (∀ j, μ • e' j = 0) → μ • f' = 0) :
    ∃ n : ℕ, Nonempty (Submodule.span (MonoidAlgebra ℂ G) {f'} ≃ₗ[MonoidAlgebra ℂ G] (Fin n → πE.asModule)) := by
  classical
  let Φ : MonoidAlgebra ℂ G →ₗ[MonoidAlgebra ℂ G] (Fin d → πE.asModule) :=
    LinearMap.pi fun j => LinearMap.toSpanSingleton (MonoidAlgebra ℂ G) πE.asModule (e' j)
  let T : MonoidAlgebra ℂ G →ₗ[MonoidAlgebra ℂ G] ρ.asModule :=
    LinearMap.toSpanSingleton (MonoidAlgebra ℂ G) ρ.asModule f'
  have hker : LinearMap.ker Φ ≤ LinearMap.ker T := by
    intro μ hμ
    rw [LinearMap.mem_ker] at hμ ⊢
    exact hyp μ fun j => congr_fun hμ j
  let ψ : (MonoidAlgebra ℂ G ⧸ LinearMap.ker Φ) →ₗ[MonoidAlgebra ℂ G] ρ.asModule := (LinearMap.ker Φ).liftQ T hker
  have hrange : LinearMap.range ψ = Submodule.span (MonoidAlgebra ℂ G) {f'} := by
    rw [Submodule.range_liftQ]
    exact (LinearMap.span_singleton_eq_range (MonoidAlgebra ℂ G) ρ.asModule f').symm
  have hisoPi : IsIsotypicOfType (MonoidAlgebra ℂ G) (Fin d → πE.asModule) πE.asModule :=
    isIsotypicOfType_pi (MonoidAlgebra ℂ G) πE.asModule d
  let eq := Φ.quotKerEquivRange
  haveI hssQ : IsSemisimpleModule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G ⧸ LinearMap.ker Φ) :=
    (LinearEquiv.isSemisimpleModule_iff eq).mpr inferInstance
  have hisoQ : IsIsotypicOfType (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G ⧸ LinearMap.ker Φ) πE.asModule :=
    hisoPi.of_injective ((LinearMap.range Φ).subtype.comp eq.toLinearMap)
      ((LinearMap.range Φ).injective_subtype.comp eq.injective)
  obtain ⟨P, hP⟩ := exists_isCompl (LinearMap.ker ψ)
  let eN : LinearMap.range ψ ≃ₗ[MonoidAlgebra ℂ G] P :=
    ψ.quotKerEquivRange.symm.trans (Submodule.quotientEquivOfIsCompl _ P hP)
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ G) (LinearMap.range ψ) := IsSemisimpleModule.range ψ
  have hisoN : IsIsotypicOfType (MonoidAlgebra ℂ G) (LinearMap.range ψ) πE.asModule :=
    hisoQ.of_injective (P.subtype.comp eN.toLinearMap) (P.injective_subtype.comp eN.injective)
  haveI : Module.Finite (MonoidAlgebra ℂ G) (LinearMap.range ψ) := by
    rw [hrange, Module.Finite.iff_fg]
    exact Submodule.fg_span_singleton f'
  obtain ⟨n, ⟨e⟩⟩ := hisoN.linearEquiv_fun
  exact ⟨n, ⟨(LinearEquiv.ofEq _ _ hrange).symm.trans e⟩⟩

private theorem funCongrLeft_swap_single (R : Type*) [Semiring R] (S : Type*) [AddCommMonoid S] [Module R S] {n : ℕ}
    (i j : Fin n) (y : S) :
    LinearEquiv.funCongrLeft R S (Equiv.swap i j) (Pi.single i y) = Pi.single j y := by
  classical
  ext k
  rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  rcases eq_or_ne k j with rfl | hkj
  · rw [Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_same]
  · rcases eq_or_ne k i with rfl | hki
    · rw [Equiv.swap_apply_left, Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hkj.symm]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

end Module

section Representation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X : Type v} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
  {E : Type w} [AddCommGroup E] [Module ℂ E] (πE : Representation ℂ G E)

set_option backward.isDefEq.respectTransparency false in

private theorem exists_le_iSup_of_forall_sum_smul_eq_zero
    (hirr : IsIrreducibleRep πE) (hsm : IsSmoothRep πE) (hadm : IsAdmissibleRep πE)
    (hK₀ : ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G))
    {d : ℕ} (e : Fin d → E) (f : X)
    (hyp : ∀ μ : G →₀ ℂ, (∀ j, (μ.sum fun h c => c • πE h (e j)) = 0) → (μ.sum fun h c => c • ρ h f) = 0) :
    ∃ (n : ℕ) (M : Fin n → Submodule ℂ X),
      (∀ i, M i ≤ Submodule.span ℂ (Set.range fun h => ρ h f)) ∧
      (∀ i, ∀ h : G, ∀ F ∈ M i, ρ h F ∈ M i) ∧
      (∀ i, M i ≠ ⊥ ∧ ∀ F ∈ M i, F ≠ 0 → M i ≤ Submodule.span ℂ (Set.range fun h => ρ h F)) ∧
      (∀ i, ∀ F ∈ M i, ∃ Uv : Subgroup G, IsOpen (Uv : Set G) ∧ ∀ k ∈ Uv, ρ k F = F) ∧
      (∀ i, ∀ Uv : Subgroup G, IsOpen (Uv : Set G) →
        ∃ B : Finset X, ∀ F ∈ M i, (∀ k ∈ Uv, ρ k F = F) → F ∈ Submodule.span ℂ (B : Set X)) ∧
      (∀ i j, ∃ T : X →ₗ[ℂ] X, Submodule.map T (M i) = M j ∧ (∀ F ∈ M i, T F = 0 → F = 0) ∧
        ∀ h : G, ∀ F ∈ M i, T (ρ h F) = ρ h (T F)) ∧
      Submodule.span ℂ (Set.range fun h => ρ h f) ≤ ⨆ i, M i := by
  classical
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) πE.asModule := isSimpleModule_of_isIrreducibleRep πE hirr

  let f' : ρ.asModule := ρ.asModuleEquiv.symm f
  let e' : Fin d → πE.asModule := fun j => πE.asModuleEquiv.symm (e j)
  have hyp' : ∀ μ : MonoidAlgebra ℂ G, (∀ j, μ • e' j = 0) → μ • f' = 0 := by
    intro μ hμ
    apply ρ.asModuleEquiv.injective
    rw [asModuleEquiv_smul, map_zero, LinearEquiv.apply_symm_apply]
    refine hyp μ.coeff fun j => ?_
    have := congrArg πE.asModuleEquiv (hμ j)
    rwa [asModuleEquiv_smul, map_zero, LinearEquiv.apply_symm_apply] at this
  obtain ⟨n, ⟨eN⟩⟩ := exists_linearEquiv_fun ρ πE e' f' hyp'

  let N' : Submodule (MonoidAlgebra ℂ G) ρ.asModule := Submodule.span (MonoidAlgebra ℂ G) {f'}
  have hN'X : toX ρ N' = Submodule.span ℂ (Set.range fun h => ρ h f) := by
    rw [toX_span_singleton, LinearEquiv.apply_symm_apply]
  let ι : Fin n → (πE.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule) := fun i =>
    N'.subtype ∘ₗ eN.symm.toLinearMap ∘ₗ LinearMap.single (MonoidAlgebra ℂ G) (fun _ : Fin n => πE.asModule) i
  have hι : ∀ i (y : πE.asModule), ι i y = (eN.symm (Pi.single i y) : ρ.asModule) := fun i y => rfl
  have hιN : ∀ i (y : πE.asModule), ι i y ∈ N' := fun i y => by rw [hι]; exact Submodule.coe_mem _
  have hιinj : ∀ i, Function.Injective (ι i) := fun i => by
    intro y y' h
    rw [hι, hι] at h
    have h2 := eN.symm.injective (Subtype.ext h)
    exact Pi.single_injective i h2

  have hρι : ∀ i (h : G) (y : πE.asModule),
      ρ h (ρ.asModuleEquiv (ι i y)) = ρ.asModuleEquiv (ι i (MonoidAlgebra.of ℂ G h • y)) := by
    intro i h y
    rw [LinearMap.map_smul, asModuleEquiv_of_smul]
  have hfix : ∀ i (k : G) (y : πE.asModule), ρ k (ρ.asModuleEquiv (ι i y)) = ρ.asModuleEquiv (ι i y) →
      πE k (πE.asModuleEquiv y) = πE.asModuleEquiv y := by
    intro i k y h
    rw [hρι] at h
    have h2 := hιinj i (ρ.asModuleEquiv.injective h)
    rw [← asModuleEquiv_of_smul, h2]

  let M : Fin n → Submodule ℂ X := fun i => toX ρ (LinearMap.range (ι i))
  have hMmem : ∀ i (y : πE.asModule), ρ.asModuleEquiv (ι i y) ∈ M i :=
    fun i y => asModuleEquiv_mem_toX ρ ⟨y, rfl⟩
  have hMex : ∀ i, ∀ F ∈ M i, ∃ y : πE.asModule, F = ρ.asModuleEquiv (ι i y) := by
    intro i F hF
    obtain ⟨y, hy⟩ := (mem_toX ρ).mp hF
    exact ⟨y, by rw [hy, LinearEquiv.apply_symm_apply]⟩

  have hsimple : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (LinearMap.range (ι i)) :=
    fun i => IsSimpleModule.congr (LinearEquiv.ofInjective (ι i) (hιinj i)).symm
  refine ⟨n, M, fun i => ?_, fun i h F hF => rho_mem_toX ρ hF h, fun i => ⟨?_, ?_⟩, fun i F hF => ?_,
    fun i Uv hUv => ?_, fun i j => ?_, ?_⟩
  ·
    rw [← hN'X]
    exact toX_mono ρ (by rintro _ ⟨y, rfl⟩; exact hιN i y)
  ·
    haveI : Nontrivial πE.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) πE.asModule
    obtain ⟨y, hy⟩ := exists_ne (0 : πE.asModule)
    rw [Submodule.ne_bot_iff]
    refine ⟨ρ.asModuleEquiv (ι i y), hMmem i y, fun h0 => hy (hιinj i ?_)⟩
    rw [map_zero]
    exact ρ.asModuleEquiv.injective (by rw [h0, map_zero])
  ·
    intro F hF hF0
    obtain ⟨y, rfl⟩ := hMex i F hF
    have hatom : IsAtom (LinearMap.range (ι i)) := isSimpleModule_iff_isAtom.mp (hsimple i)
    have hle : Submodule.span (MonoidAlgebra ℂ G) {ι i y} ≤ LinearMap.range (ι i) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact ⟨y, rfl⟩
    have hne : Submodule.span (MonoidAlgebra ℂ G) {ι i y} ≠ ⊥ := by
      rw [Ne, Submodule.span_singleton_eq_bot]
      intro h0; exact hF0 (by rw [h0, map_zero])
    have heq : Submodule.span (MonoidAlgebra ℂ G) {ι i y} = LinearMap.range (ι i) :=
      ((hatom.le_iff.mp hle).resolve_left hne)
    show toX ρ (LinearMap.range (ι i)) ≤ _
    rw [← heq, toX_span_singleton]
  ·
    obtain ⟨y, rfl⟩ := hMex i F hF
    refine ⟨repStabilizer πE (πE.asModuleEquiv y), hsm _, fun k hk => ?_⟩
    rw [mem_repStabilizer] at hk
    rw [hρι]
    congr 2
    apply πE.asModuleEquiv.injective
    rw [asModuleEquiv_of_smul, hk]
  ·
    obtain ⟨K₀, hK₀c, hK₀o⟩ := hK₀
    let K : Subgroup G := K₀ ⊓ Uv
    have hKc : IsCompact (K : Set G) := by
      rw [Subgroup.coe_inf]; exact hK₀c.inter_right (Uv.isClosed_of_isOpen hUv)
    have hKo : IsOpen (K : Set G) := by rw [Subgroup.coe_inf]; exact hK₀o.inter hUv
    haveI hfd : FiniteDimensional ℂ (fixedVectors πE K) := hadm K hKc hKo
    let L : E →ₗ[ℂ] X :=
      (ρ.asModuleEquiv : ρ.asModule →ₗ[ℂ] X) ∘ₗ (ι i).restrictScalars ℂ ∘ₗ
        (πE.asModuleEquiv.symm : E →ₗ[ℂ] πE.asModule)
    have hL : ∀ y : πE.asModule, L (πE.asModuleEquiv y) = ρ.asModuleEquiv (ι i y) := by
      intro y
      simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        LinearMap.coe_restrictScalars]
    have hfg : ((fixedVectors πE K).map L).FG := (Module.Finite.iff_fg.mp hfd).map L
    obtain ⟨B, hB⟩ := hfg
    refine ⟨B, fun F hF hFU => ?_⟩
    obtain ⟨y, rfl⟩ := hMex i F hF
    rw [hB, ← hL]
    refine Submodule.mem_map_of_mem fun k hk => ?_
    exact hfix i k y (hFU k (Subgroup.mem_inf.mp hk).2)
  ·
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (toX ρ N')
    let PN : X →ₗ[ℂ] toX ρ N' := Submodule.projectionOnto (toX ρ N') Q hQ
    have hPN : ∀ (x : X) (hx : x ∈ toX ρ N'), PN x = ⟨x, hx⟩ := fun x hx =>
      Submodule.projectionOnto_apply_left hQ ⟨x, hx⟩
    let castN : toX ρ N' →ₗ[ℂ] N' :=
      { toFun := fun z => ⟨ρ.asModuleEquiv.symm z.1, (mem_toX ρ).mp z.2⟩
        map_add' := fun z z' => by ext; simp
        map_smul' := fun c z => by ext; simp }
    have hcast : ∀ z : toX ρ N', (castN z : ρ.asModule) = ρ.asModuleEquiv.symm z.1 := fun z => rfl
    let Θ : N' ≃ₗ[MonoidAlgebra ℂ G] N' :=
      eN.trans ((LinearEquiv.funCongrLeft (MonoidAlgebra ℂ G) πE.asModule (Equiv.swap i j)).trans eN.symm)
    have hΘ : ∀ y : πE.asModule, Θ (eN.symm (Pi.single i y)) = eN.symm (Pi.single j y) := by
      intro y
      show eN.symm (LinearEquiv.funCongrLeft (MonoidAlgebra ℂ G) πE.asModule (Equiv.swap i j)
        (eN (eN.symm (Pi.single i y)))) = eN.symm (Pi.single j y)
      rw [eN.apply_symm_apply, funCongrLeft_swap_single]
    let T : X →ₗ[ℂ] X :=
      (ρ.asModuleEquiv : ρ.asModule →ₗ[ℂ] X) ∘ₗ (N'.subtype.restrictScalars ℂ) ∘ₗ
        (Θ.toLinearMap.restrictScalars ℂ) ∘ₗ castN ∘ₗ PN
    have hT : ∀ y : πE.asModule, T (ρ.asModuleEquiv (ι i y)) = ρ.asModuleEquiv (ι j y) := by
      intro y
      have hmem : ρ.asModuleEquiv (ι i y) ∈ toX ρ N' := asModuleEquiv_mem_toX ρ (hιN i y)
      have h1 : castN (PN (ρ.asModuleEquiv (ι i y))) = eN.symm (Pi.single i y) := by
        apply Subtype.ext
        rw [hcast, hPN _ hmem]
        show ρ.asModuleEquiv.symm (ρ.asModuleEquiv (ι i y)) = _
        rw [LinearEquiv.symm_apply_apply, hι]
      simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
        Submodule.coe_subtype]
      rw [h1, hΘ, ← hι]
    refine ⟨T, ?_, ?_, ?_⟩
    · apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        obtain ⟨y, rfl⟩ := hMex i F hF
        rw [hT]
        exact hMmem j y
      · intro F hF
        obtain ⟨y, rfl⟩ := hMex j F hF
        exact ⟨ρ.asModuleEquiv (ι i y), hMmem i y, hT y⟩
    · intro F hF hF0
      obtain ⟨y, rfl⟩ := hMex i F hF
      rw [hT] at hF0
      have hy : y = 0 := hιinj j (ρ.asModuleEquiv.injective (by rw [hF0, map_zero, map_zero]))
      rw [hy, map_zero, map_zero]
    · intro h F hF
      obtain ⟨y, rfl⟩ := hMex i F hF
      rw [hρι, hT, hT, hρι]
  ·
    rw [← hN'X]
    intro x hx
    obtain ⟨x', hx'⟩ : ∃ z : N', (z : ρ.asModule) = ρ.asModuleEquiv.symm x := ⟨⟨_, (mem_toX ρ).mp hx⟩, rfl⟩
    have hx2 : x = ρ.asModuleEquiv (x' : ρ.asModule) := by rw [hx', LinearEquiv.apply_symm_apply]
    have hdec : x' = ∑ k, eN.symm (Pi.single k (eN x' k)) := by
      rw [← map_sum, Finset.univ_sum_single, LinearEquiv.symm_apply_apply]
    rw [hx2, hdec, Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← hι]
    exact Submodule.mem_iSup_of_mem k (hMmem k _)

end Representation

end IsotypicSpan

end Core

section Compact

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localToAdelic3 IsCuspidalAlongP21 IsCuspidalAlongP12 AdelicGL globalPointsGL centralScalarGL valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 heckeGen1 heckeGen2 IsCosetEigenfunction IsRightInvariant IsModerateGrowth3 exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong"
namespace IsotypicSpan
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3 LanglandsTunnell"

section

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))

private def integralMatrices3 : Submonoid (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) where
  carrier := {a | ∀ i j, Valued.v (a i j) ≤ 1}
  one_mem' := by
    intro i j
    exact valued_one_entry_le3 (𝓞 ℚ) ℚ v i j
  mul_mem' := by
    intro a b ha hb i j
    exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ha i l) (fun l => hb l j)

private theorem mem_integralMatrices3 {a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} :
    a ∈ integralMatrices3 v ↔ ∀ i j, Valued.v (a i j) ≤ 1 :=
  Iff.rfl

private theorem isCompact_integralMatrices3 :
    IsCompact (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
  have hpi : IsCompact (Set.pi Set.univ fun _ : Fin 3 =>
      Set.pi Set.univ fun _ : Fin 3 => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers v
  have hset : (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) =
      (Set.pi Set.univ fun _ : Fin 3 =>
        Set.pi Set.univ fun _ : Fin 3 => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := by
    ext a
    rw [SetLike.mem_coe, mem_integralMatrices3]
    constructor
    · intro h i _ j _
      exact h i j
    · intro h i j
      exact h i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hset]
  exact hpi

private theorem localMaximalCompact3_eq_units :
    localMaximalCompact3 (𝓞 ℚ) ℚ v = (integralMatrices3 v).units := by
  ext k
  simp only [mem_localMaximalCompact3_iff, Submonoid.mem_units_iff, mem_integralMatrices3]

private theorem isCompact_localMaximalCompact3 :
    IsCompact ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  rw [localMaximalCompact3_eq_units]
  exact Submonoid.units_isCompact (isCompact_integralMatrices3 v)

end

private theorem isOpen_integralMatrices3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
  have hO : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := Valued.isOpen_integer (v.adicCompletion ℚ)
  have hset : (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) =
      ⋂ (i : Fin 3) (j : Fin 3),
        (fun a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) => a i j) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := by
    ext a
    simp only [SetLike.mem_coe, mem_integralMatrices3, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage (continuous_id.matrix_elem i j)

private theorem isOpen_localMaximalCompact3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  rw [localMaximalCompact3_eq_units]
  exact Submonoid.isOpen_units (isOpen_integralMatrices3 v)

private theorem exists_isCompact_isOpen_subgroup_localGL3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ K₀ : Subgroup (LocalGL3 v), IsCompact (K₀ : Set (LocalGL3 v)) ∧ IsOpen (K₀ : Set (LocalGL3 v)) :=
  ⟨localMaximalCompact3 (𝓞 ℚ) ℚ v, isCompact_localMaximalCompact3 v, isOpen_localMaximalCompact3 v⟩

end LanglandsTunnell.CubicInduction.IsotypicSpan

end Compact

section Translate

open Matrix IsDedekindDomain
open NumberField AutomorphicForm FLT.SmoothAdmissibleSchurCommutant

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localToAdelic3 IsCuspidalAlongP21 IsCuspidalAlongP12 AdelicGL globalPointsGL centralScalarGL valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 heckeGen1 heckeGen2 IsCosetEigenfunction IsRightInvariant IsModerateGrowth3 exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong"
namespace IsotypicSpan
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3 LanglandsTunnell"

private def translateAtRep (v : HeightOneSpectrum (𝓞 ℚ)) :
    Representation ℂ (LocalGL3 v) (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) where
  toFun h :=
    { toFun := fun F g => F (g * localToAdelic3 v h)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro F
    funext g
    show F (g * localToAdelic3 v 1) = F g
    rw [map_one, mul_one]
  map_mul' h h' := by
    apply LinearMap.ext
    intro F
    funext g
    show F (g * localToAdelic3 v (h * h')) = F (g * localToAdelic3 v h * localToAdelic3 v h')
    rw [map_mul, mul_assoc]

private theorem translateAtRep_apply (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    translateAtRep v h F = fun g => F (g * localToAdelic3 v h) := rfl

end LanglandsTunnell.CubicInduction.IsotypicSpan

end Translate

open Matrix IsDedekindDomain NumberField AutomorphicForm
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_eq_span_translates_of_isCuspidalAlong_of_isCosetEigenfunction.LanglandsTunnell LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3 P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_eq_span_translates_of_isCuspidalAlong_of_isCosetEigenfunction.LanglandsTunnell.CubicInduction"

theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (_hmg : IsModerateGrowth3 ℚ f)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) f)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) f)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
    (v : HeightOneSpectrum (𝓞 ℚ))
    (_hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g) :
    ∃ (n : ℕ) (M : Fin n → Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)),
      (∀ i, M i ≤ Submodule.span ℂ
        (Set.range fun h : LocalGL3 v => fun g : AdelicGL 3 (𝓞 ℚ) ℚ => f (g * localToAdelic3 v h))) ∧
      (∀ i, ∀ h : LocalGL3 v, ∀ F ∈ M i, (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => F (g * localToAdelic3 v h)) ∈ M i) ∧
      (∀ i, M i ≠ ⊥ ∧ ∀ F ∈ M i, F ≠ 0 → M i ≤ Submodule.span ℂ
        (Set.range fun h : LocalGL3 v => fun g : AdelicGL 3 (𝓞 ℚ) ℚ => F (g * localToAdelic3 v h))) ∧
      (∀ i, ∀ F ∈ M i, ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (g * localToAdelic3 v k) = F g) ∧
      (∀ i, ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ F ∈ M i,
          (∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (g * localToAdelic3 v k) = F g) →
            F ∈ Submodule.span ℂ (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ i j, ∃ e : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        Submodule.map e (M i) = M j ∧ (∀ F ∈ M i, e F = 0 → F = 0) ∧
          ∀ h : LocalGL3 v, ∀ F ∈ M i, e (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => F (g * localToAdelic3 v h)) =
            fun g : AdelicGL 3 (𝓞 ℚ) ℚ => e F (g * localToAdelic3 v h)) ∧
      Submodule.span ℂ (Set.range fun h : LocalGL3 v => fun g : AdelicGL 3 (𝓞 ℚ) ℚ => f (g * localToAdelic3 v h))
        ≤ ⨆ i, M i := by
  obtain ⟨E, _, _, πE, hirr, hsm, hadm, d, e, hann⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong S ω lam1 lam2 f _hc
      _haut _hcen _hmg (by exact _hP21) (by exact _hP12) _hK _hT1 _hT2 v _hsm
  obtain ⟨n, M, h1, h2, h3, h4, h5, h6, h7⟩ :=
    IsotypicSpan.exists_le_iSup_of_forall_sum_smul_eq_zero (IsotypicSpan.translateAtRep v) πE hirr hsm hadm
      (IsotypicSpan.exists_isCompact_isOpen_subgroup_localGL3 v) e f (fun μ hμ => hann μ hμ)
  refine ⟨n, M, h1, h2, h3, ?_, ?_, h6, h7⟩
  · intro i F hF
    obtain ⟨Uv, hU, hk⟩ := h4 i F hF
    exact ⟨Uv, hU, fun k hk' g => congrFun (hk k hk') g⟩
  · intro i Uv hU
    obtain ⟨B, hB⟩ := h5 i Uv hU
    exact ⟨B, fun F hF hfix => hB F hF fun k hk => funext fun g => hfix k hk g⟩

end

end S_LanglandsTunnell_CubicInduction_exists_sum_eq_span_translates_of_isCuspidalAlong_of_isCosetEigenfunction
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_eq_span_translates_of_isCuspidalAlong_of_isCosetEigenfunction (solution)

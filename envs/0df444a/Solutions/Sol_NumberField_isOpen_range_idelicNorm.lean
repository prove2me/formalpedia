-- Prove2me | solution 1 for NumberField.isOpen_range_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/006f0917-c0c4-595c-955f-67035616c01a

import Mathlib
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot
import Theorems.Thm_NumberField_isOpen_range_powMonoidHom_units_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_isOpen_range_idelicNorm
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace R2ChiOpenEngine

section BadSet

variable (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]

theorem finite_setOf_dvd {I : Ideal (𝓞 M)} (hI : I ≠ ⊥) :
    {w : HeightOneSpectrum (𝓞 M) | w.asIdeal ∣ I}.Finite := by
  classical
  have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 M) => w.asIdeal) {w | w.asIdeal ∣ I} :=
    fun v _ w _ h => HeightOneSpectrum.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine (UniqueFactorizationMonoid.normalizedFactors I).toFinset.finite_toSet.subset ?_
  rintro J ⟨w, hw, rfl⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨w.prime, hw⟩

omit [NumberField E] in

theorem exists_smul_ne {g : M ≃ₐ[E] M} (hg : g ≠ 1) : ∃ x : 𝓞 M, g • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 M, g • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hg (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 M) (K := M) z
  have hx : g (algebraMap (𝓞 M) M x) = algebraMap (𝓞 M) M x := congrArg (algebraMap (𝓞 M) M) (hcon x)
  have hy' : g (algebraMap (𝓞 M) M y) = algebraMap (𝓞 M) M y := congrArg (algebraMap (𝓞 M) M) (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

theorem finite_setOf_inertia_ne_bot :
    {w : HeightOneSpectrum (𝓞 M) | w.asIdeal.inertia (M ≃ₐ[E] M) ≠ ⊥}.Finite := by
  classical
  choose x hx using fun g : {g : M ≃ₐ[E] M // g ≠ 1} => exists_smul_ne E M g.2
  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_univ (α := {g : M ≃ₐ[E] M // g ≠ 1}))
    (fun g _ => finite_setOf_dvd M (I := Ideal.span {g.1 • x g - x g}) ?_)) ?_
  · rw [Ne, Ideal.span_singleton_eq_bot, sub_eq_zero]
    exact hx g
  · intro w hw
    simp only [Set.mem_setOf_eq] at hw
    obtain ⟨g, hgmem, hgne⟩ := (w.asIdeal.inertia (M ≃ₐ[E] M)).bot_or_exists_ne_one.resolve_left hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨⟨g, hgne⟩, Set.mem_univ _, ?_⟩
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hgmem (x ⟨g, hgne⟩)

def bad : Set (HeightOneSpectrum (𝓞 E)) :=
  (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 E)) ''
    {w : HeightOneSpectrum (𝓞 M) | w.asIdeal.inertia (M ≃ₐ[E] M) ≠ ⊥}

theorem bad_finite : (bad E M).Finite :=
  (finite_setOf_inertia_ne_bot E M).image _

theorem inertia_eq_bot_of_not_bad {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ bad E M)
    (w : v.Extension (𝓞 M)) : w.1.asIdeal.inertia (M ≃ₐ[E] M) = ⊥ := by
  by_contra h
  exact hv ⟨w.1, h, w.2⟩

theorem nonempty_extension (v : HeightOneSpectrum (𝓞 E)) : Nonempty (v.Extension (𝓞 M)) := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) v.asIdeal
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨⟨Q, hQmax.isPrime, hQ⟩, ?_⟩⟩
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  exact hQover.over.symm

end BadSet

section Tower

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

omit [NumberField K] [NumberField L] [NumberField M] in
private theorem _root_.R2ChiOpenEngine.under_under (w' : HeightOneSpectrum (𝓞 M)) :
    (w'.under (𝓞 L)).under (𝓞 K) = w'.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  exact Ideal.under_under _

p2m_export "R2ChiOpenEngine" "under_under"

def restr {v : HeightOneSpectrum (𝓞 K)} (wKM : v.Extension (𝓞 M)) : v.Extension (𝓞 L) :=
  ⟨wKM.1.under (𝓞 L), by rw [under_under K L M]; exact wKM.2⟩

def lift {v : HeightOneSpectrum (𝓞 K)} (wKM : v.Extension (𝓞 M)) :
    (restr K L M wKM).1.Extension (𝓞 M) :=
  ⟨wKM.1, rfl⟩

@[reducible] def algLM {v : HeightOneSpectrum (𝓞 K)} (wKM : v.Extension (𝓞 M)) :
    Algebra ((restr K L M wKM).1.adicCompletion L) (wKM.1.adicCompletion M) :=
  (show Algebra _ ((lift K L M wKM).1.adicCompletion M) from inferInstance)

theorem tower {v : HeightOneSpectrum (𝓞 K)} (wKM : v.Extension (𝓞 M)) :
    letI := algLM K L M wKM
    IsScalarTower (v.adicCompletion K) ((restr K L M wKM).1.adicCompletion L)
      (wKM.1.adicCompletion M) := by
  letI instLM := algLM K L M wKM
  apply IsScalarTower.of_algebraMap_eq'
  have h1 : Continuous (algebraMap (v.adicCompletion K) (wKM.1.adicCompletion M)) :=
    Extension.adicCompletionSemialgHom_continuous K M wKM
  have h2 : Continuous ((algebraMap ((restr K L M wKM).1.adicCompletion L)
      (wKM.1.adicCompletion M)).comp
      (algebraMap (v.adicCompletion K) ((restr K L M wKM).1.adicCompletion L))) :=
    (Extension.adicCompletionSemialgHom_continuous L M (lift K L M wKM)).comp
      (Extension.adicCompletionSemialgHom_continuous K L (restr K L M wKM))
  apply DFunLike.coe_injective
  funext c
  obtain ⟨c, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K v c
  induction c using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (h1.comp (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v))
      (h2.comp (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v))
  | ih a =>
  show Extension.adicCompletionSemialgHom K M wKM a =
    Extension.adicCompletionSemialgHom L M (lift K L M wKM)
      (Extension.adicCompletionSemialgHom K L (restr K L M wKM) a)
  rw [Extension.adicCompletionSemialgHom_coe, Extension.adicCompletionSemialgHom_coe]
  erw [Extension.adicCompletionSemialgHom_coe]
  congr 1
  rw [IsScalarTower.algebraMap_apply K L M]
  rfl

example {v : HeightOneSpectrum (𝓞 K)} (wKM : v.Extension (𝓞 M)) :
    Module.Finite ((restr K L M wKM).1.adicCompletion L) ((lift K L M wKM).1.adicCompletion M) :=
  inferInstance

theorem finite_LM {v : HeightOneSpectrum (𝓞 K)} (wKM : v.Extension (𝓞 M)) :
    letI := algLM K L M wKM
    Module.Finite ((restr K L M wKM).1.adicCompletion L) (wKM.1.adicCompletion M) := by
  exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions
    L M (𝓞 M) (restr K L M wKM).1 (lift K L M wKM)

private theorem _root_.R2ChiOpenEngine.norm_norm {v : HeightOneSpectrum (𝓞 K)} (wKM : v.Extension (𝓞 M))
    (y : wKM.1.adicCompletion M) :
    letI := algLM K L M wKM
    Algebra.norm (v.adicCompletion K)
        (Algebra.norm ((restr K L M wKM).1.adicCompletion L) y) =
      Algebra.norm (v.adicCompletion K) y := by
  letI := algLM K L M wKM
  haveI := tower K L M wKM
  haveI := finite_LM K L M wKM
  exact Algebra.norm_norm

p2m_export "R2ChiOpenEngine" "norm_norm"
end Tower

section OpenSet

variable (K : Type*) [Field K] [NumberField K]

def proj (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)

theorem proj_apply (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 K) K) :
    proj K v x = (x.2 : FiniteAdeleRing (𝓞 K) K) v := rfl

theorem continuous_proj (v : HeightOneSpectrum (𝓞 K)) : Continuous (proj K v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

def integralSet : Set (FiniteAdeleRing (𝓞 K) K) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 K), x v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))}

theorem isOpen_integralSet : IsOpen (integralSet K) :=
  RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _

def unitSet : Set (AdeleRing (𝓞 K) K)ˣ :=
  {u | ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) ∈ integralSet K ∧
    (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) ∈ integralSet K}

theorem isOpen_unitSet : IsOpen (unitSet K) := by
  apply IsOpen.inter
  · exact (isOpen_integralSet K).preimage (continuous_snd.comp Units.continuous_val)
  · exact (isOpen_integralSet K).preimage (continuous_snd.comp Units.continuous_coe_inv)

theorem one_mem_unitSet : (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ unitSet K := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · simp only [Units.val_one, SetLike.mem_coe]
    exact one_mem _
  · simp only [inv_one, Units.val_one, SetLike.mem_coe]
    exact one_mem _

theorem valuation_eq_one_of_mem_unitSet {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ unitSet K)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  obtain ⟨h1, h2⟩ := hu
  have ha : Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ≤ 1 :=
    (mem_adicCompletionIntegers _ _ _).mp (h1 v)
  have hb : Valued.v ((((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :
      FiniteAdeleRing (𝓞 K) K) v) ≤ 1 :=
    (mem_adicCompletionIntegers _ _ _).mp (h2 v)
  have hprod : proj K v (u : AdeleRing (𝓞 K) K) * proj K v ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
      AdeleRing (𝓞 K) K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [proj_apply, proj_apply] at hprod
  apply le_antisymm ha
  by_contra hlt
  have hlt' : Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) < 1 :=
    lt_of_le_of_ne ha (fun h => hlt (le_of_eq h.symm))
  have hv := congrArg Valued.v hprod
  rw [map_mul, map_one] at hv
  have hle : Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) *
      Valued.v ((((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :
        FiniteAdeleRing (𝓞 K) K) v) ≤
      Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) * 1 :=
    mul_le_mul_right hb _
  rw [hv, mul_one] at hle
  exact absurd (lt_of_le_of_lt hle hlt') (lt_irrefl _)

def powSet (v : HeightOneSpectrum (𝓞 K)) (d : ℕ) : Set (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (proj K v : AdeleRing (𝓞 K) K →* v.adicCompletion K)) ⁻¹'
    ((powMonoidHom d : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :
      Set (v.adicCompletion K)ˣ)

theorem isOpen_powSet (v : HeightOneSpectrum (𝓞 K)) {d : ℕ} (hd : 0 < d) : IsOpen (powSet K v d) :=
  (NumberField.isOpen_range_powMonoidHom_units_adicCompletion v hd).preimage
    (Continuous.units_map _ (continuous_proj K v))

theorem one_mem_powSet (v : HeightOneSpectrum (𝓞 K)) (d : ℕ) : (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ powSet K v d := by
  show Units.map (proj K v : AdeleRing (𝓞 K) K →* v.adicCompletion K) 1 ∈
    ((powMonoidHom d : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
  rw [map_one]
  exact one_mem _

theorem exists_pow_eq_of_mem_powSet {v : HeightOneSpectrum (𝓞 K)} {d : ℕ} {u : (AdeleRing (𝓞 K) K)ˣ}
    (hu : u ∈ powSet K v d) :
    ∃ c : (v.adicCompletion K)ˣ, (c : v.adicCompletion K) ^ d =
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := by
  have hu' : Units.map (proj K v : AdeleRing (𝓞 K) K →* v.adicCompletion K) u ∈
      ((powMonoidHom d : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) := hu
  obtain ⟨c, hc⟩ := hu'
  refine ⟨c, ?_⟩
  have := congrArg (fun x : (v.adicCompletion K)ˣ => (x : v.adicCompletion K)) hc
  simpa [Units.coe_map, proj_apply] using this

def posSet (w : InfinitePlace K) : Set (AdeleRing (𝓞 K) K)ˣ :=
  {u | ∀ hw : w.IsReal, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) w)}

theorem isOpen_posSet (w : InfinitePlace K) : IsOpen (posSet K w) := by
  by_cases hw : w.IsReal
  · have hcont : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
          (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) w) :=
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp
        ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))
    have : posSet K w = {u : (AdeleRing (𝓞 K) K)ˣ |
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
          (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) w)} := by
      ext u
      exact ⟨fun h => h hw, fun h _ => h⟩
    rw [this]
    exact isOpen_lt continuous_const hcont
  · have : posSet K w = Set.univ := by
      ext u
      exact ⟨fun _ => trivial, fun _ h => absurd h hw⟩
    rw [this]
    exact isOpen_univ

theorem one_mem_posSet (w : InfinitePlace K) : (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ posSet K w := by
  intro hw
  have h1 : ((((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) w) = 1 := rfl
  rw [h1, map_one]
  exact one_pos

end OpenSet

section Main

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def wL (v : HeightOneSpectrum (𝓞 K)) : v.Extension (𝓞 L) := Classical.choice (nonempty_extension K L v)

def deg (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Module.finrank (v.adicCompletion K) ((wL K L v).1.adicCompletion L)

theorem deg_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < deg K L v := Module.finrank_pos

variable (M : Type*) [Field M] [NumberField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K M]

def V : Set (AdeleRing (𝓞 K) K)ˣ :=
  unitSet K ∩ (⋂ v ∈ bad K M, powSet K v (deg K L v)) ∩ (⋂ w : InfinitePlace K, posSet K w)

omit [Algebra L M] [IsScalarTower K L M] [IsGalois K M] in
theorem isOpen_V : IsOpen (V K L M) := by
  refine ((isOpen_unitSet K).inter ?_).inter ?_
  · exact (bad_finite K M).isOpen_biInter fun v _ => isOpen_powSet K v (deg_pos K L v)
  · exact isOpen_iInter_of_finite fun w => isOpen_posSet K w

omit [NumberField M] [Algebra L M] [IsScalarTower K L M] [IsGalois K M] in
theorem one_mem_V : (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ V K L M := by
  refine ⟨⟨one_mem_unitSet K, ?_⟩, ?_⟩
  · simp only [Set.mem_iInter]
    exact fun v _ => one_mem_powSet K v _
  · simp only [Set.mem_iInter]
    exact fun w => one_mem_posSet K w

theorem V_subset_range (B : M4aHerbrand.AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    V K L M ⊆ (B.idelicNorm.range : Set (AdeleRing (𝓞 K) K)ˣ) := by
  intro u hu
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hu
  simp only [Set.mem_iInter] at hu2 hu3
  refine M4aHerbrand.AdeleBaseChange.mem_range_idelicNorm_of_forall_exists_norm_eq K L B u ?_ ?_
  · intro v
    by_cases hv : v ∈ bad K M
    ·
      obtain ⟨c, hc⟩ := exists_pow_eq_of_mem_powSet K (hu2 v hv)
      refine ⟨wL K L v, algebraMap _ _ (c : v.adicCompletion K), ?_⟩
      rw [Algebra.norm_algebraMap]
      exact hc
    ·
      let wKM : v.Extension (𝓞 M) := Classical.choice (nonempty_extension K M v)
      have hI := inertia_eq_bot_of_not_bad K M hv wKM
      obtain ⟨y', -, hy'⟩ :=
        IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot K M v wKM hI
          _ (valuation_eq_one_of_mem_unitSet K hu1 v)
      letI := algLM K L M wKM
      refine ⟨restr K L M wKM, Algebra.norm ((restr K L M wKM).1.adicCompletion L) y', ?_⟩
      rw [norm_norm K L M wKM y']
      exact hy'
  · intro v hv _
    exact hu3 v hv

include M in

theorem isOpen_range_of_over (B : M4aHerbrand.AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    IsOpen (B.idelicNorm.range : Set (AdeleRing (𝓞 K) K)ˣ) := by
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  exact Filter.mem_of_superset ((isOpen_V K L M).mem_nhds (one_mem_V K L M)) (V_subset_range K L M B)

end Main

section Closure

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isOpen_range (B : M4aHerbrand.AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    IsOpen (B.idelicNorm.range : Set (AdeleRing (𝓞 K) K)ˣ) := by
  haveI : NumberField (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    NumberField.of_module_finite K _
  haveI : IsGalois K (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    IsGalois.normalClosure K L (AlgebraicClosure L)
  exact isOpen_range_of_over K L (IntermediateField.normalClosure K L (AlgebraicClosure L)) B

end Closure

end R2ChiOpenEngine

end

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : M4aHerbrand.AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    IsOpen ((B.idelicNorm.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
  R2ChiOpenEngine.isOpen_range K L B

end S_NumberField_isOpen_range_idelicNorm
end P2MW
export P2MW.S_NumberField_isOpen_range_idelicNorm (solution)

-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7b9e52be-b26f-5f00-92ff-6d54af732f82

import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
import Theorems.Thm_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq
import Theorems.Thm_HaarQuotient_measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace K42Polish

open Topology

theorem polishSpace_of_addCommGroup (A : Type*) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] : PolishSpace A := by
  letI u : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace A := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (uniformity A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace A := inferInstance
  infer_instance

theorem polishSpace_of_commGroup (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] : PolishSpace G := by
  letI u : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  haveI : IsUniformGroup G := isUniformGroup_of_commGroup
  haveI : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (uniformity G).IsCountablyGenerated := IsUniformGroup.uniformity_countably_generated
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace G := inferInstance
  infer_instance

end K42Polish

namespace K42H90

open MeasureTheory NumberField Topology
open scoped ENNReal Pointwise

theorem isMulRightInvariant_of_comm {G : Type*} [CommGroup G] [MeasurableSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun x : G => x * g) = fun x => g * x := funext fun x => mul_comm x g
  rw [this]
  exact MeasureTheory.map_mul_left_eq_self μ g

end K42H90

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure] :
    ∃ cN : ℝ, 0 < cN ∧
      ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
        ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
          cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
            g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK) := by
  classical

  haveI hscL : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := Units.isInducing_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : PolishSpace (AdeleRing (𝓞 L) L)ˣ := K42Polish.polishSpace_of_commGroup (AdeleRing (𝓞 L) L)ˣ
  haveI : SigmaFinite νZL := Measure.IsHaarMeasure.sigmaFinite νZL
  haveI : SFinite νZL := inferInstance
  haveI : μAK.IsMulRightInvariant := K42H90.isMulRightInvariant_of_comm μAK
  haveI : LocallyCompactSpace N1 := hN1c.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N1 := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace N1 := Subtype.borelSpace _

  have hsc : Continuous (D.unitsAct σ) := Continuous.units_map _ (D.continuous_act σ)
  let φ : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
    { toFun := fun z => D.unitsAct σ z * z⁻¹
      map_one' := by simp
      map_mul' := fun a b => by rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hφ : ∀ z, φ z = D.unitsAct σ z * z⁻¹ := fun z => rfl
  have hφc : Continuous φ := hsc.mul continuous_inv

  obtain ⟨hinj, hfix, -, hprod⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D
  have hβinj : Function.Injective (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom) :=
    fun a b h => Units.ext (hinj (congrArg Units.val h))
  have hall : ∀ u : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ u = u ↔ ∀ τ : L ≃ₐ[K] L, D.unitsAct τ u = u := by
    intro u
    constructor
    · intro hb τ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      rw [map_zpow]
      induction n using Int.induction_on with
      | zero => simp
      | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hb, ih]
      | pred n ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have hb' : (D.unitsAct σ)⁻¹ u = u := by
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]; exact hb.symm
        rw [hb', ih]
    · intro h; exact h σ

  have hker : ∀ z, φ z = 1 ↔ z ∈ AK := by
    intro z
    rw [hφ, mul_inv_eq_one, hall, hfix z, hAK z, MonoidHom.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

  have hN1_of : ∀ z, φ z ∈ N1 := by
    intro z
    rw [hN1]
    have h1 : ∏ τ : L ≃ₐ[K] L, D.unitsAct τ (φ z) = 1 := by
      have : ∀ τ : L ≃ₐ[K] L, D.unitsAct τ (φ z) = D.unitsAct (τ * σ) z * (D.unitsAct τ z)⁻¹ := by
        intro τ; rw [hφ, map_mul, map_inv, map_mul, MulAut.mul_apply]
      simp_rw [this]
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
        Fintype.prod_equiv (Equiv.mulRight σ) (fun τ => D.unitsAct (τ * σ) z) (fun τ => D.unitsAct τ z)
          (fun τ => rfl), mul_inv_cancel]
    have h2 := hprod (φ z)
    rw [h1] at h2
    apply hβinj
    rw [map_one]
    exact h2.symm

  have hN1_surj : ∀ u : (AdeleRing (𝓞 L) L)ˣ, u ∈ N1 → ∃ z, φ z = u := by
    intro u hu
    rw [hN1] at hu
    have h1 : ∏ τ : L ≃ₐ[K] L, D.unitsAct τ u = 1 := by rw [hprod u, hu, map_one]
    have hord : orderOf σ = Nat.card (L ≃ₐ[K] L) := orderOf_eq_card_of_forall_mem_zpowers hgen
    have h2 : ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) u = 1 := by
      rw [← h1, Finset.prod_range (fun k => D.unitsAct (σ ^ k) u)]
      have hinj' : Function.Injective (fun i : Fin (orderOf σ) => σ ^ (i : ℕ)) := by
        intro i j h
        exact Fin.ext (pow_injOn_Iio_orderOf (by simp) (by simp) h)
      have hbij : Function.Bijective (fun i : Fin (orderOf σ) => σ ^ (i : ℕ)) :=
        (Fintype.bijective_iff_injective_and_card _).mpr
          ⟨hinj', by rw [Fintype.card_fin, hord, Nat.card_eq_fintype_card]⟩
      exact hbij.prod_comp (fun τ : L ≃ₐ[K] L => D.unitsAct τ u)
    obtain ⟨w, hw⟩ :=
      M4aHerbrand.IdeleGaloisDescent.exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one K L σ D u h2
    exact ⟨w, by rw [hφ, hw, mul_comm]⟩

  let φN : (AdeleRing (𝓞 L) L)ˣ →* N1 := φ.codRestrict N1 hN1_of
  have hφNc : Continuous φN := hφc.subtype_mk _
  have hφNs : Function.Surjective φN := fun n => by
    obtain ⟨z, hz⟩ := hN1_surj n n.2
    exact ⟨z, Subtype.ext hz⟩
  have hφNo : IsOpenMap φN := MonoidHom.isOpenMap_of_sigmaCompact φN hφNs hφNc

  have hcompat : ∀ a b : (AdeleRing (𝓞 L) L)ˣ, (MulAction.orbitRel AK (AdeleRing (𝓞 L) L)ˣ) a b → φN a = φN b := by
    intro a b hab
    have hab' : a ∈ MulAction.orbit AK b := hab
    rw [MulAction.mem_orbit_iff] at hab'
    obtain ⟨x, rfl⟩ := hab'
    apply Subtype.ext
    show φ ((x : (AdeleRing (𝓞 L) L)ˣ) * b) = φ b
    rw [map_mul, (hker _).mpr x.2, one_mul]
  let Φ : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ → N1 := Quotient.lift (fun z => φN z) hcompat
  have hΦmk : ∀ z, Φ (Quotient.mk'' z) = φN z := fun z => rfl
  have hΦc : Continuous Φ := hφNc.quotient_lift _
  have hΦbij : Function.Bijective Φ := by
    refine ⟨fun q₁ q₂ h => ?_, fun n => ?_⟩
    · obtain ⟨a, rfl⟩ := Quotient.exists_rep q₁
      obtain ⟨b, rfl⟩ := Quotient.exists_rep q₂
      change φN a = φN b at h
      have hab : φ (a * b⁻¹) = 1 := by
        rw [map_mul, map_inv, show φ a = φ b from congrArg Subtype.val h, mul_inv_cancel]
      apply Quotient.sound
      show a ∈ MulAction.orbit AK b
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨a * b⁻¹, (hker _).mp hab⟩, by show a * b⁻¹ * b = a; rw [inv_mul_cancel_right]⟩
    · obtain ⟨z, hz⟩ := hφNs n
      exact ⟨Quotient.mk'' z, hz⟩
  have hΦo : IsOpenMap Φ := by
    intro U hU
    have : Φ '' U = φN '' ((Quotient.mk'' : _ → MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ⁻¹' U) := by
      ext n
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨z, rfl⟩ := Quotient.exists_rep q
        exact ⟨z, hq, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨_, hz, rfl⟩
    rw [this]
    exact hφNo _ (hU.preimage continuous_quotient_mk')
  let eΦ : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ ≃ₜ N1 :=
    (Equiv.ofBijective Φ hΦbij).toHomeomorphOfContinuousOpen hΦc hΦo
  have heΦ : ∀ q, eΦ q = Φ q := fun q => rfl

  haveI : T2Space (MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) := eΦ.isEmbedding.t2Space
  haveI : SecondCountableTopology (MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) :=
    eΦ.isInducing.secondCountableTopology
  haveI : BorelSpace (MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) := inferInstance
  let eM : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ ≃ᵐ N1 := eΦ.toMeasurableEquiv
  have heM : ∀ q, eM q = Φ q := fun q => rfl

  set HQ := HaarQuotient.measure νZL AK μAK with hHQ
  set ν : Measure N1 := Measure.map eM HQ with hν

  have hright : ∀ w : (AdeleRing (𝓞 L) L)ˣ, Measure.map (· * w) νZL = νZL := fun w => by
    have : (fun x : (AdeleRing (𝓞 L) L)ˣ => x * w) = fun x => w * x := funext fun x => mul_comm x w
    rw [this]; exact MeasureTheory.map_mul_left_eq_self νZL w
  haveI hνinv : ν.IsMulLeftInvariant := by
    refine ⟨fun n => ?_⟩
    obtain ⟨w, rfl⟩ := hφNs n

    let Tw : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ → MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ :=
      Quotient.map' (fun z => w * z) (fun a b hab => by
        have hab' : a ∈ MulAction.orbit AK b := hab
        show w * a ∈ MulAction.orbit AK (w * b)
        rw [MulAction.mem_orbit_iff] at hab' ⊢
        obtain ⟨x, rfl⟩ := hab'
        exact ⟨x, by show (x : (AdeleRing (𝓞 L) L)ˣ) * (w * b) = w * ((x : (AdeleRing (𝓞 L) L)ˣ) * b); rw [mul_left_comm]⟩)
    have hTwc : Continuous Tw := (continuous_const.mul continuous_id).quotient_map' _
    have hTwm : Measurable Tw := hTwc.measurable
    have hcomm : (fun m : N1 => φN w * m) ∘ eM = eM ∘ Tw := by
      funext q
      obtain ⟨z, rfl⟩ := Quotient.exists_rep q
      show φN w * Φ (Quotient.mk'' z) = Φ (Quotient.mk'' (w * z))
      rw [hΦmk, hΦmk, map_mul]
    have hTw : Measure.map Tw HQ = HQ := by
      ext S hS
      rw [Measure.map_apply hTwm hS, ← lintegral_indicator_one (hTwm hS), ← lintegral_indicator_one hS]
      set f : (AdeleRing (𝓞 L) L)ˣ → ENNReal :=
        ((Quotient.mk'' : _ → MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ⁻¹' S).indicator 1 with hf
      have hfH : ∀ x ∈ AK, ∀ g : (AdeleRing (𝓞 L) L)ˣ, f (x * g) = f g := by
        intro x hx g
        have : (Quotient.mk'' (x * g) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) = Quotient.mk'' g :=
          Quotient.sound (by show x * g ∈ MulAction.orbit AK g; rw [MulAction.mem_orbit_iff]; exact ⟨⟨x, hx⟩, rfl⟩)
        simp only [hf, Set.indicator_apply, Set.mem_preimage, this, Pi.one_apply]
      have key := HaarQuotient.lintegral_comp_out_mul_eq_of_map_mul_right_eq νZL AK hAKc μAK f hfH w (hright w)
      have h1 : ∀ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          (Tw ⁻¹' S).indicator (1 : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ → ENNReal) q = f (q.out * w) := by
        intro q
        have hT : Tw q = Quotient.mk'' (q.out * w) := by
          have hq := congrArg Tw (Quotient.out_eq q)
          rw [← hq, mul_comm]
          rfl
        simp only [hf, Set.indicator_apply, Set.mem_preimage, hT, Pi.one_apply]
      have h2 : ∀ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          S.indicator (1 : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ → ENNReal) q = f q.out := by
        intro q
        have hq : (Quotient.mk'' q.out : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) = q := Quotient.out_eq q
        simp only [hf, Set.indicator_apply, Set.mem_preimage, hq, Pi.one_apply]
      simp_rw [h1, h2]
      exact key
    rw [hν, Measure.map_map (measurable_const_mul _) eM.measurable, hcomm, ← Measure.map_map eM.measurable hTwm, hTw]

  obtain ⟨K₀, hK₀, hK₀1⟩ := exists_compact_mem_nhds (1 : (AdeleRing (𝓞 L) L)ˣ)
  set C : Set N1 := φN '' K₀ with hC
  have hCc : IsCompact C := hK₀.image hφNc
  have hCi : (interior C).Nonempty := by
    refine ⟨φN 1, interior_mono (Set.image_mono interior_subset) ?_⟩
    exact (hφNo _ isOpen_interior).interior_eq.symm ▸ ⟨1, mem_interior_iff_mem_nhds.mpr hK₀1, rfl⟩
  have hCpre : eM ⁻¹' C = (Quotient.mk'' : _ → MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) '' K₀ := by
    ext q
    obtain ⟨z, rfl⟩ := Quotient.exists_rep q
    constructor
    · rintro ⟨z', hz', h⟩
      have : (Quotient.mk'' z' : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) = Quotient.mk'' z :=
        hΦbij.1 (by rw [hΦmk, hΦmk]; exact h)
      exact ⟨z', hz', this⟩
    · rintro ⟨z', hz', h⟩
      refine ⟨z', hz', ?_⟩
      show φN z' = Φ (Quotient.mk'' z)
      exact (hΦmk z').symm.trans (congrArg Φ h)
  have hνC : ν C = HQ ((Quotient.mk'' : _ → MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) '' K₀) := by
    rw [hν, Measure.map_apply eM.measurable hCc.isClosed.measurableSet, hCpre]
  have hνClt : ν C ≠ ⊤ := by
    rw [hνC, hHQ]
    exact (HaarQuotient.measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact νZL AK hAKc μAK K₀ hK₀).1.ne
  have hνC0 : ν C ≠ 0 := by
    rw [hνC]
    intro h0

    set T : Set (MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) := Quotient.mk'' '' K₀ with hT
    have hTm : MeasurableSet T := (hK₀.image continuous_quotient_mk').isClosed.measurableSet
    set f : (AdeleRing (𝓞 L) L)ˣ → ENNReal := (Quotient.mk'' ⁻¹' T).indicator 1 with hf
    have hfm : Measurable f := (measurable_one.indicator (hTm.preimage continuous_quotient_mk'.measurable))
    have hW := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out νZL AK hAKc μAK f hfm
    have hinner : ∀ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
        ∫⁻ x : AK, f ((x : (AdeleRing (𝓞 L) L)ˣ) * q.out) ∂μAK = T.indicator (fun _ => μAK Set.univ) q := by
      intro q
      have hq : ∀ x : AK, f ((x : (AdeleRing (𝓞 L) L)ˣ) * q.out) = T.indicator (1 : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ → ENNReal) q := by
        intro x
        have : (Quotient.mk'' ((x : (AdeleRing (𝓞 L) L)ˣ) * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) = q := by
          have h' : (Quotient.mk'' ((x : (AdeleRing (𝓞 L) L)ˣ) * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) = Quotient.mk'' q.out :=
            Quotient.sound (by show (x : (AdeleRing (𝓞 L) L)ˣ) * q.out ∈ MulAction.orbit AK q.out; rw [MulAction.mem_orbit_iff]; exact ⟨x, rfl⟩)
          exact h'.trans (Quotient.out_eq q)
        simp only [hf, Set.indicator_apply, Set.mem_preimage, this, Pi.one_apply]
      simp_rw [hq]
      rw [lintegral_const]
      by_cases hqT : q ∈ T <;> simp [Set.indicator, hqT]
    simp_rw [hinner] at hW
    rw [lintegral_indicator_const hTm, h0, mul_zero] at hW
    have hpos : 0 < νZL K₀ := Measure.measure_pos_of_mem_nhds νZL hK₀1
    have hle : νZL K₀ ≤ ∫⁻ g, f g ∂νZL := by
      rw [← lintegral_indicator_one hK₀.isClosed.measurableSet]
      refine lintegral_mono fun g => ?_
      by_cases hg : g ∈ K₀
      · have hgT : g ∈ (Quotient.mk'' : _ → MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ⁻¹' T := ⟨g, hg, rfl⟩
        rw [Set.indicator_of_mem hg, hf, Set.indicator_of_mem hgT]
      · rw [Set.indicator_of_notMem hg]
        exact bot_le
    rw [hW] at hle
    exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)
  haveI hνH : ν.IsHaarMeasure := Measure.isHaarMeasure_of_isCompact_nonempty_interior ν C hCc hCi hνC0 hνClt

  have hμ : μN = μN.haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul μN ν
  refine ⟨(μN.haarScalarFactor ν : ℝ), NNReal.coe_pos.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure μN ν), fun g => ?_⟩
  calc ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN
      = ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂(μN.haarScalarFactor ν • ν) := by rw [← hμ]
    _ = μN.haarScalarFactor ν • ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂ν := integral_smul_nnreal_measure _ _
    _ = ((μN.haarScalarFactor ν : ℝ) : ℂ) * ∫ q, g ((eM q : N1) : (AdeleRing (𝓞 L) L)ˣ) ∂HQ := by
        rw [NNReal.smul_def, Complex.real_smul]
        congr 1
        exact MeasureTheory.integral_map_equiv eM _
    _ = _ := by
        rw [hHQ]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        show g ((Φ q : N1) : (AdeleRing (𝓞 L) L)ˣ) = g (D.unitsAct σ q.out * (q.out)⁻¹)
        conv_lhs => rw [← Quotient.out_eq q]
        rfl

end S_M4aHerbrand_IdeleGaloisDescent_exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv (solution)

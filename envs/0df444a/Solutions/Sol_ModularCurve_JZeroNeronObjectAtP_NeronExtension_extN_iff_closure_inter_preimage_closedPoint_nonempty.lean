-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.extN_iff_closure_inter_preimage_closedPoint_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/08182c8d-8b50-51ae-a268-9816a12b3319

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_mem_closure_range
import Theorems.Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty.AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP"

set_option maxHeartbeats 1600000

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage Scheme.fromSpecResidueField LocallyOfFiniteType.stalkMap Surjective Spec.map_inj Spec.fromSpecStalk_eq' Spec.preimage_map Scheme.Hom Scheme.range_fromSpecResidueField IsFinite QuasiCompact LocallyOfFiniteType Spec StructureSheaf.toStalk IsIntegral Spec.map Scheme Scheme.Hom.comp_base Scheme.SpecToEquivOfField IsSeparated Spec.preimage Spec.structureSheaf IsFinite.SpecMap_iff Scheme.SpecMap_stalkMap_fromSpecStalk Scheme.Hom.comp_apply Scheme.exists_section_comp_eq_of_exists_mem_closure_range" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.exists_mem_closure_range_and_snd_eq_closedPoint_of_finite
    {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    [Algebra R R'] [Module.Finite R R']
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{0}} (x' : T ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hcl : ∃ z ∈ closure (Set.range (x' ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base),
      g.base z = IsLocalRing.closedPoint R) :
    ∃ z' ∈ closure (Set.range x'.base),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z' = IsLocalRing.closedPoint R' := by

  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hclosed : IsClosedMap (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base :=
    (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).isClosedMap
  obtain ⟨z, hz, hgz⟩ := hcl

  have hsub : closure (Set.range (x' ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base) ⊆
      (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base '' closure (Set.range x'.base) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact hclosed.closure_image_subset _
  obtain ⟨z', hz', rfl⟩ := hsub hz
  refine ⟨z', hz', ?_⟩

  have hcond : g.base ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z') =
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))).base ((pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z') := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  rw [hgz] at hcond
  have hcomap : (PrimeSpectrum.comap (algebraMap R R') ((pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z')).asIdeal =
      IsLocalRing.maximalIdeal R := by
    have h := hcond.symm
    rw [show (Spec.map (CommRingCat.ofHom (algebraMap R R'))).base ((pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z') =
        PrimeSpectrum.comap (algebraMap R R') ((pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z') from rfl] at h
    exact congrArg PrimeSpectrum.asIdeal h

  have hmax : ((pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z').asIdeal.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
    rw [show ((pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z').asIdeal.comap (algebraMap R R') =
        (PrimeSpectrum.comap (algebraMap R R') ((pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base z')).asIdeal from rfl, hcomap]
    exact IsLocalRing.maximalIdeal.isMaximal R
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal hmax

namespace S17Hens

theorem isArtinianRing_quotient_map_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  let k := R ⧸ IsLocalRing.maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  have hJR : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R (S ⧸ J) r = 0 := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ J), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  letI : Algebra k (S ⧸ J) := (Ideal.Quotient.lift _ (algebraMap R (S ⧸ J)) hJR).toAlgebra
  haveI : IsScalarTower R k (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Module.Finite k (S ⧸ J) := Module.Finite.of_restrictScalars_finite R k (S ⧸ J)
  exact IsArtinianRing.of_finite k (S ⧸ J)

theorem isLocalRing_of_isDomain_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  classical
  by_contra hS

  have h1 : ∃ a : S, ¬ IsUnit a ∧ ¬ IsUnit (1 - a) := by
    by_contra h
    push Not at h
    exact hS (IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      by_cases ha : IsUnit a
      · exact Or.inl ha
      · exact Or.inr (h a ha))
  obtain ⟨a, ha, ha'⟩ := h1
  obtain ⟨m₁, hm₁, ham₁⟩ := exists_max_ideal_of_mem_nonunits ha
  obtain ⟨m₂, hm₂, ham₂⟩ := exists_max_ideal_of_mem_nonunits ha'
  have hne : m₁ ≠ m₂ := by
    intro h
    subst h
    have : (1 : S) ∈ m₁ := by
      have := m₁.add_mem ham₁ ham₂
      rwa [add_sub_cancel] at this
    exact hm₁.ne_top ((Ideal.eq_top_iff_one _).mpr this)

  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  have hJle : ∀ m : Ideal S, m.IsMaximal → J ≤ m := by
    intro m hm
    rw [hJ, Ideal.map_le_iff_le_comap]
    haveI := hm
    have hmax : (m.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    rw [IsLocalRing.eq_maximalIdeal hmax]

  haveI : IsArtinianRing (S ⧸ J) := isArtinianRing_quotient_map_maximalIdeal
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hmaxq : ∀ m : Ideal S, m.IsMaximal → (m.map (Ideal.Quotient.mk J)).IsMaximal := by
    intro m hm
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm with h | h
    · exfalso
      have : m = ⊤ := by
        have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h
        rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top] at h2
        have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
          rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        rw [hker, sup_eq_left.mpr (hJle m hm)] at h2
        exact h2
      exact hm.ne_top this
    · exact h
  let M₁ : MaximalSpectrum (S ⧸ J) := ⟨m₁.map (Ideal.Quotient.mk J), hmaxq m₁ hm₁⟩
  let M₂ : MaximalSpectrum (S ⧸ J) := ⟨m₂.map (Ideal.Quotient.mk J), hmaxq m₂ hm₂⟩
  have hM : M₁ ≠ M₂ := by
    intro h
    apply hne
    have h2 : m₁.map (Ideal.Quotient.mk J) = m₂.map (Ideal.Quotient.mk J) := congrArg MaximalSpectrum.asIdeal h
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h2
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_map_of_surjective _ hsurj] at h3
    have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rwa [hker, sup_eq_left.mpr (hJle m₁ hm₁), sup_eq_left.mpr (hJle m₂ hm₂)] at h3

  let π := IsArtinianRing.quotNilradicalEquivPi (S ⧸ J)
  let f₀ : ∀ I : MaximalSpectrum (S ⧸ J), (S ⧸ J) ⧸ I.asIdeal := Pi.single M₁ 1
  have hf₀ : IsIdempotentElem f₀ := by
    show f₀ * f₀ = f₀
    ext I
    by_cases hI : I = M₁
    · subst hI; simp [f₀]
    · simp [f₀, hI]
  have hf₀0 : f₀ ≠ 0 := by
    intro h
    have := congrFun h M₁
    simp [f₀] at this
    exact M₁.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this.symm)
  have hf₀1 : f₀ ≠ 1 := by
    intro h
    have := congrFun h M₂
    have h0 : f₀ M₂ = 0 := Pi.single_eq_of_ne hM.symm _
    rw [h0, Pi.one_apply] at this
    exact M₂.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this)
  let ē₀ := π.symm f₀
  have hē₀ : IsIdempotentElem ē₀ := by
    show π.symm f₀ * π.symm f₀ = π.symm f₀
    rw [← map_mul, hf₀.eq]

  have hnil : ∀ y ∈ RingHom.ker (Ideal.Quotient.mk (nilradical (S ⧸ J))), IsNilpotent y := by
    intro y hy
    rw [Ideal.mk_ker] at hy
    exact hy
  obtain ⟨ē, hē, hēē₀⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (Ideal.Quotient.mk (nilradical (S ⧸ J))) hnil ē₀
    (Ideal.Quotient.mk_surjective ē₀) hē₀

  obtain ⟨e, ⟨he, hemk⟩, -⟩ := HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite ē hē

  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with h0 | h1
  · apply hf₀0
    have : ē = 0 := by rw [← hemk, h0, map_zero]
    have : ē₀ = 0 := by rw [← hēē₀, this, map_zero]
    have : f₀ = π 0 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_zero]
  · apply hf₀1
    have : ē = 1 := by rw [← hemk, h1, map_one]
    have : ē₀ = 1 := by rw [← hēē₀, this, map_one]
    have : f₀ = π 1 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_one]

end S17Hens

namespace S17Hens

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem mem_of_isIntegral {K F : Type} [Field K] [Field F] [Algebra K F]
    (O : ValuationSubring K) [Algebra O F] [IsScalarTower O K F]
    (O' : ValuationSubring F) (hO' : ∀ x : K, algebraMap K F x ∈ O' ↔ x ∈ O)
    {y : F} (hy : IsIntegral O y) : y ∈ O' := by
  by_contra hyO
  obtain ⟨p, hp, hpy⟩ := hy

  have hy0 : y ≠ 0 := fun h => hyO (h ▸ O'.zero_mem)
  have hyinv : O'.valuation y⁻¹ < 1 := by
    rw [map_inv₀, inv_lt_one₀ ((Valuation.pos_iff _).mpr hy0)]
    exact lt_of_not_ge fun h => hyO ((O'.valuation_le_one_iff y).mp h)
  have hcoef : ∀ i, O'.valuation (algebraMap O F (p.coeff i)) ≤ 1 := by
    intro i
    rw [O'.valuation_le_one_iff, IsScalarTower.algebraMap_apply O K F]
    exact (hO' _).mpr (p.coeff i).2

  set n := p.natDegree with hn
  have heval : y ^ n + ∑ i ∈ Finset.range n, algebraMap O F (p.coeff i) * y ^ i = 0 := by
    have h := hpy
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul, add_comm] at h
    exact h
  have hone : (1 : F) = - ∑ i ∈ Finset.range n, algebraMap O F (p.coeff i) * (y⁻¹) ^ (n - i) := by
    have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy0
    have h2 := congrArg (fun z => z * (y⁻¹) ^ n) heval
    simp only [add_mul, zero_mul, Finset.sum_mul] at h2
    rw [← mul_pow, mul_inv_cancel₀ hy0, one_pow] at h2
    rw [eq_neg_iff_add_eq_zero, ← h2]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [mul_assoc]
    congr 1
    rw [inv_pow, inv_pow, ← div_eq_mul_inv, eq_div_iff hyn, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ hy0), ← pow_add,
      Nat.sub_add_cancel hi.le]
  have hlt : O'.valuation (∑ i ∈ Finset.range n, algebraMap O F (p.coeff i) * (y⁻¹) ^ (n - i)) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc O'.valuation (algebraMap O F (p.coeff i)) * O'.valuation y⁻¹ ^ (n - i)
        ≤ 1 * O'.valuation y⁻¹ ^ (n - i) := by gcongr; exact hcoef i
      _ < 1 := by
        rw [one_mul]
        exact pow_lt_one₀ zero_le' hyinv (Nat.sub_ne_zero_of_lt hi)
  have : O'.valuation (1 : F) < 1 := by
    rw [hone, Valuation.map_neg]; exact hlt
  rw [map_one] at this
  exact lt_irrefl _ this

theorem valuationSubring_eq_integralClosure_of_henselian
    {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] [HenselianLocalRing O]
    [Algebra O F] [IsScalarTower O K F]
    (O' : ValuationSubring F) (hO' : ∀ x : K, algebraMap K F x ∈ O' ↔ x ∈ O) :
    O'.toSubring = (integralClosure O F).toSubring ∧ Module.Finite O (integralClosure O F) ∧
      IsDiscreteValuationRing (integralClosure O F) := by
  classical
  haveI : IsFractionRing O K := inferInstance
  haveI hCfin : Module.Finite O (integralClosure O F) := IsIntegralClosure.finite O K F (integralClosure O F)
  haveI : IsDedekindDomain (integralClosure O F) := IsIntegralClosure.isDedekindDomain O K F (integralClosure O F)
  haveI : IsFractionRing (integralClosure O F) F := integralClosure.isFractionRing_of_finite_extension K F

  haveI : IsLocalRing (integralClosure O F) := isLocalRing_of_isDomain_of_moduleFinite (R := O) (S := integralClosure O F)
  have hinjF : Function.Injective (algebraMap O F) := by
    rw [IsScalarTower.algebraMap_eq O K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective O K)
  have hinj : Function.Injective (algebraMap O (integralClosure O F)) := by
    intro a b h
    apply hinjF
    rw [IsScalarTower.algebraMap_apply O (integralClosure O F) F, IsScalarTower.algebraMap_apply O (integralClosure O F) F b, h]
  have hCnf : ¬ IsField (integralClosure O F) := by
    rw [← Algebra.IsIntegral.isField_iff_isField hinj]
    exact IsDiscreteValuationRing.not_isField O
  haveI hDVR : IsDiscreteValuationRing (integralClosure O F) :=
    ((IsDiscreteValuationRing.TFAE (integralClosure O F) hCnf).out 0 2).mpr (inferInstance : IsDedekindDomain (integralClosure O F))
  refine ⟨?_, hCfin, hDVR⟩
  have hCle : ∀ c : integralClosure O F, (c : F) ∈ O' := fun c => mem_of_isIntegral O O' hO' c.2

  let φ : integralClosure O F →+* O' :=
    { toFun := fun c => ⟨(c : F), hCle c⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ c, ((φ c : O') : F) = (c : F) := fun _ => rfl
  let P : Ideal (integralClosure O F) := (IsLocalRing.maximalIdeal O').comap φ
  haveI hP : P.IsPrime := Ideal.comap_isPrime φ _
  have hPmem : ∀ c, c ∈ P ↔ O'.valuation (c : F) < 1 := by
    intro c
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ₀K0 : (ϖ₀ : K) ≠ 0 := fun h => hϖ₀.ne_zero (Subtype.ext h)
  have hϖ₀v : O'.valuation (algebraMap O F ϖ₀) < 1 := by

    rw [IsScalarTower.algebraMap_apply O K F, ValuationSubring.algebraMap_apply]
    by_contra hge
    rw [not_lt] at hge
    have hle : O'.valuation (algebraMap K F (ϖ₀ : K)) ≤ 1 := (O'.valuation_le_one_iff _).mpr ((hO' _).mpr ϖ₀.2)
    have heq : O'.valuation (algebraMap K F (ϖ₀ : K)) = 1 := le_antisymm hle hge
    have hinv : algebraMap K F (ϖ₀ : K)⁻¹ ∈ O' := by
      rw [← O'.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
    have hinvO : (ϖ₀ : K)⁻¹ ∈ O := (hO' _).mp hinv
    apply hϖ₀.not_isUnit
    exact ⟨⟨ϖ₀, ⟨(ϖ₀ : K)⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ hϖ₀K0), Subtype.ext (inv_mul_cancel₀ hϖ₀K0)⟩, rfl⟩
  have hPne : P ≠ ⊥ := by
    intro h
    have hmem : algebraMap O (integralClosure O F) ϖ₀ ∈ P := by
      rw [hPmem]
      have : ((algebraMap O (integralClosure O F) ϖ₀ : integralClosure O F) : F) = algebraMap O F ϖ₀ :=
        (IsScalarTower.algebraMap_apply O (integralClosure O F) F ϖ₀).symm
      rw [this]; exact hϖ₀v
    rw [h, Ideal.mem_bot] at hmem
    exact hϖ₀.ne_zero (hinj (by rw [hmem, map_zero]))
  have hPmax : P = IsLocalRing.maximalIdeal (integralClosure O F) :=
    IsLocalRing.eq_maximalIdeal (hP.isMaximal hPne)

  apply le_antisymm
  · intro y hy
    change y ∈ integralClosure O F
    by_cases hy0 : y = 0
    · rw [hy0]; exact Subalgebra.zero_mem _
    haveI : ValuationRing (integralClosure O F) := inferInstance
    rcases ValuationRing.isInteger_or_isInteger (integralClosure O F) y with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [← hc]; exact c.2
    ·
      have hcF : (c : F) = y⁻¹ := hc
      by_cases hcu : IsUnit c
      · obtain ⟨d, hd⟩ := hcu.exists_right_inv
        have h2 : y⁻¹ * (d : F) = 1 := by
          have h3 := congrArg (fun z : integralClosure O F => (z : F)) hd
          simp only [Subalgebra.coe_mul, hcF, Subalgebra.coe_one] at h3
          exact h3
        have : (d : F) = y := by
          calc (d : F) = y * (y⁻¹ * d) := by rw [← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
            _ = y := by rw [h2, mul_one]
        rw [← this]; exact d.2
      · exfalso
        have hcm : c ∈ IsLocalRing.maximalIdeal (integralClosure O F) := (IsLocalRing.mem_maximalIdeal _).mpr hcu
        rw [← hPmax, hPmem, hcF, map_inv₀, inv_lt_one₀ ((Valuation.pos_iff _).mpr hy0)] at hcm
        exact absurd ((O'.valuation_le_one_iff y).mpr hy) (not_le.mpr hcm)
  · intro y hy
    exact mem_of_isIntegral O O' hO' hy

end S17Hens

p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.finiteDimensional_residueField_of_locallyOfFiniteType_of_isAlgebraic
    {K : Type} [Field K] (O : ValuationSubring K)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of ↥O)) [LocallyOfFiniteType g]
    (ξ : X) [Algebra K (X.residueField ξ)]
    (hθ : ∀ r : ↥O, algebraMap K (X.residueField ξ) (r : K) = (Spec.preimage (X.fromSpecResidueField ξ ≫ g)).hom r)
    [Algebra.IsAlgebraic K (X.residueField ξ)] :
    FiniteDimensional K (X.residueField ξ) := by

  let c : CommRingCat.of ↥O ⟶ X.residueField ξ :=
    StructureSheaf.toStalk (↥O) (g.base ξ) ≫ g.stalkMap ξ ≫ X.residue ξ
  have hfac : X.fromSpecResidueField ξ ≫ g = Spec.map c := by
    simp only [c, Spec.map_comp, Scheme.fromSpecResidueField, Category.assoc]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq']
    rfl
  have hθc : (Spec.preimage (X.fromSpecResidueField ξ ≫ g)) = c := by
    rw [hfac, Spec.preimage_map]

  have hc : c.hom.EssFiniteType := by
    have h1 : (StructureSheaf.toStalk (↥O) (g.base ξ)).hom.EssFiniteType :=
      RingHom.EssFiniteType.holdsForLocalization (R := ↥O)
        ((Spec.structureSheaf ↥O).presheaf.stalk (g.base ξ)) (g.base ξ).asIdeal.primeCompl
    have h2 : (g.stalkMap ξ).hom.EssFiniteType := LocallyOfFiniteType.stalkMap g ξ
    have h3 : (X.residue ξ).hom.EssFiniteType :=
      (RingHom.FiniteType.of_surjective _ (X.residue_surjective ξ)).essFiniteType
    have := (h1.comp h2).comp h3
    first | exact this | simpa [c, CommRingCat.hom_comp] using this | simpa +zetaDelta [c, CommRingCat.hom_comp] using this

  letI : Algebra ↥O (X.residueField ξ) := ((algebraMap K (X.residueField ξ)).comp (algebraMap ↥O K)).toAlgebra
  haveI : IsScalarTower ↥O K (X.residueField ξ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have heq : (algebraMap K (X.residueField ξ)).comp (algebraMap ↥O K) = c.hom := by
    ext r
    rw [RingHom.comp_apply, ← hθc]
    exact hθ r
  haveI : Algebra.EssFiniteType ↥O (X.residueField ξ) := by
    have : (algebraMap ↥O (X.residueField ξ)).EssFiniteType := by
      show ((algebraMap K (X.residueField ξ)).comp (algebraMap ↥O K)).EssFiniteType
      rw [heq]; exact hc
    exact RingHom.essFiniteType_algebraMap.mp this
  haveI : Algebra.EssFiniteType K (X.residueField ξ) := Algebra.EssFiniteType.of_comp ↥O K _
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic (F := K) (E := X.residueField ξ)

namespace S17N4Core
end S17N4Core

namespace S17N4Core

theorem exists_residueField_factor
    {K : Type} [Field K] (O : ValuationSubring K)
    {L : Type} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of ↥O)) [LocallyOfFiniteType g]
    (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp (algebraMap ↥O K)))) :
    ∃ (κ : Type) (_ : Field κ) (_ : Algebra K κ) (_ : FiniteDimensional K κ) (ι : κ →ₐ[K] L)
      (xκ : Spec (CommRingCat.of κ) ⟶ X),
      Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ xκ = x ∧
      xκ ≫ g = Spec.map (CommRingCat.ofHom ((algebraMap K κ).comp (algebraMap ↥O K))) ∧
      Set.range xκ.base = Set.range x.base := by
  classical

  let ξ : X := x.base (IsLocalRing.closedPoint L)
  let ι₀ : X.residueField ξ ⟶ CommRingCat.of L := (Scheme.SpecToEquivOfField L X x).2
  have hfac : Spec.map ι₀ ≫ X.fromSpecResidueField ξ = x := (Scheme.SpecToEquivOfField L X).left_inv x

  let θ : ↥O →+* X.residueField ξ := (Spec.preimage (X.fromSpecResidueField ξ ≫ g)).hom
  have hθspec : Spec.map (CommRingCat.ofHom θ) = X.fromSpecResidueField ξ ≫ g := by
    show Spec.map (Spec.preimage (X.fromSpecResidueField ξ ≫ g)) = _
    exact Spec.map_preimage _

  have hιθ : ι₀.hom.comp θ = (algebraMap K L).comp (algebraMap ↥O K) := by
    have h1 : Spec.map (CommRingCat.ofHom (ι₀.hom.comp θ)) =
        Spec.map (CommRingCat.ofHom ((algebraMap K L).comp (algebraMap ↥O K))) := by
      rw [← hx, ← hfac, Category.assoc, ← hθspec, ← Spec.map_comp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.mp h1)
  have hθinj : Function.Injective θ := by
    intro a b h
    have h2 := congrArg ι₀.hom h
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hιθ, RingHom.comp_apply, RingHom.comp_apply] at h2
    exact IsFractionRing.injective (↥O) K ((algebraMap K L).injective h2)

  letI : Algebra K (X.residueField ξ) := (IsFractionRing.lift hθinj : K →+* X.residueField ξ).toAlgebra
  have hθ : ∀ r : ↥O, algebraMap K (X.residueField ξ) (r : K) = θ r := fun r =>
    IsFractionRing.lift_algebraMap hθinj r
  have hcompK : ι₀.hom.comp (algebraMap K (X.residueField ξ)) = algebraMap K L := by
    apply IsFractionRing.ringHom_ext (A := ↥O)
    intro r
    rw [RingHom.comp_apply, ValuationSubring.algebraMap_apply, hθ]
    exact congrArg (fun f : ↥O →+* L => f r) hιθ
  let ι : X.residueField ξ →ₐ[K] L :=
    { ι₀.hom with commutes' := fun y => congrArg (fun f : K →+* L => f y) hcompK }
  have hιhom : ι.toRingHom = ι₀.hom := rfl

  haveI : Algebra.IsAlgebraic K (X.residueField ξ) := Algebra.IsAlgebraic.of_injective ι ι.toRingHom.injective
  haveI : FiniteDimensional K (X.residueField ξ) :=
    AlgebraicGeometry.finiteDimensional_residueField_of_locallyOfFiniteType_of_isAlgebraic O g ξ hθ
  refine ⟨X.residueField ξ, inferInstance, inferInstance, inferInstance, ι, X.fromSpecResidueField ξ, ?_, ?_, ?_⟩
  · rw [hιhom, CommRingCat.ofHom_hom]; exact hfac
  · rw [← hθspec]
    congr 2
    exact RingHom.ext (fun r => (hθ r).symm)
  · rw [Scheme.range_fromSpecResidueField]
    have : Set.range x.base = {x.base (IsLocalRing.closedPoint L)} := by
      rw [Set.range_unique]
      congr 2
      exact Subsingleton.elim _ _
    rw [this]

end S17N4Core

namespace S17N4Core

theorem isLocalHom_algebraMap_of_isIntegral {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Algebra.IsIntegral R S] : IsLocalHom (algebraMap R S) := by
  constructor
  intro r hr
  by_contra hru
  have hrm : r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hru
  have hle : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap]
    have hmax : ((IsLocalRing.maximalIdeal S).comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    rw [IsLocalRing.eq_maximalIdeal hmax]
  exact (IsLocalRing.mem_maximalIdeal _).mp (hle (Ideal.mem_map_of_mem _ hrm)) hr

theorem exists_section_comp_eq_of_mem_closure
    {K : Type} [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing ↥O] [HenselianLocalRing ↥O]
    {L : Type} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (φ : ↥O →+* ↥A) (hφ : ∀ r : ↥O, ((φ r : ↥A) : L) = algebraMap K L (r : K))
    (hA : ∀ y : K, algebraMap K L y ∈ A ↔ y ∈ O)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of ↥O)) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom φ))
    (hcl : ∃ z ∈ closure (Set.range x.base), g.base z = IsLocalRing.closedPoint ↥O) :
    ∃ s : Spec (CommRingCat.of ↥A) ⟶ X, s ≫ g = Spec.map (CommRingCat.ofHom φ) ∧
      Spec.map (CommRingCat.ofHom A.subtype) ≫ s = x := by
  classical

  have hφ' : (A.subtype).comp φ = (algebraMap K L).comp (algebraMap ↥O K) := by
    ext r
    exact hφ r
  have hx' : x ≫ g = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp (algebraMap ↥O K))) := by
    rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ']

  obtain ⟨κ, _, _, _, ι, xκ, hxfac, hxκg, hrange⟩ := exists_residueField_factor O g x hx'

  letI : Algebra ↥O κ := ((algebraMap K κ).comp (algebraMap ↥O K)).toAlgebra
  haveI : IsScalarTower ↥O K κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let O' : ValuationSubring κ := A.comap ι.toRingHom
  have hO' : ∀ y : K, algebraMap K κ y ∈ O' ↔ y ∈ O := by
    intro y
    show ι (algebraMap K κ y) ∈ A ↔ y ∈ O
    rw [ι.commutes]
    exact hA y
  haveI : Algebra.IsSeparable K κ := inferInstance
  obtain ⟨hOC, hCfin, hCdvr⟩ := S17Hens.valuationSubring_eq_integralClosure_of_henselian O O' hO'
  haveI := hCfin
  haveI := hCdvr
  let C := integralClosure (↥O) κ
  haveI : IsFractionRing C κ := integralClosure.isFractionRing_of_finite_extension K κ
  haveI : IsLocalHom (algebraMap ↥O C) := isLocalHom_algebraMap_of_isIntegral
  have hCA : ∀ c : C, ι (c : κ) ∈ A := by
    intro c
    have : (c : κ) ∈ O'.toSubring := by rw [hOC]; exact c.2
    exact this
  let ψ : C →+* ↥A :=
    { toFun := fun c => ⟨ι (c : κ), hCA c⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hψφ : ψ.comp (algebraMap ↥O C) = φ := by
    refine RingHom.ext (fun r => Subtype.ext ?_)
    show ι ((algebraMap ↥O C r : C) : κ) = ((φ r : ↥A) : L)
    have h1 : ((algebraMap ↥O C r : C) : κ) = algebraMap K κ (r : K) := rfl
    rw [h1, ι.commutes, hφ]
  have hψι : (A.subtype).comp ψ = ι.toRingHom.comp (algebraMap C κ) := by
    ext c; rfl

  let β := Spec.map (CommRingCat.ofHom (algebraMap ↥O C))
  have hcompat : xκ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C κ)) ≫ β := by
    rw [hxκg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let x' : Spec (CommRingCat.of κ) ⟶ pullback g β := pullback.lift xκ (Spec.map (CommRingCat.ofHom (algebraMap C κ))) hcompat
  have hx'fst : x' ≫ pullback.fst g β = xκ := pullback.lift_fst _ _ _
  have hx'snd : x' ≫ pullback.snd g β = Spec.map (CommRingCat.ofHom (algebraMap C κ)) := pullback.lift_snd _ _ _
  have hcl' : ∃ z ∈ closure (Set.range (x' ≫ pullback.fst g β).base), g.base z = IsLocalRing.closedPoint ↥O := by
    rw [hx'fst, hrange]; exact hcl
  obtain ⟨z', hz', hz's⟩ := AlgebraicGeometry.exists_mem_closure_range_and_snd_eq_closedPoint_of_finite g x' hcl'

  obtain ⟨s', hs'1, hs'2⟩ := AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_mem_closure_range κ
    (pullback.snd g β) x' hx'snd ⟨z', hz', hz's⟩
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ s' ≫ pullback.fst g β, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc s', hs'1, Category.id_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψφ]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψι, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom (algebraMap C κ))), hs'2, ← hxfac, hx'fst]

end S17N4Core

open NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace S17N4

scoped instance isLocalHom_shToPlace (A : ValuationSubring (AlgebraicClosure ℚ)) : IsLocalHom (shToPlace A) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := hx

  have hx0 : ((x : ↥(invField A)) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have : (u : ↥A) = 0 := by
      apply Subtype.ext
      rw [hu, coe_shToPlace, h0]; rfl
    exact u.ne_zero this
  have hxK0 : (x : ↥(invField A)) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
  have hinvA : ((x : ↥(invField A)) : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have h1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = ((x : ↥(invField A)) : AlgebraicClosure ℚ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have := congrArg (fun z : (↥A)ˣ => ((z : ↥A) : AlgebraicClosure ℚ)) (inv_mul_cancel u)
      simp only [Units.val_mul, Units.val_one, OneMemClass.coe_one] at this
      rw [MulMemClass.coe_mul, hu, coe_shToPlace] at this
      exact this
    rw [← h1]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  have hinv : (x : ↥(invField A))⁻¹ ∈ shRing A := by
    show algebraMap (↥(invField A)) (AlgebraicClosure ℚ) (x : ↥(invField A))⁻¹ ∈ A
    rw [map_inv₀]
    exact hinvA
  exact ⟨⟨x, ⟨(x : ↥(invField A))⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hxK0), Subtype.ext (inv_mul_cancel₀ hxK0)⟩, rfl⟩

theorem shPt_base_closedPoint (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (shPt A).base (closedPoint ↥A) = closedPoint ↥(shRing A) := by
  show PrimeSpectrum.comap (shToPlace A) (closedPoint ↥A) = closedPoint ↥(shRing A)
  exact IsLocalRing.comap_closedPoint (shToPlace A)

theorem barPt_base_specializes (A : ValuationSubring (AlgebraicClosure ℚ)) (c : ↥(Spec (CommRingCat.of ↥A))) :
    (barPt A).base (closedPoint (AlgebraicClosure ℚ)) ⤳ c := by
  refine (PrimeSpectrum.le_iff_specializes _ c).mp ?_
  show (PrimeSpectrum.comap A.subtype (closedPoint (AlgebraicClosure ℚ))).asIdeal ≤ c.asIdeal
  intro a ha
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at ha
  have : (a : AlgebraicClosure ℚ) ∈ (closedPoint (AlgebraicClosure ℚ)).asIdeal := ha
  have hbot : (closedPoint (AlgebraicClosure ℚ)).asIdeal = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField _)
  rw [hbot, Ideal.mem_bot] at this
  have ha0 : a = 0 := Subtype.ext this
  rw [ha0]; exact c.asIdeal.zero_mem

theorem closure_inter_nonempty_of_extN
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
    {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension) (x : JZero (N₀ * p)) (h : F.ExtN x) :
    (closure {(F.ptsN x).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))} ∩
        F.gN.base ⁻¹' {IsLocalRing.closedPoint ↥(shRing A)}).Nonempty := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s.1.base (closedPoint ↥A), ?_, ?_⟩
  ·
    have hξ : (F.ptsN x).1.base (closedPoint (AlgebraicClosure ℚ)) = s.1.base ((barPt A).base (closedPoint (AlgebraicClosure ℚ))) := by
      rw [hs]; rfl
    rw [hξ]
    exact ((barPt_base_specializes A (closedPoint ↥A)).map s.1.base.hom.continuous).mem_closure
  ·
    refine Set.mem_singleton_iff.mpr ?_
    change (s.1 ≫ F.gN).base (closedPoint ↥A) = closedPoint ↥(shRing A)
    rw [s.2]
    exact shPt_base_closedPoint A

end S17N4
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty.S17N4"

theorem solution
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
    {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension) (x : JZero (N₀ * p)) :
    F.ExtN x ↔
      (closure {(F.ptsN x).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))} ∩
        F.gN.base ⁻¹' {IsLocalRing.closedPoint ↥(shRing A)}).Nonempty := by
  constructor
  · exact S17N4.closure_inter_nonempty_of_extN F x
  · intro h
    obtain ⟨hDVR, -, -, -⟩ := ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA
    haveI : IsDiscreteValuationRing ↥(shRing A) := hDVR
    haveI : HenselianLocalRing ↥(shRing A) :=
      ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) A
    haveI : IsDedekindDomain ↥(shRing A) := inferInstance
    have hb := F.hN
    haveI := hb.separated
    haveI := hb.locallyOfFiniteType
    haveI := hb.quasiCompact
    haveI : Algebra.IsAlgebraic ↥(invField A) (AlgebraicClosure ℚ) := inferInstance
    have hcl : ∃ z ∈ closure (Set.range (F.ptsN x).1.base), F.gN.base z = IsLocalRing.closedPoint ↥(shRing A) := by
      obtain ⟨z, hz1, hz2⟩ := h
      refine ⟨z, ?_, hz2⟩
      rw [Set.range_unique]
      have : (default : ↥(Spec (CommRingCat.of (AlgebraicClosure ℚ)))) = IsLocalRing.closedPoint (AlgebraicClosure ℚ) :=
        Subsingleton.elim _ _
      rw [this]; exact hz1
    obtain ⟨s, hs1, hs2⟩ := S17N4Core.exists_section_comp_eq_of_mem_closure (shRing A) A (shToPlace A) (fun r => rfl)
      (fun y => Iff.rfl) F.gN (F.ptsN x).1 (F.ptsN x).2 hcl
    exact ⟨⟨s, hs1⟩, hs2.symm⟩

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty (solution)

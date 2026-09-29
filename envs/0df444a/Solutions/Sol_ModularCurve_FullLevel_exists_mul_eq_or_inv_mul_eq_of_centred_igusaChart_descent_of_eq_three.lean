-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mul_eq_or_inv_mul_eq_of_centred_igusaChart_descent_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/ff1597d3-0cfb-52e1-b8a9-0346da53d0fe

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_three
import Mathlib.RingTheory.Valuation.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mul_eq_or_inv_mul_eq_of_centred_igusaChart_descent_of_eq_three
p2m_attr_erase "instance" "DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.RegularProlongation.coe_integersEquiv ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E153J

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem isIntegral_adjoin_singleton_transport
    {R₁ R₂ E₁ E₂ : Type*} [CommRing R₁] [CommRing R₂] [Field E₁] [Field E₂] [Algebra R₁ E₁] [Algebra R₂ E₂]
    (Φ : E₁ ≃+* E₂) (x₁ : E₁) (x₂ : E₂) (hx : Φ x₁ = x₂)
    (hconst : ∀ r₁ : R₁, ∃ r₂ : R₂, Φ (algebraMap R₁ E₁ r₁) = algebraMap R₂ E₂ r₂)
    {y : E₁} (hy : IsIntegral ↥(Algebra.adjoin R₁ ({x₁} : Set E₁)) y) :
    IsIntegral ↥(Algebra.adjoin R₂ ({x₂} : Set E₂)) (Φ y) := by
  have hmap : ∀ z : E₁, z ∈ Algebra.adjoin R₁ ({x₁} : Set E₁) → Φ z ∈ Algebra.adjoin R₂ ({x₂} : Set E₂) := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [hx]
      exact Algebra.self_mem_adjoin_singleton R₂ x₂
    | algebraMap r =>
      obtain ⟨r₂, hr₂⟩ := hconst r
      rw [hr₂]
      exact Subalgebra.algebraMap_mem _ r₂
    | add a b _ _ ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact Subalgebra.mul_mem _ ha hb
  let φ : ↥(Algebra.adjoin R₁ ({x₁} : Set E₁)) →+* ↥(Algebra.adjoin R₂ ({x₂} : Set E₂)) :=
    { toFun := fun z => ⟨Φ z, hmap z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  exact hy.map_of_comp_eq φ Φ.toRingHom (by ext z; rfl)

theorem mem_chartAlg_singleton_transport
    {R₁ R₂ E₁ E₂ : Type} [CommRing R₁] [CommRing R₂] [Field E₁] [Field E₂] [Algebra R₁ E₁] [Algebra R₂ E₂]
    (Φ : E₁ ≃+* E₂) (x₁ : E₁) (x₂ : E₂) (hx : Φ x₁ = x₂)
    (hconst : ∀ r₁ : R₁, ∃ r₂ : R₂, Φ (algebraMap R₁ E₁ r₁) = algebraMap R₂ E₂ r₂)
    {y : E₁} (hy : y ∈ chartAlg R₁ E₁ {x₁}) : Φ y ∈ chartAlg R₂ E₂ {x₂} :=
  isIntegral_adjoin_singleton_transport Φ x₁ x₂ hx hconst hy

theorem mem_valuationSubring_of_mem_chartAlg {A₀ K : Type} [CommRing A₀] [Field K] [Algebra A₀ K]
    (V : ValuationSubring K) (S : Set K) (hA : ∀ a : A₀, algebraMap A₀ K a ∈ V) (hS : ∀ s ∈ S, s ∈ V)
    {y : K} (hy : y ∈ chartAlg A₀ K S) : y ∈ V := by
  have hle : ∀ z ∈ Algebra.adjoin A₀ S, z ∈ V := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz => exact hS z hz
    | algebraMap r => exact hA r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have hv := Valuation.integer.integers V.valuation
  have hle' : (Algebra.adjoin A₀ S).toSubring ≤ V.valuation.integer := fun z hz =>
    (Valuation.mem_integer_iff _ _).mpr ((V.valuation_le_one_iff z).mpr (hle z hz))
  have hint : IsIntegral ↥(V.valuation.integer) y :=
    ((mem_chartAlg_iff A₀ K).mp hy).map_of_comp_eq (Subring.inclusion hle') (RingHom.id K) (by ext; rfl)
  exact (V.valuation_le_one_iff y).mp ((hv.isIntegral_iff_v_le_one).mp hint)

theorem core {A₀ K : Type} [CommRing A₀] [Field K] [Algebra A₀ K]
    (B : Subalgebra A₀ K) (𝔪 : Ideal ↥B) [𝔪.IsMaximal]
    (hBn : ∀ y : K, IsIntegral ↥B y → y ∈ B)
    (V : ValuationSubring K) (hBV : ∀ b : ↥B, (b : K) ∈ V) (hcen : ∀ b : ↥B, b ∈ 𝔪 ↔ (b : K) ∈ V.nonunits)
    (σ : K ≃+* K) (hσA : ∀ a : A₀, σ (algebraMap A₀ K a) = algebraMap A₀ K a)
    (j j' x : K) (hj : j ≠ 0) (hx : σ j = x) (hxB : x ∈ B ∨ x⁻¹ ∈ B)
    (hjj' : j ∈ chartAlg A₀ K {j'}) (hσj' : σ j' = j')
    (hσfin : ∀ b : K, b ∈ chartAlg A₀ K {j} ↔ σ b ∈ chartAlg A₀ K {j})
    (hσinf : ∀ b : K, b ∈ chartAlg A₀ K {j'⁻¹} ↔ σ b ∈ chartAlg A₀ K {j'⁻¹})
    (h3 : ∀ y, y ∈ chartAlg A₀ K {j'⁻¹} → ∃ s, s ∈ chartAlg A₀ K {j⁻¹} ∧
      (∃ a, a ∈ chartAlg A₀ K {j⁻¹} ∧ s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlg A₀ K {j⁻¹})
    (h4 : ∀ y, y ∈ chartAlg A₀ K {j⁻¹} → ∃ s, s ∈ chartAlg A₀ K {j'⁻¹} ∧
      (∃ a, a ∈ chartAlg A₀ K {j'⁻¹} ∧ s = 1 + j'⁻¹ * a) ∧ s * y ∈ chartAlg A₀ K {j'⁻¹}) :
    (∃ b c : ↥B, c ∉ 𝔪 ∧ j * (c : K) = (b : K)) ∨ (∃ b c : ↥B, c ∉ 𝔪 ∧ j⁻¹ * (c : K) = (b : K)) := by
  classical
  have hm_ne_top : 𝔪 ≠ ⊤ := Ideal.IsMaximal.ne_top ‹_›
  have one_nmem : (1 : ↥B) ∉ 𝔪 := fun h => hm_ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hprime : 𝔪.IsPrime := Ideal.IsMaximal.isPrime ‹_›

  have tr : ∀ t y : K, y ∈ chartAlg A₀ K {t} → σ y ∈ chartAlg A₀ K {σ t} := fun t y hy =>
    mem_chartAlg_singleton_transport (R₁ := A₀) (R₂ := A₀) σ t (σ t) rfl (fun r => ⟨r, hσA r⟩) hy

  have G0 : ∀ t : K, t ∈ B → ∀ y : K, y ∈ chartAlg A₀ K {t} → y ∈ B := by
    intro t ht y hy
    apply hBn
    have hle : Algebra.adjoin A₀ {t} ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)
    exact ((mem_chartAlg_iff A₀ K).mp hy).map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id K)
      (by ext; rfl)

  have hjx : j ∈ chartAlg A₀ K {x} := by
    have h1 : σ.symm j ∈ chartAlg A₀ K {j} := by
      rw [hσfin, RingEquiv.apply_symm_apply]
      exact subset_chartAlg A₀ K _ rfl
    have h2 := tr j (σ.symm j) h1
    rwa [RingEquiv.apply_symm_apply, hx] at h2
  rcases hxB with hxB | hxB
  ·
    left
    exact ⟨⟨j, G0 x hxB j hjx⟩, 1, one_nmem, by simp⟩
  · have hx0 : x ≠ 0 := by rw [← hx]; exact (RingEquiv.map_ne_zero_iff σ).mpr hj

    obtain ⟨n, hn⟩ : ∃ n : ℕ, x⁻¹ ^ n * j ∈ chartAlg A₀ K {x⁻¹} := by
      apply exists_pow_mul_mem_chartAlg (Set.mem_singleton x⁻¹) (inv_ne_zero hx0)
      rw [inv_inv]
      exact chartAlg_mono A₀ K (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hjx
    have hnB : x⁻¹ ^ n * j ∈ B := G0 x⁻¹ hxB _ hn
    by_cases hcm : (⟨x⁻¹, hxB⟩ : ↥B) ∈ 𝔪
    ·
      right
      have hcV : V.valuation x⁻¹ < 1 := (V.mem_nonunits_iff).mp ((hcen _).mp hcm)

      have hσB : ∀ y, y ∈ chartAlg A₀ K {j⁻¹} → σ y ∈ B := by
        intro y hy
        have h := tr j⁻¹ y hy
        rw [map_inv₀, hx] at h
        exact G0 x⁻¹ hxB _ h

      have hloc : ∀ y, y ∈ chartAlg A₀ K {j'⁻¹} → ∃ t : ↥B, t ∉ 𝔪 ∧ y * (t : K) ∈ B := by
        intro y hy
        have hy' : σ.symm y ∈ chartAlg A₀ K {j'⁻¹} := by
          rw [hσinf, RingEquiv.apply_symm_apply]
          exact hy
        obtain ⟨s, hs, ⟨a, ha, hsa⟩, hsy⟩ := h3 _ hy'
        have hσs : σ s ∈ B := hσB s hs
        have hσa : σ a ∈ B := hσB a ha
        have hσsy : σ s * y ∈ B := by
          have h := hσB _ hsy
          rwa [map_mul, RingEquiv.apply_symm_apply] at h
        refine ⟨⟨σ s, hσs⟩, ?_, by rw [mul_comm]; exact hσsy⟩
        intro hmem
        apply one_nmem
        have hprod : (⟨x⁻¹, hxB⟩ * ⟨σ a, hσa⟩ : ↥B) ∈ 𝔪 := 𝔪.mul_mem_right _ hcm
        have h1 : (1 : ↥B) = ⟨σ s, hσs⟩ - ⟨x⁻¹, hxB⟩ * ⟨σ a, hσa⟩ := by
          apply Subtype.ext
          show (1 : K) = σ s - x⁻¹ * σ a
          rw [hsa, map_add, map_one, map_mul, map_inv₀, hx]
          ring
        rw [h1]
        exact 𝔪.sub_mem hmem hprod

      have hval1 : ∀ t : ↥B, t ∉ 𝔪 → V.valuation (t : K) = 1 := by
        intro t ht
        have h1 : V.valuation (t : K) ≤ 1 := (V.valuation_le_one_iff _).mpr (hBV t)
        have h2 : ¬ V.valuation (t : K) < 1 := fun h => ht ((hcen t).mpr (V.mem_nonunits_iff.mpr h))
        exact le_antisymm h1 (not_lt.mp h2)
      have hvalB : ∀ y : K, y ∈ B → V.valuation y ≤ 1 := fun y hy =>
        (V.valuation_le_one_iff _).mpr (hBV ⟨y, hy⟩)
      have hvloc : ∀ y, y ∈ chartAlg A₀ K {j'⁻¹} → V.valuation y ≤ 1 := by
        intro y hy
        obtain ⟨t, ht, hyt⟩ := hloc y hy
        have h := hvalB _ hyt
        rwa [map_mul, hval1 t ht, mul_one] at h

      have hj'V : V.valuation j'⁻¹ < 1 := by
        have hxj' : x ∈ chartAlg A₀ K {j'} := by
          have h := tr j' j hjj'
          rwa [hσj', hx] at h
        rcases V.valuation.val_le_one_or_val_inv_lt_one j' with hle | hlt
        · exfalso
          have hj'mem : j' ∈ V := (V.valuation_le_one_iff _).mp hle
          have hxV : x ∈ V :=
            mem_valuationSubring_of_mem_chartAlg V {j'} (fun a => hBV ⟨_, B.algebraMap_mem a⟩)
              (fun s hs => by rw [Set.mem_singleton_iff] at hs; subst hs; exact hj'mem) hxj'
          have h : V.valuation (x⁻¹ * x) < 1 := by
            rw [map_mul]
            exact mul_lt_one_of_lt_of_le hcV ((V.valuation_le_one_iff x).mpr hxV)
          rw [inv_mul_cancel₀ hx0, map_one] at h
          exact lt_irrefl _ h
        · exact hlt

      obtain ⟨s', hs', ⟨a', ha', hs'a'⟩, hs'j⟩ := h4 j⁻¹ (subset_chartAlg A₀ K _ rfl)
      obtain ⟨t₁, ht₁, h₁⟩ := hloc _ hs'j
      obtain ⟨t₂, ht₂, h₂⟩ := hloc _ hs'
      have hvs' : V.valuation s' = 1 := by
        rw [hs'a']
        apply Valuation.map_one_add_of_lt
        rw [map_mul]
        exact mul_lt_one_of_lt_of_le hj'V (hvloc a' ha')
      have ht₂s' : (⟨s' * (t₂ : K), h₂⟩ : ↥B) ∉ 𝔪 := by
        intro hmem
        have h := (V.mem_nonunits_iff).mp ((hcen _).mp hmem)
        change V.valuation (s' * (t₂ : K)) < 1 at h
        rw [map_mul, hvs', hval1 t₂ ht₂, mul_one] at h
        exact lt_irrefl _ h
      refine ⟨⟨s' * j⁻¹ * (t₁ : K), h₁⟩ * t₂, t₁ * ⟨s' * (t₂ : K), h₂⟩, ?_, ?_⟩
      · intro hmem
        rcases hprime.mem_or_mem hmem with h | h
        · exact ht₁ h
        · exact ht₂s' h
      · push_cast
        ring
    ·
      left
      refine ⟨⟨_, hnB⟩, ⟨x⁻¹, hxB⟩ ^ n, fun h => hcm (hprime.mem_of_pow_mem n h), ?_⟩
      push_cast
      ring

end E153J

namespace E153J

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem bridge_iff {A₀ A₁ K T : Type} [CommRing A₀] [CommRing A₁] [Field K] [Field T] [Algebra A₀ K] [Algebra A₁ T]
    (Φ : K ≃+* T)
    (hconst₁ : ∀ r₁ : A₀, ∃ r₂ : A₁, Φ (algebraMap A₀ K r₁) = algebraMap A₁ T r₂)
    (hconst₂ : ∀ r₂ : A₁, ∃ r₁ : A₀, Φ.symm (algebraMap A₁ T r₂) = algebraMap A₀ K r₁)
    (σ : T → T) (k : K) (t : T) (hk : Φ k = t)
    (hσ : ∀ b : T, b ∈ chartAlg A₁ T {t} ↔ σ b ∈ chartAlg A₁ T {t}) :
    ∀ b : K, b ∈ chartAlg A₀ K {k} ↔ Φ.symm (σ (Φ b)) ∈ chartAlg A₀ K {k} := by
  have hk' : Φ.symm t = k := by rw [← hk, RingEquiv.symm_apply_apply]
  intro b
  constructor
  · intro hb
    have h1 := mem_chartAlg_singleton_transport Φ k t hk hconst₁ hb
    have h2 := (hσ _).mp h1
    exact mem_chartAlg_singleton_transport Φ.symm t k hk' hconst₂ h2
  · intro hb
    have h1 := mem_chartAlg_singleton_transport Φ k t hk hconst₁ hb
    rw [RingEquiv.apply_symm_apply] at h1
    have h2 := (hσ _).mpr h1
    have h3 := mem_chartAlg_singleton_transport Φ.symm t k hk' hconst₂ h2
    rwa [RingEquiv.symm_apply_apply] at h3

theorem bridge_swap {A₀ A₁ K T : Type} [CommRing A₀] [CommRing A₁] [Field K] [Field T] [Algebra A₀ K] [Algebra A₁ T]
    (Φ : K ≃+* T)
    (hconst₁ : ∀ r₁ : A₀, ∃ r₂ : A₁, Φ (algebraMap A₀ K r₁) = algebraMap A₁ T r₂)
    (hconst₂ : ∀ r₂ : A₁, ∃ r₁ : A₀, Φ.symm (algebraMap A₁ T r₂) = algebraMap A₀ K r₁)
    (ku kw : K) (u w : T) (hu : Φ ku = u) (hw : Φ kw = w)
    (hT : ∀ y : T, y ∈ chartAlg A₁ T {u} → ∃ s, s ∈ chartAlg A₁ T {w} ∧
      (∃ a, a ∈ chartAlg A₁ T {w} ∧ s = 1 + w * a) ∧ s * y ∈ chartAlg A₁ T {w}) :
    ∀ y : K, y ∈ chartAlg A₀ K {ku} → ∃ s, s ∈ chartAlg A₀ K {kw} ∧
      (∃ a, a ∈ chartAlg A₀ K {kw} ∧ s = 1 + kw * a) ∧ s * y ∈ chartAlg A₀ K {kw} := by
  have hw' : Φ.symm w = kw := by rw [← hw, RingEquiv.symm_apply_apply]
  intro y hy
  have h1 := mem_chartAlg_singleton_transport Φ ku u hu hconst₁ hy
  obtain ⟨s, hs, ⟨a, ha, hsa⟩, hsy⟩ := hT _ h1
  refine ⟨Φ.symm s, mem_chartAlg_singleton_transport Φ.symm w kw hw' hconst₂ hs,
    ⟨Φ.symm a, mem_chartAlg_singleton_transport Φ.symm w kw hw' hconst₂ ha, ?_⟩, ?_⟩
  · rw [hsa, map_add, map_one, map_mul, hw']
  · have h := mem_chartAlg_singleton_transport Φ.symm w kw hw' hconst₂ hsy
    rwa [map_mul, RingEquiv.symm_apply_apply] at h

end E153J

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))

    (ℓ : CuspidalType.ProjLine q) (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg ℓ)
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg ℓ ∧ f ∉ V)
    (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) [𝔪.IsMaximal]

    (hBfg : B.FG)
    (hBn : ∀ x : ↥F₀, _root_.IsIntegral ↥B x → x ∈ B)
    (hBfrac : ∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)
    (hdimB : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes)
    (hgenB : ∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
      ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀))

    (hcompIg : ∀ ℓ' : CuspidalType.ProjLine q, (∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OIg ℓ') → ℓ' = ℓ)
    (hcompSS : ∀ s : ↥W, ¬ ∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s)
    (hcompLoc : ∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔
      ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀))
    (hcompMin : ∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
      ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀))

    (hBV : ∀ b : ↥B, (b : ↥F₀) ∈ V) (hcen : ∀ b : ↥B, b ∈ 𝔪 ↔ (b : ↥F₀) ∈ V.nonunits)

    (hJg : ∃ x : ↥F₀, (∃ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        (x : ↥(fieldBar q M')) = g ((⟨_, hjF₀⟩ : ↥F₀) : ↥(fieldBar q M'))) ∧ (x ∈ B ∨ x⁻¹ ∈ B)) :

    (∃ b c : ↥B, c ∉ 𝔪 ∧ (⟨_, hjF₀⟩ : ↥F₀) * (c : ↥F₀) = (b : ↥F₀)) ∨
    (∃ b c : ↥B, c ∉ 𝔪 ∧ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ * (c : ↥F₀) = (b : ↥F₀)) := by
  classical

  obtain ⟨k₀, π₀, hπ₀, hk₀, hπ₀π, -, -, -, -, -, -, -, -, hA₁mem, hfd, -, -, ⟨e₀, he₀⟩, F₀', hchar, hK1, hstab, hLD, hrat, hF₀', Φ, hΦ⟩ :=
    ModularCurve.FullLevel.exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase_of_eq_three
      q hq3 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr
      K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

  letI algA₁ : Algebra ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') :=
    ((Φ.toRingHom).comp ((algebraMap A₀ ↥F₀).comp e₀.symm.toRingHom)).toAlgebra
  have hcompat : ∀ a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))), ((algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) : (AlgebraicClosure ℚ)) := by
    intro a
    show ((Φ (algebraMap A₀ ↥F₀ (e₀.symm a)) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) = _
    rw [hΦ, hj₀, ← he₀ (e₀.symm a), RingEquiv.apply_symm_apply]
  have hj₁ : ((Φ (⟨_, hjF₀⟩ : ↥F₀) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) := hΦ _
  have hconst₁ : ∀ r₁ : A₀, ∃ r₂ : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))), Φ (algebraMap A₀ ↥F₀ r₁) = algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') r₂ := by
    intro r₁
    refine ⟨e₀ r₁, ?_⟩
    show Φ (algebraMap A₀ ↥F₀ r₁) = Φ (algebraMap A₀ ↥F₀ (e₀.symm (e₀ r₁)))
    rw [RingEquiv.symm_apply_apply]
  have hconst₂ : ∀ r₂ : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))), ∃ r₁ : A₀, Φ.symm (algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') r₂) = algebraMap A₀ ↥F₀ r₁ := by
    intro r₂
    refine ⟨e₀.symm r₂, ?_⟩
    show Φ.symm (Φ (algebraMap A₀ ↥F₀ (e₀.symm r₂))) = _
    rw [RingEquiv.symm_apply_apply]
  have hΦsymm : ∀ y : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'), ((Φ.symm y : ↥F₀) : ↥(fieldBar q M')) = (y : ↥(fieldBar q M')) := by
    intro y
    have h := hΦ (Φ.symm y)
    rw [RingEquiv.apply_symm_apply] at h
    exact h.symm

  have hj0 : (⟨_, hjF₀⟩ : ↥F₀) ≠ 0 := by
    intro h
    have h1 : (((⟨_, hjF₀⟩ : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := rfl
    rw [h] at h1
    exact (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr jq_ne_zero h1.symm
  haveI hfact : Fact (Φ (⟨_, hjF₀⟩ : ↥F₀) ≠ 0) := ⟨(RingEquiv.map_ne_zero_iff Φ).mpr hj0⟩

  obtain ⟨j', hj'q, -, hfin', hclosure⟩ :=
    ModularCurve.FullLevel.exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three
      q hq3 M' hqM' hle k₀ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd _ F₀' hK1 hstab hLD hrat hcompat (Φ (⟨_, hjF₀⟩ : ↥F₀)) hj₁
  obtain ⟨j'', hj''q, h3T, h4T⟩ :=
    ModularCurve.FullLevel.exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_three
      q hq3 M' hqM' hle k₀ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd _ F₀' hK1 hstab hLD hrat hcompat (Φ (⟨_, hjF₀⟩ : ↥F₀)) hj₁
  have hjj : j' = j'' := Subtype.ext (Subtype.ext (hj'q.trans hj''q.symm))
  subst hjj

  obtain ⟨x, ⟨g, hg, hxg⟩, hxB⟩ := hJg
  obtain ⟨σ, hσ, hσsymm, hσj', hσfinT, hσinfT, -⟩ := hclosure g hg
  let σF : ↥F₀ ≃+* ↥F₀ := (Φ.trans σ.toRingEquiv).trans Φ.symm
  have hσF : ∀ f : ↥F₀, ((σF f : ↥F₀) : ↥(fieldBar q M')) = g (f : ↥(fieldBar q M')) := by
    intro f
    show ((Φ.symm (σ.toRingEquiv (Φ f)) : ↥F₀) : ↥(fieldBar q M')) = _
    rw [hΦsymm]
    show ((σ (Φ f) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) = _
    rw [hσ, hΦ]
  have hσFalg : ∀ a : A₀, σF (algebraMap A₀ ↥F₀ a) = algebraMap A₀ ↥F₀ a := by
    intro a
    apply Subtype.ext
    rw [hσF, hj₀]
    exact g.commutes _
  have hxK : σF (⟨_, hjF₀⟩ : ↥F₀) = x := by
    apply Subtype.ext
    rw [hσF]
    exact hxg.symm

  have hjj'K : (⟨_, hjF₀⟩ : ↥F₀) ∈ TwoChartIntegralModel.chartAlg A₀ ↥F₀ {Φ.symm j'} := by
    have h := E153J.mem_chartAlg_singleton_transport Φ.symm j' (Φ.symm j') rfl hconst₂ hfin'
    rwa [RingEquiv.symm_apply_apply] at h
  have hσj'K : σF (Φ.symm j') = Φ.symm j' := by
    show Φ.symm (σ.toRingEquiv (Φ (Φ.symm j'))) = Φ.symm j'
    rw [RingEquiv.apply_symm_apply]
    show Φ.symm (σ j') = _
    rw [hσj']
  have hσfinK := E153J.bridge_iff Φ hconst₁ hconst₂ σ (⟨_, hjF₀⟩ : ↥F₀) (Φ (⟨_, hjF₀⟩ : ↥F₀)) rfl hσfinT
  have hσinfK := E153J.bridge_iff Φ hconst₁ hconst₂ σ (Φ.symm j')⁻¹ j'⁻¹
    (by rw [map_inv₀, RingEquiv.apply_symm_apply]) hσinfT
  have h3K := E153J.bridge_swap Φ hconst₁ hconst₂ (Φ.symm j')⁻¹ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ j'⁻¹ (Φ (⟨_, hjF₀⟩ : ↥F₀))⁻¹
    (by rw [map_inv₀, RingEquiv.apply_symm_apply]) (map_inv₀ Φ _) h3T
  have h4K := E153J.bridge_swap Φ hconst₁ hconst₂ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ (Φ.symm j')⁻¹ (Φ (⟨_, hjF₀⟩ : ↥F₀))⁻¹ j'⁻¹
    (map_inv₀ Φ _) (by rw [map_inv₀, RingEquiv.apply_symm_apply]) h4T

  exact E153J.core B 𝔪 hBn V hBV hcen σF hσFalg (⟨_, hjF₀⟩ : ↥F₀) (Φ.symm j') x hj0 hxK hxB hjj'K hσj'K hσfinK hσinfK h3K h4K

end S_ModularCurve_FullLevel_exists_mul_eq_or_inv_mul_eq_of_centred_igusaChart_descent_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mul_eq_or_inv_mul_eq_of_centred_igusaChart_descent_of_eq_three (solution)

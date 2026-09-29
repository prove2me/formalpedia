-- Prove2me | solution 1 for NumberField.ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/124bf1f4-04b7-5615-b8a3-ac3e0ea70004

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent Topology Filter Set
open scoped ENNReal Pointwise

namespace H90FD

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "G" => (AdeleRing (𝓞 L) L)ˣ

theorem secondCountableTopology_ideles : SecondCountableTopology G := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompactSpace_ideles : LocallyCompactSpace G :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sigmaCompactSpace_ideles : SigmaCompactSpace G := by
  haveI := secondCountableTopology_ideles (L := L)
  haveI := locallyCompactSpace_ideles (L := L)
  infer_instance

variable (D : IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

def HMap : G →* G where
  toFun z := D.unitsAct σ z * z⁻¹
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem HMap_apply (z : G) : HMap D σ z = D.unitsAct σ z * z⁻¹ := rfl

theorem val_unitsAct (g : L ≃ₐ[K] L) (z : G) :
    ((D.unitsAct g z : G) : AdeleRing (𝓞 L) L) = D.act g (z : AdeleRing (𝓞 L) L) := rfl

theorem continuous_unitsAct (g : L ≃ₐ[K] L) : Continuous fun z : G => D.unitsAct g z := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (D.continuous_act g).comp Units.continuous_val
  · have : (fun z : G => (((D.unitsAct g z)⁻¹ : G) : AdeleRing (𝓞 L) L)) =
        fun z : G => D.act g (((z⁻¹ : G)) : AdeleRing (𝓞 L) L) := by
      funext z; rw [← map_inv]; rfl
    rw [this]
    exact (D.continuous_act g).comp Units.continuous_coe_inv

theorem continuous_HMap : Continuous (HMap D σ) := by
  show Continuous fun z : G => D.unitsAct σ z * z⁻¹
  exact (continuous_unitsAct D σ).mul continuous_inv

theorem unitsAct_unitsMap_algebraMap (w : Lˣ) :
    D.unitsAct σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) w) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
        (Units.map ((σ : L →+* L) : L →* L) w) := by
  apply Units.ext
  rw [val_unitsAct]
  exact D.compat σ (w : L)

theorem unitsAct_eq_of_mem_range (a : G)
    (ha : a ∈ (Units.map (genuineBaseChange K L).β.toMonoidHom).range) (τ : L ≃ₐ[K] L) :
    D.unitsAct τ a = a :=
  ((injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D).2.1 a).mpr ha τ

theorem idelicNorm_unitsAct (z : G) (τ : L ≃ₐ[K] L) :
    (genuineBaseChange K L).idelicNorm (D.unitsAct τ z) = (genuineBaseChange K L).idelicNorm z := by
  obtain ⟨hinj, -, -, hnorm⟩ := injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D
  have h1 := hnorm (D.unitsAct τ z)
  have h2 := hnorm z
  have hprod : ∏ ρ : L ≃ₐ[K] L, D.unitsAct ρ (D.unitsAct τ z) = ∏ ρ : L ≃ₐ[K] L, D.unitsAct ρ z := by
    have : ∀ ρ : L ≃ₐ[K] L, D.unitsAct ρ (D.unitsAct τ z) = D.unitsAct (ρ * τ) z := by
      intro ρ; rw [map_mul]; rfl
    simp_rw [this]
    exact Fintype.prod_equiv (Equiv.mulRight τ) _ _ (fun ρ => rfl)
  rw [hprod, h2] at h1

  have : Function.Injective (Units.map (genuineBaseChange K L).β.toMonoidHom) := by
    intro u v huv
    apply Units.ext
    exact hinj (congrArg Units.val huv)
  exact (this h1).symm

theorem idelicNorm_HMap (z : G) : (genuineBaseChange K L).idelicNorm (HMap D σ z) = 1 := by
  rw [HMap_apply, map_mul, map_inv, idelicNorm_unitsAct, mul_inv_cancel]

theorem HMap_mul_of_mem_range (a z : G)
    (ha : a ∈ (Units.map (genuineBaseChange K L).β.toMonoidHom).range) :
    HMap D σ (a * z) = HMap D σ z := by
  rw [map_mul, HMap_apply D σ a, unitsAct_eq_of_mem_range D a ha σ, mul_inv_cancel, one_mul]

theorem mem_range_of_HMap_eq_one (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ)
    (hu : HMap D σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) = 1) :
    u ∈ Set.range (Units.map (algebraMap K L : K →* L)) := by
  rw [HMap_apply, mul_inv_eq_one, unitsAct_unitsMap_algebraMap] at hu
  have hσu : σ (u : L) = u := by
    have hval := congrArg (fun x : G => (x : AdeleRing (𝓞 L) L)) hu
    simp only [Units.coe_map, MonoidHom.coe_coe] at hval
    haveI : Nontrivial (AdeleRing (𝓞 L) L) := by
      show Nontrivial (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L)
      haveI : Nontrivial (InfiniteAdeleRing L) := by
        show Nontrivial ((w : InfinitePlace L) → w.Completion)
        letI : Inhabited (InfinitePlace L) := Classical.inhabited_of_nonempty inferInstance
        exact Pi.nontrivial
      infer_instance
    exact (algebraMap L (AdeleRing (𝓞 L) L)).injective hval

  have hfix : ∀ τ : L ≃ₐ[K] L, τ (u : L) = u := by
    intro τ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, hσu]; exact ih
    | pred n ih =>
      rw [zpow_sub_one, AlgEquiv.mul_apply]
      have : σ⁻¹ (u : L) = u := by
        rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
        exact hσu.symm
      rw [this]; exact ih
  have hmem : (u : L) ∈ (⊥ : IntermediateField K L) := by
    rw [← IsGalois.fixedField_top (F := K) (E := L), IntermediateField.mem_fixedField_iff]
    exact fun τ _ => hfix τ
  rw [IntermediateField.mem_bot] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact u.ne_zero hk.symm
  refine ⟨Units.mk0 k hk0, Units.ext ?_⟩
  simp [hk]

theorem exists_out_eq (AK : Subgroup G) (z : G) :
    ∃ a : AK, (Quotient.mk'' z : MulAction.orbitRel.Quotient AK G).out = (a : G) * z := by
  have h : (MulAction.orbitRel AK G) ((Quotient.mk'' z : MulAction.orbitRel.Quotient AK G).out) z :=
    Quotient.eq''.mp (Quotient.out_eq (Quotient.mk'' z : MulAction.orbitRel.Quotient AK G))
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by rw [← ha]; rfl⟩

theorem HMap_out_mk (AK : Subgroup G)
    (hAK : ∀ z : G, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (genuineBaseChange K L).β.toMonoidHom a)
    (z : G) : HMap D σ ((Quotient.mk'' z : MulAction.orbitRel.Quotient AK G).out) = HMap D σ z := by
  obtain ⟨a, ha⟩ := exists_out_eq AK z
  rw [ha]
  apply HMap_mul_of_mem_range
  obtain ⟨b, hb⟩ := (hAK a).mp a.2
  exact ⟨b, hb.symm⟩

theorem measurable_HMap_out [MeasurableSpace G] [BorelSpace G] (AK : Subgroup G)
    (hAK : ∀ z : G, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (genuineBaseChange K L).β.toMonoidHom a) :
    Measurable fun q : MulAction.orbitRel.Quotient AK G => HMap D σ q.out := by
  rw [measurable_from_quotient]
  have : (fun q : MulAction.orbitRel.Quotient AK G => HMap D σ q.out) ∘ Quotient.mk'' = HMap D σ := by
    funext z; exact HMap_out_mk D σ AK hAK z
  rw [this]
  exact (continuous_HMap D σ).measurable

section Transport

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]

theorem measure_setOf_HMap_out_mem_eq_zero
    (νZL : Measure G) (AK : Subgroup G)
    (hAK : ∀ z : G, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK)
    (N1 : Subgroup G) (hN1c : IsClosed (N1 : Set G))
    (hN1 : ∀ z : G, z ∈ N1 ↔ (genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure] (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : G → ℂ,
      ∫ n : N1, g (n : G) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK G,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))
    (T : Set G) (hT : MeasurableSet T) (hT0 : μN (Subtype.val ⁻¹' T) = 0) :
    HaarQuotient.measure νZL AK μAK
      {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ T} = 0 := by
  classical
  set P := HaarQuotient.measure νZL AK μAK with hP
  set h : MulAction.orbitRel.Quotient AK G → G := fun q => D.unitsAct σ q.out * (q.out)⁻¹ with hh_def
  have hh : Measurable h := measurable_HMap_out D σ AK hAK
  have hmem : ∀ q, h q ∈ N1 := fun q => (hN1 _).mpr (idelicNorm_HMap D σ q.out)

  haveI : SigmaCompactSpace N1 := by
    haveI := sigmaCompactSpace_ideles (L := L)
    exact hN1c.sigmaCompactSpace
  haveI : SigmaFinite μN := inferInstance

  obtain ⟨g, hgpos, hgm, hglt⟩ := exists_pos_lintegral_lt_of_sigmaFinite μN (one_ne_zero)
  set f : N1 → ℝ := fun n => (g n : ℝ) with hf
  have hfpos : ∀ n, 0 < f n := fun n => NNReal.coe_pos.mpr (hgpos n)
  have hfint : Integrable f μN := by
    have := integrable_toReal_of_lintegral_ne_top (μ := μN) (f := fun n => (g n : ℝ≥0∞))
      hgm.coe_nnreal_ennreal.aemeasurable (ne_top_of_lt hglt)
    simpa using this
  have hfm : Measurable f := hgm.coe_nnreal_real

  set ext : (N1 → ℝ) → (G → ℂ) := fun φ z => if hz : z ∈ N1 then ((φ ⟨z, hz⟩ : ℝ) : ℂ) else 0 with hext
  have ext_val : ∀ (φ : N1 → ℝ) (n : N1), ext φ (n : G) = ((φ n : ℝ) : ℂ) := by
    intro φ n; simp only [hext, dif_pos n.2]
  have ext_h : ∀ (φ : N1 → ℝ) (q : MulAction.orbitRel.Quotient AK G),
      ext φ (h q) = ((φ ⟨h q, hmem q⟩ : ℝ) : ℂ) := by
    intro φ q; simp only [hext, dif_pos (hmem q)]

  set φP : MulAction.orbitRel.Quotient AK G → ℝ := fun q => f ⟨h q, hmem q⟩ with hφP
  have hφPpos : ∀ q, 0 < φP q := fun q => hfpos _
  have hφPm : Measurable φP := hfm.comp (hh.subtype_mk)
  have hIpos : 0 < ∫ n, f n ∂μN := by
    rw [integral_pos_iff_support_of_nonneg (fun n => (hfpos n).le) hfint]
    have hsupp : Function.support f = Set.univ := by
      ext n; simp [(hfpos n).ne']
    rw [hsupp]
    exact isOpen_univ.measure_pos μN ⟨⟨1, N1.one_mem⟩, trivial⟩
  have h1 := hNc (ext f)
  simp only [ext_val] at h1
  rw [integral_complex_ofReal] at h1
  have h1' : ∫ q, ext f (h q) ∂P = ∫ q, ((φP q : ℝ) : ℂ) ∂P := by
    simp only [ext_h, hφP]
  rw [hh_def] at h1'
  have hPint : Integrable φP P := by
    by_contra hni
    have h0 : ∫ q, ((φP q : ℝ) : ℂ) ∂P = 0 := by
      rw [integral_complex_ofReal, integral_undef hni, Complex.ofReal_zero]
    have : ((∫ n, f n ∂μN : ℝ) : ℂ) = 0 := by
      rw [h1, show (∫ q, ext f (D.unitsAct σ q.out * (q.out)⁻¹) ∂P) = ∫ q, ((φP q : ℝ) : ℂ) ∂P from h1',
        h0, mul_zero]
    exact hIpos.ne' (Complex.ofReal_eq_zero.mp this)

  set S : Set (MulAction.orbitRel.Quotient AK G) := {q | h q ∈ T} with hS
  have hSm : MeasurableSet S := hh hT
  set ψ : N1 → ℝ := (Subtype.val ⁻¹' T).indicator f with hψ
  have hψ0 : ∫ n, ψ n ∂μN = 0 := by
    apply integral_eq_zero_of_ae
    have : ∀ᵐ n ∂μN, n ∉ Subtype.val ⁻¹' T := compl_mem_ae_iff.mpr hT0
    filter_upwards [this] with n hn
    simp only [hψ, Set.indicator_of_notMem hn, Pi.zero_apply]
  have h2 := hNc (ext ψ)
  simp only [ext_val] at h2
  rw [integral_complex_ofReal, hψ0, Complex.ofReal_zero] at h2
  have h2' : ∀ q, ext ψ (h q) = ((S.indicator φP q : ℝ) : ℂ) := by
    intro q
    rw [ext_h]
    simp only [hψ, hS, hφP, Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq]
  have h3 : ∫ q, ((S.indicator φP q : ℝ) : ℂ) ∂P = 0 := by
    have : (fun q => ext ψ (D.unitsAct σ q.out * (q.out)⁻¹)) = fun q => ((S.indicator φP q : ℝ) : ℂ) :=
      funext h2'
    rw [← this]
    have := h2.symm
    rcases mul_eq_zero.mp this with hc | hint
    · exact absurd (Complex.ofReal_eq_zero.mp hc) hcN.ne'
    · exact hint
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero, integral_indicator hSm] at h3
  by_contra hS0
  have hpos : 0 < ∫ q in S, φP q ∂P := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun q => (hφPpos q).le)
      hPint.integrableOn]
    have hsupp : Function.support φP = Set.univ := by ext q; simp [(hφPpos q).ne']
    rw [hsupp, Set.univ_inter]
    exact pos_iff_ne_zero.mpr hS0
  exact hpos.ne' h3

end Transport

section Assembly

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]

theorem nullT (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ)
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔ (genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure] (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))
    (S : Set N1) (hS0 : μN S = 0) :
    HaarQuotient.measure νZL AK μAK
      {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' S : Set G)} = 0 := by
  have hval : MeasurableEmbedding (Subtype.val : N1 → G) := MeasurableEmbedding.subtype_coe hN1c.measurableSet
  obtain ⟨S', hSS', hS'm, hS'0⟩ := exists_measurable_superset_of_null hS0
  have hT : MeasurableSet (Subtype.val '' S' : Set G) := hval.measurableSet_image.mpr hS'm
  have hT0 : μN (Subtype.val ⁻¹' (Subtype.val '' S' : Set G)) = 0 := by
    rw [Set.preimage_image_eq _ Subtype.val_injective]; exact hS'0
  have := measure_setOf_HMap_out_mem_eq_zero D σ νZL AK hAK μAK N1 hN1c hN1 μN cN hcN hNc _ hT hT0
  refine measure_mono_null ?_ this
  intro q hq
  obtain ⟨n, hn, hnq⟩ := hq
  exact ⟨n, hSS' hn, hnq⟩

theorem range_gen_apply (w : Lˣ) :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
      (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)) w =
    HMap D σ ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w) := by
  rw [MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, map_div, HMap_apply,
    unitsAct_unitsMap_algebraMap, div_eq_mul_inv]

theorem conj1 (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ)
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔ (genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure] (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))
    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) :
    NullMeasurableSet {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}
      (HaarQuotient.measure νZL AK μAK) := by
  have hh : Measurable fun q : MulAction.orbitRel.Quotient AK G => D.unitsAct σ q.out * (q.out)⁻¹ :=
    measurable_HMap_out D σ AK hAK
  have hval : MeasurableEmbedding (Subtype.val : N1 → G) := MeasurableEmbedding.subtype_coe hN1c.measurableSet
  obtain ⟨Θ₀, hsub, hΘ₀m, hae⟩ := hΘ₁.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hF₀m : MeasurableSet {q : MulAction.orbitRel.Quotient AK G |
      D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₀ : Set G)} :=
    hh (hval.measurableSet_image.mpr hΘ₀m)
  have hdiff : μN (Θ₁ \ Θ₀) = 0 := (ae_eq_set.mp hae).2
  have hnull := nullT D σ νZL AK hAK μAK N1 hN1c hN1 μN cN hcN hNc (Θ₁ \ Θ₀) hdiff
  have hF₀F : {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₀ : Set G)} ⊆
      {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set G)} := by
    intro q hq; obtain ⟨n, hn, hnq⟩ := hq; exact ⟨n, hsub hn, hnq⟩
  have hcover : {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set G)} \
      {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₀ : Set G)} ⊆
      {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' (Θ₁ \ Θ₀) : Set G)} := by
    intro q hq
    obtain ⟨⟨n, hn, hnq⟩, hq0⟩ := hq
    exact ⟨n, ⟨hn, fun hn0 => hq0 ⟨n, hn0, hnq⟩⟩, hnq⟩
  rw [← Set.union_diff_cancel hF₀F]
  exact hF₀m.nullMeasurableSet.union (NullMeasurableSet.of_null (measure_mono_null hcover hnull))

theorem conj2 (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ)
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔ (genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure] (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))
    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) :
    ∀ᵐ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ ∂(HaarQuotient.measure νZL AK μAK), ∃ w : Lˣ,
      (Quotient.mk'' ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
        {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)} := by
  have hmem : ∀ q : MulAction.orbitRel.Quotient AK G, D.unitsAct σ q.out * (q.out)⁻¹ ∈ N1 :=
    fun q => (hN1 _).mpr (idelicNorm_HMap D σ q.out)
  have hB0 : μN {n : N1 | ¬ ∃ g : ↥((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
      (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1), g • n ∈ Θ₁} = 0 := by
    have := hΘ₁.ae_covers
    rw [ae_iff] at this
    exact this
  have hnull := nullT D σ νZL AK hAK μAK N1 hN1c hN1 μN cN hcN hNc _ hB0
  have hae : ∀ᵐ q : MulAction.orbitRel.Quotient AK G ∂(HaarQuotient.measure νZL AK μAK),
      q ∉ {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' {n : N1 |
        ¬ ∃ g : ↥((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
          (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1), g • n ∈ Θ₁} : Set G)} :=
    compl_mem_ae_iff.mpr hnull
  filter_upwards [hae] with q hq
  have hq' : ∃ g : ↥((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
      (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1),
      g • (⟨D.unitsAct σ q.out * (q.out)⁻¹, hmem q⟩ : N1) ∈ Θ₁ := by
    by_contra hcon
    exact hq ⟨⟨_, hmem q⟩, hcon, rfl⟩
  obtain ⟨g, hg⟩ := hq'
  obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp g.2
  refine ⟨w, ?_⟩
  show D.unitsAct σ (Quotient.mk'' ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w * q.out) : MulAction.orbitRel.Quotient AK G).out *
      ((Quotient.mk'' ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w * q.out) : MulAction.orbitRel.Quotient AK G).out)⁻¹ ∈
    (Subtype.val '' Θ₁ : Set G)
  rw [← HMap_apply, HMap_out_mk D σ AK hAK, map_mul, ← range_gen_apply D σ w, hw]
  exact ⟨_, hg, rfl⟩

theorem conj3 (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ)
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔ (genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure] (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))
    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) (w w' : Lˣ) (hww' : w⁻¹ * w' ∉ Set.range (Units.map (algebraMap K L : K →* L))) :
    HaarQuotient.measure νZL AK μAK
        ({q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w)⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}} ∩
         {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w')⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}}) = 0 := by
  have hmem : ∀ q : MulAction.orbitRel.Quotient AK G, D.unitsAct σ q.out * (q.out)⁻¹ ∈ N1 :=
    fun q => (hN1 _).mpr (idelicNorm_HMap D σ q.out)
  have hιN1 : ∀ v : Lˣ, HMap D σ ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) v) ∈ N1 :=
    fun v => (hN1 _).mpr (idelicNorm_HMap D σ _)
  let gOf : Lˣ → ↥((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
      (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) := fun v =>
    ⟨⟨HMap D σ ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) v), hιN1 v⟩,
      Subgroup.mem_subgroupOf.mpr ⟨v, range_gen_apply D σ v⟩⟩
  have gOf_val : ∀ v, (((gOf v) : N1) : G) =
      HMap D σ ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) v) := fun v => rfl
  have hne : gOf w ≠ gOf w' := by
    intro heq
    apply hww'
    apply mem_range_of_HMap_eq_one D σ hgen
    have hv : HMap D σ ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w) =
        HMap D σ ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w') := by
      rw [← gOf_val, ← gOf_val, heq]
    rw [map_mul, map_inv, map_mul, map_inv, hv, inv_mul_cancel]
  have hdis : μN (gOf w • Θ₁ ∩ gOf w' • Θ₁) = 0 := hΘ₁.aedisjoint hne
  have hnull := nullT D σ νZL AK hAK μAK N1 hN1c hN1 μN cN hcN hNc _ hdis
  refine measure_mono_null ?_ hnull
  intro q hq
  obtain ⟨hq1, hq2⟩ := hq
  have key : ∀ v : Lˣ,
      (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) v)⁻¹ * q.out) :
          MulAction.orbitRel.Quotient AK G) ∈
        {q : MulAction.orbitRel.Quotient AK G | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set G)} →
      (⟨D.unitsAct σ q.out * (q.out)⁻¹, hmem q⟩ : N1) ∈ gOf v • Θ₁ := by
    intro v hv
    have hv' : HMap D σ ((Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) v)⁻¹ * q.out) :
        MulAction.orbitRel.Quotient AK G).out) ∈ (Subtype.val '' Θ₁ : Set G) := hv
    rw [HMap_out_mk D σ AK hAK, map_mul, map_inv] at hv'
    obtain ⟨θ, hθ, hθv⟩ := hv'
    refine Set.mem_smul_set.mpr ⟨θ, hθ, Subtype.ext ?_⟩
    show (((gOf v) : N1) : G) * (θ : G) = D.unitsAct σ q.out * (q.out)⁻¹
    rw [gOf_val, hθv, ← HMap_apply, mul_inv_cancel_left]
  exact ⟨⟨_, hmem q⟩, ⟨key w hq1, key w' hq2⟩, rfl⟩

end Assembly

end H90FD

open H90FD

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))
    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) :
    NullMeasurableSet {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}
      (HaarQuotient.measure νZL AK μAK) ∧
    (∀ᵐ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ ∂(HaarQuotient.measure νZL AK μAK), ∃ w : Lˣ,
      (Quotient.mk'' ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
        {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}) ∧
    (∀ w w' : Lˣ, w⁻¹ * w' ∉ Set.range (Units.map (algebraMap K L : K →* L)) →
      HaarQuotient.measure νZL AK μAK
        ({q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w)⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}} ∩
         {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w')⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}}) = 0) :=
  ⟨conj1 D σ νZL AK hAK μAK N1 hN1c hN1 μN cN hcN hNc Θ₁ hΘ₁,
   conj2 D σ νZL AK hAK μAK N1 hN1c hN1 μN cN hcN hNc Θ₁ hΘ₁,
   fun w w' hww' => conj3 D σ hgen νZL AK hAK μAK N1 hN1c hN1 μN cN hcN hNc Θ₁ hΘ₁ w w' hww'⟩

end
end S_NumberField_ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf
end P2MW
export P2MW.S_NumberField_ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf (solution)

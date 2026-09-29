-- Prove2me | solution 1 for NumberField.AdeleRing.isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dd8f2cf1-8636-5c40-86f8-41a22a242d63

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside

set_option autoImplicit false

open NumberField IsDedekindDomain Topology Filter Set
open scoped RestrictedProduct

namespace BoxIdeleK9

theorem restrictedProduct_isCompact_box {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (R i)] {B : ∀ i, S i}
    (T : Set ι) (hT : T.Finite) (F : ∀ i, Set (R i)) (hF : ∀ i, IsCompact (F i))
    (hFB : ∀ i, i ∉ T → F i ⊆ (B i : Set (R i))) :
    IsCompact {x : Πʳ i, [R i, B i] | ∀ i, x i ∈ F i} := by
  let Sc : Set ι := Tᶜ
  have hS : (cofinite : Filter ι) ≤ 𝓟 Sc := Filter.le_principal_iff.mpr hT.compl_mem_cofinite
  let box' : Set (Πʳ i, [R i, B i]_[𝓟 Sc]) := {y | ∀ i, y i ∈ F i}
  have hbox' : IsCompact box' := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have : ((⇑) : Πʳ i, [R i, B i]_[𝓟 Sc] → ∀ i, R i) '' box' = Set.pi univ F := by
      ext z
      simp only [mem_image, mem_univ_pi]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hz
        refine ⟨⟨z, ?_⟩, hz, rfl⟩
        rw [Filter.eventually_principal]
        intro i hi
        exact hFB i hi (hz i)
    rw [this]
    exact isCompact_univ_pi hF
  have heq : {x : Πʳ i, [R i, B i] | ∀ i, x i ∈ F i} =
      RestrictedProduct.inclusion R (fun i => (B i : Set (R i))) hS '' box' := by
    ext x
    simp only [mem_setOf_eq, mem_image]
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, ?_⟩
      · rw [Filter.eventually_principal]
        intro i hi
        exact hFB i hi (hx i)
      · ext i; rfl
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [heq]
  exact hbox'.image (RestrictedProduct.continuous_inclusion hS)

variable (K : Type) [Field K] [NumberField K]

theorem isCompact_finBox (S : Finset (HeightOneSpectrum (𝓞 K)))
    (G : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)) (hG : ∀ v ∈ S, IsCompact (G v)) :
    IsCompact {a : FiniteAdeleRing (𝓞 K) K |
      (∀ v ∈ S, a v ∈ G v) ∧ (∀ v ∉ S, a v ∈ v.adicCompletionIntegers K)} := by
  classical
  let F : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K) := fun v =>
    if v ∈ S then G v else (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hF : ∀ v, IsCompact (F v) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [F, hv, if_true]; exact hG v hv
    · simp only [F, hv, if_false]
      exact isCompact_iff_compactSpace.mpr (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hFB : ∀ v, v ∉ (↑S : Set (HeightOneSpectrum (𝓞 K))) → F v ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v hv
    rw [Finset.mem_coe] at hv
    simp only [F, hv, if_false]
    exact Subset.rfl
  have hbox := restrictedProduct_isCompact_box (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K) _ S.finite_toSet F hF hFB
  have e : {a : FiniteAdeleRing (𝓞 K) K | (∀ v ∈ S, a v ∈ G v) ∧ (∀ v ∉ S, a v ∈ v.adicCompletionIntegers K)} =
      {a : FiniteAdeleRing (𝓞 K) K | ∀ v, a v ∈ F v} := by
    ext a
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S
      · simp only [F, hv, if_true]; exact h1 v hv
      · simp only [F, hv, if_false]; exact h2 v hv
    · intro h
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have := h v; simp only [F, hv, if_true] at this; exact this
      · have := h v; simp only [F, hv, if_false] at this; exact this
  rw [e]
  exact hbox

theorem isCompact_inv_image (v : HeightOneSpectrum (𝓞 K)) (C : Set (v.adicCompletion K)) (hC : IsCompact C)
    (h0 : (0 : v.adicCompletion K) ∉ C) : IsCompact ((fun x : v.adicCompletion K => x⁻¹) '' C) :=
  hC.image_of_continuousOn (continuousOn_inv₀.mono fun x hx h => h0 (by rw [Set.mem_singleton_iff] at h; exact h ▸ hx))

theorem inv_snd_apply (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((↑z⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = ((((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))⁻¹ := by
  have h : (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) * (((↑z⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
    have h1 := congrArg (fun a : AdeleRing (𝓞 K) K => (a.2 : FiniteAdeleRing (𝓞 K) K) v) z.mul_inv
    exact h1
  exact eq_inv_of_mul_eq_one_right h

end BoxIdeleK9

open BoxIdeleK9 in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K))
    (hCf : ∀ v ∈ S, IsCompact (Cf v)) (hCf0 : ∀ v ∈ S, (0 : v.adicCompletion K) ∉ Cf v) :
    IsCompact ({z : (AdeleRing (𝓞 K) K)ˣ |
        Units.map (AdelicLevel.adeleArch (𝓞 K) K) z ∈ Ca ∧
        ∀ v ∈ S, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v} ∩
      ↑(NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))))) := by
  classical

  have hB₁ := isCompact_finBox K S Cf hCf
  have hB₂ := isCompact_finBox K S (fun v => (fun x : v.adicCompletion K => x⁻¹) '' Cf v)
    (fun v hv => isCompact_inv_image K v (Cf v) (hCf v hv) (hCf0 v hv))
  have hC₁ : IsCompact (((↑) : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) '' Ca) := hCa.image Units.continuous_val
  have hC₂ : IsCompact ((fun c : (InfiniteAdeleRing K)ˣ => (↑c⁻¹ : InfiniteAdeleRing K)) '' Ca) :=
    hCa.image Units.continuous_coe_inv
  have hbig := (Units.isClosedEmbedding_embedProduct (α := AdeleRing (𝓞 K) K)).isCompact_preimage
    (((hC₁.prod hB₁).prod ((hC₂.prod hB₂).image MulOpposite.continuous_op)))

  have hca : Continuous (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) := continuous_fst
  have hcv : ∀ v : HeightOneSpectrum (𝓞 K), Continuous (fun a : AdeleRing (𝓞 K) K => ((a.2 : FiniteAdeleRing (𝓞 K) K) v)) :=
    fun v => (RestrictedProduct.continuous_eval v).comp continuous_snd

  have hPa : IsClosed {z : (AdeleRing (𝓞 K) K)ˣ | Units.map (AdelicLevel.adeleArch (𝓞 K) K) z ∈ Ca} :=
    hCa.isClosed.preimage (Continuous.units_map _ hca)
  have hPb : IsClosed {z : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v} := by
    have e : {z : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v} =
        ⋂ v ∈ S, (fun z : (AdeleRing (𝓞 K) K)ˣ => (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ⁻¹' Cf v := by
      ext z; simp only [mem_setOf_eq, mem_iInter, mem_preimage]
    rw [e]
    exact isClosed_biInter fun v hv => (hCf v hv).isClosed.preimage ((hcv v).comp Units.continuous_val)
  have hPc : IsClosed (↑(NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K)))) :
      Set (AdeleRing (𝓞 K) K)ˣ) := by
    have e : (↑(NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K)))) :
        Set (AdeleRing (𝓞 K) K)ˣ) =
        ⋂ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ,
          ((fun z : (AdeleRing (𝓞 K) K)ˣ => (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ⁻¹'
              (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ∩
           (fun z : (AdeleRing (𝓞 K) K)ˣ => (((↑z⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ⁻¹'
              (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
      ext z
      simp only [SetLike.mem_coe, mem_iInter, mem_inter_iff, mem_preimage, mem_compl_iff]
      exact Iff.rfl
    rw [e]
    exact isClosed_biInter fun v _ =>
      ((isCompact_iff_compactSpace.mpr (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)).isClosed.preimage
        ((hcv v).comp Units.continuous_val)).inter
      ((isCompact_iff_compactSpace.mpr (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)).isClosed.preimage
        ((hcv v).comp Units.continuous_coe_inv))
  have hcl : IsClosed ({z : (AdeleRing (𝓞 K) K)ˣ |
        Units.map (AdelicLevel.adeleArch (𝓞 K) K) z ∈ Ca ∧
        ∀ v ∈ S, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v} ∩
      ↑(NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))))) := by
    rw [Set.setOf_and]
    exact (hPa.inter hPb).inter hPc

  refine hbig.of_isClosed_subset hcl ?_
  rintro z ⟨⟨ha, hb⟩, hc⟩
  have hc' : ∀ v ∉ S, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ v.adicCompletionIntegers K ∧
      (((↑z⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ v.adicCompletionIntegers K :=
    fun v hv => hc v (by rwa [Finset.mem_coe])
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_image]
  refine ⟨⟨⟨_, ha, rfl⟩, fun v hv => hb v hv, fun v hv => (hc' v hv).1⟩,
    ⟨((↑z⁻¹ : AdeleRing (𝓞 K) K)), ⟨⟨_, ha, rfl⟩, fun v hv => ?_, fun v hv => (hc' v hv).2⟩, rfl⟩⟩
  exact ⟨_, hb v hv, (inv_snd_apply K z v).symm⟩

end S_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
end P2MW
export P2MW.S_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside (solution)

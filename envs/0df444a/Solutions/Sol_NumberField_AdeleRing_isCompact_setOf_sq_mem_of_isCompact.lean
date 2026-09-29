-- Prove2me | solution 1 for NumberField.AdeleRing.isCompact_setOf_sq_mem_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/30e0be6f-b2c3-5c95-a955-7834d0b1646b

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact

set_option autoImplicit false

open NumberField Topology Filter Set

namespace SqProper9

theorem normedField_isCompact_sq_preimage {F : Type*} [NormedField F] [ProperSpace F] (D : Set F)
    (hD : IsCompact D) : IsCompact {a : F | a ^ 2 ∈ D} := by
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le.mp hD.isBounded)
  have hcl : IsClosed {a : F | a ^ 2 ∈ D} := hD.isClosed.preimage (continuous_pow 2)
  refine (isCompact_closedBall (0 : F) (max 1 M)).of_isClosed_subset hcl ?_
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖a‖ ^ 2 ≤ M := by rw [← norm_pow]; exact hM _ ha
  by_contra h
  rw [not_le] at h
  have h2 : (1 : ℝ) < ‖a‖ := lt_of_le_of_lt (le_max_left _ _) h
  have h3 : M < ‖a‖ := lt_of_le_of_lt (le_max_right _ _) h
  nlinarith

theorem pi_isCompact_sq_preimage {ι : Type*} {X : ι → Type*} [∀ i, Monoid (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, ContinuousMul (X i)] [∀ i, T2Space (X i)]
    (h : ∀ i (D : Set (X i)), IsCompact D → IsCompact {a : X i | a ^ 2 ∈ D})
    (D : Set (∀ i, X i)) (hD : IsCompact D) : IsCompact {x : ∀ i, X i | x ^ 2 ∈ D} := by
  have hcl : IsClosed {x : ∀ i, X i | x ^ 2 ∈ D} := hD.isClosed.preimage (continuous_pow 2)
  refine (isCompact_univ_pi fun i => h i _ (hD.image (continuous_apply i))).of_isClosed_subset hcl ?_
  intro x hx
  simp only [mem_univ_pi, mem_setOf_eq, mem_image]
  exact fun i => ⟨x ^ 2, hx, rfl⟩

theorem prod_isCompact_sq_preimage {X Y : Type*} [Monoid X] [Monoid Y] [TopologicalSpace X] [TopologicalSpace Y]
    [ContinuousMul X] [ContinuousMul Y] [T2Space X] [T2Space Y]
    (hX : ∀ D : Set X, IsCompact D → IsCompact {a : X | a ^ 2 ∈ D})
    (hY : ∀ D : Set Y, IsCompact D → IsCompact {a : Y | a ^ 2 ∈ D})
    (D : Set (X × Y)) (hD : IsCompact D) : IsCompact {p : X × Y | p ^ 2 ∈ D} := by
  have hcl : IsClosed {p : X × Y | p ^ 2 ∈ D} := hD.isClosed.preimage (continuous_pow 2)
  refine ((hX _ (hD.image continuous_fst)).prod (hY _ (hD.image continuous_snd))).of_isClosed_subset hcl ?_
  intro p hp
  exact ⟨⟨p ^ 2, hp, rfl⟩, ⟨p ^ 2, hp, rfl⟩⟩

open scoped RestrictedProduct

theorem restrictedProduct_isCompact_sq_preimage {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, ContinuousMul (R i)] [∀ i, T2Space (R i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {B : ∀ i, S i}
    (hBo : ∀ i, IsOpen (B i : Set (R i))) (hBc : ∀ i, IsCompact (B i : Set (R i)))
    (hBsq : ∀ i (a : R i), a ^ 2 ∈ (B i : Set (R i)) → a ∈ (B i : Set (R i)))
    (h : ∀ i (D : Set (R i)), IsCompact D → IsCompact {a : R i | a ^ 2 ∈ D})
    (D : Set (Πʳ i, [R i, B i])) (hD : IsCompact D) : IsCompact {x : Πʳ i, [R i, B i] | x ^ 2 ∈ D} := by
  classical
  haveI : Fact (∀ i, IsOpen (B i : Set (R i))) := ⟨hBo⟩

  obtain ⟨T, hT⟩ : ∃ T : Finset ι, D ⊆ {x : Πʳ i, [R i, B i] | ∀ i, i ∉ T → x i ∈ (B i : Set (R i))} := by
    refine hD.elim_directed_cover (fun T : Finset ι => {x : Πʳ i, [R i, B i] | ∀ i, i ∉ T → x i ∈ (B i : Set (R i))})
      (fun T => RestrictedProduct.isOpen_forall_imp_mem hBo) ?_ ?_
    · intro x _
      have hx : ∀ᶠ i in cofinite, x i ∈ (B i : Set (R i)) := x.2
      rw [Filter.eventually_cofinite] at hx
      refine mem_iUnion.mpr ⟨hx.toFinset, fun i hi => ?_⟩
      by_contra hxi
      exact hi (hx.mem_toFinset.mpr hxi)
    · intro T₁ T₂
      exact ⟨T₁ ∪ T₂, fun x hx i hi => hx i fun h' => hi (Finset.mem_union_left _ h'),
        fun x hx i hi => hx i fun h' => hi (Finset.mem_union_right _ h')⟩

  let E : ∀ i, Set (R i) := fun i => {a : R i | a ^ 2 ∈ (fun x : Πʳ i, [R i, B i] => x i) '' D}
  have hE : ∀ i, IsCompact (E i) := fun i => h i _ (hD.image (RestrictedProduct.continuous_eval i))
  let F : ∀ i, Set (R i) := fun i => if i ∈ T then E i else E i ∩ (B i : Set (R i))
  have hF : ∀ i, IsCompact (F i) := by
    intro i
    by_cases hi : i ∈ T
    · simp only [F, hi, if_true]; exact hE i
    · simp only [F, hi, if_false]; exact (hE i).inter_right (hBc i).isClosed
  have hFB : ∀ i, i ∉ T → F i ⊆ (B i : Set (R i)) := by
    intro i hi
    simp only [F, hi, if_false]
    exact inter_subset_right
  let Sc : Set ι := (↑T : Set ι)ᶜ
  have hS : (cofinite : Filter ι) ≤ 𝓟 Sc := Filter.le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite
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
  have hbox : IsCompact (RestrictedProduct.inclusion R (fun i => (B i : Set (R i))) hS '' box') :=
    hbox'.image (RestrictedProduct.continuous_inclusion hS)

  have hcl : IsClosed {x : Πʳ i, [R i, B i] | x ^ 2 ∈ D} := hD.isClosed.preimage (continuous_pow 2)
  refine hbox.of_isClosed_subset hcl ?_
  intro x hx
  have hxE : ∀ i, x i ∈ E i := fun i => ⟨x ^ 2, hx, by simp only [RestrictedProduct.pow_apply]⟩
  have hxB : ∀ i, i ∉ T → x i ∈ (B i : Set (R i)) := fun i hi =>
    hBsq i (x i) (by rw [← RestrictedProduct.pow_apply]; exact hT hx i hi)
  have hxF : ∀ i, x i ∈ F i := by
    intro i
    by_cases hi : i ∈ T
    · simp only [F, hi, if_true]; exact hxE i
    · simp only [F, hi, if_false]; exact ⟨hxE i, hxB i hi⟩
  refine ⟨⟨x, ?_⟩, hxF, ?_⟩
  · rw [Filter.eventually_principal]
    intro i hi
    exact hxB i hi
  · ext i; rfl

variable (K : Type) [Field K] [NumberField K]

open IsDedekindDomain

omit [NumberField K] in
theorem infiniteAdeleRing_isCompact_sq_preimage (D : Set (InfiniteAdeleRing K)) (hD : IsCompact D) :
    IsCompact {a : InfiniteAdeleRing K | a ^ 2 ∈ D} :=
  pi_isCompact_sq_preimage (X := fun v : InfinitePlace K => v.Completion)
    (fun v D hD => by
      haveI : ProperSpace v.Completion := ⟨fun x r => by
        rw [← (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).preimage_closedBall x r]
        exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.isCompact_preimage
          (isCompact_closedBall _ _)⟩
      exact normedField_isCompact_sq_preimage D hD) D hD

theorem finiteAdeleRing_isCompact_sq_preimage (D : Set (FiniteAdeleRing (𝓞 K) K)) (hD : IsCompact D) :
    IsCompact {a : FiniteAdeleRing (𝓞 K) K | a ^ 2 ∈ D} := by
  refine restrictedProduct_isCompact_sq_preimage (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
    (fun v => Valued.isOpen_valuationSubring _)
    (fun v => by
      show IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      exact isCompact_iff_compactSpace.mpr (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v))
    (fun v a ha => ?_) (fun v D hD => normedField_isCompact_sq_preimage D hD) D hD
  change a ∈ v.adicCompletionIntegers K
  change a ^ 2 ∈ v.adicCompletionIntegers K at ha
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
  rw [map_pow, pow_two] at ha
  by_contra h'
  exact absurd ha (not_le.mpr (one_lt_mul_of_lt_of_le' (not_le.mp h') (not_le.mp h').le))

theorem adeleRing_isCompact_sq_preimage (D : Set (AdeleRing (𝓞 K) K)) (hD : IsCompact D) :
    IsCompact {a : AdeleRing (𝓞 K) K | a ^ 2 ∈ D} :=
  prod_isCompact_sq_preimage (infiniteAdeleRing_isCompact_sq_preimage K) (finiteAdeleRing_isCompact_sq_preimage K) D hD

end SqProper9

open SqProper9 in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (C : Set (AdeleRing (𝓞 K) K)ˣ) (hC : IsCompact C) :
    IsCompact {u : (AdeleRing (𝓞 K) K)ˣ | u ^ 2 ∈ C} := by
  have hcl : IsClosed {u : (AdeleRing (𝓞 K) K)ˣ | u ^ 2 ∈ C} := hC.isClosed.preimage (continuous_pow 2)
  have h1 : IsCompact {a : AdeleRing (𝓞 K) K | a ^ 2 ∈ ((↑) : (AdeleRing (𝓞 K) K)ˣ → AdeleRing (𝓞 K) K) '' C} :=
    adeleRing_isCompact_sq_preimage K _ (hC.image Units.continuous_val)
  have h2 : IsCompact {a : AdeleRing (𝓞 K) K | a ^ 2 ∈ (fun u : (AdeleRing (𝓞 K) K)ˣ => (↑u⁻¹ : AdeleRing (𝓞 K) K)) '' C} :=
    adeleRing_isCompact_sq_preimage K _ (hC.image Units.continuous_coe_inv)
  have h3 := Units.isClosedEmbedding_embedProduct.isCompact_preimage (h1.prod (h2.image MulOpposite.continuous_op))
  refine h3.of_isClosed_subset hcl ?_
  intro u hu
  simp only [Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, Set.mem_setOf_eq, Set.mem_image]
  refine ⟨⟨u ^ 2, hu, ?_⟩, ⟨(↑u⁻¹ : AdeleRing (𝓞 K) K), ⟨u ^ 2, hu, ?_⟩, rfl⟩⟩
  · exact Units.val_pow_eq_pow_val u 2
  · rw [← inv_pow]; exact Units.val_pow_eq_pow_val u⁻¹ 2

end S_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact
end P2MW
export P2MW.S_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact (solution)

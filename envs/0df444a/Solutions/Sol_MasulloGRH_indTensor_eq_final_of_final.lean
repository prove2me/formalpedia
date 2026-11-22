-- Prove2me | solution 1 for MasulloGRH.indTensor_eq_final_of_final
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:36:02.3528+00:00
-- url     : https://prove2.me/submissions/29f2b9b4-5ede-46a2-90e0-6bd5dd79e63c

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace Sol_MasulloGRH_indTensor_eq_final_of_final

open MasulloGRH

universe w

/-- Re-indexing a defining family of seminorms by its range: a topology defined by a family of
seminorms indexed by a type in an arbitrary universe is defined by a family indexed by a type in
the universe of the space. -/
theorem isLocallyConvexTopology_of_withSeminorms {X : Type u} [AddCommGroup X] [Module ℂ X]
    (t : TopologicalSpace X) {ι : Type v} [Nonempty ι] (q : SeminormFamily ℂ X ι)
    (hq : @WithSeminorms ℂ X ι _ _ _ q t) : IsLocallyConvexTopology X t := by
  let _ : TopologicalSpace X := t
  have : IsTopologicalAddGroup X := hq.topologicalAddGroup
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let q' : SeminormFamily ℂ X (Set.range q) := fun s => s.1
  have : Nonempty (Set.range q) := ⟨⟨q i₀, i₀, rfl⟩⟩
  refine ⟨Set.range q, inferInstance, q', ?_⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at hq ⊢
  rw [hq]
  exact (iInf_range' (fun s : Seminorm ℂ X => (𝓝 (0 : ℝ)).comap s) q).symm

/-- The topology induced by a linear map from a locally convex topology is locally convex. -/
theorem isLocallyConvexTopology_induced {X : Type u} {G : Type v} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup G] [Module ℂ G] (tG : TopologicalSpace G) (hG : IsLocallyConvexTopology G tG)
    (T : X →ₗ[ℂ] G) : IsLocallyConvexTopology X (TopologicalSpace.induced T tG) := by
  obtain ⟨ι, hι, p, hp⟩ := hG
  let _ : TopologicalSpace G := tG
  exact isLocallyConvexTopology_of_withSeminorms _ (p.comp T) (T.withSeminorms_induced hp)

/-- A locally convex topology is a group topology. -/
theorem isTopologicalAddGroup_of_isLocallyConvexTopology {X : Type u} [AddCommGroup X]
    [Module ℂ X] (t : TopologicalSpace X) (ht : IsLocallyConvexTopology X t) :
    @IsTopologicalAddGroup X t _ := by
  obtain ⟨ι, hι, p, hp⟩ := ht
  let _ : TopologicalSpace X := t
  exact hp.topologicalAddGroup

section tensor

variable {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- For the inductive topology the canonical bilinear map is continuous in the second variable. -/
theorem continuous_tmul_left (x : X) :
    @Continuous Y (X ⊗[ℂ] Y) _ (indTensorTopology X Y) (fun y => x ⊗ₜ[ℂ] y) := by
  unfold indTensorTopology
  exact continuous_sInf_rng.2 fun t ht => ht.2.1 x

/-- For the inductive topology the canonical bilinear map is continuous in the first variable. -/
theorem continuous_tmul_right (y : Y) :
    @Continuous X (X ⊗[ℂ] Y) _ (indTensorTopology X Y) (fun x => x ⊗ₜ[ℂ] y) := by
  unfold indTensorTopology
  exact continuous_sInf_rng.2 fun t ht => ht.2.2 y

/-- Universal property of the inductive topology: a linear map from `X ⊗ Y` into a locally convex
space whose associated bilinear map is separately continuous is continuous for the inductive
topology. -/
theorem continuous_indTensor_of_separately {G : Type v} [AddCommGroup G] [Module ℂ G]
    (tG : TopologicalSpace G) (hG : IsLocallyConvexTopology G tG) (T : X ⊗[ℂ] Y →ₗ[ℂ] G)
    (h₁ : ∀ x : X, @Continuous Y G _ tG (fun y => T (x ⊗ₜ[ℂ] y)))
    (h₂ : ∀ y : Y, @Continuous X G _ tG (fun x => T (x ⊗ₜ[ℂ] y))) :
    @Continuous (X ⊗[ℂ] Y) G (indTensorTopology X Y) tG T := by
  have hle : indTensorTopology X Y ≤ TopologicalSpace.induced T tG :=
    sInf_le ⟨isLocallyConvexTopology_induced tG hG T,
      fun x => continuous_induced_rng.2 (h₁ x), fun y => continuous_induced_rng.2 (h₂ y)⟩
  exact continuous_iff_le_induced.2 hle

end tensor

/-- Universal property of a locally convex final topology: a linear map from `E`, endowed with
the finest locally convex topology making all `a i` continuous, into a locally convex space is
continuous as soon as all its composites with the `a i` are continuous. -/
theorem continuous_of_lcFinal {E : Type u} [AddCommGroup E] [Module ℂ E] {I : Type*}
    (X : I → Type v) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, TopologicalSpace (X i)] (a : ∀ i, X i →ₗ[ℂ] E)
    {G : Type w} [AddCommGroup G] [Module ℂ G]
    (tG : TopologicalSpace G) (hG : IsLocallyConvexTopology G tG) (T : E →ₗ[ℂ] G)
    (h : ∀ i, @Continuous (X i) G _ tG (fun x => T (a i x))) :
    @Continuous E G
      (sInf {t | IsLocallyConvexTopology E t ∧ ∀ i, @Continuous (X i) E _ t (a i)}) tG T :=
  continuous_iff_le_induced.2
    (sInf_le ⟨isLocallyConvexTopology_induced tG hG T, fun i => continuous_induced_rng.2 (h i)⟩)

end Sol_MasulloGRH_indTensor_eq_final_of_final

open MasulloGRH Sol_MasulloGRH_indTensor_eq_final_of_final

theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    {I J : Type*} (X : I → Type v) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, TopologicalSpace (X i)]
    (Y : J → Type v) [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)]
    [∀ j, TopologicalSpace (Y j)]
    (hX : ∀ i, IsHLCS (X i)) (hY : ∀ j, IsHLCS (Y j)) (hE : IsHLCS E) (hF : IsHLCS F)
    (a : ∀ i, X i →ₗ[ℂ] E) (b : ∀ j, Y j →ₗ[ℂ] F)
    (ha : ⨆ i, LinearMap.range (a i) = ⊤) (hb : ⨆ j, LinearMap.range (b j) = ⊤)
    (htopE : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ i, @Continuous (X i) E _ t (a i)})
    (htopF : ‹TopologicalSpace F› =
      sInf {t | IsLocallyConvexTopology F t ∧ ∀ j, @Continuous (Y j) F _ t (b j)}) :
    indTensorTopology E F =
      sInf {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧ ∀ i j,
        @Continuous (X i ⊗[ℂ] Y j) (E ⊗[ℂ] F) (indTensorTopology (X i) (Y j)) t
          (TensorProduct.map (a i) (b j))} := by
  -- the Hausdorff / local convexity hypotheses on the spaces are not needed
  have _ := hX
  have _ := hY
  have _ := hE
  have _ := hF
  -- the structure maps are continuous
  have hca : ∀ i, Continuous (a i) := by
    intro i
    rw [htopE]
    exact continuous_sInf_rng.2 fun t ht => ht.2 i
  have hcb : ∀ j, Continuous (b j) := by
    intro j
    rw [htopF]
    exact continuous_sInf_rng.2 fun t ht => ht.2 j
  -- a locally convex topology on `E ⊗ F` makes `⊗` separately continuous iff it makes all the
  -- maps `a i ⊗ b j` continuous for the inductive topologies of the stages
  have key : ∀ t : TopologicalSpace (E ⊗[ℂ] F), IsLocallyConvexTopology (E ⊗[ℂ] F) t →
      (((∀ x : E, @Continuous F (E ⊗[ℂ] F) _ t (fun y => x ⊗ₜ[ℂ] y)) ∧
        (∀ y : F, @Continuous E (E ⊗[ℂ] F) _ t (fun x => x ⊗ₜ[ℂ] y))) ↔
      ∀ i j, @Continuous (X i ⊗[ℂ] Y j) (E ⊗[ℂ] F) (indTensorTopology (X i) (Y j)) t
          (TensorProduct.map (a i) (b j))) := by
    intro t ht
    constructor
    · -- separately continuous on `E × F` implies separately continuous on each `X i × Y j`
      rintro ⟨h₁, h₂⟩ i j
      refine continuous_indTensor_of_separately t ht _ (fun x => ?_) (fun y => ?_)
      · exact @Continuous.comp (Y j) F (E ⊗[ℂ] F) _ _ t _ _ (h₁ (a i x)) (hcb j)
      · exact @Continuous.comp (X i) E (E ⊗[ℂ] F) _ _ t _ _ (h₂ (b j y)) (hca i)
    · intro h
      have hgrp : @IsTopologicalAddGroup (E ⊗[ℂ] F) t _ :=
        isTopologicalAddGroup_of_isLocallyConvexTopology t ht
      have hadd : @ContinuousAdd (E ⊗[ℂ] F) t _ := @IsTopologicalAddGroup.toContinuousAdd _ t _ hgrp
      constructor
      · intro x
        -- by the universal property of `F` it suffices to test on each `Y j`
        have hx : @Continuous F (E ⊗[ℂ] F) _ t (TensorProduct.mk ℂ E F x) := by
          rw [htopF]
          refine continuous_of_lcFinal Y b t ht _ fun j => ?_
          -- `x` is a finite sum of elements of the images of the `a i`
          have hmem : x ∈ ⨆ i, LinearMap.range (a i) := by rw [ha]; exact Submodule.mem_top
          refine Submodule.iSup_induction (fun i => LinearMap.range (a i))
            (motive := fun x => @Continuous (Y j) (E ⊗[ℂ] F) _ t (fun y => x ⊗ₜ[ℂ] b j y))
            hmem ?_ ?_ ?_
          · rintro i _ ⟨x₀, rfl⟩
            exact @Continuous.comp (Y j) (X i ⊗[ℂ] Y j) (E ⊗[ℂ] F) _
              (indTensorTopology (X i) (Y j)) t _ _ (h i j) (continuous_tmul_left x₀)
          · simp only [zero_tmul]
            exact @continuous_const _ _ _ t _
          · intro x₁ x₂ h₁ h₂
            simp only [add_tmul]
            exact @Continuous.add _ t _ hadd _ _ _ _ h₁ h₂
        exact hx
      · intro y
        have hy : @Continuous E (E ⊗[ℂ] F) _ t ((TensorProduct.mk ℂ E F).flip y) := by
          rw [htopE]
          refine continuous_of_lcFinal X a t ht _ fun i => ?_
          have hmem : y ∈ ⨆ j, LinearMap.range (b j) := by rw [hb]; exact Submodule.mem_top
          refine Submodule.iSup_induction (fun j => LinearMap.range (b j))
            (motive := fun y => @Continuous (X i) (E ⊗[ℂ] F) _ t (fun x => a i x ⊗ₜ[ℂ] y))
            hmem ?_ ?_ ?_
          · rintro j _ ⟨y₀, rfl⟩
            exact @Continuous.comp (X i) (X i ⊗[ℂ] Y j) (E ⊗[ℂ] F) _
              (indTensorTopology (X i) (Y j)) t _ _ (h i j) (continuous_tmul_right y₀)
          · simp only [tmul_zero]
            exact @continuous_const _ _ _ t _
          · intro y₁ y₂ h₁ h₂
            simp only [tmul_add]
            exact @Continuous.add _ t _ hadd _ _ _ _ h₁ h₂
        exact hy
  -- hence the two families of topologies coincide, and so do their infima
  have hset : {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧
      (∀ x : E, @Continuous F (E ⊗[ℂ] F) _ t (fun y => x ⊗ₜ[ℂ] y)) ∧
      (∀ y : F, @Continuous E (E ⊗[ℂ] F) _ t (fun x => x ⊗ₜ[ℂ] y))} =
      {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧ ∀ i j,
        @Continuous (X i ⊗[ℂ] Y j) (E ⊗[ℂ] F) (indTensorTopology (X i) (Y j)) t
          (TensorProduct.map (a i) (b j))} := by
    ext t
    exact and_congr_right (key t)
  exact congrArg sInf hset

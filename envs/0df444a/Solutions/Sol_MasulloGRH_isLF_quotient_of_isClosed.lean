-- Prove2me | solution 1 for MasulloGRH.isLF_quotient_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:37:19.207002+00:00
-- url     : https://prove2.me/submissions/604f041c-000a-4228-a7d6-5b6dd3c3d9e6

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_isLF_quotient_of_isClosed

universe u

section lc

open scoped ComplexOrder in
/-- A complex topological vector space whose `0`-neighbourhoods have a base of convex sets is
locally convex in the sense of `IsLocallyConvexTopology`: its topology is defined by the gauges of
its absolutely convex open sets. -/
theorem isLocallyConvexTopology_of_locallyConvexSpace (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [LocallyConvexSpace ℝ E] : IsLocallyConvexTopology E inferInstance := by
  have : LocallyConvexSpace ℂ E := by
    refine (locallyConvexSpace_iff_exists_convex_subset_zero ℂ E).mpr fun U hU => ?_
    obtain ⟨S, hS, hconv, hSU⟩ :=
      (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp inferInstance U hU
    refine ⟨S, hS, convex_of_nonneg_surjective_algebraMap ℂ (fun x hx => ?_) hconv, hSU⟩
    obtain ⟨r, hr, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp (Set.mem_Ici.mp hx)
    exact ⟨r, hr, rfl⟩
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact ⟨AbsConvexOpenSets ℂ E, inferInstance, gaugeSeminormFamily ℂ E, with_gaugeSeminormFamily⟩

/-- The quotient of a locally convex space by a subspace is locally convex. -/
theorem isLocallyConvexTopology_quotient (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsLocallyConvexTopology E inferInstance) (W : Submodule ℂ E) :
    IsLocallyConvexTopology (E ⧸ W) inferInstance := by
  obtain ⟨ι, _, p, hp⟩ := hE
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  have : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  have : LocallyConvexSpace ℝ (E ⧸ W) := by
    refine LocallyConvexSpace.ofBasisZero ℝ (E ⧸ W) (fun s : Set E => W.mkQ '' s)
      (fun s => s ∈ 𝓝 (0 : E) ∧ Convex ℝ s) ?_ ?_
    · have h := (LocallyConvexSpace.convex_basis_zero ℝ E).map W.mkQ
      have h2 : Filter.map W.mkQ (𝓝 (0 : E)) = 𝓝 (0 : E ⧸ W) := by
        have := W.isOpenMap_mkQ.map_nhds_eq W.continuous_mkQ.continuousAt (x := 0)
        simpa using this
      rw [h2] at h
      exact h
    · rintro s ⟨-, hs⟩
      exact hs.is_linear_image (W.mkQ.restrictScalars ℝ).isLinear
  exact isLocallyConvexTopology_of_locallyConvexSpace (E ⧸ W)

end lc

section complete

open Uniformity

variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- For a topological vector space, the Cauchy filters of the additive uniform structure are the
filters that are Cauchy in the sense of `IsCauchyFilter`. -/
theorem cauchy_iff_isCauchyFilter (f : Filter E) :
    @Cauchy E (IsTopologicalAddGroup.rightUniformSpace E) f ↔ IsCauchyFilter f := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  rw [cauchy_iff]
  refine and_congr Iff.rfl ⟨fun h U hU => ?_, fun h s hs => ?_⟩
  · have h2 : (fun p : E × E => p.2 + -p.1) ⁻¹' U ∈ 𝓤 E := by
      rw [uniformity_eq_comap_nhds_zero' E]
      exact Filter.preimage_mem_comap hU
    obtain ⟨A, hA, hAU⟩ := h _ h2
    refine ⟨A, hA, fun x hx y hy => ?_⟩
    have h3 : x + -y ∈ U := hAU (Set.mk_mem_prod hy hx)
    rwa [← sub_eq_add_neg] at h3
  · rw [uniformity_eq_comap_nhds_zero' E] at hs
    obtain ⟨U, hU, hUs⟩ := Filter.mem_comap.mp hs
    obtain ⟨A, hA, hAU⟩ := h U hU
    refine ⟨A, hA, fun q hq => hUs ?_⟩
    have h3 : q.2 - q.1 ∈ U := hAU q.2 hq.2 q.1 hq.1
    rwa [sub_eq_add_neg] at h3

/-- Completeness in the sense of `IsCompleteTVS` is Hausdorffness together with completeness of
the additive uniform structure. -/
theorem isCompleteTVS_iff :
    IsCompleteTVS E ↔
      T2Space E ∧ @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h f hf => ?_⟩
  · let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    exact ⟨fun {f} hf => h f ((cauchy_iff_isCauchyFilter f).mp hf)⟩
  · let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    exact h.complete ((cauchy_iff_isCauchyFilter f).mpr hf)

end complete

/-- **Quotients of Fréchet spaces.** The quotient of a Fréchet space by a closed subspace is a
Fréchet space. -/
theorem isFrechet_quotient (F : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hF : IsFrechet F) (K : Submodule ℂ F) (hK : IsClosed (K : Set F)) : IsFrechet (F ⧸ K) := by
  obtain ⟨hlc, hcomp, hmet⟩ := hF
  obtain ⟨ι, _, p, hp⟩ := id hlc
  have := hp.topologicalAddGroup
  have : IsClosed (K : Set F) := hK
  have hT2 : T2Space (F ⧸ K) := inferInstance
  refine ⟨isLocallyConvexTopology_quotient F hlc K, ?_, ?_⟩
  · rw [isCompleteTVS_iff] at hcomp ⊢
    refine ⟨hT2, ?_⟩
    have := hcomp.2
    exact QuotientAddGroup.completeSpace_right' F K.toAddSubgroup
  · let : UniformSpace (F ⧸ K) := IsTopologicalAddGroup.rightUniformSpace (F ⧸ K)
    have : IsUniformAddGroup (F ⧸ K) := isUniformAddGroup_of_addCommGroup
    have : FirstCountableTopology (F ⧸ K) :=
      QuotientAddGroup.instFirstCountableTopology (N := K.toAddSubgroup)
    have : (uniformity (F ⧸ K)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.metrizableSpace

/-- The Fréchet property is invariant under linear homeomorphisms. -/
theorem isFrechet_of_linearEquiv {A B : Type u} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₗ[ℂ] B) (he : Continuous e)
    (he' : Continuous e.symm) (hA : IsFrechet A) : IsFrechet B := by
  obtain ⟨⟨ι, hι, p, hp⟩, ⟨hT2, hcomplete⟩, hmet⟩ := hA
  let h : B ≃ₜ A :=
    { toEquiv := e.symm.toEquiv
      continuous_toFun := he'
      continuous_invFun := he }
  have hind : IsInducing (e.symm : B →ₗ[ℂ] A) := h.isInducing
  refine ⟨⟨ι, hι, p.comp (e.symm : B →ₗ[ℂ] A), hind.withSeminorms hp⟩,
    ⟨h.symm.t2Space, fun f hf => ?_⟩, h.isEmbedding.metrizableSpace⟩
  obtain ⟨hne, hc⟩ := hf
  have hcauchy : IsCauchyFilter (f.map e.symm) := by
    refine ⟨Filter.map_neBot, fun U hU => ?_⟩
    have hU' : e.symm ⁻¹' U ∈ 𝓝 (0 : B) :=
      he'.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨S, hS, hSU⟩ := hc _ hU'
    refine ⟨e.symm '' S, Filter.image_mem_map hS, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hSU a ha b hb
    simpa using this
  obtain ⟨a, ha⟩ := hcomplete _ hcauchy
  refine ⟨e a, ?_⟩
  have h1 : (f.map e.symm).map e ≤ 𝓝 (e a) := (Filter.map_mono ha).trans he.continuousAt
  rwa [Filter.map_map, show (e ∘ e.symm : B → B) = id from funext e.apply_symm_apply,
    Filter.map_id] at h1

/-- The image of a Fréchet space under a surjective linear map with closed kernel, with the
quotient (coinduced) topology, is a Fréchet space. -/
theorem isFrechet_coinduced {F G : Type u} [AddCommGroup F] [Module ℂ F] [AddCommGroup G]
    [Module ℂ G] [τ : TopologicalSpace F] (hF : IsFrechet F) (g : F →ₗ[ℂ] G)
    (hg : Function.Surjective g) (hker : IsClosed (LinearMap.ker g : Set F)) :
    @IsFrechet G _ _ (TopologicalSpace.coinduced g τ) := by
  let : TopologicalSpace G := TopologicalSpace.coinduced g τ
  let e : (F ⧸ LinearMap.ker g) ≃ₗ[ℂ] G := g.quotKerEquivOfSurjective hg
  have he : Continuous e := by
    refine (LinearMap.ker g).isQuotientMap_mkQ.continuous_iff.mpr ?_
    exact continuous_coinduced_rng
  have he' : Continuous e.symm := by
    refine continuous_coinduced_dom.mpr ?_
    have : (e.symm ∘ g : F → F ⧸ LinearMap.ker g) = (LinearMap.ker g).mkQ := by
      funext x
      exact e.symm_apply_eq.mpr rfl
    rw [this]
    exact (LinearMap.ker g).continuous_mkQ
  exact isFrechet_of_linearEquiv e he he' (isFrechet_quotient F hF _ hker)

end Sol_MasulloGRH_isLF_quotient_of_isClosed

open Sol_MasulloGRH_isLF_quotient_of_isClosed in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsLF E) (W : Submodule ℂ E) (hW : IsClosed (W : Set E)) :
    IsLF (E ⧸ W) := by
  obtain ⟨⟨hlc, hT2⟩, X, τ, hcov, hFr, htrans, htop⟩ := hE
  obtain ⟨ι, _, p, hp⟩ := id hlc
  have := hp.topologicalAddGroup
  have : IsClosed (W : Set E) := hW
  have hT2' : T2Space (E ⧸ W) := inferInstance
  -- the inclusions of the steps into `E` are continuous
  have hval : ∀ n, @Continuous (X n) E (τ n) _ Subtype.val := by
    intro n
    rw [htop]
    exact continuous_sInf_rng.mpr fun t ht => ht.2 n
  -- the steps of the quotient: the images of the steps, with the quotient topologies
  let Y : ℕ → Submodule ℂ (E ⧸ W) := fun n => (X n).map W.mkQ
  let g : ∀ n, X n →ₗ[ℂ] Y n := fun n => W.mkQ.submoduleMap (X n)
  let σ : ∀ n, TopologicalSpace (Y n) := fun n => TopologicalSpace.coinduced (g n) (τ n)
  have hgsurj : ∀ n, Function.Surjective (g n) := fun n => W.mkQ.submoduleMap_surjective (X n)
  have hgcont : ∀ n, @Continuous (X n) (Y n) (τ n) (σ n) (g n) := fun n =>
    continuous_coinduced_rng
  have hLC : IsLocallyConvexTopology (E ⧸ W) inferInstance :=
    isLocallyConvexTopology_quotient E hlc W
  refine ⟨⟨hLC, hT2'⟩, Y, σ, ?_, ?_, ?_, ?_⟩
  · -- the steps cover the quotient
    intro y
    obtain ⟨x, rfl⟩ := W.mkQ_surjective y
    obtain ⟨n, hn⟩ := hcov x
    exact ⟨n, Submodule.mem_map_of_mem hn⟩
  · -- each step is a Fréchet space
    intro n
    refine @isFrechet_coinduced (X n) (Y n) _ _ _ _ (τ n) (hFr n) (g n) (hgsurj n) ?_
    have hker : (LinearMap.ker (g n) : Set (X n)) = Subtype.val ⁻¹' (W : Set E) := by
      ext x
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Set.mem_preimage]
      rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.coe_eq_zero]
      rfl
    rw [hker]
    exact @IsClosed.preimage (X n) E (τ n) _ _ (hval n) _ hW
  · -- the transition maps
    intro n
    obtain ⟨h, hc⟩ := htrans n
    refine ⟨Submodule.map_mono h, ?_⟩
    refine continuous_coinduced_dom.mpr ?_
    have hcomm : (Submodule.inclusion (Submodule.map_mono h) ∘ g n : X n → Y (n + 1)) =
        g (n + 1) ∘ Submodule.inclusion h := rfl
    rw [hcomm]
    exact @Continuous.comp (X n) (X (n + 1)) (Y (n + 1)) (τ n) (τ (n + 1)) (σ (n + 1)) _ _
      (hgcont (n + 1)) hc
  · -- the quotient topology is the locally convex inductive limit topology of the steps
    refine le_antisymm (le_sInf fun t ht => ?_) (sInf_le ⟨hLC, fun n => ?_⟩)
    · obtain ⟨⟨κ, hκ, q, hq⟩, hcont⟩ := ht
      have h1 : ‹TopologicalSpace E› ≤ TopologicalSpace.induced W.mkQ t := by
        rw [htop]
        refine sInf_le ⟨⟨κ, hκ, q.comp W.mkQ, ?_⟩, fun n => ?_⟩
        · exact @LinearMap.withSeminorms_induced ℂ ℂ E (E ⧸ W) κ _ _ _ _ _ _ _ _ t q hq W.mkQ
        · refine continuous_induced_rng.mpr ?_
          have hcomm : (W.mkQ ∘ (Subtype.val : X n → E)) =
              (Subtype.val : Y n → E ⧸ W) ∘ g n := rfl
          rw [hcomm]
          exact @Continuous.comp (X n) (Y n) (E ⧸ W) (τ n) (σ n) t _ _ (hcont n) (hgcont n)
      have h2 : @Continuous E (E ⧸ W) _ t W.mkQ := continuous_iff_le_induced.mpr h1
      have h3 : @Continuous (E ⧸ W) (E ⧸ W) (QuotientModule.Quotient.topologicalSpace W) t id :=
        (@Topology.IsQuotientMap.continuous_iff E (E ⧸ W) (E ⧸ W) W.mkQ id _
          (QuotientModule.Quotient.topologicalSpace W) t W.isQuotientMap_mkQ).mpr h2
      exact continuous_id_iff_le.mp h3
    · refine continuous_coinduced_dom.mpr ?_
      have hcomm : ((Subtype.val : Y n → E ⧸ W) ∘ g n) = W.mkQ ∘ (Subtype.val : X n → E) := rfl
      rw [hcomm]
      exact @Continuous.comp (X n) E (E ⧸ W) (τ n) _ _ _ _ W.continuous_mkQ (hval n)

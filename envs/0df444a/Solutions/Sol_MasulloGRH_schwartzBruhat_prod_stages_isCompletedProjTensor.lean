-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_prod_stages_isCompletedProjTensor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:02:24.37364+00:00
-- url     : https://prove2.me/submissions/8ddaa270-9360-4c62-a511-15c8489bec9b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_TopologicalTensorProduct_Completion
import Theorems.Thm_MasulloGRH_exists_cofinal_structuralPairs
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_schwartzBruhat_averaging
import Theorems.Thm_MasulloGRH_schwartzBruhat_stage_isEmbedding_and_bounded
import Theorems.Thm_MasulloGRH_schwartzBruhat_main_structure
import Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel
import Theorems.Thm_MasulloGRH_projTensor_isHLCS
import Theorems.Thm_MasulloGRH_continuous_projTensor_iff
import Theorems.Thm_MasulloGRH_isStructuralPair_prod_and_le_prod
import Theorems.Thm_MasulloGRH_elemSchwartz_prod_isCompletedProjTensor

open TensorProduct Topology

set_option autoImplicit false

universe u

namespace Sol_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor

open MasulloGRH

section transport

universe u₁ u₂ u₃ u₄

lemma induced_eq_of_leftInverse {X : Type u₁} {Y : Type u₂} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] (f : X → Y) (g : Y → X) (hgf : ∀ x, g (f x) = x)
    (hf : Continuous f) (hg : Continuous g) : tX = TopologicalSpace.induced f tY := by
  apply le_antisymm
  · exact continuous_iff_le_induced.1 hf
  · have h1 : tY ≤ TopologicalSpace.induced g tX := continuous_iff_le_induced.1 hg
    calc TopologicalSpace.induced f tY ≤ TopologicalSpace.induced f (TopologicalSpace.induced g tX) :=
          induced_mono h1
      _ = TopologicalSpace.induced (g ∘ f) tX := induced_compose
      _ = tX := by
          have : g ∘ f = id := funext hgf
          rw [this, induced_id]

lemma isCauchyFilter_map {E : Type u₁} {F : Type u₂} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (L : E →ₗ[ℂ] F) (hL : Continuous L) {f : Filter E} (hf : IsCauchyFilter f) :
    IsCauchyFilter (Filter.map L f) := by
  refine ⟨hf.1.map _, fun U hU => ?_⟩
  have hV : (L : E → F) ⁻¹' U ∈ 𝓝 (0 : E) := by
    apply hL.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨A, hA, hAU⟩ := hf.2 _ hV
  refine ⟨L '' A, Filter.image_mem_map hA, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have := hAU x hx y hy
  simpa [map_sub] using this

lemma isCompleteTVS_of_equiv {E : Type u₁} {F : Type u₂} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (e : E ≃ₗ[ℂ] F) (he : Continuous e) (he' : Continuous e.symm) (hF : IsCompleteTVS F) :
    IsCompleteTVS E := by
  have hemb : Topology.IsEmbedding e :=
    Function.LeftInverse.isEmbedding (f := e.symm) (g := e) (fun x => by simp) he' he
  refine ⟨?_, fun f hf => ?_⟩
  · have := hF.1
    exact hemb.t2Space
  · obtain ⟨y, hy⟩ := hF.2 _ (isCauchyFilter_map e.toLinearMap he hf)
    refine ⟨e.symm y, ?_⟩
    have h1 : Filter.map e.symm (Filter.map e f) ≤ Filter.map e.symm (𝓝 y) := Filter.map_mono hy
    rw [Filter.map_map] at h1
    have h2 : (e.symm ∘ e : E → E) = id := funext fun x => by simp
    rw [h2, Filter.map_id] at h1
    exact h1.trans (he'.tendsto y)

/-- `T₁ ⊗ T₂` is continuous for the projective topologies. -/
lemma projTensor_map_continuous (E₁ E₂ : Type u₁) (F₁ F₂ : Type u₂)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂)
    (L₁ : E₁ →ₗ[ℂ] F₁) (L₂ : E₂ →ₗ[ℂ] F₂) (hL₁ : Continuous L₁) (hL₂ : Continuous L₂) :
    @Continuous (E₁ ⊗[ℂ] E₂) (F₁ ⊗[ℂ] F₂) (projTensorTopology E₁ E₂) (projTensorTopology F₁ F₂)
      (TensorProduct.map L₁ L₂) := by
  let _ : TopologicalSpace (F₁ ⊗[ℂ] F₂) := projTensorTopology F₁ F₂
  have hG : IsLocallyConvexTopology (F₁ ⊗[ℂ] F₂) (projTensorTopology F₁ F₂) :=
    (projTensor_isHLCS F₁ F₂ hF₁ hF₂).1
  refine (continuous_projTensor_iff E₁ E₂ hE₁ hE₂ (F₁ ⊗[ℂ] F₂) hG (TensorProduct.map L₁ L₂)).2 ?_
  have htm : Continuous (fun p : F₁ × F₂ => p.1 ⊗ₜ[ℂ] p.2) := by
    show @Continuous (F₁ × F₂) (F₁ ⊗[ℂ] F₂) _ (projTensorTopology F₁ F₂) _
    unfold projTensorTopology
    rw [continuous_sInf_rng]
    intro t ht
    exact ht.2
  have : (fun p : E₁ × E₂ => TensorProduct.map L₁ L₂ (p.1 ⊗ₜ[ℂ] p.2)) =
      (fun p : F₁ × F₂ => p.1 ⊗ₜ[ℂ] p.2) ∘ (fun p : E₁ × E₂ => (L₁ p.1, L₂ p.2)) := by
    funext p; simp
  rw [this]
  exact htm.comp ((hL₁.comp continuous_fst).prodMk (hL₂.comp continuous_snd))

lemma projTensor_congr_induced (E₁ E₂ : Type u₁) (F₁ F₂ : Type u₂)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂)
    (e₁ : E₁ ≃ₗ[ℂ] F₁) (e₂ : E₂ ≃ₗ[ℂ] F₂) (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (he₁' : Continuous e₁.symm) (he₂' : Continuous e₂.symm) :
    projTensorTopology E₁ E₂ =
      TopologicalSpace.induced (TensorProduct.congr e₁ e₂) (projTensorTopology F₁ F₂) := by
  let _ : TopologicalSpace (E₁ ⊗[ℂ] E₂) := projTensorTopology E₁ E₂
  let _ : TopologicalSpace (F₁ ⊗[ℂ] F₂) := projTensorTopology F₁ F₂
  refine induced_eq_of_leftInverse (TensorProduct.congr e₁ e₂) (TensorProduct.congr e₁ e₂).symm
    (fun x => by simp) ?_ ?_
  · exact projTensor_map_continuous E₁ E₂ F₁ F₂ hE₁ hE₂ hF₁ hF₂ e₁.toLinearMap e₂.toLinearMap
      he₁ he₂
  · exact projTensor_map_continuous F₁ F₂ E₁ E₂ hF₁ hF₂ hE₁ hE₂ e₁.symm.toLinearMap
      e₂.symm.toLinearMap he₁' he₂'

lemma isCompletedProjTensor_transport (E₁ E₂ : Type u₁) (F₁ F₂ : Type u₂)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    {Y : Type u₃} {Y' : Type u₄} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Y'] [Module ℂ Y'] [TopologicalSpace Y']
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂) (hY' : IsHLCS Y')
    (e₁ : E₁ ≃ₗ[ℂ] F₁) (e₂ : E₂ ≃ₗ[ℂ] F₂) (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (he₁' : Continuous e₁.symm) (he₂' : Continuous e₂.symm)
    (ε : Y ≃ₗ[ℂ] Y') (hε : Continuous ε) (hε' : Continuous ε.symm)
    (j : F₁ ⊗[ℂ] F₂ →ₗ[ℂ] Y) (hj : IsCompletedProjTensor F₁ F₂ j) :
    IsCompletedProjTensor E₁ E₂
      (ε.toLinearMap ∘ₗ j ∘ₗ (TensorProduct.congr e₁ e₂).toLinearMap) := by
  obtain ⟨-, hYc, hinj, htop, hdense⟩ := hj
  refine ⟨hY', isCompleteTVS_of_equiv ε.symm hε' (by simpa using hε) hYc, ?_, ?_, ?_⟩
  · exact ε.injective.comp (hinj.comp (TensorProduct.congr e₁ e₂).injective)
  · have h1 := projTensor_congr_induced E₁ E₂ F₁ F₂ hE₁ hE₂ hF₁ hF₂ e₁ e₂ he₁ he₂ he₁' he₂'
    have h2 : ‹TopologicalSpace Y› =
        TopologicalSpace.induced ε ‹TopologicalSpace Y'› :=
      induced_eq_of_leftInverse ε ε.symm (fun x => by simp) hε hε'
    rw [h1, htop, h2, induced_compose, induced_compose]
    rfl
  · have hsurj : Function.Surjective (TensorProduct.congr e₁ e₂) :=
      (TensorProduct.congr e₁ e₂).surjective
    have hd : DenseRange (j ∘ (TensorProduct.congr e₁ e₂)) := by
      unfold DenseRange; rw [hsurj.range_comp]; exact hdense
    exact ε.surjective.denseRange.comp hd hε

end transport

end Sol_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor
namespace Sol_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor

open MasulloGRH

section stages

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma topology_eq : instTopologicalSpaceSchwartzBruhat G =
    sInf {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
    ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat G) _ t
        (SchwartzBruhat.ofElem Γ k π hs hπ)} := rfl

lemma ofElem_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  rw [continuous_iff_le_induced, topology_eq, ← continuous_iff_le_induced, continuous_sInf_rng]
  intro t ht
  exact ht.2 Γ k m n r s d π hs hπ

lemma elem_ext {m n r s : ℕ} {d : Fin s → ℕ} {g g' : ElemSchwartz m n r s d}
    (h : g.toFun = g'.toFun) : g = g' := Subtype.ext h

lemma ofElem_injective {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Function.Injective (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  intro g g' h
  have h' : extendPullback Γ π g.toFun = extendPullback Γ π g'.toFun := congrArg Subtype.val h
  apply elem_ext
  funext y
  obtain ⟨x, hx⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd y)
  have := congrFun h' (x : G)
  simp only [extendPullback, dif_pos x.2, Subtype.coe_eta, hx, toAdd_ofAdd] at this
  exact this

lemma ofElem_add {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g g' : ElemSchwartz m n r s d) :
    SchwartzBruhat.ofElem Γ k π hs hπ (g + g') =
      SchwartzBruhat.ofElem Γ k π hs hπ g + SchwartzBruhat.ofElem Γ k π hs hπ g' := by
  apply Subtype.ext
  show extendPullback Γ π (g + g').toFun = extendPullback Γ π g.toFun + extendPullback Γ π g'.toFun
  funext x
  simp only [extendPullback, Pi.add_apply]
  split_ifs
  · rfl
  · simp

lemma ofElem_smul {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (c : ℂ) (g : ElemSchwartz m n r s d) :
    SchwartzBruhat.ofElem Γ k π hs hπ (c • g) = c • SchwartzBruhat.ofElem Γ k π hs hπ g := by
  apply Subtype.ext
  show extendPullback Γ π (c • g).toFun = c • extendPullback Γ π g.toFun
  funext x
  simp only [extendPullback, Pi.smul_apply]
  split_ifs
  · rfl
  · simp

/-- The stage inclusion `S(Γ/k) → S(G)` as a linear map. -/
noncomputable def ofElemₗ {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : ElemSchwartz m n r s d →ₗ[ℂ] SchwartzBruhat G where
  toFun := SchwartzBruhat.ofElem Γ k π hs hπ
  map_add' := ofElem_add Γ k π hs hπ
  map_smul' := ofElem_smul Γ k π hs hπ

/-- The stage `S(k, Γ) ⊆ S(G)`. -/
noncomputable def stage {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Submodule ℂ (SchwartzBruhat G) :=
  LinearMap.range (ofElemₗ Γ k π hs hπ)

/-- `S(Γ/k) ≃ S(k, Γ)`. -/
noncomputable def stageEquiv {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : ElemSchwartz m n r s d ≃ₗ[ℂ] stage Γ k π hs hπ :=
  LinearEquiv.ofInjective (ofElemₗ Γ k π hs hπ) (ofElem_injective Γ k π hs hπ)

lemma stageEquiv_apply {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemSchwartz m n r s d) :
    ((stageEquiv Γ k π hs hπ g : stage Γ k π hs hπ) : SchwartzBruhat G) =
      SchwartzBruhat.ofElem Γ k π hs hπ g := rfl

lemma ofElem_stageEquiv_symm {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (x : stage Γ k π hs hπ) :
    SchwartzBruhat.ofElem Γ k π hs hπ ((stageEquiv Γ k π hs hπ).symm x) = x :=
  LinearEquiv.ofInjective_symm_apply (f := ofElemₗ Γ k π hs hπ) x

lemma stageEquiv_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (stageEquiv Γ k π hs hπ) :=
  (ofElem_continuous Γ k π hs hπ).subtype_mk _

lemma stageEquiv_symm_continuous [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (stageEquiv Γ k π hs hπ).symm := by
  have hemb := (schwartzBruhat_stage_isEmbedding_and_bounded G).1 Γ k m n r s d π hs hπ
  rw [hemb.continuous_iff]
  have : (SchwartzBruhat.ofElem Γ k π hs hπ ∘ (stageEquiv Γ k π hs hπ).symm) = Subtype.val := by
    funext x
    exact ofElem_stageEquiv_symm Γ k π hs hπ x
  rw [this]
  exact continuous_subtype_val

lemma submodule_isLC {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsLocallyConvexTopology E ‹_›) (X : Submodule ℂ E) :
    IsLocallyConvexTopology X (inferInstance : TopologicalSpace X) := by
  obtain ⟨ι, hι, p, hp⟩ := hE
  exact ⟨ι, hι, p.comp X.subtype, LinearMap.withSeminorms_induced hp X.subtype⟩

lemma stage_isHLCS [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : IsHLCS (stage Γ k π hs hπ) := by
  have hHLCS := (schwartzBruhat_main_structure G).1
  have := hHLCS.2
  exact ⟨submodule_isLC hHLCS.1 _, inferInstance⟩

lemma stage_isFrechet [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : IsFrechet (stage Γ k π hs hπ) := by
  have hE := (elemSchwartz_frechet_nuclear_montel m n r s d hπ.1).1
  have := hE.2.2
  refine ⟨(stage_isHLCS Γ k π hs hπ).1,
    isCompleteTVS_of_equiv (stageEquiv Γ k π hs hπ).symm (stageEquiv_symm_continuous Γ k π hs hπ)
      (by simpa using stageEquiv_continuous Γ k π hs hπ) hE.2.1, ?_⟩
  exact (Function.LeftInverse.isEmbedding (f := stageEquiv Γ k π hs hπ)
    (g := (stageEquiv Γ k π hs hπ).symm) (fun x => by simp) (stageEquiv_continuous Γ k π hs hπ)
    (stageEquiv_symm_continuous Γ k π hs hπ)).metrizableSpace

/-- Monotonicity of stages, from the averaging operators. -/
lemma ofElem_mono [T2Space G] [LocallyCompactSpace G] {m n r s : ℕ} {d : Fin s → ℕ}
    {m' n' r' s' : ℕ} {d' : Fin s' → ℕ} (Γ k Γ' k' : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π)
    (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' k')
    (hπ' : IsElemPresentation Γ' k' π') (hΓ : Γ ≤ Γ') (hk : k' ≤ k) :
    ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d', Continuous T ∧
      ∀ g, SchwartzBruhat.ofElem Γ k π hs hπ g = SchwartzBruhat.ofElem Γ' k' π' hs' hπ' (T g) := by
  obtain ⟨A, -, h2, -, h4⟩ := schwartzBruhat_averaging G
  obtain ⟨T, hT, hTeq⟩ := h4 Γ k m n r s d π hs hπ Γ' k' m' n' r' s' d' π' hs' hπ'
  exact ⟨T, hT, fun g => (h2 Γ k m n r s d π hs hπ Γ' k' hs' hΓ hk g).symm.trans (hTeq g)⟩

/-- A monotone cofinal sequence of structural pairs gives a strict inductive limit description. -/
lemma stages_seq [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (Γs ks : ℕ → Subgroup G) (m n r s : ℕ → ℕ) (d : (N : ℕ) → Fin (s N) → ℕ)
    (π : (N : ℕ) → ↥(Γs N) →* Multiplicative (ElemGroup (m N) (n N) (r N) (s N) (d N)))
    (hs : ∀ N, IsStructuralPair (Γs N) (ks N))
    (hπ : ∀ N, IsElemPresentation (Γs N) (ks N) (π N))
    (hΓ : Monotone Γs) (hk : Antitone ks)
    (hcof : ∀ Γ' k' : Subgroup G, IsStructuralPair Γ' k' → ∃ M, Γ' ≤ Γs M ∧ ks M ≤ k') :
    Monotone (fun N => stage (Γs N) (ks N) (π N) (hs N) (hπ N)) ∧
    (∀ f : SchwartzBruhat G, ∃ N, f ∈ stage (Γs N) (ks N) (π N) (hs N) (hπ N)) ∧
    (inferInstance : TopologicalSpace (SchwartzBruhat G)) =
      sInf {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
        ∀ N, @Continuous (stage (Γs N) (ks N) (π N) (hs N) (hπ N)) (SchwartzBruhat G) _ t
          Subtype.val} := by
  have hHLCS : IsHLCS (SchwartzBruhat G) := (schwartzBruhat_main_structure G).1
  let X : ℕ → Submodule ℂ (SchwartzBruhat G) := fun N => stage (Γs N) (ks N) (π N) (hs N) (hπ N)
  have hfac : ∀ (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' k')
      (hπ' : IsElemPresentation Γ' k' π'), ∃ (M : ℕ) (φ : ElemSchwartz m' n' r' s' d' → X M),
        Continuous φ ∧ SchwartzBruhat.ofElem Γ' k' π' hs' hπ' = Subtype.val ∘ φ := by
    intro Γ' k' m' n' r' s' d' π' hs' hπ'
    obtain ⟨M, hM1, hM2⟩ := hcof Γ' k' hs'
    obtain ⟨T, hT, hTeq⟩ :=
      ofElem_mono Γ' k' (Γs M) (ks M) π' hs' hπ' (π M) (hs M) (hπ M) hM1 hM2
    refine ⟨M, fun g => stageEquiv (Γs M) (ks M) (π M) (hs M) (hπ M) (T g),
      (stageEquiv_continuous _ _ _ _ _).comp hT, ?_⟩
    funext g
    exact hTeq g
  have hmono : Monotone X := by
    intro N M hNM f hf
    obtain ⟨g, rfl⟩ := hf
    obtain ⟨T, -, hTeq⟩ := ofElem_mono (Γs N) (ks N) (Γs M) (ks M) (π N) (hs N) (hπ N) (π M)
      (hs M) (hπ M) (hΓ hNM) (hk hNM)
    exact ⟨T g, (hTeq g).symm⟩
  have hexh : ∀ (x : G → ℂ) (hx : x ∈ schwartzBruhatSubmodule G),
      ∃ N, (⟨x, hx⟩ : SchwartzBruhat G) ∈ X N := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Γ', k', m', n', r', s', d', π', g, hs', hπ', rfl⟩ := hx
      obtain ⟨M, φ, -, heq⟩ := hfac Γ' k' m' n' r' s' d' π' hs' hπ'
      refine ⟨M, ?_⟩
      have : SchwartzBruhat.ofElem Γ' k' π' hs' hπ' g = (φ g : SchwartzBruhat G) := congrFun heq g
      show SchwartzBruhat.ofElem Γ' k' π' hs' hπ' g ∈ X M
      rw [this]
      exact (φ g).2
    | zero => exact ⟨0, zero_mem _⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨N, hN⟩ := ihx
      obtain ⟨M, hM⟩ := ihy
      refine ⟨max N M, ?_⟩
      have := add_mem (hmono (le_max_left N M) hN) (hmono (le_max_right N M) hM)
      exact this
    | smul c x hx ih =>
      obtain ⟨N, hN⟩ := ih
      exact ⟨N, (X N).smul_mem c hN⟩
  refine ⟨hmono, fun f => hexh f.1 f.2, ?_⟩
  apply le_antisymm
  · refine le_sInf ?_
    rintro t ⟨htlc, htc⟩
    rw [topology_eq]
    refine sInf_le ⟨htlc, ?_⟩
    intro Γ' k' m' n' r' s' d' π' hs' hπ'
    obtain ⟨M, φ, hφ, heq⟩ := hfac Γ' k' m' n' r' s' d' π' hs' hπ'
    rw [heq]
    exact @Continuous.comp (ElemSchwartz m' n' r' s' d') (X M) (SchwartzBruhat G) _
      (@instTopologicalSpaceSubtype _ _ (instTopologicalSpaceSchwartzBruhat G)) t _ _ (htc M) hφ
  · exact sInf_le ⟨hHLCS.1, fun N => continuous_subtype_val⟩

end stages

end Sol_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor
namespace Sol_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor

open MasulloGRH

section prodPres

set_option linter.unusedSectionVars false
variable {G₁ G₂ : Type u} [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  {m₁ n₁ r₁ s₁ : ℕ} {d₁ : Fin s₁ → ℕ} {m₂ n₂ r₂ s₂ : ℕ} {d₂ : Fin s₂ → ℕ}
  {m n r s : ℕ} {d : Fin s → ℕ}

/-- First component of an element of `Γ₁ × Γ₂`. -/
def pr₁ (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) (γ : ↥(Γ₁.prod Γ₂)) : Γ₁ :=
  ⟨(γ : G₁ × G₂).1, (Subgroup.mem_prod.1 γ.2).1⟩

/-- Second component of an element of `Γ₁ × Γ₂`. -/
def pr₂ (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) (γ : ↥(Γ₁.prod Γ₂)) : Γ₂ :=
  ⟨(γ : G₁ × G₂).2, (Subgroup.mem_prod.1 γ.2).2⟩

/-- The presentation `φ ∘ (π₁ × π₂)` of the product pair. -/
noncomputable def prodPres (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂)
    (π₁ : ↥Γ₁ →* Multiplicative (ElemGroup m₁ n₁ r₁ s₁ d₁))
    (π₂ : ↥Γ₂ →* Multiplicative (ElemGroup m₂ n₂ r₂ s₂ d₂))
    (φ : (ElemGroup m₁ n₁ r₁ s₁ d₁ × ElemGroup m₂ n₂ r₂ s₂ d₂) ≃ₜ+ ElemGroup m n r s d) :
    ↥(Γ₁.prod Γ₂) →* Multiplicative (ElemGroup m n r s d) :=
  MonoidHom.mk' (fun γ => Multiplicative.ofAdd (φ (Multiplicative.toAdd (π₁ (pr₁ Γ₁ Γ₂ γ)),
      Multiplicative.toAdd (π₂ (pr₂ Γ₁ Γ₂ γ))))) (by
    intro a b
    have e₁ : pr₁ Γ₁ Γ₂ (a * b) = pr₁ Γ₁ Γ₂ a * pr₁ Γ₁ Γ₂ b := rfl
    have e₂ : pr₂ Γ₁ Γ₂ (a * b) = pr₂ Γ₁ Γ₂ a * pr₂ Γ₁ Γ₂ b := rfl
    show Multiplicative.ofAdd (φ (Multiplicative.toAdd (π₁ (pr₁ Γ₁ Γ₂ (a * b))),
      Multiplicative.toAdd (π₂ (pr₂ Γ₁ Γ₂ (a * b))))) = _
    rw [e₁, e₂, MonoidHom.map_mul π₁, MonoidHom.map_mul π₂]
    show Multiplicative.ofAdd (φ (Multiplicative.toAdd (π₁ (pr₁ Γ₁ Γ₂ a)) +
      Multiplicative.toAdd (π₁ (pr₁ Γ₁ Γ₂ b)), Multiplicative.toAdd (π₂ (pr₂ Γ₁ Γ₂ a)) +
      Multiplicative.toAdd (π₂ (pr₂ Γ₁ Γ₂ b)))) = _
    rw [← Prod.mk_add_mk, map_add]
    rfl)

lemma prodPres_apply (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂)
    (π₁ : ↥Γ₁ →* Multiplicative (ElemGroup m₁ n₁ r₁ s₁ d₁))
    (π₂ : ↥Γ₂ →* Multiplicative (ElemGroup m₂ n₂ r₂ s₂ d₂))
    (φ : (ElemGroup m₁ n₁ r₁ s₁ d₁ × ElemGroup m₂ n₂ r₂ s₂ d₂) ≃ₜ+ ElemGroup m n r s d)
    (γ : ↥(Γ₁.prod Γ₂)) :
    Multiplicative.toAdd (prodPres Γ₁ Γ₂ π₁ π₂ φ γ) =
      φ (Multiplicative.toAdd (π₁ (pr₁ Γ₁ Γ₂ γ)), Multiplicative.toAdd (π₂ (pr₂ Γ₁ Γ₂ γ))) := rfl

lemma prodPres_isElemPresentation (Γ₁ k₁ : Subgroup G₁) (Γ₂ k₂ : Subgroup G₂)
    (π₁ : ↥Γ₁ →* Multiplicative (ElemGroup m₁ n₁ r₁ s₁ d₁))
    (π₂ : ↥Γ₂ →* Multiplicative (ElemGroup m₂ n₂ r₂ s₂ d₂))
    (φ : (ElemGroup m₁ n₁ r₁ s₁ d₁ × ElemGroup m₂ n₂ r₂ s₂ d₂) ≃ₜ+ ElemGroup m n r s d)
    (hπ₁ : IsElemPresentation Γ₁ k₁ π₁) (hπ₂ : IsElemPresentation Γ₂ k₂ π₂) (hd : ∀ i, d i ≠ 0) :
    IsElemPresentation (Γ₁.prod Γ₂) (k₁.prod k₂) (prodPres Γ₁ Γ₂ π₁ π₂ φ) := by
  obtain ⟨-, hc₁, ho₁, hsurj₁, hker₁⟩ := hπ₁
  obtain ⟨-, hc₂, ho₂, hsurj₂, hker₂⟩ := hπ₂
  have hpr₁ : Continuous (pr₁ Γ₁ Γ₂) := (continuous_subtype_val.fst).subtype_mk _
  have hpr₂ : Continuous (pr₂ Γ₁ Γ₂) := (continuous_subtype_val.snd).subtype_mk _
  have hfun : (prodPres Γ₁ Γ₂ π₁ π₂ φ : ↥(Γ₁.prod Γ₂) → Multiplicative (ElemGroup m n r s d)) =
      (Multiplicative.ofAdd ∘ φ) ∘
        (Prod.map (Multiplicative.toAdd ∘ π₁) (Multiplicative.toAdd ∘ π₂)) ∘
        (Homeomorph.Set.prod (Γ₁ : Set G₁) (Γ₂ : Set G₂) : ↥(Γ₁.prod Γ₂) → Γ₁ × Γ₂) := by
    funext γ; rfl
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · have : Continuous (fun γ : ↥(Γ₁.prod Γ₂) =>
        (Multiplicative.toAdd (π₁ (pr₁ Γ₁ Γ₂ γ)), Multiplicative.toAdd (π₂ (pr₂ Γ₁ Γ₂ γ)))) :=
      (continuous_toAdd.comp (hc₁.comp hpr₁)).prodMk (continuous_toAdd.comp (hc₂.comp hpr₂))
    exact continuous_ofAdd.comp (φ.continuous.comp this)
  · rw [hfun]
    have hoA : ∀ {X : Type} [TopologicalSpace X], IsOpenMap (Multiplicative.toAdd : Multiplicative X → X) :=
      fun {X} _ => IsOpenMap.of_inverse continuous_ofAdd (fun x => rfl) (fun x => rfl)
    have hoM : ∀ {X : Type} [TopologicalSpace X], IsOpenMap (Multiplicative.ofAdd : X → Multiplicative X) :=
      fun {X} _ => IsOpenMap.of_inverse continuous_toAdd (fun x => rfl) (fun x => rfl)
    refine (hoM.comp φ.toHomeomorph.isOpenMap).comp
      ((IsOpenMap.prodMap (hoA.comp ho₁) (hoA.comp ho₂)).comp ?_)
    exact (Homeomorph.Set.prod (Γ₁ : Set G₁) (Γ₂ : Set G₂)).isOpenMap
  · intro z
    obtain ⟨γ₁, hγ₁⟩ := hsurj₁ (Multiplicative.ofAdd (φ.symm (Multiplicative.toAdd z)).1)
    obtain ⟨γ₂, hγ₂⟩ := hsurj₂ (Multiplicative.ofAdd (φ.symm (Multiplicative.toAdd z)).2)
    refine ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [prodPres_apply]
    have h1 : pr₁ Γ₁ Γ₂ ⟨((γ₁ : G₁), (γ₂ : G₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩ = γ₁ := rfl
    have h2 : pr₂ Γ₁ Γ₂ ⟨((γ₁ : G₁), (γ₂ : G₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩ = γ₂ := rfl
    rw [h1, h2, hγ₁, hγ₂, toAdd_ofAdd, toAdd_ofAdd, Prod.mk.eta, ContinuousAddEquiv.apply_symm_apply]
  · intro γ
    rw [Subgroup.mem_prod]
    change _ ↔ ((pr₁ Γ₁ Γ₂ γ : G₁) ∈ k₁ ∧ (pr₂ Γ₁ Γ₂ γ : G₂) ∈ k₂)
    rw [← hker₁ (pr₁ Γ₁ Γ₂ γ), ← hker₂ (pr₂ Γ₁ Γ₂ γ)]
    constructor
    · intro h
      have h' : φ (Multiplicative.toAdd (π₁ (pr₁ Γ₁ Γ₂ γ)), Multiplicative.toAdd (π₂ (pr₂ Γ₁ Γ₂ γ))) =
          φ 0 := by
        rw [← prodPres_apply, h, map_zero]; rfl
      have h'' := Prod.ext_iff.1 (φ.injective h')
      exact ⟨Multiplicative.toAdd.injective h''.1, Multiplicative.toAdd.injective h''.2⟩
    · rintro ⟨h1, h2⟩
      apply Multiplicative.toAdd.injective
      rw [prodPres_apply, h1, h2]
      show φ (0, 0) = 0
      exact map_zero φ

/-- The stage function of the product pair on a value `φ (x, y) ↦ f x g y` is the product of the
stage functions. -/
lemma ofElem_prodPres (Γ₁ k₁ : Subgroup G₁) (Γ₂ k₂ : Subgroup G₂)
    (π₁ : ↥Γ₁ →* Multiplicative (ElemGroup m₁ n₁ r₁ s₁ d₁))
    (π₂ : ↥Γ₂ →* Multiplicative (ElemGroup m₂ n₂ r₂ s₂ d₂))
    (φ : (ElemGroup m₁ n₁ r₁ s₁ d₁ × ElemGroup m₂ n₂ r₂ s₂ d₂) ≃ₜ+ ElemGroup m n r s d)
    (hs₁ : IsStructuralPair Γ₁ k₁) (hπ₁ : IsElemPresentation Γ₁ k₁ π₁)
    (hs₂ : IsStructuralPair Γ₂ k₂) (hπ₂ : IsElemPresentation Γ₂ k₂ π₂)
    (hs : IsStructuralPair (Γ₁.prod Γ₂) (k₁.prod k₂))
    (hπ : IsElemPresentation (Γ₁.prod Γ₂) (k₁.prod k₂) (prodPres Γ₁ Γ₂ π₁ π₂ φ))
    (f : ElemSchwartz m₁ n₁ r₁ s₁ d₁) (g : ElemSchwartz m₂ n₂ r₂ s₂ d₂)
    (h : ElemSchwartz m n r s d) (hh : ∀ x y, h.toFun (φ (x, y)) = f.toFun x * g.toFun y)
    (p : G₁ × G₂) :
    (SchwartzBruhat.ofElem (Γ₁.prod Γ₂) (k₁.prod k₂) (prodPres Γ₁ Γ₂ π₁ π₂ φ) hs hπ h :
        G₁ × G₂ → ℂ) p =
      (SchwartzBruhat.ofElem Γ₁ k₁ π₁ hs₁ hπ₁ f : G₁ → ℂ) p.1 *
        (SchwartzBruhat.ofElem Γ₂ k₂ π₂ hs₂ hπ₂ g : G₂ → ℂ) p.2 := by
  show extendPullback (Γ₁.prod Γ₂) (prodPres Γ₁ Γ₂ π₁ π₂ φ) h.toFun p =
    extendPullback Γ₁ π₁ f.toFun p.1 * extendPullback Γ₂ π₂ g.toFun p.2
  unfold extendPullback
  by_cases h₁ : p.1 ∈ Γ₁
  · by_cases h₂ : p.2 ∈ Γ₂
    · have hp : p ∈ Γ₁.prod Γ₂ := Subgroup.mem_prod.2 ⟨h₁, h₂⟩
      rw [dif_pos hp, dif_pos h₁, dif_pos h₂, prodPres_apply, hh]
      rfl
    · have hp : p ∉ Γ₁.prod Γ₂ := fun hp => h₂ (Subgroup.mem_prod.1 hp).2
      rw [dif_neg hp, dif_neg h₂, mul_zero]
  · have hp : p ∉ Γ₁.prod Γ₂ := fun hp => h₁ (Subgroup.mem_prod.1 hp).1
    rw [dif_neg hp, dif_neg h₁, zero_mul]

end prodPres

end Sol_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor
open MasulloGRH Sol_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor in
theorem solution
    (G₁ G₂ : Type u) [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁]
    [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] :
    ∃ (X₁ : ℕ → Submodule ℂ (SchwartzBruhat G₁)) (X₂ : ℕ → Submodule ℂ (SchwartzBruhat G₂))
      (Y : ℕ → Submodule ℂ (SchwartzBruhat (G₁ × G₂))),
      Monotone X₁ ∧ Monotone X₂ ∧ Monotone Y ∧
      (∀ f, ∃ n, f ∈ X₁ n) ∧ (∀ g, ∃ n, g ∈ X₂ n) ∧ (∀ h, ∃ n, h ∈ Y n) ∧
      (∀ n, IsFrechet (X₁ n)) ∧ (∀ n, IsFrechet (X₂ n)) ∧
      (inferInstance : TopologicalSpace (SchwartzBruhat G₁)) =
        sInf {t | IsLocallyConvexTopology (SchwartzBruhat G₁) t ∧
          ∀ n, @Continuous (X₁ n) (SchwartzBruhat G₁) _ t Subtype.val} ∧
      (inferInstance : TopologicalSpace (SchwartzBruhat G₂)) =
        sInf {t | IsLocallyConvexTopology (SchwartzBruhat G₂) t ∧
          ∀ n, @Continuous (X₂ n) (SchwartzBruhat G₂) _ t Subtype.val} ∧
      (inferInstance : TopologicalSpace (SchwartzBruhat (G₁ × G₂))) =
        sInf {t | IsLocallyConvexTopology (SchwartzBruhat (G₁ × G₂)) t ∧
          ∀ n, @Continuous (Y n) (SchwartzBruhat (G₁ × G₂)) _ t Subtype.val} ∧
      ∀ n, ∃ jn : X₁ n ⊗[ℂ] X₂ n →ₗ[ℂ] Y n,
        (∀ (f : X₁ n) (g : X₂ n) (p : G₁ × G₂),
          ((jn (f ⊗ₜ[ℂ] g) : SchwartzBruhat (G₁ × G₂)) : G₁ × G₂ → ℂ) p =
            (f : SchwartzBruhat G₁) p.1 * (g : SchwartzBruhat G₂) p.2) ∧
        IsCompletedProjTensor (X₁ n) (X₂ n) jn := by
  obtain ⟨Γ₁, k₁, m₁, n₁, r₁, s₁, d₁, π₁, hp₁, hΓ₁, hk₁, hcof₁⟩ := exists_cofinal_structuralPairs G₁
  obtain ⟨Γ₂, k₂, m₂, n₂, r₂, s₂, d₂, π₂, hp₂, hΓ₂, hk₂, hcof₂⟩ := exists_cofinal_structuralPairs G₂
  have hcof₁' : ∀ Γ' k' : Subgroup G₁, IsStructuralPair Γ' k' → ∃ M, Γ' ≤ Γ₁ M ∧ k₁ M ≤ k' := by
    intro Γ' k' h
    obtain ⟨m', n', r', s', d', π', hπ'⟩ := exists_elemPresentation_of_isStructuralPair G₁ Γ' k' h
    exact hcof₁ Γ' k' m' n' r' s' d' π' h hπ'
  have hcof₂' : ∀ Γ' k' : Subgroup G₂, IsStructuralPair Γ' k' → ∃ M, Γ' ≤ Γ₂ M ∧ k₂ M ≤ k' := by
    intro Γ' k' h
    obtain ⟨m', n', r', s', d', π', hπ'⟩ := exists_elemPresentation_of_isStructuralPair G₂ Γ' k' h
    exact hcof₂ Γ' k' m' n' r' s' d' π' h hπ'
  obtain ⟨hprod, hdom⟩ := isStructuralPair_prod_and_le_prod G₁ G₂
  choose m n r s d φ j hd hjf hj using fun N => elemSchwartz_prod_isCompletedProjTensor
    (m₁ N) (n₁ N) (r₁ N) (s₁ N) (d₁ N) (m₂ N) (n₂ N) (r₂ N) (s₂ N) (d₂ N) (hp₁ N).2.1 (hp₂ N).2.1
  let Γ : ℕ → Subgroup (G₁ × G₂) := fun N => (Γ₁ N).prod (Γ₂ N)
  let k : ℕ → Subgroup (G₁ × G₂) := fun N => (k₁ N).prod (k₂ N)
  have hs : ∀ N, IsStructuralPair (Γ N) (k N) := fun N => hprod _ _ _ _ (hp₁ N).1 (hp₂ N).1
  let π := fun N => prodPres (Γ₁ N) (Γ₂ N) (π₁ N) (π₂ N) (φ N)
  have hπ : ∀ N, IsElemPresentation (Γ N) (k N) (π N) := fun N =>
    prodPres_isElemPresentation (Γ₁ N) (k₁ N) (Γ₂ N) (k₂ N) (π₁ N) (π₂ N) (φ N) (hp₁ N).2
      (hp₂ N).2 (hd N)
  have hΓ : Monotone Γ := fun N M h => Subgroup.prod_mono (hΓ₁ h) (hΓ₂ h)
  have hk : Antitone k := fun N M h => Subgroup.prod_mono (hk₁ h) (hk₂ h)
  have hcof : ∀ Γ' k' : Subgroup (G₁ × G₂), IsStructuralPair Γ' k' → ∃ M, Γ' ≤ Γ M ∧ k M ≤ k' := by
    intro Γ' k' h
    obtain ⟨A₁, B₁, A₂, B₂, h₁, h₂, hle, hge⟩ := hdom Γ' k' h
    obtain ⟨M₁, hM₁, hM₁'⟩ := hcof₁' A₁ B₁ h₁
    obtain ⟨M₂, hM₂, hM₂'⟩ := hcof₂' A₂ B₂ h₂
    refine ⟨max M₁ M₂, hle.trans (Subgroup.prod_mono (hM₁.trans (hΓ₁ (le_max_left _ _)))
      (hM₂.trans (hΓ₂ (le_max_right _ _)))), le_trans (Subgroup.prod_mono
      ((hk₁ (le_max_left _ _)).trans hM₁') ((hk₂ (le_max_right _ _)).trans hM₂')) hge⟩
  obtain ⟨hX₁m, hX₁e, hX₁t⟩ := stages_seq Γ₁ k₁ m₁ n₁ r₁ s₁ d₁ π₁ (fun N => (hp₁ N).1)
    (fun N => (hp₁ N).2) hΓ₁ hk₁ hcof₁'
  obtain ⟨hX₂m, hX₂e, hX₂t⟩ := stages_seq Γ₂ k₂ m₂ n₂ r₂ s₂ d₂ π₂ (fun N => (hp₂ N).1)
    (fun N => (hp₂ N).2) hΓ₂ hk₂ hcof₂'
  obtain ⟨hYm, hYe, hYt⟩ := stages_seq Γ k m n r s d π hs hπ hΓ hk hcof
  refine ⟨fun N => stage (Γ₁ N) (k₁ N) (π₁ N) (hp₁ N).1 (hp₁ N).2,
    fun N => stage (Γ₂ N) (k₂ N) (π₂ N) (hp₂ N).1 (hp₂ N).2,
    fun N => stage (Γ N) (k N) (π N) (hs N) (hπ N), hX₁m, hX₂m, hYm, hX₁e, hX₂e, hYe,
    fun N => stage_isFrechet _ _ _ _ _, fun N => stage_isFrechet _ _ _ _ _, hX₁t, hX₂t, hYt, ?_⟩
  intro N
  set e₁ := stageEquiv (Γ₁ N) (k₁ N) (π₁ N) (hp₁ N).1 (hp₁ N).2
  set e₂ := stageEquiv (Γ₂ N) (k₂ N) (π₂ N) (hp₂ N).1 (hp₂ N).2
  set ε := stageEquiv (Γ N) (k N) (π N) (hs N) (hπ N)
  have hE₁ := (elemSchwartz_frechet_nuclear_montel (m₁ N) (n₁ N) (r₁ N) (s₁ N) (d₁ N) (hp₁ N).2.1).1
  have hE₂ := (elemSchwartz_frechet_nuclear_montel (m₂ N) (n₂ N) (r₂ N) (s₂ N) (d₂ N) (hp₂ N).2.1).1
  refine ⟨ε.toLinearMap ∘ₗ j N ∘ₗ (TensorProduct.congr e₁.symm e₂.symm).toLinearMap, ?_, ?_⟩
  · intro f g p
    have h1 : ((ε.toLinearMap ∘ₗ j N ∘ₗ (TensorProduct.congr e₁.symm e₂.symm).toLinearMap)
        (f ⊗ₜ[ℂ] g) : SchwartzBruhat (G₁ × G₂)) =
        SchwartzBruhat.ofElem (Γ N) (k N) (π N) (hs N) (hπ N) (j N (e₁.symm f ⊗ₜ[ℂ] e₂.symm g)) :=
      rfl
    rw [h1, ← ofElem_stageEquiv_symm (Γ₁ N) (k₁ N) (π₁ N) (hp₁ N).1 (hp₁ N).2 f,
      ← ofElem_stageEquiv_symm (Γ₂ N) (k₂ N) (π₂ N) (hp₂ N).1 (hp₂ N).2 g]
    exact ofElem_prodPres (Γ₁ N) (k₁ N) (Γ₂ N) (k₂ N) (π₁ N) (π₂ N) (φ N) (hp₁ N).1 (hp₁ N).2
      (hp₂ N).1 (hp₂ N).2 (hs N) (hπ N) _ _ _ (hjf N _ _) p
  · exact isCompletedProjTensor_transport _ _ _ _ (stage_isHLCS _ _ _ _ _) (stage_isHLCS _ _ _ _ _)
      ⟨hE₁.1, hE₁.2.1.1⟩ ⟨hE₂.1, hE₂.2.1.1⟩ (stage_isHLCS _ _ _ _ _) e₁.symm e₂.symm
      (stageEquiv_symm_continuous _ _ _ _ _) (stageEquiv_symm_continuous _ _ _ _ _)
      (by simpa using stageEquiv_continuous _ _ _ _ _)
      (by simpa using stageEquiv_continuous _ _ _ _ _)
      ε (stageEquiv_continuous _ _ _ _ _) (stageEquiv_symm_continuous _ _ _ _ _) (j N) (hj N)

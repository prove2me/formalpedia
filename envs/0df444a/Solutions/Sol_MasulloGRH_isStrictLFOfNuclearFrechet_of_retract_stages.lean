-- Prove2me | solution 1 for MasulloGRH.isStrictLFOfNuclearFrechet_of_retract_stages
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:52:35.9489+00:00
-- url     : https://prove2.me/submissions/20bb776c-cc70-4332-8220-e1b2a02521ce

import Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv

set_option autoImplicit false

universe u

namespace MasulloGRHStagesAux

open MasulloGRH Topology Filter

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {F : Type u} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- a continuous linear retract `X ≃ F` transfers the Fréchet property -/
lemma frechet_of_equiv (e : E ≃L[ℂ] F) (hF : IsFrechet F) : IsFrechet E := by
  obtain ⟨⟨ι, hι, p, hp⟩, ⟨hT2, hc⟩, hmet⟩ := hF
  haveI := hT2
  haveI := hmet
  haveI : IsTopologicalAddGroup F := hp.topologicalAddGroup
  have hemb : IsEmbedding e := e.toHomeomorph.isEmbedding
  refine ⟨⟨ι, hι, p.comp (e : E →ₗ[ℂ] F), hemb.isInducing.withSeminorms hp⟩,
    ⟨hemb.t2Space, fun f hf => ?_⟩, hemb.metrizableSpace⟩
  obtain ⟨hne, hcf⟩ := hf
  obtain ⟨z, hz⟩ := hc (map e f) ⟨Filter.map_neBot, fun U hU => by
    obtain ⟨A, hA, hAU⟩ := hcf _ (e.continuous.tendsto 0 (by rw [map_zero]; exact hU))
    refine ⟨e '' A, image_mem_map hA, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_sub]; exact hAU x hx y hy⟩
  refine ⟨e.symm z, ?_⟩
  have h : f = map e.symm (map e f) := by
    rw [Filter.map_map]
    have : (e.symm ∘ e : E → E) = id := funext e.symm_apply_apply
    rw [this, Filter.map_id]
  rw [h]
  exact (Filter.map_mono hz).trans (e.symm.continuous.tendsto z)


lemma cont_comp_expl {α β γ : Type*} (tα : TopologicalSpace α) (tβ : TopologicalSpace β)
    (tγ : TopologicalSpace γ) {g : β → γ} {f : α → β} (hg : @Continuous β γ tβ tγ g)
    (hf : @Continuous α β tα tβ f) : @Continuous α γ tα tγ (g ∘ f) := hg.comp hf

section stages

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {F : Type u} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (J : F →ₗ[ℂ] E) (P : E →ₗ[ℂ] F)

/-- the stage `X = J(F)` with the induced topology is isomorphic to `F` -/
def stageEquiv (hJ : Continuous J) (hP : Continuous P) (hPJ : ∀ y, P (J y) = y) :
    LinearMap.range J ≃L[ℂ] F where
  toFun x := P x.1
  invFun y := ⟨J y, y, rfl⟩
  map_add' x y := by simp
  map_smul' c x := by simp
  left_inv x := by
    obtain ⟨_, y, rfl⟩ := x
    apply Subtype.ext
    simp [hPJ]
  right_inv y := hPJ y
  continuous_toFun := hP.comp continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 hJ

end stages

end MasulloGRHStagesAux

open MasulloGRH MasulloGRHStagesAux in
theorem solution
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (F : ℕ → Type u) [∀ N, AddCommGroup (F N)] [∀ N, Module ℂ (F N)]
    [∀ N, TopologicalSpace (F N)] (hF : ∀ N, IsFrechet (F N) ∧ IsNuclear (F N))
    (J : (N : ℕ) → F N →ₗ[ℂ] E) (P : (N : ℕ) → E →ₗ[ℂ] F N)
    (hJ : ∀ N, Continuous (J N)) (hP : ∀ N, Continuous (P N))
    (hPJ : ∀ N y, P N (J N y) = y)
    (hmono : ∀ N M, N ≤ M → LinearMap.range (J N) ≤ LinearMap.range (J M))
    (hexh : ∀ x : E, ∃ N, x ∈ LinearMap.range (J N))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ N, @Continuous (F N) E _ t (J N)}) :
    IsStrictLFOfNuclearFrechet E := by
  let e := fun N => stageEquiv (J N) (P N) (hJ N) (hP N) (hPJ N)
  refine ⟨fun N => LinearMap.range (J N), fun N M h => hmono N M h, hexh,
    fun N => ⟨frechet_of_equiv (e N) (hF N).1,
      nuclear_of_continuousLinearEquiv _ _ (e N) (hF N).2⟩, htop.trans ?_⟩
  have hc : ∀ N, Continuous (e N) := fun N => (e N).continuous
  have hcs : ∀ N, Continuous (e N).symm := fun N => (e N).symm.continuous
  have h1 : ∀ N, (Subtype.val : LinearMap.range (J N) → E) = J N ∘ (e N) := by
    intro N
    funext x
    obtain ⟨_, y, rfl⟩ := x
    show J N y = J N (P N (J N y))
    rw [hPJ]
  have h2 : ∀ N, (J N : F N → E) = Subtype.val ∘ (e N).symm := fun N => by
    funext y; rfl
  congr 1
  ext t
  refine and_congr_right fun _ => forall_congr' fun N => ⟨fun h => ?_, fun h => ?_⟩
  · rw [h1 N]
    exact cont_comp_expl _ _ _ h (hc N)
  · rw [h2 N]
    exact cont_comp_expl _ _ _ h (hcs N)

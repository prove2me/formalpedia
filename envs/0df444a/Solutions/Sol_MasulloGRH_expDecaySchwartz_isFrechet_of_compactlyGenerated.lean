-- Prove2me | solution 1 for MasulloGRH.expDecaySchwartz_isFrechet_of_compactlyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T18:59:57.886615+00:00
-- url     : https://prove2.me/submissions/83d7b842-6865-4946-b6e6-4f5c98743396

import Theorems.Thm_MasulloGRH_rposModulated_isGoodSubgroup_bot
import Theorems.Thm_MasulloGRH_expDecayStage_frechet_nuclear
import Theorems.Thm_MasulloGRH_expDecayStage_transition

set_option autoImplicit false

universe u v

namespace MasulloGRHFrechetCGAux

open MasulloGRH Topology Filter

lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

/-- Fréchet transfers along a continuous linear equivalence -/
lemma frechet_of_equiv {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (e : E ≃L[ℂ] F) (hF : IsFrechet F) : IsFrechet E := by
  obtain ⟨⟨ι, hι, p, hp⟩, ⟨hT2, hc⟩, hmet⟩ := hF
  haveI := hT2
  haveI := hmet
  haveI : IsTopologicalAddGroup F := hp.topologicalAddGroup
  have hemb : IsEmbedding e := e.toHomeomorph.isEmbedding
  have hws : WithSeminorms (p.comp (e : E →ₗ[ℂ] F)) := hemb.isInducing.withSeminorms hp
  haveI : IsTopologicalAddGroup E := hws.topologicalAddGroup
  refine ⟨⟨{q : Seminorm ℂ E // Continuous q}, ⟨⟨0, continuous_const⟩⟩, _, ws_all hws⟩,
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

end MasulloGRHFrechetCGAux

open MasulloGRH MasulloGRHFrechetCGAux in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (G1 : Subgroup G) (hG1 : ∀ g : G, g ∈ G1 ↔ m g = 1)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty)
    (hcg : IsCompactlyGeneratedSubgroup (⊤ : Subgroup (PontryaginDual G1))) :
    IsFrechet (ExpDecaySchwartz G m I) := by
  have hbot : IsGoodSubgroup (⊥ : Subgroup G) :=
    rposModulated_isGoodSubgroup_bot G m hm G1 hG1 hcg
  have hFr : IsFrechet (ExpDecayStage G m I ⊥) :=
    (expDecayStage_frechet_nuclear G m hm I hI hne ⊥ hbot).1
  have hsurj : Function.Surjective (ExpDecayStage.incl G m I ⊥) := by
    intro ϕ
    refine ⟨⟨ϕ, fun h hh g => ?_⟩, rfl⟩
    rw [Subgroup.mem_bot.1 hh, mul_one]
  let e : ExpDecayStage G m I ⊥ ≃ₗ[ℂ] ExpDecaySchwartz G m I :=
    LinearEquiv.ofBijective (ExpDecayStage.incl G m I ⊥) ⟨Subtype.val_injective, hsurj⟩
  have he : ∀ y, e y = ExpDecayStage.incl G m I ⊥ y := fun y => rfl
  have hcont : Continuous e := continuous_sInf_rng.2 fun _ ht => ht.2 ⊥ hbot
  have hcont' : Continuous e.symm := by
    obtain ⟨⟨ι, hι, p, hp⟩, -, -⟩ := hFr
    rw [continuous_iff_le_induced]
    letI t : TopologicalSpace (ExpDecaySchwartz G m I) :=
      TopologicalSpace.induced e.symm inferInstance
    have hws : WithSeminorms
        (p.comp (e.symm : ExpDecaySchwartz G m I →ₗ[ℂ] ExpDecayStage G m I ⊥)) :=
      LinearMap.withSeminorms_induced hp _
    haveI : IsTopologicalAddGroup (ExpDecaySchwartz G m I) := hws.topologicalAddGroup
    refine sInf_le ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, ws_all hws⟩, ?_⟩
    intro k hk
    obtain ⟨f, hfc, hf⟩ := expDecayStage_transition G m hm I hI hne k ⊥ hk hbot bot_le
    refine continuous_induced_rng.2 ?_
    have : (fun y : ExpDecayStage G m I k => e.symm y.1) = f := by
      funext y
      have h1 : y.1 = e (f y) := (hf y).symm
      rw [h1, LinearEquiv.symm_apply_apply]
    show @Continuous (ExpDecayStage G m I k) _ inferInstance _
      (fun y : ExpDecayStage G m I k => e.symm y.1)
    rw [this]
    exact hfc
  let E : ExpDecayStage G m I ⊥ ≃L[ℂ] ExpDecaySchwartz G m I :=
    { e with continuous_toFun := hcont, continuous_invFun := hcont' }
  exact frechet_of_equiv E.symm hFr

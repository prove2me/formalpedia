-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_equiv_elem_of_single_stage
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:16:30.20818+00:00
-- url     : https://prove2.me/submissions/341a7d0d-7dfb-464a-8d86-d2ef03418fc2

import Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel

set_option autoImplicit false

universe u v

namespace MasulloGRHSingleAux

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

/-- Fréchet transfers along a continuous linear equivalence, across universes -/
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

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- the inclusion of a structural pair, as a linear map -/
noncomputable def ofElemL {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : ElemSchwartz m n r s d →ₗ[ℂ] SchwartzBruhat H where
  toFun := SchwartzBruhat.ofElem Γ k π hs hπ
  map_add' f g := by
    apply Subtype.ext
    funext x
    show extendPullback Γ π (f + g).toFun x = extendPullback Γ π f.toFun x + extendPullback Γ π g.toFun x
    unfold extendPullback
    split_ifs
    · rfl
    · simp
  map_smul' c f := by
    apply Subtype.ext
    funext x
    show extendPullback Γ π (c • f).toFun x = c * extendPullback Γ π f.toFun x
    unfold extendPullback
    split_ifs
    · rfl
    · simp

lemma ofElem_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) :=
  continuous_sInf_rng.2 fun _ ht => ht.2 Γ k m n r s d π hs hπ

lemma ofElem_injective {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Function.Injective (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  intro g g' h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  funext e
  obtain ⟨x, hx⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd e)
  have := congrFun h' (x : H)
  simp only [SchwartzBruhat.ofElem, extendPullback, dif_pos x.2] at this
  rw [Subtype.coe_eta, hx, toAdd_ofAdd] at this
  exact this

end MasulloGRHSingleAux

open MasulloGRH MasulloGRHSingleAux in
theorem solution (H : Type u) [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ₀ k₀ : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
    (π₀ : Γ₀ →* Multiplicative (ElemGroup m n r s d)) (hs₀ : IsStructuralPair Γ₀ k₀)
    (hπ₀ : IsElemPresentation Γ₀ k₀ π₀)
    (hfac : ∀ (Γ k : Subgroup H) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      ∃ φ : ElemSchwartz m' n' r' s' d' →ₗ[ℂ] ElemSchwartz m n r s d, Continuous φ ∧
        ∀ g, SchwartzBruhat.ofElem Γ k π hs hπ g = SchwartzBruhat.ofElem Γ₀ k₀ π₀ hs₀ hπ₀ (φ g)) :
    Nonempty (ElemSchwartz m n r s d ≃L[ℂ] SchwartzBruhat H) ∧ IsFrechet (SchwartzBruhat H) := by
  set L := ofElemL Γ₀ k₀ π₀ hs₀ hπ₀ with hL
  have hinj : Function.Injective L := ofElem_injective Γ₀ k₀ π₀ hs₀ hπ₀
  have hsurj : Function.Surjective L := by
    intro f
    have hle : schwartzBruhatSubmodule H ≤
        Submodule.map (schwartzBruhatSubmodule H).subtype (LinearMap.range L) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨Γ, k, m', n', r', s', d', π, g, hs, hπ, rfl⟩
      obtain ⟨φ, -, hφ⟩ := hfac Γ k m' n' r' s' d' π hs hπ
      exact ⟨L (φ g), ⟨φ g, rfl⟩, by
        show (SchwartzBruhat.ofElem Γ₀ k₀ π₀ hs₀ hπ₀ (φ g)).1 = _
        rw [← hφ g]; rfl⟩
    obtain ⟨y, ⟨x, rfl⟩, hy⟩ := hle f.2
    exact ⟨x, Subtype.ext hy⟩
  let e : ElemSchwartz m n r s d ≃ₗ[ℂ] SchwartzBruhat H := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have he : ∀ y, e y = SchwartzBruhat.ofElem Γ₀ k₀ π₀ hs₀ hπ₀ y := fun y => rfl
  obtain ⟨hFr, -⟩ := elemSchwartz_frechet_nuclear_montel m n r s d hπ₀.1
  have hcont : Continuous e := ofElem_continuous Γ₀ k₀ π₀ hs₀ hπ₀
  have hcont' : Continuous e.symm := by
    obtain ⟨⟨ι, hι, p, hp⟩, -, -⟩ := hFr
    rw [continuous_iff_le_induced]
    letI t : TopologicalSpace (SchwartzBruhat H) :=
      TopologicalSpace.induced e.symm inferInstance
    have hws : WithSeminorms (p.comp (e.symm : SchwartzBruhat H →ₗ[ℂ] ElemSchwartz m n r s d)) :=
      LinearMap.withSeminorms_induced hp _
    haveI : IsTopologicalAddGroup (SchwartzBruhat H) := hws.topologicalAddGroup
    refine sInf_le ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, ws_all hws⟩, ?_⟩
    intro Γ k m' n' r' s' d' π hs hπ
    obtain ⟨φ, hφc, hφ⟩ := hfac Γ k m' n' r' s' d' π hs hπ
    refine continuous_induced_rng.2 ?_
    have : (e.symm ∘ SchwartzBruhat.ofElem Γ k π hs hπ) = φ := by
      funext g
      simp only [Function.comp_apply, hφ g, ← he, LinearEquiv.symm_apply_apply]
    rw [this]; exact hφc
  let E : ElemSchwartz m n r s d ≃L[ℂ] SchwartzBruhat H :=
    { e with continuous_toFun := hcont, continuous_invFun := hcont' }
  exact ⟨⟨E⟩, frechet_of_equiv E.symm hFr⟩

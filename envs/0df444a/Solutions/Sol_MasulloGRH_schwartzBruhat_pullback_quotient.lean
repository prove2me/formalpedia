-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_pullback_quotient
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:24:14.814587+00:00
-- url     : https://prove2.me/submissions/3dd067f3-e2fd-46c3-9807-99c38f48b292

import Theorems.Thm_MasulloGRH_isStructuralPair_comap_quotient
import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

universe u

namespace PullbackAux

open MasulloGRH

lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← Filter.tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

/-- a `WithSeminorms` topology, with any index, is locally convex -/
lemma lc_of_ws {E : Type u} [AddCommGroup E] [Module ℂ E] (t : TopologicalSpace E)
    {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : @WithSeminorms ℂ E ι _ _ _ p t) :
    IsLocallyConvexTopology E t := by
  letI := t
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  exact ⟨{q : Seminorm ℂ E // Continuous q}, ⟨⟨0, continuous_const⟩⟩, _, ws_all hp⟩

/-- an infimum of locally convex topologies is locally convex -/
lemma lc_sInf {E : Type u} [AddCommGroup E] [Module ℂ E] (S : Set (TopologicalSpace E))
    (hS : ∀ t ∈ S, IsLocallyConvexTopology E t) : IsLocallyConvexTopology E (sInf S) := by
  choose ι _ p hp using fun t : S => hS t.1 t.2
  rw [sInf_eq_iInf']
  exact lc_of_ws _ (withSeminorms_iInf (p := p) (t := fun t : S => t.1) hp)

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- the topology of `S(H)` is locally convex -/
lemma sb_lc : IsLocallyConvexTopology (SchwartzBruhat H) inferInstance :=
  lc_sInf _ fun _ ht => ht.1

/-- universal property of the inductive limit topology of `S(H)` -/
lemma sb_continuous_of_ofElem {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hX : IsLocallyConvexTopology X inferInstance) (Q : SchwartzBruhat H →ₗ[ℂ] X)
    (hQ : ∀ (Γ k : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π), Continuous (fun g => Q (SchwartzBruhat.ofElem Γ k π hs hπ g))) :
    Continuous Q := by
  obtain ⟨ι, hι, p, hp⟩ := hX
  rw [continuous_iff_le_induced]
  refine sInf_le ⟨lc_of_ws _ (LinearMap.withSeminorms_induced hp Q), fun Γ k m n r s d π hs hπ => ?_⟩
  exact continuous_induced_rng.2 (hQ Γ k m n r s d π hs hπ)

lemma ofElem_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) :=
  continuous_sInf_rng.2 fun _ ht => ht.2 Γ k m n r s d π hs hπ

end PullbackAux

open MasulloGRH PullbackAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') (hle : k' ≤ k) :
    ∃ P : SchwartzBruhat (G ⧸ k) →L[ℂ] SchwartzBruhat (G ⧸ k'),
      ∀ (f : SchwartzBruhat (G ⧸ k)) (x : G ⧸ k'),
        (P f).toFun x = f.toFun (QuotientGroup.map k' k (MonoidHom.id G) hle x) := by
  classical
  set p := QuotientGroup.map k' k (MonoidHom.id G) hle with hpdef
  have hpmk : ∀ g : G, p (QuotientGroup.mk g) = QuotientGroup.mk g := fun _ => rfl
  have hpc : Continuous p := continuous_coinduced_dom.2 continuous_quot_mk
  have hpo : IsOpenMap p := by
    intro W hW
    have : p '' W = (QuotientGroup.mk : G → G ⧸ k) '' ((QuotientGroup.mk : G → G ⧸ k') ⁻¹' W) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        exact ⟨g, hx, rfl⟩
      · rintro ⟨g, hg, rfl⟩; exact ⟨_, hg, rfl⟩
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ (hW.preimage continuous_quot_mk)
  -- pulled-back presentations
  have hpull : ∀ (Γ k₁ : Subgroup (G ⧸ k)) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k₁)
      (hπ : IsElemPresentation Γ k₁ π),
      ∃ (π' : Γ.comap p →* Multiplicative (ElemGroup m n r s d))
        (hs' : IsStructuralPair (Γ.comap p) (k₁.comap p))
        (hπ' : IsElemPresentation (Γ.comap p) (k₁.comap p) π'),
        ∀ g : ElemSchwartz m n r s d,
          extendPullback (Γ.comap p) π' g.toFun = extendPullback Γ π g.toFun ∘ p := by
    intro Γ k₁ m n r s d π hs hπ
    let pΓ : Γ.comap p →* Γ := (p.comp (Γ.comap p).subtype).codRestrict Γ (fun x => x.2)
    have hpΓc : Continuous pΓ := (hpc.comp continuous_subtype_val).subtype_mk _
    have hΓ'o : IsOpen ((Γ.comap p : Subgroup (G ⧸ k')) : Set (G ⧸ k')) := hs.1.preimage hpc
    have hpΓo : IsOpenMap pΓ := by
      intro W hW
      obtain ⟨W₀, hW₀, rfl⟩ := isOpen_induced_iff.1 hW
      have : pΓ '' (((↑) : Γ.comap p → G ⧸ k') ⁻¹' W₀) =
          ((↑) : Γ → G ⧸ k) ⁻¹' (p '' (W₀ ∩ (Γ.comap p : Set (G ⧸ k')))) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
        · rintro ⟨z, ⟨hz, hzΓ⟩, hzy⟩
          exact ⟨⟨z, hzΓ⟩, hz, Subtype.ext hzy⟩
      rw [this]
      exact (hpo _ (hW₀.inter hΓ'o)).preimage continuous_subtype_val
    have hpΓs : Function.Surjective pΓ := by
      intro y
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.1
      have hx : p (QuotientGroup.mk g) = y.1 := by rw [hpmk]; exact hg
      exact ⟨⟨QuotientGroup.mk g, show p (QuotientGroup.mk g) ∈ Γ by rw [hx]; exact y.2⟩,
        Subtype.ext hx⟩
    refine ⟨π.comp pΓ, isStructuralPair_comap_quotient G k k' hk hk' hle Γ k₁ hs,
      ⟨hπ.1, hπ.2.1.comp hpΓc, hπ.2.2.1.comp hpΓo, hπ.2.2.2.1.comp hpΓs, fun x => ?_⟩, fun g => ?_⟩
    · exact hπ.2.2.2.2 (pΓ x)
    · funext x
      unfold extendPullback
      by_cases hx : x ∈ Γ.comap p
      · have hx' : p x ∈ Γ := hx
        rw [dif_pos hx, Function.comp_apply, dif_pos hx']
        rfl
      · have hx' : p x ∉ Γ := hx
        rw [dif_neg hx, Function.comp_apply, dif_neg hx']
  -- membership
  have hmem : ∀ f ∈ schwartzBruhatSubmodule (G ⧸ k), f ∘ p ∈ schwartzBruhatSubmodule (G ⧸ k') := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨Γ, k₁, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hf
      obtain ⟨π', hs', hπ', he⟩ := hpull Γ k₁ m n r s d π hs hπ
      exact Submodule.subset_span ⟨_, _, m, n, r, s, d, π', g, hs', hπ', (he g).symm⟩
    | zero => exact Submodule.zero_mem _
    | add f₁ f₂ _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
    | smul c f _ h => exact Submodule.smul_mem _ c h
  let P : SchwartzBruhat (G ⧸ k) →ₗ[ℂ] SchwartzBruhat (G ⧸ k') :=
    { toFun := fun f => ⟨f.1 ∘ p, hmem f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hP : Continuous P := by
    refine sb_continuous_of_ofElem sb_lc P fun Γ k₁ m n r s d π hs hπ => ?_
    obtain ⟨π', hs', hπ', he⟩ := hpull Γ k₁ m n r s d π hs hπ
    have : (fun g => P (SchwartzBruhat.ofElem Γ k₁ π hs hπ g)) =
        SchwartzBruhat.ofElem (Γ.comap p) (k₁.comap p) π' hs' hπ' := by
      funext g
      apply Subtype.ext
      exact (he g).symm
    rw [this]
    exact ofElem_continuous _ _ _ _ _
  exact ⟨⟨P, hP⟩, fun f x => rfl⟩

-- Prove2me | solution 1 for MasulloGRH.expDecayStage_weighted_closedRange
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:53:31.371457+00:00
-- url     : https://prove2.me/submissions/603790ba-b964-4354-bc15-c44d14e92199

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_quotient_goodSubgroup_dual_compactlyGenerated
import Theorems.Thm_MasulloGRH_schwartzBruhat_average_mem
import Theorems.Thm_MasulloGRH_schwartzBruhat_descent_goodSubgroup
import Theorems.Thm_MasulloGRH_schwartzBruhat_exists_stages
import Theorems.Thm_MasulloGRH_schwartz_correspondence
import Theorems.Thm_MasulloGRH_schwartzBruhat_modulus_multiplier
import Theorems.Thm_MasulloGRH_expDecayStage_weighted_mem
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le
import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace QComapAux

open MasulloGRH Set Topology

variable {A B : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [LocallyCompactSpace A] [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]

/-- compact sets lift along open continuous surjections from a locally compact group -/
lemma exists_compact_lift (p : A →* B) (hpc : Continuous p) (hpo : IsOpenMap p)
    (hps : Function.Surjective p) (K : Set B) (hK : IsCompact K) :
    ∃ L : Set A, IsCompact L ∧ p '' L = K := by
  classical
  choose N hN using fun g : A => exists_compact_mem_nhds g
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun g : A => p '' interior (N g))
    (fun g => hpo _ isOpen_interior) (by
    intro x _
    obtain ⟨g, rfl⟩ := hps x
    exact mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hN g).2, rfl⟩)
  refine ⟨(⋃ g ∈ t, N g) ∩ p ⁻¹' K, ?_, ?_⟩
  · exact ((t.isCompact_biUnion fun g _ => (hN g).1)).inter_right (hK.isClosed.preimage hpc)
  · apply Subset.antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
    · intro y hy
      obtain ⟨g, hg, x, hx, rfl⟩ := by simpa using ht hy
      exact ⟨x, ⟨mem_biUnion hg (interior_subset hx), hy⟩, rfl⟩

/-- preimages of compactly generated subgroups under open continuous surjections with compact
kernel are compactly generated -/
lemma isCompactlyGenerated_comap (p : A →* B) (hpc : Continuous p) (hpo : IsOpenMap p)
    (hps : Function.Surjective p) (hK : IsCompact (p.ker : Set A)) (Γ : Subgroup B)
    (hΓ : IsCompactlyGeneratedSubgroup Γ) : IsCompactlyGeneratedSubgroup (Γ.comap p) := by
  obtain ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hcl⟩ := hΓ
  obtain ⟨L, hLc, hLU⟩ := exists_compact_lift p hpc hpo hps U hUc
  let U' : Set A := (fun x : A × A => x.1 * x.2) '' ((L ∪ {1}) ×ˢ (p.ker : Set A))
  have hU'c : IsCompact U' :=
    ((hLc.union isCompact_singleton).prod hK).image continuous_mul
  have hpU' : p '' U' = U ∪ {1} := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨l, c⟩, ⟨hl, hc⟩, rfl⟩, rfl⟩
      have hc1 : p c = 1 := hc
      simp only [map_mul, hc1, mul_one]
      rcases hl with hl | hl
      · exact Or.inl (hLU ▸ mem_image_of_mem p hl)
      · have h1 : l = 1 := hl
        rw [h1, map_one]; exact Or.inr rfl
    · rintro (hy | hy)
      · rw [← hLU] at hy
        obtain ⟨l, hl, rfl⟩ := hy
        exact ⟨l * 1, ⟨(l, 1), ⟨Or.inl hl, p.ker.one_mem⟩, rfl⟩, by simp⟩
      · rw [mem_singleton_iff.1 hy]
        exact ⟨1 * 1, ⟨(1, 1), ⟨Or.inr rfl, p.ker.one_mem⟩, rfl⟩, by simp⟩
  have hkerU' : (p.ker : Set A) ⊆ U' := fun c hc =>
    ⟨(1, c), ⟨Or.inr rfl, hc⟩, by simp⟩
  refine ⟨U', hU'c, ?_, ⟨p ⁻¹' V, hpc.continuousAt.preimage_mem_nhds (by rwa [map_one]), ?_⟩, ?_⟩
  · rintro _ ⟨⟨l, c⟩, ⟨hl, hc⟩, rfl⟩
    have hc1 : p c = 1 := hc
    show p (l * c) ∈ Γ
    rw [map_mul, hc1, mul_one]
    rcases hl with hl | hl
    · exact hUΓ (hLU ▸ mem_image_of_mem p hl)
    · have h1 : l = 1 := hl
      rw [h1, map_one]; exact Γ.one_mem
  · rintro x ⟨hxV, hxΓ⟩
    have : p x ∈ U := hVU ⟨hxV, hxΓ⟩
    rw [← hLU] at this
    obtain ⟨l, hl, hlx⟩ := this
    refine ⟨(l, l⁻¹ * x), ⟨Or.inl hl, ?_⟩, by simp⟩
    show p (l⁻¹ * x) = 1
    rw [map_mul, map_inv, hlx, inv_mul_cancel]
  · have hmap : (Subgroup.closure U').map p = Γ := by
      rw [MonoidHom.map_closure, hpU', Subgroup.closure_union, hcl, Subgroup.closure_singleton_one,
        sup_bot_eq]
    rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.2]
    intro c hc
    exact Subgroup.subset_closure (hkerU' hc)

end QComapAux

open MasulloGRH QComapAux Set Topology in
theorem isStructuralPair_comap_mk
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k' : Subgroup G)
    (hk' : IsGoodSubgroup k')
    (Γ k₁ : Subgroup (G ⧸ k')) (hs : IsStructuralPair Γ k₁) :
    IsStructuralPair (Γ.comap (QuotientGroup.mk' k')) (k₁.comap (QuotientGroup.mk' k')) := by
  classical
  haveI : IsClosed (k' : Set G) := hk'.1
  set p := QuotientGroup.mk' k' with hpdef
  have hpc : Continuous p := continuous_quot_mk
  have hpo : IsOpenMap p := fun W hW => QuotientGroup.isOpenMap_coe W hW
  have hps : Function.Surjective p := QuotientGroup.mk_surjective
  have hker : (p.ker : Set G) = (k' : Set G) := by rw [hpdef, QuotientGroup.ker_mk']
  have hkerc : IsCompact (p.ker : Set G) := by
    rw [hker]; exact isCompact_of_isGoodSubgroup G k' hk'
  let pc : G →ₜ* (G ⧸ k') := ⟨p, hpc⟩
  let Φ := PontryaginDual.map pc
  have hΦ : ∀ χ x, Φ χ x = χ (p x) := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    intro χ ψ h
    ext x
    obtain ⟨y, rfl⟩ := hps x
    have := congrArg (fun f : PontryaginDual G => f y) h
    simp only [hΦ] at this
    rw [this]
  have hind : IsInducing Φ := by
    refine ⟨le_antisymm (continuous_iff_le_induced.1 (map_continuous Φ)) ?_⟩
    show TopologicalSpace.induced Φ _ ≤ TopologicalSpace.induced
      (ContinuousMonoidHom.toContinuousMap) ContinuousMap.compactOpen
    rw [ContinuousMap.compactOpen_eq, induced_generateFrom_eq]
    refine le_generateFrom ?_
    rintro _ ⟨_, ⟨K, hK, U, hU, rfl⟩, rfl⟩
    obtain ⟨L, hL, hLK⟩ := exists_compact_lift p hpc hpo hps K hK
    refine ⟨{ψ : PontryaginDual G | MapsTo ψ L U}, ?_, ?_⟩
    · exact (ContinuousMap.isOpen_setOfPred_mapsTo (X := G) (Y := Circle) hL hU).preimage
        (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous
    · ext χ
      change MapsTo (fun g => χ (p g)) L U ↔ MapsTo (fun x => χ x) K U
      constructor
      · intro h y hy
        rw [← hLK] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact h hx
      · intro h x hx
        exact h (by rw [← hLK]; exact ⟨x, hx, rfl⟩)
  have hann : ∀ c : Subgroup (G ⧸ k'), annihilator (c.comap p) = Φ '' annihilator c := by
    intro c
    ext χ
    constructor
    · intro hχ
      let ψ0 : G ⧸ k' →* Circle := QuotientGroup.lift k' χ.toMonoidHom (fun g hg => by
          show χ g = 1
          apply hχ
          show (QuotientGroup.mk g : G ⧸ k') ∈ c
          rw [(QuotientGroup.eq_one_iff g).2 hg]; exact c.one_mem)
      have hψc : Continuous ψ0 := continuous_coinduced_dom.2 χ.continuous
      refine ⟨⟨ψ0, hψc⟩, fun y hy => ?_, ?_⟩
      · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
        show χ g = 1
        exact hχ _ (show p g ∈ c from hy)
      · ext x
        rfl
    · rintro ⟨ψ, hψ, rfl⟩ x hx
      rw [hΦ]; exact hψ _ hx
  -- the range is open
  have hrange : IsOpen (range Φ) := by
    have hr : range Φ = annihilator p.ker := by
      have := hann ⊥
      rw [show annihilator (⊥ : Subgroup (G ⧸ k')) = univ by ext χ; simp [annihilator],
        image_univ] at this
      rw [← this]; rfl
    rw [hr]
    haveI : CompactSpace p.ker := isCompact_iff_compactSpace.mp hkerc
    let r := PontryaginDual.map (⟨p.ker.subtype, continuous_subtype_val⟩ : p.ker →ₜ* G)
    have : annihilator p.ker = r ⁻¹' {1} := by
      ext χ
      simp only [annihilator, mem_setOf_eq, mem_preimage, mem_singleton_iff]
      constructor
      · intro h; ext x; exact congrArg _ (h x x.2)
      · intro h x hx
        have := congrArg (fun f : PontryaginDual p.ker => f ⟨x, hx⟩) h
        exact this
    rw [this]
    exact (isOpen_discrete _).preimage (map_continuous r)
  have hopen : ∀ W, IsOpen W → IsOpen (Φ '' W) := by
    intro W hW
    obtain ⟨W'', hW'', rfl⟩ := isOpen_induced_iff.1 (hind.eq_induced ▸ hW)
    rw [image_preimage_eq_inter_range]
    exact hW''.inter hrange
  refine ⟨hs.1.preimage hpc, isCompactlyGenerated_comap p hpc hpo hps hkerc Γ hs.2.1, ⟨?_, ?_, ?_⟩,
    Subgroup.comap_mono hs.2.2.2⟩
  · exact hs.2.2.1.1.preimage hpc
  · rw [hann]; exact hopen _ hs.2.2.1.2.1
  · obtain ⟨A₁, hA₁, U, hUc, hUA, ⟨V, hV, hVU⟩, hcl⟩ := hs.2.2.1.2.2
    refine ⟨A₁.map Φ.toMonoidHom, ?_, Φ '' U, hUc.image (map_continuous Φ), ?_, ?_, ?_⟩
    · rw [Subgroup.coe_map, hann]; exact congrArg _ hA₁
    · exact image_mono hUA
    · rw [hind.nhds_eq_comap, map_one] at hV
      obtain ⟨V'', hV'', hV''V⟩ := hV
      refine ⟨V'', hV'', ?_⟩
      rintro y ⟨hyV, ⟨a, ha, rfl⟩⟩
      exact ⟨a, hVU ⟨hV''V hyV, ha⟩, rfl⟩
    · rw [← hcl, MonoidHom.map_closure]; rfl


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
theorem schwartzBruhat_pullback_mk
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k : Subgroup G)
    (hk : IsGoodSubgroup k) :
    ∃ P : SchwartzBruhat (G ⧸ k) →L[ℂ] SchwartzBruhat G,
      ∀ (f : SchwartzBruhat (G ⧸ k)) (x : G), (P f).toFun x = f.toFun (QuotientGroup.mk x) := by
  classical
  haveI : IsClosed (k : Set G) := hk.1
  set p := QuotientGroup.mk' k with hpdef
  have hpc : Continuous p := continuous_quot_mk
  have hpo : IsOpenMap p := fun W hW => QuotientGroup.isOpenMap_coe W hW
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
    have hΓ'o : IsOpen ((Γ.comap p : Subgroup (G)) : Set (G)) := hs.1.preimage hpc
    have hpΓo : IsOpenMap pΓ := by
      intro W hW
      obtain ⟨W₀, hW₀, rfl⟩ := isOpen_induced_iff.1 hW
      have : pΓ '' (((↑) : Γ.comap p → G) ⁻¹' W₀) =
          ((↑) : Γ → G ⧸ k) ⁻¹' (p '' (W₀ ∩ (Γ.comap p : Set (G)))) := by
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
      exact ⟨⟨g, show p g ∈ Γ by rw [show p g = y.1 from hg]; exact y.2⟩, Subtype.ext hg⟩
    refine ⟨π.comp pΓ, isStructuralPair_comap_mk G k hk Γ k₁ hs,
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
  have hmem : ∀ f ∈ schwartzBruhatSubmodule (G ⧸ k), f ∘ p ∈ schwartzBruhatSubmodule (G) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨Γ, k₁, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hf
      obtain ⟨π', hs', hπ', he⟩ := hpull Γ k₁ m n r s d π hs hπ
      exact Submodule.subset_span ⟨_, _, m, n, r, s, d, π', g, hs', hπ', (he g).symm⟩
    | zero => exact Submodule.zero_mem _
    | add f₁ f₂ _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
    | smul c f _ h => exact Submodule.smul_mem _ c h
  let P : SchwartzBruhat (G ⧸ k) →ₗ[ℂ] SchwartzBruhat (G) :=
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


namespace AvgAux

open MasulloGRH MeasureTheory

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

lemma avg_eq_haar (k : Subgroup H) (hk : IsCompact (k : Set H)) (F : H → ℂ) (x : H) :
    letI : MeasurableSpace k := borel k
    haveI : BorelSpace k := ⟨rfl⟩
    haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
    schwartzBruhatAverage ⊤ k F x = ∫ y : k, F (x * y) ∂(Measure.haarMeasure ⊤) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h2 : subgroupHaar k = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk]
  rw [h2]

lemma avg_add (k : Subgroup H) (hk : IsCompact (k : Set H)) (F₁ F₂ : H → ℂ)
    (h₁ : Continuous F₁) (h₂ : Continuous F₂) (x : H) :
    schwartzBruhatAverage ⊤ k (F₁ + F₂) x =
      schwartzBruhatAverage ⊤ k F₁ x + schwartzBruhatAverage ⊤ k F₂ x := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  rw [avg_eq_haar k hk, avg_eq_haar k hk, avg_eq_haar k hk]
  have hi : ∀ F : H → ℂ, Continuous F →
      Integrable (fun y : k => F (x * y)) (Measure.haarMeasure ⊤) := by
    intro F hF
    have hc : Continuous (fun y : k => F (x * y)) :=
      hF.comp (continuous_const.mul continuous_subtype_val)
    exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)
  simp only [Pi.add_apply]
  exact integral_add (hi F₁ h₁) (hi F₂ h₂)

lemma avg_mul_left (k : Subgroup H) (w F : H → ℂ) (x : H)
    (hw : ∀ y ∈ k, w (x * y) = w x) :
    schwartzBruhatAverage ⊤ k (fun z => w z * F z) x = w x * schwartzBruhatAverage ⊤ k F x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have : (fun y : k => w (x * y) * F (x * y)) = fun y : k => w x * F (x * y) :=
    funext fun y => by rw [hw y y.2]
  simp only [this]
  exact integral_const_mul _ _

lemma avg_smul (k : Subgroup H) (c : ℂ) (F : H → ℂ) (x : H) :
    schwartzBruhatAverage ⊤ k (c • F) x = c * schwartzBruhatAverage ⊤ k F x :=
  avg_mul_left k (fun _ => c) F x (fun _ _ => rfl)

lemma avg_congr (k : Subgroup H) (F F' : H → ℂ) (x : H)
    (h : ∀ y ∈ k, F (x * y) = F' (x * y)) :
    schwartzBruhatAverage ⊤ k F x = schwartzBruhatAverage ⊤ k F' x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have : (fun y : k => F (x * y)) = fun y : k => F' (x * y) := funext fun y => h y y.2
  simp only [this]

lemma avg_mul_inv (k : Subgroup H) (hk : IsCompact (k : Set H)) (F : H → ℂ) (x h : H)
    (hh : h ∈ k) :
    schwartzBruhatAverage ⊤ k F (x * h) = schwartzBruhatAverage ⊤ k F x := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  rw [avg_eq_haar k hk, avg_eq_haar k hk]
  have := integral_mul_left_eq_self (μ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k))
    (fun y : k => F (x * y)) (⟨h, hh⟩ : k)
  rw [← this]
  congr 1
  funext y
  simp [mul_assoc]

lemma avg_continuous (k : Subgroup H) (hk : IsCompact (k : Set H)) [LocallyCompactSpace H] [FirstCountableTopology H]
    (F : H → ℂ) (hF : Continuous F) : Continuous (schwartzBruhatAverage ⊤ k F) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  have : schwartzBruhatAverage ⊤ k F = fun x => ∫ y : k, F (x * y) ∂(Measure.haarMeasure ⊤) :=
    funext fun x => avg_eq_haar k hk F x
  rw [this]
  have hc : Continuous (Function.uncurry fun (x : H) (y : k) => F (x * y)) :=
    hF.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))
  have := continuous_parametric_integral_of_continuous (μ := Measure.haarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts k)) hc isCompact_univ
  simpa [Measure.restrict_univ] using this

end AvgAux

open MasulloGRH AvgAux in
/-- membership half of the pushforward (continuity still open) -/
theorem pushforward_mem
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') (F : SchwartzBruhat (G ⧸ k')) :
    (fun x : G ⧸ k => schwartzBruhatAverage ⊤ k (fun z => F.toFun (QuotientGroup.mk z)) x.out)
      ∈ schwartzBruhatSubmodule (G ⧸ k) := by
  obtain ⟨P, hP⟩ := schwartzBruhat_pullback_mk G k' hk'
  have hf : (fun z : G => F.toFun (QuotientGroup.mk z)) ∈ schwartzBruhatSubmodule G := by
    have := (P F).2
    convert this using 1
    funext z; exact (hP F z).symm
  exact schwartzBruhat_descent_goodSubgroup G k hk _
    (schwartzBruhat_average_mem G k hk _ hf)
    (fun h hh g => avg_mul_inv k (isCompact_of_isGoodSubgroup G k hk) _ g h hh)



namespace ElemContAux

open MasulloGRH Topology

variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma lift_quot : IsQuotientMap (fun xt : (Fin m → ℝ) × (Fin n → ℝ) =>
    ((xt.1, fun j => ((xt.2 j : ℝ) : UnitAddCircle)) : (Fin m → ℝ) × (Fin n → UnitAddCircle))) := by
  have hmk : IsOpenMap (fun x : ℝ => (x : UnitAddCircle)) := QuotientAddGroup.isOpenMap_coe
  have hpi : IsOpenMap (fun t : Fin n → ℝ => fun j => ((t j : ℝ) : UnitAddCircle)) :=
    IsOpenMap.piMap (f := fun _ : Fin n => fun x : ℝ => (x : UnitAddCircle)) (fun _ => hmk)
      (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)
  have hmkc : Continuous (fun x : ℝ => (x : UnitAddCircle)) := AddCircle.continuous_mk' 1
  refine IsOpenMap.isQuotientMap ((IsOpenMap.id).prodMap hpi) (by fun_prop) ?_
  rintro ⟨x, z⟩
  choose t ht using fun j => QuotientAddGroup.mk_surjective (z j)
  exact ⟨(x, t), by simp only [Prod.mk.injEq, true_and]; funext j; exact ht j⟩

lemma rapid_continuous (g : ElemGroup m n r s d → ℂ) (hg : IsRapidDecay g) : Continuous g := by
  let e : ElemGroup m n r s d ≃ₜ ((Fin m → ℝ) × (Fin n → UnitAddCircle)) ×
      ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) :=
    (Homeomorph.prodAssoc _ _ _).symm
  have : g = (fun p => g (e.symm p)) ∘ e := by funext x; simp
  rw [this]
  refine Continuous.comp ?_ e.continuous
  refine continuous_prod_of_discrete_right.2 fun ab => ?_
  refine (lift_quot.continuous_iff).2 ?_
  have := (hg.1 ab.1 ab.2).continuous
  exact this

lemma elem_continuous (g : ElemSchwartz m n r s d) : Continuous g.toFun := by
  obtain ⟨f, hf⟩ := g
  show Continuous f
  induction hf using Submodule.span_induction with
  | mem f hf => exact rapid_continuous f hf
  | zero => exact continuous_const
  | add f₁ f₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul c f _ h => exact continuous_const.mul h

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma extendPullback_continuous (Γ : Subgroup G) (hΓ : IsOpen (Γ : Set G))
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπ : Continuous π)
    (g : ElemGroup m n r s d → ℂ) (hg : Continuous g) : Continuous (extendPullback Γ π g) := by
  classical
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_isOpen Γ hΓ
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Γ
  · have hc : Continuous fun y : Γ => g (Multiplicative.toAdd (π y)) :=
      hg.comp (continuous_toAdd.comp hπ)
    have : ContinuousAt (fun y : Γ => extendPullback Γ π g y) ⟨x, hx⟩ := by
      have he : (fun y : Γ => extendPullback Γ π g y) = fun y : Γ => g (Multiplicative.toAdd (π y)) := by
        funext y; unfold extendPullback; rw [dif_pos (show (y : G) ∈ Γ from y.2)]
      rw [he]; exact hc.continuousAt
    exact (hΓ.isOpenEmbedding_subtypeVal.continuousAt_iff (g := extendPullback Γ π g) (x := ⟨x, hx⟩)).1 this
  · refine (continuousAt_const (y := (0:ℂ))).congr ?_
    filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    unfold extendPullback; rw [dif_neg (show y ∉ Γ from hy)]

lemma sb_fun_continuous (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hf
    exact extendPullback_continuous Γ hs.1 π hπ.2.1 _ (elem_continuous g)
  | zero => exact continuous_const
  | add f₁ f₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul c f _ h => exact continuous_const.mul h

end ElemContAux


namespace AvgMemAux

open MasulloGRH MeasureTheory

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

lemma average_eq (k₀ : Subgroup H) (hk₀ : IsCompact (k₀ : Set H)) (f : H → ℂ)
    (hf : ∀ x, ∀ y ∈ k₀, f (x * y) = f x) (x : H) :
    schwartzBruhatAverage ⊤ k₀ f x = f x := by
  letI : MeasurableSpace k₀ := borel k₀
  haveI : BorelSpace k₀ := ⟨rfl⟩
  haveI : CompactSpace k₀ := isCompact_iff_compactSpace.mp hk₀
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h1 : (fun y : k₀ => f (x * y)) = fun _ => f x := funext fun y => hf x y y.2
  have h2 : subgroupHaar k₀ = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk₀]
  simp only [h1, h2, integral_const]
  have h3 : (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k₀)) Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts k₀))
    simpa using this
  simp [measureReal_def, h3]


lemma avg_eq_haar (k : Subgroup H) (hk : IsCompact (k : Set H)) (F : H → ℂ) (x : H) :
    letI : MeasurableSpace k := borel k
    haveI : BorelSpace k := ⟨rfl⟩
    haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
    schwartzBruhatAverage ⊤ k F x = ∫ y : k, F (x * y) ∂(Measure.haarMeasure ⊤) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h2 : subgroupHaar k = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk]
  rw [h2]

lemma avg_subgroupOf [SecondCountableTopology H] (Ω k : Subgroup H) (hkΩ : k ≤ Ω)
    (hk : IsCompact (k : Set H)) (F : H → ℂ) (p : Ω) :
    schwartzBruhatAverage ⊤ (k.subgroupOf Ω) (fun x : Ω => F x) p =
      schwartzBruhatAverage ⊤ k F p := by
  have hk2 : IsCompact ((k.subgroupOf Ω : Subgroup Ω) : Set Ω) := by
    rw [Subtype.isCompact_iff]
    have : ((↑) : Ω → H) '' ((k.subgroupOf Ω : Subgroup Ω) : Set Ω) = (k : Set H) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hkΩ hx⟩, hx, rfl⟩
    rw [this]; exact hk
  haveI : SecondCountableTopology k := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology Ω := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (k.subgroupOf Ω) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  letI : MeasurableSpace (k.subgroupOf Ω) := borel _
  haveI : BorelSpace (k.subgroupOf Ω) := ⟨rfl⟩
  haveI : CompactSpace (k.subgroupOf Ω) := isCompact_iff_compactSpace.mp hk2
  rw [avg_eq_haar _ hk2, avg_eq_haar k hk]
  let e : (k.subgroupOf Ω) ≃* k := Subgroup.subgroupOfEquivOfLe hkΩ
  have hec : Continuous e := by
    show Continuous fun x : k.subgroupOf Ω => (⟨x.1.1, x.2⟩ : k)
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hsymm : Continuous e.symm :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  let E : (k.subgroupOf Ω) ≃ₜ k := ⟨e.toEquiv, hec, hsymm⟩
  haveI := MulEquiv.isHaarMeasure_map
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω))) e hec hsymm
  have hmap : Measure.map e
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω))) =
      Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k) := by
    rw [Measure.haarMeasure_unique (Measure.map e
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω)))) ⊤]
    have h1 : (Measure.map e (Measure.haarMeasure
        (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω))))
        ((⊤ : TopologicalSpace.PositiveCompacts k) : Set k) = 1 := by
      rw [Measure.map_apply hec.measurable (by simp)]
      have := Measure.haarMeasure_self
        (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (k.subgroupOf Ω)))
      simpa using this
    rw [h1, one_smul]
  rw [← hmap]
  exact (E.measurableEmbedding.integral_map (fun y : k => F (↑p * ↑y))).symm


lemma avg_mul_left (k : Subgroup H) (w F : H → ℂ) (x : H)
    (hw : ∀ y ∈ k, w (x * y) = w x) :
    schwartzBruhatAverage ⊤ k (fun z => w z * F z) x = w x * schwartzBruhatAverage ⊤ k F x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have : (fun y : k => w (x * y) * F (x * y)) = fun y : k => w x * F (x * y) :=
    funext fun y => by rw [hw y y.2]
  simp only [this]
  exact integral_const_mul _ _

lemma avg_congr (k : Subgroup H) (F F' : H → ℂ) (x : H)
    (h : ∀ y ∈ k, F (x * y) = F' (x * y)) :
    schwartzBruhatAverage ⊤ k F x = schwartzBruhatAverage ⊤ k F' x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have : (fun y : k => F (x * y)) = fun y : k => F' (x * y) := funext fun y => h y y.2
  simp only [this]

end AvgMemAux

open MasulloGRH AvgMemAux Set Topology in
theorem stage_push
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k : Subgroup G) (hk : IsGoodSubgroup k)
    (Γ k₁ : Subgroup G) {m n r s : ℕ} {d : Fin s → ℕ}
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k₁)
    (hπ : IsElemPresentation Γ k₁ π) :
    ∃ (Γ' : Subgroup (G ⧸ k)) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π' : Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' ⊥)
      (hπ' : IsElemPresentation Γ' ⊥ π')
      (T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d'), Continuous T ∧
      ∀ g : ElemSchwartz m n r s d, ∀ x : G ⧸ k,
        schwartzBruhatAverage ⊤ k (extendPullback Γ π g.toFun) x.out =
          extendPullback Γ' π' (T g).toFun x := by
  classical
  haveI : IsClosed (k : Set G) := hk.1
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hk
  -- the quotient
  let q : G →* G ⧸ k := QuotientGroup.mk' k
  have hqc : Continuous q := continuous_quot_mk
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  let Γ' : Subgroup (G ⧸ k) := Γ.map q
  let Ω : Subgroup G := Γ'.comap q
  have hΓΩ : Γ ≤ Ω := Subgroup.le_comap_map q Γ
  have hkΩ : k ≤ Ω := fun x hx => by
    show q x ∈ Γ'
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).2 hx]; exact Γ'.one_mem
  have hΓo : IsOpen (Γ : Set G) := hs.1
  have hΩo : IsOpen (Ω : Set G) := Subgroup.isOpen_mono hΓΩ hΓo
  have hΓ'o : IsOpen (Γ' : Set (G ⧸ k)) := by
    rw [Subgroup.coe_map]; exact hqo _ hΓo
  have hΓ'cg : IsCompactlyGeneratedSubgroup Γ' := by
    obtain ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hcl⟩ := hs.2.1
    refine ⟨q '' U, hUc.image hqc, ?_, ⟨q '' (V ∩ Γ), ?_, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hUΓ hx, rfl⟩
    · have := hqo.image_mem_nhds (Filter.inter_mem hV (hΓo.mem_nhds Γ.one_mem))
      rwa [map_one] at this
    · rintro _ ⟨⟨x, hx, rfl⟩, -⟩; exact ⟨x, hVU hx, rfl⟩
    · rw [← MonoidHom.map_closure, hcl]
  have hbot : IsGoodSubgroup (⊥ : Subgroup (G ⧸ k)) := by
    refine ⟨?_, ?_, ⊤, ?_, quotient_goodSubgroup_dual_compactlyGenerated G k hk⟩
    · show IsClosed ((⊥ : Subgroup (G ⧸ k)) : Set (G ⧸ k))
      rw [Subgroup.coe_bot]; exact isClosed_singleton
    · have : annihilator (⊥ : Subgroup (G ⧸ k)) = Set.univ := by
        ext χ; simp [annihilator]
      rw [this]; exact isOpen_univ
    · ext χ; simp [annihilator]
  have hs' : IsStructuralPair Γ' ⊥ := ⟨hΓ'o, hΓ'cg, hbot, bot_le⟩
  obtain ⟨m', n', r', s', d', π', hπ'⟩ := exists_elemPresentation_of_isStructuralPair (G ⧸ k) Γ' ⊥ hs'
  -- the groups for the correspondence
  haveI : LocallyCompactSpace Ω := hΩo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let P₀ : Subgroup Ω := Γ.subgroupOf Ω
  have hP₀ : IsOpen (P₀ : Set Ω) := by
    rw [Subgroup.coe_subgroupOf]; exact hΓo.preimage continuous_subtype_val
  let e := Subgroup.subgroupOfEquivOfLe hΓΩ
  have hec : Continuous e := by
    show Continuous fun x : P₀ => (⟨x.1.1, x.2⟩ : Γ)
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hsymm : Continuous e.symm :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  let E : P₀ ≃ₜ Γ := ⟨e.toEquiv, hec, hsymm⟩
  have heo : IsOpenMap e := E.isOpenMap
  let α : P₀ →* Multiplicative (ElemGroup m n r s d) :=
    π.comp e.toMonoidHom
  have hαc : Continuous α := hπ.2.1.comp hec
  have hαo : IsOpenMap α := hπ.2.2.1.comp heo
  have hαk : IsCompact {x : P₀ | α x = 1} := by
    have hK : IsCompact {y : Γ | π y = 1} := by
      rw [Subtype.isCompact_iff]
      have : ((↑) : Γ → G) '' {y : Γ | π y = 1} = (k₁ : Set G) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩; exact (hπ.2.2.2.2 y).1 hy
        · intro hx; exact ⟨⟨x, hs.2.2.2 hx⟩, (hπ.2.2.2.2 _).2 hx, rfl⟩
      rw [this]; exact isCompact_of_isGoodSubgroup G k₁ hs.2.2.1
    exact E.isCompact_preimage.2 hK
  let qΩ : Ω →* Γ' := (q.comp Ω.subtype).codRestrict Γ' (fun x => x.2)
  let β : Ω →* Multiplicative (ElemGroup m' n' r' s' d') := π'.comp qΩ
  have hqΩc : Continuous qΩ := (hqc.comp continuous_subtype_val).subtype_mk _
  have hβc : Continuous β := hπ'.2.1.comp hqΩc
  have hqΩo : IsOpenMap qΩ := by
    intro W hW
    obtain ⟨W₀, hW₀, rfl⟩ := isOpen_induced_iff.1 hW
    have : qΩ '' (((↑) : Ω → G) ⁻¹' W₀) = ((↑) : Γ' → G ⧸ k) ⁻¹' (q '' (W₀ ∩ Ω)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hzΩ⟩, hzy⟩
        exact ⟨⟨z, hzΩ⟩, hz, Subtype.ext hzy⟩
    rw [this]
    exact (hqo _ (hW₀.inter hΩo)).preimage continuous_subtype_val
  have hβo : IsOpenMap β := hπ'.2.2.1.comp hqΩo
  have hβker : ∀ x : Ω, β x = 1 ↔ (x : G) ∈ k := by
    intro x
    rw [show β x = π' (qΩ x) from rfl, hπ'.2.2.2.2, Subgroup.mem_bot]
    exact QuotientGroup.eq_one_iff _
  have hβk : IsCompact {x : Ω | β x = 1} := by
    rw [Subtype.isCompact_iff]
    have : ((↑) : Ω → G) '' {x : Ω | β x = 1} = (k : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact (hβker y).1 hy
      · intro hx; exact ⟨⟨x, hkΩ hx⟩, (hβker _).2 hx, rfl⟩
    rw [this]; exact hkc
  obtain ⟨T, hTc, hT⟩ := schwartz_correspondence Ω P₀ hP₀ m n r s d hπ.1
    α hαc hαo hαk m' n' r' s' d' β hβc hβo hβk
  refine ⟨Γ', m', n', r', s', d', π', hs', hπ', T, hTc, fun g => ?_⟩
  set f := extendPullback Γ π g.toFun with hfΓ
  have hext : ∀ x : Ω, extendPullback P₀ α g.toFun x = f x := by
    intro x
    rw [hfΓ]
    by_cases hx : (x : G) ∈ Γ
    · have hx' : x ∈ P₀ := hx
      unfold extendPullback
      rw [dif_pos hx', dif_pos hx]
      rfl
    · have hx' : x ∉ P₀ := hx
      unfold extendPullback
      rw [dif_neg hx', dif_neg hx]
  have hβker' : β.ker = k.subgroupOf Ω := by
    ext x; rw [MonoidHom.mem_ker, hβker]; rfl
  have havg : ∀ p : Ω, (T g).toFun (Multiplicative.toAdd (β p)) = schwartzBruhatAverage ⊤ k f p := by
    intro p
    rw [(hT g).1 p, hβker']
    have : extendPullback P₀ α g.toFun = fun x : Ω => f x := funext hext
    rw [this, avg_subgroupOf Ω k hkΩ hkc f p]
  have hΩeq : Ω = Γ ⊔ k := by
    show Subgroup.comap q (Subgroup.map q Γ) = Γ ⊔ k
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hΩcg : IsCompactlyGeneratedSubgroup Ω := by
    obtain ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hcl⟩ := hs.2.1
    refine ⟨U ∪ k, hUc.union hkc, Set.union_subset (hUΓ.trans hΓΩ) hkΩ,
      ⟨V ∩ Γ, Filter.inter_mem hV (hΓo.mem_nhds Γ.one_mem), ?_⟩, ?_⟩
    · rintro x ⟨⟨hxV, hxΓ⟩, -⟩; exact Or.inl (hVU ⟨hxV, hxΓ⟩)
    · rw [Subgroup.closure_union, hcl, Subgroup.closure_eq, hΩeq]
  have hβs : Function.Surjective β := by
    intro e'
    obtain ⟨y, rfl⟩ := hπ'.2.2.2.1 e'
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hΓΩ hx⟩, by show π' (qΩ _) = π' y; congr 1; exact Subtype.ext hxy⟩
  have hs'' : IsStructuralPair Ω k := ⟨hΩo, hΩcg, hk, hkΩ⟩
  have hπ'' : IsElemPresentation Ω k β := ⟨hπ'.1, hβc, hβo, hβs, hβker⟩
  have hfun : schwartzBruhatAverage ⊤ k f = extendPullback Ω β (T g).toFun := by
    funext x
    by_cases hx : x ∈ Ω
    · unfold extendPullback
      rw [dif_pos hx, havg ⟨x, hx⟩]
    · unfold extendPullback
      rw [dif_neg hx]
      have h0 : schwartzBruhatAverage ⊤ k f x = schwartzBruhatAverage ⊤ k (fun z => (0 : ℂ) * f z) x := by
        refine avg_congr k _ _ x fun y hy => ?_
        rw [zero_mul, hfΓ]
        unfold extendPullback
        rw [dif_neg]
        intro hxy
        apply hx
        have := Ω.mul_mem (hΓΩ hxy) (Ω.inv_mem (hkΩ hy))
        simpa using this
      rw [h0, avg_mul_left k (fun _ => (0 : ℂ)) f x (fun _ _ => rfl), zero_mul]
  intro x
  rw [hfun]
  have hmem : x.out ∈ Ω ↔ x ∈ Γ' := by
    show q x.out ∈ Γ' ↔ _
    rw [show q x.out = x from QuotientGroup.out_eq' x]
  by_cases hx : x ∈ Γ'
  · unfold extendPullback
    rw [dif_pos (hmem.2 hx), dif_pos hx]
    have hq : (qΩ ⟨x.out, hmem.2 hx⟩ : Γ') = ⟨x, hx⟩ := Subtype.ext (QuotientGroup.out_eq' x)
    show (T g).toFun (Multiplicative.toAdd (π' (qΩ ⟨x.out, hmem.2 hx⟩))) = _
    rw [hq]
  · unfold extendPullback
    rw [dif_neg (mt hmem.1 hx), dif_neg hx]


open MasulloGRH QComapAux PullbackAux AvgAux ElemContAux AvgMemAux Set Topology in
theorem pushforward_aux
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') :
    ∃ Q : SchwartzBruhat (G ⧸ k') →L[ℂ] SchwartzBruhat (G ⧸ k),
      ∀ (F : SchwartzBruhat (G ⧸ k')) (x : G ⧸ k),
        (Q F).toFun x = schwartzBruhatAverage ⊤ k (fun z => F.toFun (QuotientGroup.mk z)) x.out := by
  classical
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hk
  obtain ⟨P, hP⟩ := schwartzBruhat_pullback_mk G k' hk'
  have hPf : ∀ F : SchwartzBruhat (G ⧸ k'), (P F).1 = fun z => F.toFun (QuotientGroup.mk z) :=
    fun F => funext (hP F)
  have hcont : ∀ F : SchwartzBruhat (G ⧸ k'),
      Continuous (fun z : G => F.toFun (QuotientGroup.mk z)) := fun F => by
    rw [← hPf]; exact sb_fun_continuous _ (P F).2
  let Q : SchwartzBruhat (G ⧸ k') →ₗ[ℂ] SchwartzBruhat (G ⧸ k) :=
    { toFun := fun F => ⟨_, pushforward_mem G k k' hk hk' F⟩
      map_add' := fun F₁ F₂ => by
        apply Subtype.ext; funext x
        show schwartzBruhatAverage ⊤ k ((fun z => F₁.toFun (QuotientGroup.mk z)) +
            fun z => F₂.toFun (QuotientGroup.mk z)) x.out = _ + _
        exact avg_add k hkc _ _ (hcont F₁) (hcont F₂) x.out
      map_smul' := fun c F => by
        apply Subtype.ext; funext x
        show schwartzBruhatAverage ⊤ k (c • fun z => F.toFun (QuotientGroup.mk z)) x.out =
          c * schwartzBruhatAverage ⊤ k (fun z => F.toFun (QuotientGroup.mk z)) x.out
        exact avg_smul k c _ x.out }
  haveI : IsClosed (k' : Set G) := hk'.1
  set p := QuotientGroup.mk' k' with hpdef
  have hpc : Continuous p := continuous_quot_mk
  have hpo : IsOpenMap p := fun W hW => QuotientGroup.isOpenMap_coe W hW
  -- pulled-back presentations
  have hpull : ∀ (Γ k₁ : Subgroup (G ⧸ k')) (m n r s : ℕ) (d : Fin s → ℕ)
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
    have hΓ'o : IsOpen ((Γ.comap p : Subgroup (G)) : Set (G)) := hs.1.preimage hpc
    have hpΓo : IsOpenMap pΓ := by
      intro W hW
      obtain ⟨W₀, hW₀, rfl⟩ := isOpen_induced_iff.1 hW
      have : pΓ '' (((↑) : Γ.comap p → G) ⁻¹' W₀) =
          ((↑) : Γ → G ⧸ k') ⁻¹' (p '' (W₀ ∩ (Γ.comap p : Set (G)))) := by
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
      exact ⟨⟨g, show p g ∈ Γ by rw [show p g = y.1 from hg]; exact y.2⟩, Subtype.ext hg⟩
    refine ⟨π.comp pΓ, isStructuralPair_comap_mk G k' hk' Γ k₁ hs,
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
  refine ⟨⟨Q, ?_⟩, fun F x => rfl⟩
  refine sb_continuous_of_ofElem sb_lc Q fun Γ k₁ m n r s d π hs hπ => ?_
  obtain ⟨π', hs', hπ', he⟩ := hpull Γ k₁ m n r s d π hs hπ
  obtain ⟨Γ', m', n', r', s', d', π'', hs'', hπ'', T, hTc, hT⟩ :=
    stage_push G k hk (Γ.comap p) (k₁.comap p) π' hs' hπ'
  have : (fun g => Q (SchwartzBruhat.ofElem Γ k₁ π hs hπ g)) =
      SchwartzBruhat.ofElem Γ' ⊥ π'' hs'' hπ'' ∘ T := by
    funext g
    apply Subtype.ext
    funext x
    show schwartzBruhatAverage ⊤ k (fun z => extendPullback Γ π g.toFun (p z)) x.out =
      extendPullback Γ' π'' (T g).toFun x
    rw [← hT g x, he g]
    rfl
  rw [this]
  exact (ofElem_continuous _ _ _ _ _).comp hTc

namespace MasulloGRHWMemAux

open MasulloGRH

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- the kernel of a module as a subgroup -/
def modKer {m : G → ℝ} (hm : IsModule m) : Subgroup G where
  carrier := {g | m g = 1}
  one_mem' := by
    show m 1 = 1
    have h := hm.map_mul 1 1
    rw [mul_one] at h
    have hp := hm.pos 1
    nlinarith
  mul_mem' {a b} ha hb := by
    show m (a * b) = 1
    rw [hm.map_mul, show m a = 1 from ha, show m b = 1 from hb, one_mul]
  inv_mem' {a} ha := by
    show m a⁻¹ = 1
    have h := hm.map_mul a a⁻¹
    rw [mul_inv_cancel, show m a = 1 from ha, one_mul] at h
    have h1 := hm.map_mul 1 1
    rw [mul_one] at h1
    have hp := hm.pos 1
    have : m 1 = 1 := by nlinarith
    rw [← h, this]


variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma elem_eval_continuous (e : ElemGroup m n r s d) :
    Continuous fun g : ElemSchwartz m n r s d => g.toFun e := by
  obtain ⟨x, z, a, b⟩ := e
  choose t ht using fun j => QuotientAddGroup.mk_surjective (z j)
  have hz : (fun j => ((t j : ℝ) : UnitAddCircle)) = z := funext ht
  let q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)) := (a, b, (x, t))
  have h0 : Continuous (fun (g : ElemSchwartz m n r s d) (p : ℕ × ℕ × ℕ) =>
      UniformFun.ofFun
        (fun q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)) := continuous_induced_dom
  have hc : Continuous fun g : ElemSchwartz m n r s d =>
      (‖q.1‖ ^ (0:ℕ) * ‖q.2.2.1‖ ^ (0:ℕ)) • iteratedFDeriv ℝ 0 (elemLift g.toFun q.1 q.2.1) q.2.2 :=
    ((UniformFun.uniformContinuous_eval _ q).continuous.comp
      (continuous_apply ((0, 0, 0) : ℕ × ℕ × ℕ))).comp h0
  have he : (fun g : ElemSchwartz m n r s d => g.toFun (x, z, a, b)) = fun g =>
      ((‖q.1‖ ^ (0:ℕ) * ‖q.2.2.1‖ ^ (0:ℕ)) • iteratedFDeriv ℝ 0 (elemLift g.toFun q.1 q.2.1) q.2.2)
        (fun _ => 0) := by
    funext g
    rw [ContinuousMultilinearMap.smul_apply, iteratedFDeriv_zero_apply]
    simp only [pow_zero, mul_one, one_smul, q, elemLift]
    rw [hz]
  rw [he]
  exact (continuous_eval_const (fun _ => (0 : (Fin m → ℝ) × (Fin n → ℝ)))).comp hc

end MasulloGRHWMemAux

open MasulloGRH PullbackAux MasulloGRHWMemAux in
lemma sb_eval_continuous {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (x : H) : Continuous fun F : SchwartzBruhat H => F.toFun x := by
  classical
  let E : SchwartzBruhat H →ₗ[ℂ] ULift.{u} ℂ :=
    { toFun := fun F => ULift.up (F.toFun x), map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
  have hlc : IsLocallyConvexTopology (ULift.{u} ℂ) inferInstance :=
    lc_of_ws _ (norm_withSeminorms ℂ (ULift.{u} ℂ))
  suffices hE : Continuous E from continuous_uliftDown.comp hE
  refine sb_continuous_of_ofElem hlc E fun Γ k m n r s d π hs hπ => ?_
  by_cases hx : x ∈ Γ
  · have : (fun g => E (SchwartzBruhat.ofElem Γ k π hs hπ g)) =
        fun g : ElemSchwartz m n r s d => ULift.up (g.toFun (Multiplicative.toAdd (π ⟨x, hx⟩))) := by
      funext g
      show ULift.up (extendPullback Γ π g.toFun x) = _
      unfold extendPullback; rw [dif_pos hx]
    rw [this]; exact continuous_uliftUp.comp (elem_eval_continuous _)
  · have : (fun g => E (SchwartzBruhat.ofElem Γ k π hs hπ g)) = fun _ => ULift.up 0 := by
      funext g
      show ULift.up (extendPullback Γ π g.toFun x) = _
      unfold extendPullback; rw [dif_neg hx]
    rw [this]; exact continuous_const

open MasulloGRH PullbackAux MasulloGRHWMemAux ElemContAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k)
    (J : Set ℝ) (hJ : J ⊆ I) (hbet : ∀ a ∈ I, ∃ a₁ ∈ J, ∃ a₂ ∈ J, a₁ ≤ a ∧ a ≤ a₂) :
    IsClosed (Set.range fun (y : ExpDecayStage G m I k) (j : ULift.{u} J) =>
      ExpDecaySchwartz.weighted k (j.down : ℝ) y.1) := by
  classical
  haveI : IsClosed (k : Set G) := hk.1
  obtain ⟨c, hc⟩ := hne
  obtain ⟨j₀, hj₀, -, -, -, -⟩ := hbet c hc
  let J₀ : ULift.{u} J := ⟨⟨j₀, hj₀⟩⟩
  have hm1 : ∀ h ∈ k, m h = 1 := by
    intro h hh
    exact (isCompact_moduleKernel_and_compact_le G m hm (modKer hm.1) (fun g => Iff.rfl)).2
      k (isCompact_of_isGoodSubgroup G k hk) hh
  have hμmk : ∀ g : G, m (QuotientGroup.mk g : G ⧸ k).out = m g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul k g
    rw [hh, hm.1.map_mul, hm1 h h.2, mul_one]
  have hpos : ∀ g, 0 < m g := hm.1.pos
  have hW : ∀ (b : ℝ) (hb : b ∈ I) (y : ExpDecayStage G m I k),
      (ExpDecaySchwartz.weighted k b y.1).1 =
        fun x : G ⧸ k => ((m x.out ^ b : ℝ) : ℂ) * y.1.toFun x.out := by
    intro b hb y
    have hmem := expDecayStage_weighted_mem G m hm I hI ⟨c, hc⟩ k hk y b hb
    unfold ExpDecaySchwartz.weighted
    first | (erw [dif_pos hmem]) | (rw [dif_pos hmem]) | simp only [dif_pos hmem]
  have hrp : ∀ (t : ℝ), 0 < t → ∀ u v : ℝ, t ^ u * t ^ v = t ^ (u + v) := fun t ht u v =>
    (Real.rpow_add ht u v).symm
  -- the closed set
  let S : Set (ULift.{u} J → SchwartzBruhat (G ⧸ k)) := {F | ∀ (j : ULift.{u} J) (x : G ⧸ k),
    (F j).toFun x = ((m x.out ^ ((j.down : ℝ) - j₀) : ℝ) : ℂ) * (F J₀).toFun x}
  have hSc : IsClosed S := by
    have : S = ⋂ (j : ULift.{u} J) (x : G ⧸ k), {F | (F j).toFun x =
        ((m x.out ^ ((j.down : ℝ) - j₀) : ℝ) : ℂ) * (F J₀).toFun x} := by
      ext F; simp [S]
    rw [this]
    refine isClosed_iInter fun j => isClosed_iInter fun x => isClosed_eq ?_ ?_
    · exact (sb_eval_continuous x).comp (continuous_apply j)
    · exact continuous_const.mul ((sb_eval_continuous x).comp (continuous_apply J₀))
  suffices hR : Set.range (fun (y : ExpDecayStage G m I k) (j : ULift.{u} J) =>
      ExpDecaySchwartz.weighted k (j.down : ℝ) y.1) = S by rw [hR]; exact hSc
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩ j x
    show (ExpDecaySchwartz.weighted k (j.down : ℝ) y.1).1 x =
      _ * (ExpDecaySchwartz.weighted k (J₀.down : ℝ) y.1).1 x
    rw [hW _ (hJ j.down.2), hW _ (hJ hj₀)]
    show ((m x.out ^ (j.down : ℝ) : ℝ) : ℂ) * _ = ((m x.out ^ ((j.down : ℝ) - j₀) : ℝ) : ℂ) *
      (((m x.out ^ j₀ : ℝ) : ℂ) * _)
    rw [← mul_assoc, ← Complex.ofReal_mul, hrp _ (hpos _)]
    congr 3 <;> ring
  · intro F hF
    obtain ⟨P, hP⟩ := schwartzBruhat_pullback_mk G k hk
    have hPF : ∀ j, (fun g : G => (F j).toFun (QuotientGroup.mk g)) ∈ schwartzBruhatSubmodule G := by
      intro j
      have := (P (F j)).2
      convert this using 1
      funext z; exact (hP (F j) z).symm
    let φ : G → ℂ := fun g => ((m g ^ (-j₀) : ℝ) : ℂ) * (F J₀).toFun (QuotientGroup.mk g)
    have hφc : Continuous φ := by
      refine (Complex.continuous_ofReal.comp ?_).mul (sb_fun_continuous _ (hPF J₀))
      exact hm.1.continuous.rpow_const fun g => Or.inl (hpos g).ne'
    have hφJ : ∀ j : ULift.{u} J, (fun g => ((m g ^ (j.down : ℝ) : ℝ) : ℂ) * φ g) =
        fun g => (F j).toFun (QuotientGroup.mk g) := by
      intro j
      funext g
      rw [hF j (QuotientGroup.mk g), hμmk]
      show _ * (((m g ^ (-j₀) : ℝ) : ℂ) * _) = _
      rw [← mul_assoc, ← Complex.ofReal_mul, hrp _ (hpos _)]
      congr 3 <;> ring
    have hφa : ∀ a ∈ I, (fun g => ((m g ^ a : ℝ) : ℂ) * φ g) ∈ schwartzBruhatSubmodule G := by
      intro a ha
      obtain ⟨a₁, ha₁, a₂, ha₂, hle₁, hle₂⟩ := hbet a ha
      obtain ⟨M, hM⟩ := schwartzBruhat_modulus_multiplier G m hm.1.continuous hpos hm.1.map_mul
        (a₁ - a) (a₂ - a) (by linarith) (by linarith)
      let j₁ : ULift.{u} J := ⟨⟨a₁, ha₁⟩⟩
      let j₂ : ULift.{u} J := ⟨⟨a₂, ha₂⟩⟩
      let f₁ : SchwartzBruhat G := ⟨_, hPF j₁⟩
      let f₂ : SchwartzBruhat G := ⟨_, hPF j₂⟩
      convert (M (f₁ + f₂)).2 using 1
      funext g
      have h := hM (f₁ + f₂) g
      show _ = (M (f₁ + f₂)).toFun g
      rw [h]
      show _ = _ * ((F j₁).toFun (QuotientGroup.mk g) + (F j₂).toFun (QuotientGroup.mk g))
      rw [← congrFun (hφJ j₁) g, ← congrFun (hφJ j₂) g]
      have ht := hpos g
      show ((m g ^ a : ℝ) : ℂ) * φ g = ((m g ^ (a₁ - a) + m g ^ (a₂ - a) : ℝ)⁻¹ : ℂ) *
        (((m g ^ a₁ : ℝ) : ℂ) * φ g + ((m g ^ a₂ : ℝ) : ℂ) * φ g)
      have e1 : m g ^ a₁ = m g ^ (a₁ - a) * m g ^ a := by rw [hrp _ ht]; ring_nf
      have e2 : m g ^ a₂ = m g ^ (a₂ - a) * m g ^ a := by rw [hrp _ ht]; ring_nf
      have hS : (m g ^ (a₁ - a) + m g ^ (a₂ - a) : ℝ) ≠ 0 := by
        have := Real.rpow_pos_of_pos ht (a₁ - a)
        have := Real.rpow_pos_of_pos ht (a₂ - a)
        linarith
      have hS' : ((m g ^ (a₁ - a) + m g ^ (a₂ - a) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hS
      rw [e1, e2]
      push_cast at hS' ⊢
      field_simp
    have hφmem : φ ∈ expDecaySubmodule G m I := Submodule.subset_span ⟨hφc, hφa⟩
    let φ' : ExpDecaySchwartz G m I := ⟨φ, hφmem⟩
    have hφinv : φ' ∈ expDecayInvSubmodule G m I k := by
      intro h hh g
      show φ (g * h) = φ g
      simp only [φ]
      rw [hm.1.map_mul, hm1 h hh, mul_one, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff h).2 hh, mul_one]
    refine ⟨⟨φ', hφinv⟩, ?_⟩
    funext j
    apply Subtype.ext
    refine (hW _ (hJ j.down.2) ⟨φ', hφinv⟩).trans ?_
    funext x
    have h1 := congrFun (hφJ j) x.out
    show ((m x.out ^ (j.down : ℝ) : ℝ) : ℂ) * φ x.out = (F j).toFun x
    rw [h1, QuotientGroup.out_eq']

-- Prove2me | solution 1 for MonotoneLight.isClosed_fiberRel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:31.22048+00:00
-- url     : https://prove2.me/submissions/afaaef59-e260-4f7a-ab29-ede5d8b203f7

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
section
@[expose] public section
open Set Function Topology
universe u v
namespace MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
private theorem fiber_pair_separation [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) {x y : X}
    (he : f y = f x) (hn : ¬ FiberRel f x y) :
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬ FiberRel f a b := by
  let F := f ⁻¹' {f x}
  have hF : IsClosed F := isClosed_singleton.preimage hf
  have : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let a : F := ⟨x, rfl⟩
  let b : F := ⟨y, he⟩
  have hb : b ∉ connectedComponent a := by
    intro hb
    apply hn
    rw [FiberRel, connectedComponentIn_eq_image (show x ∈ F from rfl)]
    exact ⟨b, hb, rfl⟩
  rw [connectedComponent_eq_iInter_isClopen] at hb
  simp only [mem_iInter, Subtype.forall, not_forall] at hb
  obtain ⟨s, hs, hbs⟩ := hb
  have hsc : IsClosed (Subtype.val '' s : Set X) :=
    (hs.1.isClosed.isCompact.image continuous_subtype_val).isClosed
  have htc : IsClosed (Subtype.val '' sᶜ : Set X) :=
    (hs.1.compl.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hdis : Disjoint (Subtype.val '' s : Set X) (Subtype.val '' sᶜ) := by
    exact disjoint_image_of_injective Subtype.val_injective disjoint_compl_right
  obtain ⟨U, V, hU, hV, hsU, htV, hUV⟩ := normal_separation hsc htc hdis
  have hcover : F ⊆ U ∪ V := by
    intro z hz
    by_cases hzs : (⟨z, hz⟩ : F) ∈ s
    · exact Or.inl (hsU ⟨⟨z, hz⟩, hzs, rfl⟩)
    · exact Or.inr (htV ⟨⟨z, hz⟩, hzs, rfl⟩)
  let W := (f '' (U ∪ V)ᶜ)ᶜ
  have hW : IsOpen W := (hf.isClosedMap _ (hU.union hV).isClosed_compl).isOpen_compl
  have hxW : f x ∈ W := by
    rintro ⟨z, hz, hze⟩
    exact hz (hcover hze)
  have hfull : f ⁻¹' W ⊆ U ∪ V := by
    intro z hz
    by_contra h
    exact hz ⟨z, h, rfl⟩
  refine ⟨U ∩ f ⁻¹' W, V ∩ f ⁻¹' W, hU.inter (hW.preimage hf),
    hV.inter (hW.preimage hf), ⟨hsU ⟨a, hs.2, rfl⟩, hxW⟩,
    ⟨htV ⟨b, hbs, rfl⟩, show f y ∈ W by rw [he]; exact hxW⟩, ?_⟩
  rintro p ⟨hpU, hpW⟩ q ⟨hqV, _⟩ hpq
  have hc : connectedComponentIn (f ⁻¹' {f p}) p ⊆ U ∪ V := by
    intro z hz
    apply hfull
    change f z ∈ W
    rw [connectedComponentIn_subset _ _ hz]
    exact hpW
  have hd := isPreconnected_connectedComponentIn.subset_or_subset hU hV hUV hc
  rcases hd with hd | hd
  · exact disjoint_left.mp hUV (hd hpq) hqV
  · exact disjoint_left.mp hUV hpU (hd (mem_connectedComponentIn rfl))
end MonotoneLight
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
namespace MonotoneLight
theorem _root_.solution [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) : IsClosed {p : X × X | FiberRel f p.1 p.2} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨x, y⟩ hn
  by_cases he : f y = f x
  · obtain ⟨A, B, hA, hB, hx, hy, hab⟩ := fiber_pair_separation hf he hn
    exact Filter.mem_of_superset ((hA.prod hB).mem_nhds ⟨hx, hy⟩)
      (fun p hp => hab p.1 hp.1 p.2 hp.2)
  · have ho : IsOpen {p : X × X | f p.2 ≠ f p.1} :=
      (isClosed_eq (hf.comp continuous_snd) (hf.comp continuous_fst)).isOpen_compl
    exact Filter.mem_of_superset (ho.mem_nhds he) (fun p hp hr => hp hr.map_eq)
end MonotoneLight

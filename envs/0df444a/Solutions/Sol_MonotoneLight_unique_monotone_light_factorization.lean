-- Prove2me | solution 1 for MonotoneLight.unique_monotone_light_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:42:23.162919+00:00
-- url     : https://prove2.me/submissions/eabc0d73-a542-484f-9cd3-89da9a9d644b

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
public import Theorems.Thm_MonotoneLight_light_monotone
attribute [local simp] MonotoneLight.light_monotone
section
@[expose] public section
open Set Function Topology
universe u v
namespace MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
omit [TopologicalSpace Y] in
private theorem kernel_of_factorization {Z : Type*} [_tZ : TopologicalSpace Z]
    {f : X → Y} {m : X → Z} {l : Z → Y} (hm : Continuous m) (he : f = l ∘ m)
    (hmc : ∀ z, IsConnected (m ⁻¹' {z}))
    (hl : ∀ y, IsTotallyDisconnected (l ⁻¹' {y})) (x y : X) :
    FiberRel f x y ↔ m x = m y := by
  constructor
  · intro hxy
    let C := connectedComponentIn (f ⁻¹' {f x}) x
    have hc : IsPreconnected (m '' C) :=
      isPreconnected_connectedComponentIn.image m hm.continuousOn
    have hsub : m '' C ⊆ l ⁻¹' {f x} := by
      rintro z ⟨a, ha, rfl⟩
      change l (m a) = f x
      exact (congrFun he a).symm.trans
        (show f a ∈ ({f x} : Set Y) from
          connectedComponentIn_subset (f ⁻¹' {f x}) x ha)
    exact hl (f x) (m '' C) hsub hc
      ⟨x, mem_connectedComponentIn rfl, rfl⟩ ⟨y, hxy, rfl⟩
  · intro hxy
    have hs : m ⁻¹' {m x} ⊆ f ⁻¹' {f x} := by
      intro a ha
      change m a = m x at ha
      change f a = f x
      rw [he]
      exact congrArg l ha
    exact (hmc (m x)).2.subset_connectedComponentIn rfl hs hxy.symm
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
theorem _root_.solution [_cX : CompactSpace X] [_hX : T2Space X]
    [_cY : CompactSpace Y] [_hY : T2Space Y]
    {Z W : Type*} [_tZ : TopologicalSpace Z] [_tW : TopologicalSpace W]
    [_cZ : CompactSpace Z] [_hZ : T2Space Z] [_cW : CompactSpace W] [_hW : T2Space W]
    {f : X → Y} {m : X → Z} {l : Z → Y} {n : X → W} {k : W → Y}
    (hm : Continuous m) (hn : Continuous n) (hms : Surjective m) (hns : Surjective n)
    (hfm : f = l ∘ m) (hfn : f = k ∘ n)
    (hmc : ∀ z, IsConnected (m ⁻¹' {z})) (hnc : ∀ w, IsConnected (n ⁻¹' {w}))
    (hl : ∀ y, IsTotallyDisconnected (l ⁻¹' {y}))
    (hk : ∀ y, IsTotallyDisconnected (k ⁻¹' {y})) :
    ∃! h : Z ≃ₜ W, (fun x => h (m x)) = n ∧ l = k ∘ h := by
  classical
  have hker : ∀ x y, m x = m y ↔ n x = n y := fun x y =>
    (kernel_of_factorization hm hfm hmc hl x y).symm.trans
      (kernel_of_factorization hn hfn hnc hk x y)
  let g : Z → W := fun z => n (Classical.choose (hms z))
  have hgm : ∀ x, g (m x) = n x := by
    intro x
    exact (hker _ x).mp (Classical.choose_spec (hms (m x)))
  have hgcomp : g ∘ m = n := funext hgm
  have hgc : Continuous g :=
    (IsQuotientMap.of_surjective_continuous hms hm).continuous_iff.mpr (hgcomp ▸ hn)
  have hgi : Injective g := by
    intro z w hzw
    obtain ⟨x, rfl⟩ := hms z
    obtain ⟨y, rfl⟩ := hms w
    apply (hker x y).mpr
    simpa only [hgm] using hzw
  have hgs : Surjective g := by
    intro w
    obtain ⟨x, rfl⟩ := hns w
    exact ⟨m x, hgm x⟩
  let e : Z ≃ W := Equiv.ofBijective g ⟨hgi, hgs⟩
  let h : Z ≃ₜ W := Continuous.homeoOfEquivCompactToT2 (f := e) hgc
  have hhm : ∀ x, h (m x) = n x := hgm
  have hlk : l = k ∘ h := by
    funext z
    obtain ⟨x, rfl⟩ := hms z
    change l (m x) = k (h (m x))
    rw [hhm]
    exact (congrFun hfm x).symm.trans (congrFun hfn x)
  refine ⟨h, ⟨funext hhm, hlk⟩, ?_⟩
  intro h' hh'
  apply Homeomorph.ext
  intro z
  obtain ⟨x, rfl⟩ := hms z
  exact (congrFun hh'.1 x).trans (hhm x).symm
end MonotoneLight

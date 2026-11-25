-- Prove2me | solution 1 for MonotoneLight.middle_t2Space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:46:48.189505+00:00
-- url     : https://prove2.me/submissions/a12f67d4-a194-45ee-9436-61d068d4b94d

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
public import Theorems.Thm_MonotoneLight_isClosed_fiberRel
public import Theorems.Thm_MonotoneLight_monotone_eq_iff
public import Theorems.Thm_MonotoneLight_surjective_monotone
public import Theorems.Thm_MonotoneLight_isClosedMap_monotone

set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
namespace MonotoneLight
theorem _root_.solution [_cX : CompactSpace X] [_hX : T2Space X] [_hY : T2Space Y]
    {f : X → Y} (hf : Continuous f) : T2Space (Middle f) := by
  have hm := isClosedMap_monotone hf
  have hqc : ∀ q : Middle f, IsClosed (monotone f ⁻¹' {q}) := by
    intro q
    obtain ⟨x, rfl⟩ := surjective_monotone f q
    have hc : IsClosed {z : X | FiberRel f x z} :=
      (isClosed_fiberRel hf).preimage
        (show Continuous (fun z : X => (x, z)) from continuous_const.prodMk continuous_id)
    convert hc using 1
    ext z
    exact (monotone_eq_iff.trans ⟨(fiberSetoid f).symm, (fiberSetoid f).symm⟩)
  refine ⟨fun q r hqr => ?_⟩
  have hd : Disjoint (monotone f ⁻¹' {q}) (monotone f ⁻¹' {r}) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hqr (hx.symm.trans hy)
  obtain ⟨U, V, hU, hV, hqU, hrV, hUV⟩ := normal_separation (hqc q) (hqc r) hd
  refine ⟨kernImage (monotone f) U, kernImage (monotone f) V,
    isClosedMap_iff_kernImage.mp hm hU, isClosedMap_iff_kernImage.mp hm hV,
    hqU, hrV, ?_⟩
  apply disjoint_left.mpr
  intro z hzU hzV
  obtain ⟨x, rfl⟩ := surjective_monotone f z
  exact disjoint_left.mp hUV (hzU rfl) (hzV rfl)
end MonotoneLight
